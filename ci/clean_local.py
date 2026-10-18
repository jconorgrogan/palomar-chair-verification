"""Local-only immutable file and native-validator loading boundaries."""
from __future__ import annotations
from contextlib import contextmanager
from pathlib import Path
import hashlib, importlib.util, json, os, stat, sys, threading, types

class Rejected(ValueError): pass

def need(value, message):
    if not value: raise Rejected(message)

def json_bytes(value): return (json.dumps(value,sort_keys=True,indent=2,allow_nan=False)+'\n').encode()
def sha(data): return hashlib.sha256(data).hexdigest()
def parse(raw):
    def pairs(items):
        result={}
        for key,value in items:
            need(key not in result,'duplicate JSON key');result[key]=value
        return result
    return json.loads(raw,object_pairs_hook=pairs,parse_constant=lambda _:(_ for _ in ()).throw(Rejected('nonfinite JSON')))
def canonical(value):
    need(type(value) is str and value.startswith('/') and str(Path(value))==value and '..' not in Path(value).parts,'noncanonical absolute path')
    path=Path(value)
    for part in [path,*path.parents]:
        need(not part.is_symlink(),'symlink path forbidden')
    return path

def regular(path):
    path=canonical(str(path));s=path.lstat()
    need(stat.S_ISREG(s.st_mode) and s.st_nlink==1,'regular single-link file required')
    return s

def file_sha(path):
    regular(path);h=hashlib.sha256()
    with path.open('rb') as stream:
        for block in iter(lambda:stream.read(1024**2),b''):h.update(block)
    return h.hexdigest()
def read_pinned(path,digest,maximum=32*1024**2):
    need(regular(path).st_size<=maximum,'input exceeds byte cap');raw=path.read_bytes()
    need(sha(raw)==digest,'pinned bytes changed');return raw

def tree(root):
    canonical(str(root));need(root.is_dir(),'directory required');out={}
    for path in sorted(root.rglob('*')):
        need(not path.is_symlink(),'tree symlink forbidden')
        if path.is_dir():continue
        s=regular(path);out[path.relative_to(root).as_posix()]={'bytes':s.st_size,'sha256':file_sha(path)}
    directories={str(p) for name in out for p in Path(name).parents if str(p)!='.'}
    actual={p.relative_to(root).as_posix() for p in root.rglob('*') if p.is_dir()}
    need(actual==directories,'unexpected empty directory')
    return out

def durable(path,raw):
    canonical(str(path));need(not path.exists(),'durable output must be new')
    with path.open('xb') as stream:stream.write(raw);stream.flush();os.fsync(stream.fileno())
    need(file_sha(path)==sha(raw),'durable write readback mismatch')
    fd=os.open(path.parent,os.O_RDONLY|os.O_DIRECTORY)
    try:os.fsync(fd)
    finally:os.close(fd)

