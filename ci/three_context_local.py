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

def executor_refused(*args,**kwargs):raise Rejected('admission-only executor is disabled')

@contextmanager
def frozen_prior(root,expected_files):
    """Load exactly four pinned historical modules; preserve all source bytes."""
    root=canonical(str(root));need(threading.current_thread() is threading.main_thread() and threading.active_count()==1,'single main thread required')
    def verify():
        expected_ci={k[3:]:v for k,v in expected_files.items() if k.startswith('ci/')}
        need(tree(root/'ci')==expected_ci,'historical CI file inventory changed')
        for name,info in expected_files.items():
            path=root/name
            need(regular(path).st_size==info['bytes'] and file_sha(path)==info['sha256'],'historical checkout file changed')
    verify()
    ci=root/'ci';names=('fresh_stage','original','original.fresh_stage','continuation_policy','continuation_runner')
    prior={name:sys.modules.get(name) for name in names};saved_path=list(sys.path);saved_bytecode=sys.dont_write_bytecode
    loaded={};sys.dont_write_bytecode=True
    try:
        for name in names:sys.modules.pop(name,None)
        package=types.ModuleType('original');package.__path__=[str(ci/'original')];package.__package__='original';sys.modules['original']=package
        for name,relative in [('fresh_stage','fresh_stage.py'),('original.fresh_stage','original/fresh_stage.py'),('continuation_policy','continuation_policy.py'),('continuation_runner','continuation_runner.py')]:
            path=ci/relative;need(file_sha(path)==expected_files['ci/'+relative]['sha256'],'historical module pin changed')
            spec=importlib.util.spec_from_file_location(name,path);module=importlib.util.module_from_spec(spec);sys.modules[name]=module;spec.loader.exec_module(module);loaded[name]=module
            need(Path(module.__file__)==path,'historical module loaded from wrong path')
        runner=loaded['continuation_runner'];f=loaded['fresh_stage'];p=loaded['continuation_policy'];old=loaded['original.fresh_stage']
        need(runner.f is f and runner.p is p and runner.old_f is old and p.f is f,'historical import alias contamination')
        yield types.SimpleNamespace(f=f,p=p,old=old,runner=runner,loaded=loaded)
        verify()
        for name,module in loaded.items():need(sys.modules.get(name) is module,'historical module identity changed')
    finally:
        for name in names:
            if prior[name] is None:sys.modules.pop(name,None)
            else:sys.modules[name]=prior[name]
        sys.path[:]=saved_path;sys.dont_write_bytecode=saved_bytecode

@contextmanager
def admission_only_guard(runtime_root,modules,check_budget=lambda:None):
    """Trap execution and runtime-file access without editing frozen validators."""
    runtime=canonical(str(runtime_root));need(runtime.is_dir() and not list(runtime.iterdir()),'runtime placeholder must be empty')
    need(sys.getprofile() is None and threading.active_count()==1,'unexpected profiler or thread')
    state={'active':True};files={str(Path(m.__file__)) for m in modules}
    forbidden={'subprocess.Popen','os.system','os.exec','os.posix_spawn','socket.__new__','socket.connect','ctypes.dlopen'}
    def audit(event,args):
        if not state['active']:return
        if event=='open':check_budget()
        need(event not in forbidden and not event.startswith(('socket.','subprocess.','os.exec','os.spawn','os.posix_spawn','os.fork')),'admission-only process/network/native execution forbidden')
        if event=='open' and args and isinstance(args[0],(str,bytes,os.PathLike)):
            value=os.fsdecode(args[0]);path=Path(os.path.abspath(value))
            need(path!=runtime and runtime not in path.parents,'runtime file access forbidden in inventory-only admission')
    def profile(frame,event,arg):
        if event=='call' and frame.f_code.co_filename in files and frame.f_code.co_name in {'read_artifacts','_receipt_envelope','verify_checked_objects','imported','file_sha','extract_verified_archive'}:check_budget()
        if event=='call' and frame.f_code.co_filename in files and frame.f_code.co_name in {'command','run','run_process','cli'}:
            raise Rejected('historical execution entrypoint forbidden during admission')
    sys.addaudithook(audit);sys.setprofile(profile)
    try:yield audit
    finally:sys.setprofile(None);state['active']=False
