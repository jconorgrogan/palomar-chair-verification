"""Exact reviewed fingerprint functions, no fixture or guard-mode entrypoint."""
import sys, os
def reject_bytecode(event, args):
    # -B prevents cache writes, not reads. Install before any fixture or ordinary
    # stdlib imports. FileNotFoundError preserves normal source-loader fallback;
    # marshal is not globally disabled and official stdlib source is unmodified.
    if event == 'open' and args and isinstance(args[0], (str, bytes, os.PathLike)):
        if os.fsdecode(args[0]).endswith(('.pyc', '.pyo')):
            raise FileNotFoundError('smoke bytecode reads are permanently forbidden')
sys.addaudithook(reject_bytecode)
import hashlib, importlib, json, stat, sysconfig
from pathlib import Path
def need(ok,message):
    if not ok:raise ValueError(message)

def raw(path,pin=None):
    path=Path(path);need(path.is_absolute() and '..' not in path.parts,'absolute source path')
    for item in (path,*path.parents):need(not item.is_symlink(),'source symlink')
    st=path.lstat();need(stat.S_ISREG(st.st_mode) and st.st_nlink==1 and not st.st_mode&0o022 and st.st_size<=64*1024**2,'single-link nonshared source')
    fd=os.open(path,os.O_RDONLY|os.O_NOFOLLOW)
    try:
        stable=lambda v:(v.st_dev,v.st_ino,v.st_size,v.st_mode,v.st_nlink,v.st_uid,v.st_gid,v.st_mtime_ns,v.st_ctime_ns)
        need(stable(os.fstat(fd))==stable(st),'source identity changed');data=b''
        while block:=os.read(fd,1024**2):
            data+=block;need(len(data)<=64*1024**2,'bounded source bytes')
        need(stable(os.fstat(fd))==stable(st) and stable(path.lstat())==stable(st),'source changed')
    finally:os.close(fd)
    if pin is not None:need({'bytes':len(data),'sha256':hashlib.sha256(data).hexdigest()}==pin,'source pin mismatch')
    return data

def file_pin(path):
    data=raw(path);return {'bytes':len(data),'sha256':hashlib.sha256(data).hexdigest()}

def fingerprint():
    stdlib=Path(sysconfig.get_path('stdlib')).resolve()
    names=('pathlib','shutil','tarfile','tempfile','dataclasses','inspect','os','posixpath','stat','fractions',
      'importlib','importlib._bootstrap','importlib._bootstrap_external','ctypes','json','json.encoder','json.decoder')
    sources={}
    for name in names:
        module=importlib.import_module(name);path=Path(module.__file__).resolve()
        need(path.is_relative_to(stdlib),'stdlib source escaped trusted root')
        sources[name]={'relative_path':str(path.relative_to(stdlib)),**file_pin(path)}
    extensions={}
    for name in ('_ctypes','_ssl','_hashlib','_posixsubprocess','zlib','_bz2','_lzma','math'):
        module=importlib.import_module(name)
        if getattr(module,'__file__',None):
            path=Path(module.__file__).resolve();need(path.is_relative_to(stdlib),'stdlib extension escaped trusted root')
            extensions[name]={'relative_path':str(path.relative_to(stdlib)),**file_pin(path)}
        else:extensions[name]={'builtin_in_interpreter':True}
    executable=Path('/usr/bin/python3').resolve(strict=True)
    return {'schema':'c087-interpreter-fingerprint-v1','invoked_path':'/usr/bin/python3','executable_realpath':str(executable),
      'executable':file_pin(executable),'sys_version':sys.version,'version_info':list(sys.version_info),
      'implementation':sys.implementation.name,'cache_tag':sys.implementation.cache_tag,'stdlib_root':str(stdlib),
      'stdlib_sources':sources,'stdlib_extensions':extensions}

def main():
    need(sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode, 'fresh isolated source-only interpreter')
    need(len(sys.argv)==1, 'no arguments')
    need(dict(os.environ)=={'LANG':'C.UTF-8','LC_ALL':'C.UTF-8','TZ':'UTC','PWD':str(Path(__file__).resolve().parent)}, 'exact token-free environment')
    need(len(os.sched_getaffinity(0))==1, 'one CPU')
    need(Path(sys.executable).resolve()==Path('/usr/bin/python3').resolve(), 'exact interpreter')
    observed=fingerprint()
    print(json.dumps({'schema':'c087-unapproved-python-fingerprint-v1','runtime_fingerprint':observed,
       'profile_approved':False,'fixtures_executed':False,'guard_modes_executed':False,
       'runtime_installed':False,'proof_pass_claimed':False},sort_keys=True,allow_nan=False),flush=True)
if __name__=='__main__':main()
