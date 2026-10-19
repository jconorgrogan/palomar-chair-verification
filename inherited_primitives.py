#!/usr/bin/env python3
"""Inherited bounded acquisition, capture and collection primitives; no main entry point."""
from __future__ import annotations
import time
ENTRY_TIME = time.monotonic()
import argparse, hashlib, importlib.util, json, os, re, shutil, stat, sys, urllib.request
from pathlib import Path
RAW_FILE = Path(__file__).absolute()
for ancestor in [RAW_FILE,*RAW_FILE.parents]:
    if ancestor.is_symlink():raise RuntimeError('symlink script ancestry')
ROOT = RAW_FILE.parent
VENDOR = ROOT/'vendor/pipeline'
# Before importing trusted helpers: fixed finite file reads only. The eventual
# deadline is measured from ENTRY_TIME, not reset after these checks.
API_SHA = '72d311d1797040e7f9b106792d26b87c6c2b7d9b3a40040af1398e134919cadb'
PREIMPORT_FILES = {'cache_diagnostic.py': {'bytes': 81922, 'sha256': '72d311d1797040e7f9b106792d26b87c6c2b7d9b3a40040af1398e134919cadb'}, 'collect_evidence.py': {'bytes': 22654, 'sha256': '1d6ddba8bc4d29f207da62fb93c1eb226e7dce40269af423f58fb2998840be6a'}, 'conditional_transport.py': {'bytes': 55492, 'sha256': 'd8688bf50ffdd460653a007876798c2adf7a21ed7f7fd0e57b564f7c7021469e'}, 'fresh_stage.py': {'bytes': 50298, 'sha256': '6adfa8e43f8e0997ffef27210c4338d555b203b48ca50cb5c7b7b99ac49991d8'}, 'higher_policy.py': {'bytes': 58899, 'sha256': '5bbb593b97e3e686faa466bd755d5817b0c9d39e5d3ade4d4fd85b3e2f567e8a'}, 'source_header.py': {'bytes': 2551, 'sha256': '3eca76608279cbd7fb659eec960177bed6e7ad4829c5e5636f6ad23636645701'}, 'toolchain_install.py': {'bytes': 6752, 'sha256': '9b8fefa2020be7e58bbf04f79445f603657bd647c0afe0b1196078f92629f038'}}
for name,row in PREIMPORT_FILES.items():
    candidate=VENDOR/'ci'/name
    for ancestor in [candidate,*candidate.parents]:
        if ancestor.is_symlink():raise RuntimeError('symlink helper ancestry')
    st=candidate.lstat()
    if not stat.S_ISREG(st.st_mode) or st.st_nlink!=1 or st.st_size!=row['bytes'] or hashlib.sha256(candidate.read_bytes()).hexdigest()!=row['sha256']:
        raise RuntimeError('fixed helper pre-import identity differs')
p = VENDOR/'ci/cache_diagnostic.py'
for parent in [p,*p.parents]:
    if parent.is_symlink():raise RuntimeError('symlink helper parent')
if p.is_symlink() or p.stat().st_size > 256*1024 or hashlib.sha256(p.read_bytes()).hexdigest() != API_SHA:
    raise RuntimeError('vendored acquisition API identity differs')
spec = importlib.util.spec_from_file_location('visibility_acquisition_api', p)
a = importlib.util.module_from_spec(spec); sys.modules[spec.name] = a; spec.loader.exec_module(a)
f = a.f
GIB = 1024**3


def read_capture(path,maximum,watchdog):
    watchdog.check();f.no_symlink_path(path)
    fd=os.open(path,os.O_RDONLY|os.O_NOFOLLOW|os.O_NONBLOCK)
    def identity(st):return (st.st_dev,st.st_ino,st.st_mode,st.st_nlink,st.st_size,st.st_mtime_ns,st.st_ctime_ns)
    try:
        before=os.fstat(fd);f.need(stat.S_ISREG(before.st_mode) and before.st_nlink==1 and before.st_size<=maximum,'unsafe or oversized probe capture')
        data=bytearray()
        while len(data)<=maximum:
            block=os.read(fd,min(65536,maximum+1-len(data)))
            if not block:break
            data.extend(block)
        after=os.fstat(fd)
        f.need(identity(before)==identity(after) and len(data)==before.st_size,'probe capture changed or short read')
    finally:os.close(fd)
    # Recheck the named file and every parent after the retained descriptor closes.
    f.no_symlink_path(path);f.need(identity(path.lstat())==identity(before),'probe capture named identity changed after close')
    watchdog.check();return bytes(data)

def clean_command(r):
    flags=['timed_out','log_overflow','memory_exceeded','surviving_children','process_group_empty','descendants_empty','escaped_descendants','new_sessions_explicitly_allowed']
    f.need(all(type(r.get(k)) is bool for k in flags) and type(r.get('exit_code')) is int,'native safety receipt scalar types differ')
    return not any(r[k] for k in flags[:4]) and r['process_group_empty'] and r['descendants_empty'] and (not r['escaped_descendants'] or r['new_sessions_explicitly_allowed'])

def acquire_runtime(work, env, command):
    archive=work/'lean.tar.zst'; downloaded=0; start=time.monotonic()
    with urllib.request.urlopen(a.ARCHIVE_URL,timeout=60) as response, archive.open('xb') as out:
        while True:
            block=response.read(1024**2)
            if not block:break
            downloaded+=len(block)
            f.need(downloaded<=a.ARCHIVE_BYTES and time.monotonic()-start<900, 'release download bound')
            out.write(block)
    f.need(downloaded==a.ARCHIVE_BYTES,'official archive size differs')
    runtime=work/'runtime'; inv=a.install_archive(archive,runtime);archive.unlink()
    f.need(f.sha(f.json_bytes(inv))==a.RUNTIME_INVENTORY_SHA,'canonical runtime inventory differs')
    actual={p.relative_to(runtime).as_posix() for p in runtime.rglob('*') if not p.is_dir() or p.is_symlink()}
    f.need(actual==set(inv['files'])|set(inv['symlinks']),'runtime missing/extra entries')
    a.write_json(work/'evidence/runtime-inventory.json',inv)
    env.update(a.safe_env(runtime,work/'home',work/'tmp'))
    env['LEAN_PATH']=str(work/'objects')+':'+str(runtime/'lib/lean')
    command('bwrap-preflight',a.sandbox(['/bin/true'],runtime=runtime,sources=[],writable=[work/'home',work/'tmp'],cwd=work/'tmp',env=env),seconds=30,env=env,allowed_sessions=True)
    a.readonly_boundary_preflight(runtime,work,env,command)
    return runtime

def revalidate_runtime(runtime,inv):
    f.need(f.sha(f.json_bytes(inv))==a.RUNTIME_INVENTORY_SHA,'final runtime inventory pin differs')
    actual={p.relative_to(runtime).as_posix() for p in runtime.rglob('*') if not p.is_dir() or p.is_symlink()}
    f.need(actual==set(inv['files'])|set(inv['symlinks']),'runtime final membership differs')
    for rel,row in inv['files'].items():
        p=runtime/rel;f.no_symlink_path(p)
        f.need(p.stat().st_size==row['bytes'] and f.file_sha(p)==row['sha256'] and stat.S_IMODE(p.stat().st_mode)==row['mode'],'runtime final bytes/mode differ')
    for rel,target in inv['symlinks'].items():
        f.need((runtime/rel).is_symlink() and os.readlink(runtime/rel)==target and (runtime/rel).resolve(strict=True).is_relative_to(runtime),'runtime final symlink differs')

def compile_argv(runtime,source,staging,module):
    rel=module.replace('.','/')
    return [runtime/'bin/lean','-j1','-M4096','-DElab.async=false',
            '-o',staging/(rel+'.olean'),'-i',staging/(rel+'.ilean'),'-c',staging/(rel+'.c'),source/(rel+'.lean')]

def validate_capture_collection(c,work,watchdog):
    names=command_order(c);allowed_logs={name+'.'+stream for name in names for stream in ['stdout','stderr']}
    for directory in ['evidence','logs','native-captures']:
        f.no_symlink_path(work/directory)
    allowed=EVIDENCE_NAMES|{'logs/'+name for name in allowed_logs}
    for p in (work/'evidence').rglob('*'):
        f.need(not p.is_symlink(),'evidence symlink')
        if p.is_dir():f.need(p.relative_to(work/'evidence').as_posix()=='logs','unexpected evidence directory');continue
        st=p.lstat();f.need(stat.S_ISREG(st.st_mode) and st.st_nlink==1 and p.relative_to(work/'evidence').as_posix() in allowed,'unexpected/nonregular evidence member')
    f.need({p.name for p in (work/'logs').glob('*')}<=allowed_logs,'unexpected admitted log')
    f.need({p.name for p in (work/'native-captures').glob('*')}<=allowed_logs,'unexpected native capture')
    commands=[];path=work/'evidence/commands.jsonl'
    if path.exists():
        data=read_capture(path,8*1024**2,watchdog);f.need(data.endswith(b'\n'),'truncated commands')
        commands=[f.parse_json(line) for line in data.splitlines()]
    f.need([r['name'] for r in commands]==names[:len(commands)],'incomplete native command prefix differs')
    selected=[];path=work/'evidence/selected-cache-closure.json'
    if path.exists():selected=f.parse_json(read_capture(path,2*1024**2,watchdog))['modules']
    accepted=set();omitted=[];total=0
    for r in commands:
        validate_command_spec(c,work,r,[x['module'] for x in selected])
        if r['capture_status']!='accepted_bounded_complete':
            omitted.append({'command':r['name'],'reason':'native_captures_not_safety_admitted'});continue
        f.need(clean_command(r),'unsafe capture marked accepted')
        f.need(set(r['captures'])=={'stdout','stderr'},'capture receipt streams differ')
        combined=0
        for stream in ['stdout','stderr']:
            name=r['name']+'.'+stream;row=r['captures'][stream]
            f.need(set(row)=={'bytes','sha256'} and type(row['bytes']) is int and 0<=row['bytes']<=LIMITS['per_command_log_max_bytes'] and f.SHA256.fullmatch(row['sha256']),'capture pin malformed')
            # Raw native captures are never revisited. Only already safety-admitted host copies are read.
            data=read_capture(work/'logs'/name,LIMITS['per_command_log_max_bytes'],watchdog)
            f.need(len(data)==row['bytes'] and f.sha(data)==row['sha256']==r[stream+'_sha256'],'admitted log changed')
            combined+=len(data);accepted.add(name)
        f.need(combined<=LIMITS['per_command_log_max_bytes'],'combined capture overflow');total+=combined
    raw_names={p.name for p in (work/'native-captures').glob('*')}
    for name in names[len(commands):]:
        if any(name+'.'+stream in raw_names for stream in ['stdout','stderr']):
            omitted.append({'command':name,'reason':'native_helper_returned_no_admissible_receipt'})
    f.need({p.name for p in (work/'logs').glob('*')}==accepted,'unadmitted host log')
    for p in (work/'evidence/logs').glob('*'):
        f.need(p.name in accepted,'unadmitted evidence log')
        data=read_capture(p,LIMITS['per_command_log_max_bytes'],watchdog)
        host=read_capture(work/'logs'/p.name,LIMITS['per_command_log_max_bytes'],watchdog)
        f.need(data==host,'evidence log changed from admitted host copy')
    f.need(total<=LIMITS['aggregate_log_max_bytes'],'aggregate admitted log overflow')
    a.write_json(work/'evidence/capture-collection-scope.json',{'native_capture_omissions':omitted,'all_native_captures_admitted':not omitted,'admitted_bytes':total})
    return omitted

def copy_logs(work):
    total=0;dest=work/'evidence/logs';dest.mkdir(exist_ok=True)
    for p in sorted((work/'logs').glob('*')):
        s=p.lstat();f.need(stat.S_ISREG(s.st_mode) and s.st_nlink==1,'nonregular log')
        total+=s.st_size;f.need(total<=LIMITS['aggregate_log_max_bytes']+2*LIMITS['per_command_log_max_bytes'],'interrupted aggregate logs bound')
        q=dest/p.name
        if not q.exists():shutil.copyfile(p,q)
        else:f.need(f.file_sha(q)==f.file_sha(p),'captured log changed')

def collect(c,contract_sha,work,watchdog):
    validate_contract(c)
    f.no_symlink_path(work);(work/'evidence').mkdir(parents=True,exist_ok=True)
    result=work/'evidence/result.json'
    if not result.exists():a.write_json(result,{'status':'INCOMPLETE_BEFORE_RECEIPT','full_official_verification_claimed':False})
    omissions=validate_capture_collection(c,work,watchdog)
    copy_logs(work)
    issue=None;verified=False
    try:verify_success(c,contract_sha,work/'evidence',work);verified=True
    except Exception as error:issue=str(error)
    upload=work/'upload';f.need(not upload.exists(),'upload directory must be new');upload.mkdir()
    rows=[];omitted=[];total=0
    for p in sorted((work/'evidence').rglob('*'),key=lambda p:(p.name!='result.json',p.as_posix())):
        f.need(not p.is_symlink(),'evidence symlink');s=p.lstat()
        if stat.S_ISDIR(s.st_mode):continue
        f.need(stat.S_ISREG(s.st_mode) and s.st_nlink==1,'nonregular evidence')
        f.need(len(rows)+len(omitted)<20000,'evidence count bound');rel=p.relative_to(work/'evidence').as_posix()
        if total+s.st_size>LIMITS['evidence_max_bytes']:omitted.append({'path':rel,'bytes':s.st_size});continue
        q=upload/rel;q.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(p,q);total+=s.st_size
        rows.append({'path':rel,'bytes':s.st_size,'sha256':f.file_sha(q)})
    receipt={'schema':'bounded-root7-import-cut-evidence-v1','files':rows,'omitted':omitted,'bytes_copied':total,
             'all_available_files_copied':not omitted,'smoke_acceptance_evidence_complete':verified and not omitted and not omissions,'native_capture_omissions':omissions,
             'acceptance_blocker':issue,'runner_status':f.load_json(result).get('status'),'full_official_verification_claimed':False}
    data=f.json_bytes(receipt);f.need(len(data)<=LIMITS['collection_reserve_bytes'] and total+len(data)<=LIMITS['upload_max_bytes'],'collection manifest bound')
    (upload/'collection.json').write_bytes(data)
    f.need(not omitted,'evidence collection incomplete')
    f.need(receipt['runner_status']!=SUCCESS or receipt['smoke_acceptance_evidence_complete'],'claimed success has inconsistent evidence')
    print(json.dumps({k:v for k,v in receipt.items() if k not in ['files','omitted']},sort_keys=True))

def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--contract-sha256',required=True);ap.add_argument('--work',type=Path,required=True);ap.add_argument('--collect',action='store_true');args=ap.parse_args()
    f.need(sys.flags.isolated and sys.dont_write_bytecode,'invoke with Python -I -B')
    work=args.work.absolute();f.need(args.work.is_absolute(),'work path must be absolute')
    # Collection has its separate fixed120-second host envelope. Acceptance run
    # includes imports, contract hashing and all host I/O in the7200-second clock.
    watchdog=a.HostDeadline(ENTRY_TIME+(120 if args.collect else 7200));watchdog.arm()
    try:
        c=f.pinned_load(ROOT/'smoke-contract.json',args.contract_sha256)
        if args.collect:collect(c,args.contract_sha256,work,watchdog)
        else:run(c,args.contract_sha256,work,watchdog)
    finally:watchdog.close()
