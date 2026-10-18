#!/usr/bin/env python3
"""One early official-runtime heap-option observation; no project restore or proof claim."""
from __future__ import annotations
import argparse,hashlib,importlib.util,json,os,re,stat,sys,time,urllib.request
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
CACHE_HELPER_SHA='3bb36711ba6ae605e95bab9536e18665f1a492f0f7b36ba01bfa2ceb9588fd61'
helper=ROOT/'ci/cache_diagnostic.py'
if helper.is_symlink() or hashlib.sha256(helper.read_bytes()).hexdigest()!=CACHE_HELPER_SHA:
    raise RuntimeError('retained probe helper identity differs')
spec=importlib.util.spec_from_file_location('cache_diagnostic',helper)
a=importlib.util.module_from_spec(spec);sys.modules['cache_diagnostic']=a;spec.loader.exec_module(a)
f=a.f
GIB=1024**3
FIXED={'schema':'higher-heap-runtime-probe-v1','purpose':'compiled-default-and-max_memory-override-only',
 'publication_branch':'verify/higher-heap-probe-20261018','publication_parent_commit':'ecf44513ecddd29507fec9f6046d47771fd6e0cd',
 'workflow_path':'.github/workflows/higher-heap-probe.yml','workflow_job':'heap_option_probe',
 'official_archive_url':a.ARCHIVE_URL,'official_archive_bytes':a.ARCHIVE_BYTES,'official_archive_sha256':f.TOOLCHAIN_SHA256,
 'official_runtime_inventory_sha256':a.RUNTIME_INVENTORY_SHA,'lean_heap_mib':5120,
 'probe_address_space_bytes':24*GIB,'preflight_address_space_bytes':12*GIB,'rss_tree_bytes':8*GIB,
 'max_created_file_bytes':512*1024**2,'per_command_log_max_bytes':1024**2,'aggregate_log_max_bytes':2*1024**2,
 'aggregate_command_deadline_seconds':1800,'outer_timeout_minutes':35,'download_timeout_seconds':900,
 'preflight_timeout_seconds':30,'probe_timeout_seconds':600,'failure_evidence_grace_seconds':5,
 'evidence_max_bytes':124*1024**2,'native_command_count':2,'project_modules_recompiled':0,
 'project_restore':False,'predecessor_acquisition':False,'proof_certified':False,
 'source_diagnosis_sha256':'48685c5fb4e184937771ea6191704d7b04ef2e77948e4170e0e37498b6ff5559',
 'failed_heap5120_terminal_review_sha256':'fb9c28a8f31be7e8a096e8669501f9516ee58960694fdfa976bb5cd172b367e7',
 'accessor_source_binding_sha256':'9dff679e6128c10df0976782ea6af487e3bc040291c5eb498c77bc9a6c8bbb58'}
INPUT_PATHS={'ci/cache_diagnostic.py',*('ci/'+n for n in a.HELPERS),
 'probe/heap_probe.py','probe/HeapProbe.lean','probe/README.md',
 'probe/provenance/SOURCE_DIAGNOSIS.json','probe/provenance/FAILED_TERMINAL_REVIEW.json',
 'probe/provenance/ACCESSOR_SOURCE_BINDING.json','probe/provenance/Options.lean','probe/provenance/KVMap.lean',
 'origin/lean-memory/Shell.lean'}
PROVENANCE={'probe/provenance/SOURCE_DIAGNOSIS.json':FIXED['source_diagnosis_sha256'],
 'probe/provenance/FAILED_TERMINAL_REVIEW.json':FIXED['failed_heap5120_terminal_review_sha256'],
 'probe/provenance/ACCESSOR_SOURCE_BINDING.json':FIXED['accessor_source_binding_sha256'],
 'probe/provenance/Options.lean':'ea52d63ede2afb64ea83f199fbe8c778fdb5991683f98dccd2ff6e345dbaa1e9',
 'probe/provenance/KVMap.lean':'41b05306978e2acf64a482d7521958ee73bbee345e8af45530e23cab7867730e',
 'origin/lean-memory/Shell.lean':'bbfcf01a93bcb9ca3f4d1264d3ad9890f3a6384dbbc949f5bf3cc286c0ec2225'}
STDOUT=re.compile(rb'LEAN_HEAP_PROBE_V1 default_mib=(0|[1-9][0-9]{0,19}) override=(absent|other|nat:(0|[1-9][0-9]{0,19}))\n\Z')

def parse_stdout(data):
    f.need(type(data) is bytes and len(data)<=160,'probe stdout bound/type differs')
    m=STDOUT.fullmatch(data);f.need(m is not None,'probe stdout grammar differs')
    default=int(m[1]);value=int(m[3]) if m[3] is not None else None
    f.need(default<2**64 and (value is None or value<2**64),'probe scalar exceeds fixed uint64 bound')
    kind='natural' if m[2].startswith(b'nat:') else m[2].decode('ascii')
    return {'compiled_default_mib':default,'override_present':kind!='absent','override_kind':kind,'override_value_mib':value}

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

def read_stdout(path,watchdog):return parse_stdout(read_capture(path,160,watchdog))

def validate_contract(c,*,active=False):
    f.need(set(c)==set(FIXED)|{'review_status','activation_admission','inputs'},'probe contract field set differs')
    for k,v in FIXED.items():f.need(type(c[k]) is type(v) and c[k]==v,'probe fixed profile differs: '+k)
    pending=c['review_status']=='inactive_pending_review';f.need(pending or c['review_status']=='reviewed_for_execution','probe review status differs')
    expected={'schema':'higher-heap-probe-activation-v1','source_review_pending':pending,'diagnostic_only':True}
    if not pending:
        r=c['activation_admission'].get('independent_source_review_sha256');f.need(type(r) is str and f.SHA256.fullmatch(r),'probe review pin missing');expected['independent_source_review_sha256']=r
    f.need(c['activation_admission']==expected and (not active or not pending),'INACTIVE or altered probe admission')
    f.need(set(c['inputs'])==INPUT_PATHS,'probe input member set differs')
    total=0
    for rel,row in c['inputs'].items():
        f.need(set(row)=={'bytes','sha256'} and type(row['bytes']) is int and 0<row['bytes']<=4*1024**2 and type(row['sha256']) is str and f.SHA256.fullmatch(row['sha256']),'probe input pin differs')
        p=ROOT/rel;f.no_symlink_path(p);s=p.lstat();f.need(stat.S_ISREG(s.st_mode) and s.st_nlink==1 and s.st_size==row['bytes'] and f.file_sha(p)==row['sha256'],'probe input bytes differ');total+=s.st_size
    f.need(total<=4*1024**2,'probe input aggregate cap')
    for rel,sha in {**PROVENANCE,'ci/cache_diagnostic.py':CACHE_HELPER_SHA,**{'ci/'+k:v for k,v in a.HELPERS.items()}}.items():f.need(c['inputs'][rel]['sha256']==sha,'fixed source/helper provenance differs')

def checkout_identity(c):
    f.need(os.environ.get('GITHUB_REPOSITORY')=='jconorgrogan/palomar-chair-verification','probe repository differs')
    f.need(os.environ.get('GITHUB_REF')=='refs/heads/'+c['publication_branch'],'probe branch differs')
    sha=os.environ.get('GITHUB_SHA','');f.need(f.COMMIT.fullmatch(sha),'probe commit malformed')
    f.need(a.git_capture(ROOT,'rev-parse','HEAD').decode().strip()==sha,'probe checkout commit differs')
    f.need(not a.git_capture(ROOT,'status','--porcelain=v1','--untracked-files=all','--ignored'),'probe checkout not clean')
    run=os.environ.get('GITHUB_RUN_ID','');attempt=os.environ.get('GITHUB_RUN_ATTEMPT','')
    f.need(re.fullmatch(r'[1-9][0-9]{0,19}',run) and re.fullmatch(r'[1-9][0-9]{0,9}',attempt),'probe run identity malformed')
    return {'repository':'jconorgrogan/palomar-chair-verification','workflow_commit':sha,'run_id':run,'run_attempt':attempt}

def acquire_runtime(work,watchdog):
    archive=work/'lean.tar.zst';downloaded=0;start=time.monotonic();watchdog.check()
    with urllib.request.urlopen(a.ARCHIVE_URL,timeout=60) as response,archive.open('xb') as out:
        while True:
            block=response.read(1024**2)
            if not block:break
            downloaded+=len(block);f.need(downloaded<=a.ARCHIVE_BYTES and time.monotonic()-start<900,'release download bound');out.write(block);watchdog.check()
    f.need(downloaded==a.ARCHIVE_BYTES,'official release size differs')
    runtime=work/'runtime';inventory=a.install_archive(archive,runtime);archive.unlink();watchdog.check()
    f.need(f.sha(f.json_bytes(inventory))==a.RUNTIME_INVENTORY_SHA,'canonical runtime inventory differs')
    actual={p.relative_to(runtime).as_posix() for p in runtime.rglob('*') if not p.is_dir() or p.is_symlink()}
    f.need(actual==set(inventory['files'])|set(inventory['symlinks']),'runtime member set differs')
    a.write_json(work/'evidence/runtime-inventory.json',inventory);watchdog.check();return runtime

def command_specs(work,runtime):
    env=a.safe_env(runtime,work/'home',work/'tmp');env['LEAN_PATH']=str(runtime/'lib/lean')
    def spec(name,argv,seconds,address_space,sources,cwd):
        return {'name':name,'argv':a.sandbox(argv,runtime=runtime,sources=sources,writable=[work/'home',work/'tmp'],cwd=cwd,env=env),'cwd':str(work),'env':env,'requested_timeout_seconds':seconds,'address_space_bytes':address_space}
    return [spec('bwrap-preflight',['/bin/true'],30,12*GIB,[],work/'tmp'),
            spec('heap-options-probe',[runtime/'bin/lean','-j1','-M5120','--run',work/'probe/HeapProbe.lean'],600,24*GIB,[work/'probe'],work/'probe')]

def capture_safe(r):
    flags=['timed_out','log_overflow','memory_exceeded','surviving_children','process_group_empty','descendants_empty','escaped_descendants','new_sessions_explicitly_allowed']
    f.need(all(type(r.get(k)) is bool for k in flags) and type(r.get('exit_code')) is int,'native safety receipt scalar types differ')
    return not any(r[k] for k in flags[:4]) and r['process_group_empty'] and r['descendants_empty'] and (not r['escaped_descendants'] or r['new_sessions_explicitly_allowed'])

def command_ok(r):return capture_safe(r) and r['exit_code']==0

def execute_probe(c,work,identity,contract_sha,watchdog):
    f.no_symlink_path(work);f.need(not work.exists(),'probe workspace must be new');work.mkdir()
    for name in ['logs','native-captures','evidence','home','tmp','probe']:(work/name).mkdir()
    (work/'probe/HeapProbe.lean').write_bytes((ROOT/'probe/HeapProbe.lean').read_bytes())
    result={'schema':c['schema'],'status':'PROBE_INCOMPLETE','proof_certified':False,'project_modules_recompiled':0,'project_restore':False,'predecessor_acquisition':False,'contract_sha256':contract_sha,'identity':identity,'phase':'runtime_acquisition','command_count':0,'native_attempt_count':0,'complete_log_bytes':0,'capture_evidence_complete':False,'runtime_threshold_directly_observed':False}
    commands=[]
    def persist():
        a.write_json(work/'evidence/result.json',result)
        if commands:
            (work/'evidence/commands.jsonl').write_text(''.join(json.dumps(r,sort_keys=True,separators=(',',':'))+'\n' for r in commands))
            a.write_json(work/'evidence/last_command.json',commands[-1])
    persist()
    try:
        runtime=acquire_runtime(work,watchdog)
        for spec in command_specs(work,runtime):
            result['phase']=spec['name'];watchdog.check();seconds=min(spec['requested_timeout_seconds'],max(1,int(watchdog.deadline-time.monotonic())))
            out=work/'native-captures'/(spec['name']+'.stdout');err=work/'native-captures'/(spec['name']+'.stderr')
            limits={'address_space_bytes':spec['address_space_bytes'],'rss_tree_bytes':8*GIB,'max_created_file_bytes':512*1024**2}
            result['native_attempt_count']+=1;persist()
            watchdog.in_command=True
            try:r=f.run_process(spec['argv'],cwd=work,env=spec['env'],timeout=seconds,stdout=out,stderr=err,max_log_bytes=1024**2,limits=limits,allow_new_sessions=True)
            finally:
                watchdog.in_command=False
                if watchdog.expired:watchdog.failure_receipt_grace()
            r.update(name=spec['name'],argv=spec['argv'],cwd=str(work),requested_timeout_seconds=spec['requested_timeout_seconds'],effective_timeout_seconds=seconds,max_log_bytes=1024**2,limits=limits,address_space_bytes=limits['address_space_bytes'],max_rss_bytes=8*GIB,max_created_file_bytes=512*1024**2,allow_new_sessions=True,capture_status='excluded_pending_safety_and_bounds')
            commands.append(r);result['command_count']=len(commands);persist()
            if not capture_safe(r):
                r['capture_status']='excluded_unsafe_native_result';persist()
                raise f.Rejected('unsafe native result; captures excluded without reading')
            stdout_data=read_capture(out,1024**2,watchdog);stderr_data=read_capture(err,1024**2,watchdog)
            f.need(len(stdout_data)+len(stderr_data)<=1024**2,'native capture aggregate bound')
            r.update(capture_status='accepted_bounded_complete',captures={stream:{'bytes':len(data),'sha256':f.sha(data)} for stream,data in [('stdout',stdout_data),('stderr',stderr_data)]})
            result['complete_log_bytes']+=len(stdout_data)+len(stderr_data);persist()
            f.need(result['complete_log_bytes']<=2*1024**2 and r['exit_code']==0,'probe native command failed');watchdog.check()
            if spec['name']=='heap-options-probe':
                result['phase']='probe_stdout';f.need(stderr_data==b'','probe stderr is not empty')
                observation=parse_stdout(stdout_data);watchdog.check()
                observation.update(schema='lean-compiled-heap-options-observation-v1',phase='early-standalone-Lean.Shell-before-project-restore',argv_heap_mib=5120,runtime_inventory_sha256=a.RUNTIME_INVENTORY_SHA,runtime_threshold_directly_observed=False,failed_auditor_process_observed=False)
                a.write_json(work/'evidence/probe-observation.json',observation)
        f.need(result['command_count']==2,'probe command count differs');watchdog.check()
        result.update(status='PROBE_OBSERVED',phase='complete',capture_evidence_complete=True,observation_sha256=f.file_sha(work/'evidence/probe-observation.json'))
        a.write_json(work/'evidence/result.json',result);return result
    except Exception:
        result.update(status='PROBE_FAILED_OR_INCOMPLETE',failure_reason='fixed_probe_validation_or_execution_failed')
        a.write_json(work/'evidence/result.json',result);raise

def collect_probe(c,work,contract_sha):
    f.no_symlink_path(work);f.need(not work.exists() or work.is_dir(),'probe work is not a directory')
    names=['bwrap-preflight','heap-options-probe'];log_names={n+'.'+stream for n in names for stream in ['stdout','stderr']}
    allowed={'result.json','runtime-inventory.json','commands.jsonl','last_command.json','probe-observation.json','probe-collection-scope.json',*('logs/'+n for n in log_names)}
    f.no_symlink_path(work/'evidence');f.no_symlink_path(work/'logs');f.no_symlink_path(work/'native-captures')
    for q in (work/'evidence').rglob('*'):
        f.need(not q.is_symlink(),'probe evidence alias refused')
        if not q.is_dir():
            st=q.lstat();f.need(stat.S_ISREG(st.st_mode) and st.st_nlink==1,'probe evidence nonregular or aliased')
    existing={q.relative_to(work/'evidence').as_posix() for q in (work/'evidence').rglob('*') if q.is_file()}
    f.need(existing<=allowed,'unexpected probe evidence member')
    # The native writer never sees work/logs. Only this collector promotes complete,
    # safety-approved bounded captures. No unsafe or interrupted capture is read.
    f.need(not list((work/'logs').glob('*')) and not list((work/'evidence/logs').glob('*')),'probe admitted log destination not empty')
    f.need({q.name for q in (work/'native-captures').glob('*')}<=log_names,'unexpected native capture member')
    wd=a.HostDeadline(time.monotonic()+120)
    commands_path=work/'evidence/commands.jsonl';commands=[]
    if commands_path.exists():
        data=read_capture(commands_path,65536,wd);f.need(data.endswith(b'\n'),'incomplete probe command receipt')
        commands=[f.parse_json(line) for line in data.splitlines()];f.need(len(commands)<=2 and [r['name'] for r in commands]==names[:len(commands)],'probe command receipt order differs')
    omissions=[];accepted={}
    specs=command_specs(work,work/'runtime')
    for r,spec in zip(commands,specs):
        for key in ['name','argv','cwd','requested_timeout_seconds','address_space_bytes']:f.need(r[key]==spec[key],'probe command capture provenance differs')
        f.need(r['limits']=={'address_space_bytes':spec['address_space_bytes'],'rss_tree_bytes':8*GIB,'max_created_file_bytes':512*1024**2} and r['max_log_bytes']==1024**2,'probe capture limits differ')
        if r['capture_status']!='accepted_bounded_complete':
            omissions.append({'command':r['name'],'reason':'native_captures_not_safety_admitted'});continue
        f.need(capture_safe(r) and set(r['captures'])=={'stdout','stderr'},'unsafe capture marked accepted')
        total=0
        for stream in ['stdout','stderr']:
            row=r['captures'][stream];f.need(set(row)=={'bytes','sha256'} and type(row['bytes']) is int and 0<=row['bytes']<=1024**2 and f.SHA256.fullmatch(row['sha256']),'capture pin differs');total+=row['bytes']
            data=read_capture(work/'native-captures'/(r['name']+'.'+stream),1024**2,wd)
            f.need(len(data)==row['bytes'] and f.sha(data)==row['sha256'],'admitted capture identity changed')
            accepted[r['name']+'.'+stream]=data
        f.need(total<=1024**2,'admitted capture aggregate bound')
    # A helper interruption can leave captures without any returned scalar receipt.
    for name in names[len(commands):]:
        if any((work/'native-captures'/(name+'.'+s)).exists() for s in ['stdout','stderr']):omissions.append({'command':name,'reason':'native_helper_returned_no_admissible_receipt'})
    (work/'logs').mkdir(parents=True,exist_ok=True)
    for name,data in accepted.items():(work/'logs'/name).write_bytes(data)
    a.write_json(work/'evidence/probe-collection-scope.json',{'schema':'probe-only-collection-scope-v1','proof_certified':False,'stage_replay_acceptance_expected':False,'legacy_conditional_C_collection_label':'non-applicable inherited collector metadata; this probe proves no project theorem','runtime_threshold_directly_observed':False,'native_capture_omissions':omissions,'all_native_captures_admitted':not omissions})
    collector=a.load_helper('collect_evidence');receipt=collector.collect(work,c,contract_sha)
    f.need(receipt['all_available_files_copied'] and not receipt['replay_acceptance_evidence_complete'],'probe capture incomplete or incorrectly claims stage acceptance')
    f.need({r['path'] for r in receipt['files']}<=allowed,'unexpected collected probe member')
    return receipt

def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--collect',action='store_true');p.add_argument('--contract-sha256',required=True);p.add_argument('--work',type=Path,required=True);args=p.parse_args()
    f.need(sys.flags.isolated and sys.dont_write_bytecode,'invoke with Python -I -B')
    c=f.pinned_load(ROOT/'probe/contract.json',args.contract_sha256)
    watchdog=a.HostDeadline(time.monotonic()+1800);watchdog.arm()
    try:
        validate_contract(c,active=not args.collect);watchdog.check()
        if args.collect:
            receipt=collect_probe(c,args.work.absolute(),args.contract_sha256);print(json.dumps({'runner_status':receipt['runner_status'],'all_available_files_copied':True,'replay_acceptance_evidence_complete':False,'proof_certified':False},sort_keys=True));return
        identity=checkout_identity(c);watchdog.check();result=execute_probe(c,args.work.absolute(),identity,args.contract_sha256,watchdog)
        print(json.dumps({'status':result['status'],'proof_certified':False,'observation_sha256':result['observation_sha256']},sort_keys=True))
    finally:watchdog.close()

if __name__=='__main__':main()
