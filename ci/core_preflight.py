#!/usr/bin/env python3
"""C087 isolated core-only compile/check/serialized-auditor smoke. No research import."""
from pathlib import Path
import argparse,hashlib,importlib.util,json,os,resource,shutil,signal,stat,sys,time,urllib.request
from collections import Counter
from datetime import datetime,timezone
ROOT=Path(__file__).resolve().parents[1]
GIB=1024**3
RUNTIME_SHA='42bd268b1ca3e9bf89f4149ac427d6c0e76f735233b092a6df4ca27a2c2db7ea'
ARCHIVE_SHA='b67d0e0ba959fc74e186f1b44aebca32d6ecb6a28f8e9a029fc4e9f73398a049'
ARCHIVE_BYTES=595391556
URL='https://github.com/leanprover/lean4/releases/download/v4.35.0-rc2/lean-4.35.0-rc2-linux.tar.zst'
REPO='jconorgrogan/palomar-chair-verification'
FAMILIES={'helpers':['C087RawContract','AuditC087Raw'],'negative':['C087NegativeControls'],'shape':['C087SourceShapeControl'],'default':['DefaultOptionControl'],'disabled':['DisabledOptionControl'],'fixture':['C087SerializedFixture.Model','SpectreFinite.RadiusFiveCertified','SpectreFinite.RadiusFivePruningRounds','SpectreFinite.RadiusFivePruningCertified']}
SUCCESS='C087_CORE_HELPERS_CONTROLS_AND_SERIALIZED_SMOKE_PASSED'
WORKFLOW='.github/workflows/core-controls.yml'
f=None;b=None;policy=None
EXPIRY='2026-10-22T06:15:54Z'

def need(ok,msg):
    if not ok:raise RuntimeError(msg)
def sha(path):
    h=hashlib.sha256()
    with Path(path).open('rb') as stream:
        for block in iter(lambda:stream.read(1024**2),b''):h.update(block)
    return h.hexdigest()
def canonical(v):return (json.dumps(v,sort_keys=True,indent=2)+'\n').encode()
def write(path,value):
    path=Path(path);path.parent.mkdir(parents=True,exist_ok=True);path.write_bytes(canonical(value))
def load_module(name,path):
    spec=importlib.util.spec_from_file_location(name,path);mod=importlib.util.module_from_spec(spec);sys.modules[name]=mod;spec.loader.exec_module(mod);return mod

def profile(c):
    exact={'schema':'c087-core-preflight-v1','scope':'C087_CORE_HELPERS_CONTROLS_AND_SYNTHETIC_SERIALIZED_TARGET','research_theorem_claimed':False,'mathlib_cache_used':False,'research_objects_loaded':False,'aggregate_seconds':1800,'job_timeout_minutes':35,'compile_seconds':120,'check_seconds':120,'lean_heap_mib':768,'address_space_bytes':8*GIB,'rss_tree_bytes':8*GIB,'max_created_file_bytes':512*1024**2,'per_command_log_bytes':1024**2,'aggregate_log_bytes':8*1024**2,'output_max_bytes':64*1024**2,'evidence_max_bytes':32*1024**2,'minimum_free_disk_bytes':1536*1024**2,'runtime_inventory_sha256':RUNTIME_SHA,'runtime_archive_sha256':ARCHIVE_SHA,'runtime_archive_bytes':ARCHIVE_BYTES,'runtime_archive_url':URL,'families':FAMILIES,'expected_command_count':23,'expected_companion_count':70,'maximum_parallel_jobs':1,'original_deadline_utc':EXPIRY}
    for k,v in exact.items():need(type(c.get(k)) is type(v) and c[k]==v,'core profile mismatch: '+k)
    need(c['publication_branch']=='verify/c087-core-preflight-20261017','branch differs')
    need(set(c['controls'])=={'negative','shape','default','disabled'},'control scope differs')
    need(c['controls']==json.loads((ROOT/'CONTROL_EXPECTATIONS.json').read_text()),'control expectations differ')

def validate_inputs(c,root=ROOT):
    expected=set(c['inputs'])|{'contract.json',WORKFLOW}
    actual=set()
    for p in root.rglob('*'):
        rel=p.relative_to(root)
        if rel.parts[0]=='.git':continue
        need(not p.is_symlink(),'package symlink forbidden')
        if p.is_dir():continue
        need(p.is_file() and p.stat().st_nlink==1,'package nonregular/hardlink')
        actual.add(rel.as_posix())
    need(actual==expected,'package exact file set differs')
    for rel,row in c['inputs'].items():
        need(rel and not rel.startswith('/') and '..' not in Path(rel).parts and '\\' not in rel,'package path invalid')
        p=root/rel;need(p.stat().st_size==row['bytes'] and sha(p)==row['sha256'],'input pin differs: '+rel)
    wanted={f"src/{family}/{module.replace('.', '/')}.lean" for family,names in FAMILIES.items() for module in names}
    need({p for p in c['inputs'] if p.startswith('src/')}==wanted,'unapproved source file')

def specs(c,work,runtime):
    env=b.safe_env(runtime,work/'home',work/'tmp');rows=[]
    def add(name,inner,sources,writable,cwd,environment,seconds):
        argv=b.sandbox(inner,runtime=runtime,sources=sources,writable=writable,cwd=cwd,env=environment)
        rows.append({'name':name,'argv':list(map(str,argv)),'cwd':str(work),'env':environment,'requested_timeout_seconds':seconds,'allow_new_sessions':True})
    add('bwrap-preflight',['/bin/true'],[],[work/'home',work/'tmp'],work/'tmp',env,30)
    committed=work/'preflight-read-only';staging=work/'preflight-quarantine'
    script='test -r "$1/predecessor"; if printf bad > "$1/predecessor"; then exit 11; fi; if chmod 0600 "$1/predecessor"; then exit 12; fi; if mkdir "$1/SpectreGeometry"; then exit 13; fi; printf allowed > "$2/output"'
    add('read-only-committed-root-preflight',['/bin/sh','-eu','-c',script,'readonly-boundary-control',committed,staging],[committed],[staging,work/'home',work/'tmp'],staging,env,30)
    for family,names in FAMILIES.items():
        source=ROOT/'src'/family;objects=work/'objects'/family
        deps=[objects]
        if family not in ('helpers','fixture'):deps+=[work/'objects/helpers']
        family_env=dict(env,LEAN_PATH=':'.join(map(str,[*deps,runtime/'lib/lean'])))
        for module in names:
            staging=work/'quarantine'/module;target=staging/module.replace('.','/')
            flags=['-j1','-M768','-Dcompiler.postponeCompile=false']
            if family=='disabled':flags+=['-DElab.async=false']
            compile_argv=[runtime/'bin/lean',*flags,'-o',str(target)+'.olean','-i',str(target)+'.ilean','-c',str(target)+'.c',source/(module.replace('.','/')+'.lean')]
            add('compile-'+module,compile_argv,[source,*deps],[staging,work/'home',work/'tmp'],source,family_env,120)
            add('check-'+module,[runtime/'bin/leanchecker',module],[source,*deps],[work/'home',work/'tmp'],source,family_env,120)
    source=ROOT/'src/helpers';deps=[work/'objects/helpers',work/'objects/fixture']
    audit_env=dict(env,LEAN_PATH=':'.join(map(str,[*deps,runtime/'lib/lean'])))
    add('run-fixed-serialized-auditor',[runtime/'bin/lean','-j1','-M768','--run',source/'AuditC087Raw.lean'],[source,*deps],[work/'home',work/'tmp'],source,audit_env,120)
    return rows

def accept_command(row,spec,c):
    for key in ['name','argv','cwd','env','requested_timeout_seconds','allow_new_sessions']:need(row.get(key)==spec[key],'command specification differs: '+key)
    limits={'address_space_bytes':8*GIB,'rss_tree_bytes':8*GIB,'max_created_file_bytes':512*1024**2}
    need(row.get('limits')==limits and row.get('max_log_bytes')==c['per_command_log_bytes'],'command resource profile differs')
    effective=row.get('effective_timeout_seconds');need(type(effective) is int and 0<effective<=spec['requested_timeout_seconds'] and row.get('timeout_seconds')==effective,'command deadline differs')
    need(row.get('new_sessions_explicitly_allowed') is True and type(row.get('escaped_descendants')) is bool,'nested session lacks explicit admission')
    need(type(row.get('exit_code')) is int and row.get('exit_code')==0 and all(row.get(k) is False for k in ['timed_out','log_overflow','memory_exceeded','surviving_children']) and row.get('process_group_empty') is True and row.get('descendants_empty') is True,'command failed or cleanup incomplete')

def check_markers(text,row):
    lines=text.splitlines();need(lines==row['exact_stdout_lines'],'exact control output differs')

def parse_fixture_audit(raw):
    rows=policy.parse_audit(raw)
    need(all(row['all_owned_transitive_axioms']==[] for row in rows),'synthetic serialized fixture must have no transitive axioms')
    return rows

def verify_runtime(runtime,inventory):
    need(hashlib.sha256(canonical(inventory)).hexdigest()==RUNTIME_SHA and inventory['archive_sha256']==ARCHIVE_SHA,'runtime inventory identity differs')
    actual={p.relative_to(runtime).as_posix() for p in runtime.rglob('*') if not p.is_dir() or p.is_symlink()}
    need(actual==set(inventory['files'])|set(inventory['symlinks']),'runtime entry set differs')
    for rel,row in inventory['files'].items():
        p=runtime/rel;f.no_symlink_path(p);need(p.is_file() and p.stat().st_size==row['bytes'] and stat.S_IMODE(p.stat().st_mode)==row['mode'] and sha(p)==row['sha256'],'runtime file changed')
    for rel,target in inventory['symlinks'].items():
        p=runtime/rel;need(p.is_symlink() and os.readlink(p)==target and p.resolve(strict=True).is_relative_to(runtime),'runtime link changed')

def validate_final(c,work,commands,outputs,runtime):
    expected=specs(c,work,runtime);need(len(commands)==len(expected)==23,'command count differs')
    for r,spec in zip(commands,expected):
        accept_command(r,spec,c)
        for stream in ['stdout','stderr']:
            path=work/'logs'/(spec['name']+'.'+stream);need(path.is_file() and sha(path)==r[stream+'_sha256'],'log changed')
    need(set(outputs)==set(FAMILIES),'output family set differs')
    for family,names in FAMILIES.items():
        rows=outputs[family];need(set(rows)==set().union(*(b.module_outputs(m) for m in names)),'family companion set differs')
        b.verify_owned_final(work/'objects'/family,rows,c['output_max_bytes'])
        if family in c['controls']:check_markers((work/'logs'/('compile-'+names[0]+'.stdout')).read_text(),c['controls'][family])
    parse_fixture_audit((work/'logs/run-fixed-serialized-auditor.stdout').read_bytes())
    need(sum(r['bytes'] for rows in outputs.values() for r in rows.values())<=c['output_max_bytes'],'combined output cap exceeded')
    validate_inputs(c)

def collect(work,c,*,recollect=False):
    evidence=work/'evidence';logs=work/'logs';need(evidence.is_dir(),'missing evidence root')
    if logs.exists():
        dest=evidence/'logs'
        if dest.exists():
            need(recollect,'preexisting evidence logs');need(b.checked_inventory(logs,maximum=c['aggregate_log_bytes'])==b.checked_inventory(dest,maximum=c['aggregate_log_bytes']),'retained failure logs differ')
        else:shutil.copytree(logs,dest,symlinks=True)
    rows={};total=0
    for p in sorted(evidence.rglob('*')):
        need(not p.is_symlink(),'evidence link forbidden')
        if p.is_dir():continue
        need(p.is_file() and p.stat().st_nlink==1,'evidence nonregular/hardlink')
        total+=p.stat().st_size;need(total<=c['evidence_max_bytes']-1024**2,'evidence cap exceeded')
        rows[p.relative_to(evidence).as_posix()]={'bytes':p.stat().st_size,'sha256':sha(p)}
    data=canonical({'schema':'core-preflight-evidence-v1','files':rows,'bytes':total})
    need(len(data)<=1024**2 and total+len(data)<=c['evidence_max_bytes'],'collection manifest exceeds cap')
    (evidence/'collection.json').write_bytes(data)

def failure_evidence(c,work,result,error):
    # Only the exclusively created invocation workspace is supplied by main.
    # Drop prior success/collection markers before rewriting failure evidence.
    evidence=work/'evidence'
    for name in ('completion.json','.completion.pending','collection.json'):
        path=evidence/name;f.no_symlink_path(path)
        if path.exists():
            st=path.lstat();need(stat.S_ISREG(st.st_mode) and st.st_nlink==1,'failure marker is not owned regular file');path.unlink()
    result.update(status='FAILED',error_type=type(error).__name__,error=str(error)[:2000]);write(evidence/'result.json',result)
    collect(work,c,recollect=True)

def run_pairs(c,work,runtime,all_specs,commands,outputs,command,watchdog):
    for family,names in FAMILIES.items():
        objects=work/'objects'/family
        for module in names:
            watchdog.check();need(shutil.disk_usage(work).free>=c['minimum_free_disk_bytes'],'minimum disk reserve before compile')
            staging=work/'quarantine'/module;staging.mkdir();(staging/module.replace('.','/')).parent.mkdir(parents=True,exist_ok=True)
            deps=[objects] + ([work/'objects/helpers'] if family not in ('helpers','fixture') else [])
            b.namespace_providers([*deps,runtime/'lib/lean'])
            spec=all_specs[len(commands)];command(spec['name'],spec['argv'],env=spec['env'],seconds=spec['requested_timeout_seconds'],allowed_sessions=True)
            other=sum(r['bytes'] for fam,rows in outputs.items() if fam!=family for r in rows.values())
            outputs[family]=b.admit_quarantine(staging,objects,module,outputs[family],c['output_max_bytes']-other)
            shutil.rmtree(staging)
            spec=all_specs[len(commands)];command(spec['name'],spec['argv'],env=spec['env'],seconds=spec['requested_timeout_seconds'],allowed_sessions=True)
            for fam,rows in outputs.items():b.verify_owned_final(work/'objects'/fam,rows,c['output_max_bytes'])
            if family in c['controls']:check_markers((work/'logs'/('compile-'+module+'.stdout')).read_text(),c['controls'][family])
            write(work/'evidence/outputs.json',outputs)
    b.namespace_providers([work/'objects/helpers',work/'objects/fixture',runtime/'lib/lean'])
    spec=all_specs[len(commands)];command(spec['name'],spec['argv'],env=spec['env'],seconds=spec['requested_timeout_seconds'],allowed_sessions=True)
    parse_fixture_audit((work/'logs/run-fixed-serialized-auditor.stdout').read_bytes())
    return outputs

def finalize_success(c,work,commands,outputs,runtime,inventory,result,contract_sha,watchdog):
    validate_final(c,work,commands,outputs,runtime);verify_runtime(runtime,inventory)
    need(shutil.disk_usage(work).free>=c['minimum_free_disk_bytes'],'final disk reserve')
    watchdog.check();result.update(status=SUCCESS,compile_check_pairs=10,companions=70,synthetic_serialized_audit=True,control_markers={'negative_pass_lines':45,'source_shape':2,'option_controls':2},output_inventory_sha256=sha(work/'evidence/outputs.json'))
    write(work/'evidence/result.json',result);collect(work,c);watchdog.check()
    pending=work/'evidence/.completion.pending';need(not pending.exists() and not (work/'evidence/completion.json').exists(),'preexisting completion marker');pending.write_bytes(canonical({'schema':'core-preflight-completion-v1','result_sha256':sha(work/'evidence/result.json'),'collection_sha256':sha(work/'evidence/collection.json'),'contract_sha256':contract_sha}))
    watchdog.check();os.replace(pending,work/'evidence/completion.json');watchdog.check();watchdog.close()

def expiry_watchdog(deadline):
    class ExpiryWatchdog(b.HostDeadline):
        def __init__(self,deadline):
            super().__init__(deadline);self.previous_wall=None
        def check(self):
            now=datetime.now(timezone.utc);expiry=datetime.strptime(EXPIRY,'%Y-%m-%dT%H:%M:%SZ').replace(tzinfo=timezone.utc)
            need(self.previous_wall is None or now>=self.previous_wall,'backward wall clock');self.previous_wall=now
            need(now<expiry,'original expiry reached')
            self.deadline=min(self.deadline,time.monotonic()+(expiry-now).total_seconds())
            return super().check()
    result=ExpiryWatchdog(deadline);result.check();return result

def main():
    global f,b,policy
    started=time.monotonic()
    ap=argparse.ArgumentParser();ap.add_argument('--contract-sha256',required=True);ap.add_argument('--work',type=Path,required=True);args=ap.parse_args()
    need(sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode,'use Python -I -S -B')
    need(sha(ROOT/'contract.json')==args.contract_sha256,'contract digest mismatch');c=json.loads((ROOT/'contract.json').read_text());profile(c)
    need(c['review_status']=='reviewed_for_execution','INACTIVE: exact review required');validate_inputs(c)
    f=load_module('fresh_stage',ROOT/'ci/fresh_stage.py');b=load_module('boundary',ROOT/'ci/boundary.py');b.f=f
    installer=load_module('toolchain_install',ROOT/'ci/toolchain_install.py');policy=load_module('probe_policy',ROOT/'ci/probe_policy.py')
    need(os.environ.get('GITHUB_ACTIONS')=='true' and os.environ.get('GITHUB_REPOSITORY')==REPO and os.environ.get('GITHUB_REPOSITORY_ID')=='1407290933','Actions repository differs')
    need(os.environ.get('GITHUB_REF')=='refs/heads/'+c['publication_branch'],'Actions branch differs')
    commit=os.environ.get('GITHUB_SHA','');need(len(commit)==40 and all(x in '0123456789abcdef' for x in commit),'invalid commit')
    need(b.git_capture(ROOT,'rev-parse','HEAD').decode().strip()==commit,'checkout commit differs')
    need(not b.git_capture(ROOT,'status','--porcelain=v1','--untracked-files=all','--ignored'),'checkout not clean')
    need(args.work.is_absolute() and str(args.work)==str(args.work.absolute()) and '..' not in args.work.parts,'canonical absolute work root required');work=args.work.absolute();f.no_symlink_path(work);need(not work.exists(),'work root must be fresh');work.mkdir()
    for rel in ['home','tmp','logs','evidence','quarantine',*['objects/'+x for x in FAMILIES]]:(work/rel).mkdir(parents=True)
    deadline=started+c['aggregate_seconds'];watchdog=expiry_watchdog(deadline);watchdog.arm()
    if hasattr(os,'sched_setaffinity'):os.sched_setaffinity(0,{min(os.sched_getaffinity(0))})
    resource.setrlimit(resource.RLIMIT_AS,(8*GIB,8*GIB));resource.setrlimit(resource.RLIMIT_CPU,(1800,1800))
    result={'schema':c['schema'],'status':'INCOMPLETE','scope':c['scope'],'research_theorem_claimed':False,'mathlib_cache_used':False,'research_objects_loaded':False,'contract_sha256':args.contract_sha256,'workflow_commit':commit,'run_id':os.environ.get('GITHUB_RUN_ID'),'run_attempt':os.environ.get('GITHUB_RUN_ATTEMPT'),'command_count':0}
    write(work/'evidence/result.json',result);commands=[];outputs={k:{} for k in FAMILIES};runtime=work/'runtime';all_specs=[]
    def command(name,argv,*,env,cwd=None,seconds,allowed_sessions):
        need(allowed_sessions is True,'core commands require explicit nested session');watchdog.check()
        spec=all_specs[len(commands)];need(spec['name']==name and spec['argv']==list(map(str,argv)) and spec['env']==env and spec['requested_timeout_seconds']==seconds,'unlisted command')
        effective=min(seconds,int(watchdog.deadline-time.monotonic()));need(effective>0,'shared execution deadline exhausted');out=work/'logs'/(name+'.stdout');err=work/'logs'/(name+'.stderr')
        watchdog.in_command=True
        try:r=f.run_process(spec['argv'],cwd=work,env=env,timeout=effective,stdout=out,stderr=err,max_log_bytes=c['per_command_log_bytes'],limits={'address_space_bytes':8*GIB,'rss_tree_bytes':8*GIB,'max_created_file_bytes':512*1024**2},allow_new_sessions=True)
        finally:
            watchdog.in_command=False
            if watchdog.expired:watchdog.failure_receipt_grace()
        r.update(spec,timeout_seconds=effective,effective_timeout_seconds=effective,limits={'address_space_bytes':8*GIB,'rss_tree_bytes':8*GIB,'max_created_file_bytes':512*1024**2},max_log_bytes=c['per_command_log_bytes'],stdout_sha256=sha(out),stderr_sha256=sha(err))
        commands.append(r);write(work/'evidence/commands.json',commands);write(work/'evidence/last_command.json',r)
        result['command_count']=len(commands);write(work/'evidence/result.json',result)
        need(sum(p.stat().st_size for p in (work/'logs').iterdir())<=c['aggregate_log_bytes'],'aggregate log cap exceeded')
        watchdog.check();accept_command(r,spec,c);return out,True
    try:
        need(shutil.disk_usage(work).free>=7*GIB,'insufficient runtime acquisition disk')
        archive=work/'lean.tar.zst';count=0;start=time.monotonic()
        with urllib.request.urlopen(URL,timeout=60) as response,archive.open('xb') as stream:
            while block:=response.read(1024**2):
                count+=len(block);need(count<=ARCHIVE_BYTES and time.monotonic()-start<600,'official archive download bound');stream.write(block)
        need(count==ARCHIVE_BYTES and sha(archive)==ARCHIVE_SHA,'official runtime archive identity')
        inventory=installer.install_archive(archive,runtime);verify_runtime(runtime,inventory);write(work/'evidence/runtime-inventory.json',inventory)
        result['runtime_inventory_sha256']=RUNTIME_SHA;write(work/'evidence/result.json',result)
        all_specs=specs(c,work,runtime);env=b.safe_env(runtime,work/'home',work/'tmp')
        first=all_specs[0];command(first['name'],first['argv'],env=first['env'],seconds=first['requested_timeout_seconds'],allowed_sessions=True)
        b.readonly_boundary_preflight(runtime,work,env,command)
        run_pairs(c,work,runtime,all_specs,commands,outputs,command,watchdog)
        finalize_success(c,work,commands,outputs,runtime,inventory,result,args.contract_sha256,watchdog)
    except BaseException as error:
        failure_evidence(c,work,result,error)
        raise
    finally:watchdog.close()
if __name__=='__main__':main()
