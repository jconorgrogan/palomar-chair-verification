#!/usr/bin/env python3
"""Two fixed uniform helper/control pairs before any project-origin acquisition."""
from pathlib import Path
import argparse,math,hashlib,importlib.util,json,os,resource,shutil,signal,stat,sys,time,urllib.request
ROOT=Path(__file__).resolve().parents[1]
GIB=1024**3
RUNTIME_SHA='42bd268b1ca3e9bf89f4149ac427d6c0e76f735233b092a6df4ca27a2c2db7ea'
ARCHIVE_SHA='b67d0e0ba959fc74e186f1b44aebca32d6ecb6a28f8e9a029fc4e9f73398a049'
ARCHIVE_BYTES=595391556
URL='https://github.com/leanprover/lean4/releases/download/v4.35.0-rc2/lean-4.35.0-rc2-linux.tar.zst'
REPO='jconorgrogan/palomar-chair-verification'
FAMILIES={'uniform':['AuditUniformPhysicalEndpoints','UniformInspectorControl']}
SUCCESS='UNIFORM_CORE_INSPECTOR_AND_CONTROL_COMPILE_CHECK_PASSED'
WORKFLOW='.github/workflows/uniform-core-preflight.yml'
f=None;b=None

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

def native_projection(result):
 """Numeric/boolean result only; never argv, environment, logs or arbitrary repr."""
 booleans=('timed_out','log_overflow','memory_exceeded','surviving_children','escaped_descendants','new_sessions_explicitly_allowed','process_group_empty','descendants_empty')
 times=('cleanup_bound_seconds','cleanup_elapsed_seconds','elapsed_seconds')
 if type(result) is not dict or set(result)!={*booleans,*times,'exit_code','peak_sampled_tree_rss_bytes'}:return None
 if any(type(result[k]) is not bool for k in booleans):return None
 if type(result['exit_code']) is not int or not -255<=result['exit_code']<=255:return None
 if type(result['peak_sampled_tree_rss_bytes']) is not int or not 0<=result['peak_sampled_tree_rss_bytes']<2**63:return None
 if any(type(result[k]) not in (int,float) or not math.isfinite(result[k]) or not 0<=result[k]<=10**9 for k in times):return None
 return dict(result)

def profile(c):
    exact={'schema':'core-inspector-preflight-v1','scope':'TWO_UNIFORM_CORE_ONLY_HELPER_CONTROL_PAIRS','research_theorem_claimed':False,'mathlib_cache_used':False,'research_objects_loaded':False,'aggregate_seconds':1800,'job_timeout_minutes':35,'compile_seconds':180,'check_seconds':120,'lean_heap_mib':4096,'address_space_bytes':12*GIB,'rss_tree_bytes':8*GIB,'max_created_file_bytes':512*1024**2,'per_command_log_bytes':1024**2,'aggregate_log_bytes':8*1024**2,'output_max_bytes':64*1024**2,'evidence_max_bytes':32*1024**2,'minimum_free_disk_bytes':1536*1024**2,'runtime_inventory_sha256':RUNTIME_SHA,'runtime_archive_sha256':ARCHIVE_SHA,'runtime_archive_bytes':ARCHIVE_BYTES,'runtime_archive_url':URL,'families':FAMILIES,'expected_command_count':6,'expected_companion_count':14,'maximum_parallel_jobs':1}
    for k,v in exact.items():need(type(c.get(k)) is type(v) and c[k]==v,'core profile mismatch: '+k)
    need(set(c['controls'])==set(FAMILIES),'control family set differs')
    for family,count in [('uniform',45)]:
        row=c['controls'][family]
        need(set(row)=={'module','pass_labels','success_marker'} and row['module']==FAMILIES[family][1],'control row scope differs')
        need(len(row['pass_labels'])==len(set(row['pass_labels']))==count and all(isinstance(x,str) and x and '\n' not in x for x in row['pass_labels']),'control labels differ')
        need(row['success_marker']==family.upper()+'_INSPECTOR_CORE_CONTROL_PASSED','control marker differs')
    need(c['publication_branch']=='verify/uniform-core-preflight-20261018','branch differs')

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
    wanted={f'src/{family}/{module}.lean' for family,names in FAMILIES.items() for module in names}
    need({p for p in c['inputs'] if p.startswith('src/')}==wanted,'unapproved source file')

def specs(c,work,runtime):
    env=b.safe_env(runtime,work/'home',work/'tmp')
    rows=[]
    def add(name,inner,sources,writable,cwd,environment,seconds):
        argv=b.sandbox(inner,runtime=runtime,sources=sources,writable=writable,cwd=cwd,env=environment)
        rows.append({'name':name,'argv':list(map(str,argv)),'cwd':str(work),'env':environment,'requested_timeout_seconds':seconds,'allow_new_sessions':True})
    add('bwrap-preflight',['/bin/true'],[],[work/'home',work/'tmp'],work/'tmp',env,30)
    committed=work/'preflight-read-only';staging=work/'preflight-quarantine'
    script='test -r "$1/predecessor"; if printf bad > "$1/predecessor"; then exit 11; fi; if chmod 0600 "$1/predecessor"; then exit 12; fi; if mkdir "$1/SpectreGeometry"; then exit 13; fi; printf allowed > "$2/output"'
    add('read-only-committed-root-preflight',['/bin/sh','-eu','-c',script,'readonly-boundary-control',committed,staging],[committed],[staging,work/'home',work/'tmp'],staging,env,30)
    for family,names in FAMILIES.items():
        source=ROOT/'src'/family;objects=work/'objects'/family
        family_env=dict(env,LEAN_PATH=str(objects)+':'+str(runtime/'lib/lean'))
        for module in names:
            staging=work/'quarantine'/module;target=staging/module
            compile_argv=[runtime/'bin/lean','-j1','-M4096','-Dcompiler.postponeCompile=false','-o',str(target)+'.olean','-i',str(target)+'.ilean','-c',str(target)+'.c',source/(module+'.lean')]
            add('compile-'+module,compile_argv,[source,objects],[staging,work/'home',work/'tmp'],source,family_env,180)
            add('check-'+module,[runtime/'bin/leanchecker',module],[source,objects],[work/'home',work/'tmp'],source,family_env,120)
    return rows

def accept_command(row,spec,c):
    for key in ['name','argv','cwd','env','requested_timeout_seconds','allow_new_sessions']:need(row.get(key)==spec[key],'command specification differs: '+key)
    limits={'address_space_bytes':12*GIB,'rss_tree_bytes':8*GIB,'max_created_file_bytes':512*1024**2}
    need(row.get('limits')==limits and row.get('max_log_bytes')==c['per_command_log_bytes'],'command resource profile differs')
    effective=row.get('effective_timeout_seconds');need(type(effective) is int and 0<effective<=spec['requested_timeout_seconds'] and row.get('timeout_seconds')==effective,'command deadline differs')
    need(row.get('new_sessions_explicitly_allowed') is True and type(row.get('escaped_descendants')) is bool,'nested session lacks explicit admission')
    need(row.get('exit_code')==0 and all(row.get(k) is False for k in ['timed_out','log_overflow','memory_exceeded','surviving_children']) and row.get('process_group_empty') is True and row.get('descendants_empty') is True,'command failed or cleanup incomplete')

def check_markers(text,row):
    lines=text.splitlines();passed=[x for x in lines if x.startswith('PASS ')]
    need(passed==['PASS '+x for x in row['pass_labels']],'control labels missing, extra or reordered')
    need(lines.count(row['success_marker'])==1,'control success marker missing/duplicate')
    need(not any(x.startswith('UNIFORM_PHYSICAL_ENDPOINT_AUDIT_') or x.startswith('HIGHER_PHYSICAL_ENDPOINT_AUDIT_') for x in lines),'unexpected research endpoint claim')

def verify_runtime(runtime,inventory):
    need(hashlib.sha256(canonical(inventory)).hexdigest()==RUNTIME_SHA and inventory['archive_sha256']==ARCHIVE_SHA,'runtime inventory identity differs')
    actual={p.relative_to(runtime).as_posix() for p in runtime.rglob('*') if not p.is_dir() or p.is_symlink()}
    need(actual==set(inventory['files'])|set(inventory['symlinks']),'runtime entry set differs')
    for rel,row in inventory['files'].items():
        p=runtime/rel;f.no_symlink_path(p);need(p.is_file() and p.stat().st_size==row['bytes'] and stat.S_IMODE(p.stat().st_mode)==row['mode'] and sha(p)==row['sha256'],'runtime file changed')
    for rel,target in inventory['symlinks'].items():
        p=runtime/rel;need(p.is_symlink() and os.readlink(p)==target and p.resolve(strict=True).is_relative_to(runtime),'runtime link changed')

def validate_final(c,work,commands,outputs,runtime):
    expected=specs(c,work,runtime);need(len(commands)==len(expected)==6,'command count differs')
    for r,s in zip(commands,expected):
        accept_command(r,s,c)
        for stream in ['stdout','stderr']:
            p=work/'logs'/(s['name']+'.'+stream);need(p.is_file() and sha(p)==r[stream+'_sha256'],'log changed')
    need(set(outputs)==set(FAMILIES),'output family set differs')
    for family,names in FAMILIES.items():
        rows=outputs[family];need(set(rows)==set().union(*(b.module_outputs(m) for m in names)),'family companion set differs')
        b.verify_owned_final(work/'objects'/family,rows,c['output_max_bytes'])
        check_markers((work/'logs'/('compile-'+names[1]+'.stdout')).read_text(),c['controls'][family])
    need(sum(r['bytes'] for rows in outputs.values() for r in rows.values())<=c['output_max_bytes'],'combined output cap exceeded')
    validate_inputs(c)

def capture_identity(st):
    return (st.st_dev,st.st_ino,st.st_mode,st.st_nlink,st.st_size,st.st_mtime_ns,st.st_ctime_ns)

def accepted_capture_bytes(path, expected, maximum):
    # Same-owner fixed captures only, after native cleanup/safety acceptance.
    path=Path(path);f.no_symlink_path(path);before=path.lstat()
    need(stat.S_ISREG(before.st_mode) and before.st_nlink==1 and 0<=before.st_size<=maximum,'capture type/size rejected')
    with path.open('rb') as stream:
        opened=os.fstat(stream.fileno());need(capture_identity(opened)==capture_identity(before),'capture changed before read')
        data=stream.read(maximum+1);need(len(data)==before.st_size and len(data)<=maximum,'capture complete bound rejected')
        need(capture_identity(os.fstat(stream.fileno()))==capture_identity(before),'capture changed during read')
    need(capture_identity(path.lstat())==capture_identity(before) and hashlib.sha256(data).hexdigest()==expected,'capture identity/hash changed')
    return data

def collect(work,c,commands):
    evidence=work/'evidence';need(evidence.is_dir(),'missing evidence root')
    # Never walk or copy the live log tree: a rejected child may have unsafe captures.
    if commands:
        dest=evidence/'logs';need(not dest.exists(),'preexisting evidence logs');dest.mkdir()
        names=set();capture_total=0
        for row in commands:
            name=row['name'];need(name in {'bwrap-preflight','read-only-committed-root-preflight',
                *('compile-'+m for names in FAMILIES.values() for m in names),
                *('check-'+m for names in FAMILIES.values() for m in names)},'unknown accepted command')
            need(name not in names,'duplicate accepted command');names.add(name)
            for stream in ('stdout','stderr'):
                filename=name+'.'+stream
                data=accepted_capture_bytes(work/'logs'/filename,row[stream+'_sha256'],c['per_command_log_bytes'])
                capture_total+=len(data);need(capture_total<=c['aggregate_log_bytes'],'accepted aggregate log cap exceeded')
                with (dest/filename).open('xb') as output:output.write(data)
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

def run_pairs(c,work,runtime,all_specs,commands,outputs,command,watchdog):
    for family,names in FAMILIES.items():
        objects=work/'objects'/family
        for module in names:
            watchdog.check();need(shutil.disk_usage(work).free>=c['minimum_free_disk_bytes'],'minimum disk reserve before compile')
            staging=work/'quarantine'/module;staging.mkdir();b.namespace_providers([objects,runtime/'lib/lean'])
            spec=all_specs[len(commands)];command(spec['name'],spec['argv'],env=spec['env'],seconds=spec['requested_timeout_seconds'],allowed_sessions=True)
            other=sum(r['bytes'] for fam,rows in outputs.items() if fam!=family for r in rows.values())
            outputs[family]=b.admit_quarantine(staging,objects,module,outputs[family],c['output_max_bytes']-other)
            shutil.rmtree(staging)
            spec=all_specs[len(commands)];command(spec['name'],spec['argv'],env=spec['env'],seconds=spec['requested_timeout_seconds'],allowed_sessions=True)
            b.verify_owned_final(objects,outputs[family],c['output_max_bytes'])
            if module==names[1]:check_markers((work/'logs'/('compile-'+module+'.stdout')).read_text(),c['controls'][family])
            write(work/'evidence/outputs.json',outputs)
    return outputs

def finalize_success(c,work,commands,outputs,runtime,inventory,result,contract_sha,watchdog):
    validate_final(c,work,commands,outputs,runtime);verify_runtime(runtime,inventory)
    need(shutil.disk_usage(work).free>=c['minimum_free_disk_bytes'],'final disk reserve')
    watchdog.check();result.update(status=SUCCESS,compile_check_pairs=2,companions=14,control_markers={'uniform':45},output_inventory_sha256=sha(work/'evidence/outputs.json'))
    write(work/'evidence/result.json',result);collect(work,c,commands);watchdog.check()
    pending=work/'evidence/.completion.pending';need(not pending.exists() and not (work/'evidence/completion.json').exists(),'preexisting completion marker');pending.write_bytes(canonical({'schema':'core-preflight-completion-v1','result_sha256':sha(work/'evidence/result.json'),'collection_sha256':sha(work/'evidence/collection.json'),'contract_sha256':contract_sha}))
    watchdog.check();os.replace(pending,work/'evidence/completion.json');watchdog.close()

def main():
    global f,b
    started=time.monotonic()
    os.environ.pop('GH_TOKEN',None);os.environ.pop('GITHUB_TOKEN',None)
    ap=argparse.ArgumentParser();ap.add_argument('--contract-sha256',required=True);ap.add_argument('--work',type=Path,required=True);args=ap.parse_args()
    need(sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode,'use Python -I -S -B')
    need(sha(ROOT/'contract.json')==args.contract_sha256,'contract digest mismatch');c=json.loads((ROOT/'contract.json').read_text());profile(c)
    need(c['review_status']=='reviewed_for_execution','INACTIVE: exact review required');validate_inputs(c)
    f=load_module('fresh_stage',ROOT/'ci/fresh_stage.py');b=load_module('boundary',ROOT/'ci/boundary.py');b.f=f
    installer=load_module('toolchain_install',ROOT/'ci/toolchain_install.py')
    need(os.environ.get('GITHUB_ACTIONS')=='true' and os.environ.get('GITHUB_REPOSITORY')==REPO and os.environ.get('GITHUB_REPOSITORY_ID')=='1407290933','Actions repository differs')
    need(os.environ.get('GITHUB_REF')=='refs/heads/'+c['publication_branch'],'Actions branch differs')
    commit=os.environ.get('GITHUB_SHA','');need(len(commit)==40 and all(x in '0123456789abcdef' for x in commit),'invalid commit')
    need(b.git_capture(ROOT,'rev-parse','HEAD').decode().strip()==commit,'checkout commit differs')
    need(not b.git_capture(ROOT,'status','--porcelain=v1','--untracked-files=all','--ignored'),'checkout not clean')
    work=args.work.absolute();f.no_symlink_path(work);need(not work.exists(),'work root must be fresh');work.mkdir()
    for rel in ['home','tmp','logs','evidence','quarantine','objects/uniform']:(work/rel).mkdir(parents=True)
    deadline=started+c['aggregate_seconds'];watchdog=b.HostDeadline(deadline);watchdog.arm()
    if hasattr(os,'sched_setaffinity'):os.sched_setaffinity(0,{min(os.sched_getaffinity(0))})
    resource.setrlimit(resource.RLIMIT_AS,(12*GIB,12*GIB));resource.setrlimit(resource.RLIMIT_CPU,(1800,1800))
    result={'schema':c['schema'],'status':'INCOMPLETE','scope':c['scope'],'research_theorem_claimed':False,'mathlib_cache_used':False,'research_objects_loaded':False,'contract_sha256':args.contract_sha256,'workflow_commit':commit,'run_id':os.environ.get('GITHUB_RUN_ID'),'run_attempt':os.environ.get('GITHUB_RUN_ATTEMPT'),'command_count':0,'phase':'runtime_download'}
    write(work/'evidence/result.json',result);commands=[];outputs={k:{} for k in FAMILIES};runtime=work/'runtime';all_specs=[]
    def command(name,argv,*,env,cwd=None,seconds,allowed_sessions):
        need(allowed_sessions is True,'core commands require explicit nested session');watchdog.check()
        spec=all_specs[len(commands)];need(spec['name']==name and spec['argv']==list(map(str,argv)) and spec['env']==env and spec['requested_timeout_seconds']==seconds,'unlisted command')
        need(deadline-time.monotonic()>3,'cleanup reserve exhausted')
        effective=min(seconds,max(1,int(deadline-time.monotonic()-3)));out=work/'logs'/(name+'.stdout');err=work/'logs'/(name+'.stderr')
        result.pop('native_result',None);result['command_name']=name;result['phase']='native_command'
        watchdog.in_command=True
        try:
            r=f.run_process(spec['argv'],cwd=work,env=env,timeout=effective,stdout=out,stderr=err,max_log_bytes=c['per_command_log_bytes'],limits={'address_space_bytes':12*GIB,'rss_tree_bytes':8*GIB,'max_created_file_bytes':512*1024**2},allow_new_sessions=True)
            projection=native_projection(r)
            result['native_result']=projection
            write(work/'evidence/result.json',result)
            need(projection is not None and projection['new_sessions_explicitly_allowed'] is True and
                 all(projection[k] is False for k in ('timed_out','log_overflow','memory_exceeded','surviving_children')) and
                 projection['process_group_empty'] is True and projection['descendants_empty'] is True and
                 projection['peak_sampled_tree_rss_bytes']<=8*GIB and
                 projection['cleanup_bound_seconds']==3 and
                 projection['cleanup_elapsed_seconds']<=projection['cleanup_bound_seconds'], 'native safety or cleanup rejected')
        finally:
            watchdog.in_command=False
            if watchdog.expired:watchdog.failure_receipt_grace()
        # Validate complete bounded files before hashing or admitting capture names.
        for capture in (out,err):
            f.no_symlink_path(capture);st=capture.lstat()
            need(stat.S_ISREG(st.st_mode) and st.st_nlink==1 and st.st_size<=c['per_command_log_bytes'],'capture type/size rejected')
        need(out.stat().st_size+err.stat().st_size<=c['per_command_log_bytes'],'paired capture cap exceeded')
        r.update(spec,timeout_seconds=effective,effective_timeout_seconds=effective,limits={'address_space_bytes':12*GIB,'rss_tree_bytes':8*GIB,'max_created_file_bytes':512*1024**2},max_log_bytes=c['per_command_log_bytes'],stdout_sha256=sha(out),stderr_sha256=sha(err))
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
        result['phase']='runtime_install';write(work/'evidence/result.json',result)
        inventory=installer.install_archive(archive,runtime)
        result['phase']='runtime_verify';write(work/'evidence/result.json',result)
        verify_runtime(runtime,inventory);write(work/'evidence/runtime-inventory.json',inventory)
        result['runtime_inventory_sha256']=RUNTIME_SHA;write(work/'evidence/result.json',result)
        all_specs=specs(c,work,runtime);env=b.safe_env(runtime,work/'home',work/'tmp')
        first=all_specs[0];command(first['name'],first['argv'],env=first['env'],seconds=first['requested_timeout_seconds'],allowed_sessions=True)
        b.readonly_boundary_preflight(runtime,work,env,command)
        run_pairs(c,work,runtime,all_specs,commands,outputs,command,watchdog)
        result['phase']='finalize';write(work/'evidence/result.json',result)
        finalize_success(c,work,commands,outputs,runtime,inventory,result,args.contract_sha256,watchdog)
    except BaseException as error:
        result.update(status='FAILED',reason_code='REQUIRED_GATE_FAILED',proof_pass_claimed=False);write(work/'evidence/result.json',result)
        if not (work/'evidence/collection.json').exists():collect(work,c,commands)
        raise
    finally:watchdog.close()
if __name__=='__main__':main()
