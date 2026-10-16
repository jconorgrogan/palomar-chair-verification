#!/usr/bin/env python3
"""One-module scheduling diagnostic; no conditional endpoint completion claim."""
from __future__ import annotations
import argparse,hashlib,importlib.util,json,os,re,shutil,signal,stat,sys,time,urllib.request
from pathlib import Path
ROOT=Path(__file__).resolve().parent/'baseline'
PACKAGE=ROOT.parent
RUNNER_SHA='bf2a94cb02d91ee1e3f38d434c2c0d803ba8e0d0f4e4161340d3b278269acd8f'
BASE_CONTRACT_SHA='cbba2b835ef2578ad4810068cab863918af442d5fa30abea5cafcfa78ce35a38'
TARGET='SpectreGeometry.PolygonProductKeyReferenceFinite'
TARGET_SHA='1bca6dbb7f17e7a897293c3cf8da9b5d686c02245ac5230be3b27c108953a45b'
TARGET_IMPORTS=['Mathlib.Data.Fintype.BigOperators','Mathlib.Data.Fin.VecNotation','Mathlib.Tactic.NormNum']
PROFILES=[('default',[]),('async_off',['-DElab.async=false'])]
if hashlib.sha256((ROOT/'ci/cache_diagnostic.py').read_bytes()).hexdigest()!=RUNNER_SHA:
    raise RuntimeError('baseline runner changed before import')
spec=importlib.util.spec_from_file_location('reviewed_baseline',ROOT/'ci/cache_diagnostic.py')
b=importlib.util.module_from_spec(spec);sys.modules[spec.name]=b;spec.loader.exec_module(b)
# All imported functions keep their original reviewed implementation and baseline ROOT.
f=b.f
GIB=b.GIB
DIAGNOSTIC_RSS_BYTES=b.DIAGNOSTIC_RSS_BYTES
DIAGNOSTIC_HEAP_MIB=b.DIAGNOSTIC_HEAP_MIB
ARCHIVE_URL=b.ARCHIVE_URL
ARCHIVE_BYTES=b.ARCHIVE_BYTES
RUNTIME_INVENTORY_SHA=b.RUNTIME_INVENTORY_SHA
OFFICIAL_REPOS=b.OFFICIAL_REPOS
HostDeadline=b.HostDeadline
write_json=b.write_json
safe_env=b.safe_env
sandbox=b.sandbox
checked_inventory=b.checked_inventory
namespace_providers=b.namespace_providers
git_capture=b.git_capture
validate_session_policy=b.validate_session_policy
extract_owned_sources=b.extract_owned_sources
validate_owned_graph=b.validate_owned_graph
install_archive=b.install_archive
readonly_boundary_preflight=b.readonly_boundary_preflight
validate_dependencies=b.validate_dependencies
source_snapshot=b.source_snapshot
cache_interface_identity=b.cache_interface_identity
direct_import_receipt=b.direct_import_receipt
module_outputs=b.module_outputs
admit_quarantine=b.admit_quarantine
verify_owned_final=b.verify_owned_final
audit_axiom_output=b.audit_axiom_output

def validate_package(contract):
    f.need(contract['schema']=='one-module-async-scheduling-diagnostic-v1','diagnostic schema differs')
    f.need(contract['review_status']=='inactive_pending_independent_review' or contract['review_status']=='reviewed_for_execution','unknown review state')
    f.need(contract['target']==TARGET and contract['target_sha256']==TARGET_SHA and contract['target_bytes']==4880,'target differs')
    f.need(contract['profiles']==[{'name':n,'extra_lean_arguments':a} for n,a in PROFILES],'profiles differ')
    expected={'aggregate_command_deadline_seconds':19200,'outer_timeout_minutes':330,'maximum_parallel_jobs':1,'compile_timeout_seconds':180,'check_timeout_seconds':120,'address_space_bytes':12*GIB,'rss_tree_bytes':8*GIB,'lean_heap_mib':4096,'per_command_log_max_bytes':1048576,'aggregate_log_max_bytes':64*1024**2,'evidence_max_bytes':124*1024**2}
    for k,v in expected.items():f.need(type(contract.get(k)) is type(v) and contract[k]==v,'diagnostic resource differs: '+k)
    f.need(contract['baseline_contract_sha256']==BASE_CONTRACT_SHA,'baseline contract differs')
    f.need(contract['official_lean_inventory_sha256']==RUNTIME_INVENTORY_SHA,'official runtime inventory pin differs')
    f.need(contract['work_root']=='/home/runner/work/_temp/conditional-geometry','producer work root differs')
    f.need(contract['proof_certified'] is False and contract['conditional_endpoint_replay_completed'] is False,'diagnostic claim changed')
    expected=set(contract['inputs'])|{'contract.json','.github/workflows/conditional-async-diagnostic.yml'}
    f.need(contract['distribution_files']==sorted(expected),'diagnostic tree manifest differs')
    actual={};dirs={str(q) for n in expected for q in Path(n).parents if str(q)!='.'}
    for parent,ds,fs in os.walk(PACKAGE,followlinks=False):
        parent=Path(parent)
        if parent==PACKAGE and '.git' in ds:ds.remove('.git')
        for n in ds:
            q=parent/n;f.need(not q.is_symlink() and str(q.relative_to(PACKAGE)) in dirs,'unexpected diagnostic directory')
        for n in fs:
            q=parent/n;s=q.lstat();rel=str(q.relative_to(PACKAGE));f.need(stat.S_ISREG(s.st_mode) and s.st_nlink==1,'nonregular diagnostic file');actual[rel]=q
    f.need(set(actual)==expected,'diagnostic exact tree differs')
    for n,row in contract['inputs'].items():
        q=actual[n];f.need(q.stat().st_size==row['bytes'] and f.file_sha(q)==row['sha256'],'diagnostic input differs: '+n)


def require_profile_disk_and_output_budget(work,contract):
    f.need(shutil.disk_usage(work).free>=contract['minimum_free_disk_bytes'],'insufficient measured disk reserve before diagnostic compile')
    total=0
    for name in ['objects','auditor-objects','profile-default-objects','profile-async_off-objects','quarantine']:
        root=work/name
        if root.exists():total+=checked_inventory(root,maximum=contract['owned_output_max_bytes'])['bytes']
    f.need(total<=contract['owned_output_max_bytes'],'aggregate retained diagnostic output budget exceeded')


def expected_command_specs(work,default_accepted):
    f.need(type(default_accepted) is bool,'invalid baseline acceptance discriminator')
    work=Path(work);runtime=work/'runtime'
    contract=f.pinned_load(ROOT/'contract.json',BASE_CONTRACT_SHA)
    pins=f.load_json(ROOT/'locks/dependencies.json')['packages']
    required=f.load_json(ROOT/'locks/required-modules.json')['modules']
    search=[str(work/'packages'/pin['name']/'.lake/build/lib/lean') for pin in pins]
    expected={'producer_work':str(work),'runtime':str(runtime),'contract':contract,'dependency_pins':pins,
              'cache_rows':[r['module'] for r in required],'cache_search':search,'stage_rows':[],'stage_id':'F0_common'}
    specs=b.transport.command_specs(expected,b)
    def add(name,argv,seconds):
        specs.append({'name':name,'argv':list(map(str,argv)),'cwd':str(work),'requested_timeout_seconds':seconds,'max_rss_bytes':8*GIB,'allow_new_sessions':True})
    controls=work/'controls';auditor_objects=work/'auditor-objects'
    core_env=safe_env(runtime,work/'home',work/'tmp');core_env['LEAN_PATH']=str(auditor_objects)+':'+str(runtime/'lib/lean')
    def core(name,extra):
        staging=work/'quarantine'/name
        argv=[runtime/'bin/lean','-j1','-M4096','-Dcompiler.postponeCompile=false',*extra,'-o',staging/(name+'.olean'),'-i',staging/(name+'.ilean'),'-c',staging/(name+'.c'),controls/(name+'.lean')]
        kw=dict(runtime=runtime,sources=[controls,auditor_objects],writable=[staging,work/'home',work/'tmp'],cwd=controls,env=core_env)
        add('compile-control-'+name,sandbox(argv,**kw),180)
        kw['writable']=[work/'home',work/'tmp'];add('check-control-'+name,sandbox([runtime/'bin/leanchecker',name],**kw),120)
    core('AuditAsyncTarget',[])
    for profile,extra in PROFILES:
        core('DefaultOptionControl' if profile=='default' else 'DisabledOptionControl',extra)
        objects=work/('profile-'+profile+'-objects');staging=work/'quarantine'/('target-'+profile);rel=TARGET.replace('.','/')
        env=safe_env(runtime,work/'home',work/'tmp');env['MATHLIB_CACHE_DIR']=str(work/'cache');env['LEAN_PATH']=':'.join([str(objects),*search,str(runtime/'lib/lean')])
        kw=dict(runtime=runtime,sources=[work/'packages',work/'src',objects],writable=[staging,work/'home',work/'tmp'],cwd=work/'src',env=env)
        argv=[runtime/'bin/lean','-j1','-M4096','-Dcompiler.postponeCompile=false',*extra,'-o',staging/(rel+'.olean'),'-i',staging/(rel+'.ilean'),'-c',staging/(rel+'.c'),work/'src'/(rel+'.lean')]
        add('compile-profile-'+profile,sandbox(argv,**kw),180)
        if profile=='async_off' or default_accepted:
            kw['writable']=[work/'home',work/'tmp'];add('check-profile-'+profile,sandbox([runtime/'bin/leanchecker',TARGET],**kw),120)
            audit_env=dict(env);audit_env['LEAN_PATH']=str(auditor_objects)+':'+env['LEAN_PATH']
            akw=dict(runtime=runtime,sources=[controls,auditor_objects,objects,work/'packages'],writable=[work/'home',work/'tmp'],cwd=controls,env=audit_env)
            add('audit-profile-'+profile,sandbox([runtime/'bin/lean','-j1','-M4096','--run',controls/'AuditAsyncTarget.lean'],**akw),600)
    return specs


def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--contract-sha256',required=True);ap.add_argument('--work',type=Path,required=True)
    a=ap.parse_args();f.need(sys.flags.isolated and sys.dont_write_bytecode,'invoke with Python -I -B')
    diagnostic=f.pinned_load(PACKAGE/'contract.json',a.contract_sha256)
    f.need(diagnostic['review_status']=='reviewed_for_execution','INACTIVE: diagnostic is not reviewed')
    validate_package(diagnostic)
    contract=f.pinned_load(ROOT/'contract.json',BASE_CONTRACT_SHA)
    b.validate_diagnostic_profile(contract);b.validate_stage_plan(contract);b.validate_distribution_layout(contract)
    f.need(os.environ.get('GITHUB_REF')=='refs/heads/'+diagnostic['publication_branch'],'unexpected diagnostic branch')
    f.need(git_capture(PACKAGE,'rev-parse','HEAD').decode().strip()==os.environ.get('GITHUB_SHA'),'workflow commit mismatch')
    f.need(not git_capture(PACKAGE,'status','--porcelain=v1','--untracked-files=all','--ignored'),'workflow checkout is not clean')
    owned=f.load_json(ROOT/'locks/owned-sources.json');required_lock=f.load_json(ROOT/'locks/required-modules.json')
    target=next(r for r in owned['sources'] if r['module']==TARGET)
    f.need(target['sha256']==TARGET_SHA and target['bytes']==4880 and target['ordered_imports']==TARGET_IMPORTS,'target source closure differs')
    f.need(not any(d in {r['module'] for r in owned['sources']} for d in TARGET_IMPORTS),'target has an owned prerequisite')
    work=a.work.absolute();f.need(str(work)==diagnostic['work_root'],'unexpected diagnostic work root');f.no_symlink_path(work);f.need(not work.exists(),'diagnostic workspace must be new');work.mkdir()
    for n in ['logs','evidence','packages','home','tmp','cache','objects','bootstrap','quarantine','auditor-objects']:(work/n).mkdir()
    deadline=time.monotonic()+diagnostic['aggregate_command_deadline_seconds'];commands=[];runtime=None;terminal_ready=False
    watchdog=HostDeadline(deadline);watchdog.arm()
    result={'schema':diagnostic['schema'],'status':'INCOMPLETE','proof_certified':False,'conditional_endpoint_replay_completed':False,
      'conditional_C_remains_explicit':True,'final_C_proof_certified':False,'unconditional_monotile_proof_certified':False,
      'contract_sha256':a.contract_sha256,'baseline_contract_sha256':BASE_CONTRACT_SHA,'source_sha256':TARGET_SHA,
      'workflow_commit':os.environ.get('GITHUB_SHA'),'run_id':os.environ.get('GITHUB_RUN_ID'),'run_attempt':os.environ.get('GITHUB_RUN_ATTEMPT'),
      'producer_work':str(work),'command_count':0,'complete_log_bytes':0,'profiles':{},'thread_virtual_memory_sampling':'Not collected by unchanged pinned process helper; mechanism remains unproven.'}
    write_json(work/'evidence/result.json',result)
    # These optional inherited setup branches are unreachable in this fresh diagnostic.
    a.runtime=None;a.runtime_inventory=None;a.local_dependencies=None
    def command(name,argv,*,cwd=None,env=None,seconds=1800,rss=8*GIB,allowed_sessions=False,expect_success=True):
        f.need(time.monotonic()<deadline,'diagnostic aggregate deadline exceeded')
        requested_seconds=seconds
        seconds=min(seconds,max(1,int(deadline-time.monotonic())))
        validate_session_policy(name,list(map(str,argv)),allowed_sessions,work,contract)
        out=work/'logs'/(name+'.stdout');err=work/'logs'/(name+'.stderr')
        watchdog.in_command=True
        try:
            r=f.run_process(list(map(str,argv)),cwd=cwd or work,env=env or safe_env(runtime or Path('/usr'),work/'home',work/'tmp'),timeout=seconds,stdout=out,stderr=err,max_log_bytes=contract['per_command_log_max_bytes'],
              limits={'address_space_bytes':12*GIB,'rss_tree_bytes':rss,'max_created_file_bytes':512*1024**2},allow_new_sessions=allowed_sessions)
        finally:
            watchdog.in_command=False
            if watchdog.expired:watchdog.failure_receipt_grace()
        r.update(timeout_seconds=seconds,max_log_bytes=contract['per_command_log_max_bytes'],limits={'address_space_bytes':12*GIB,'rss_tree_bytes':rss,'max_created_file_bytes':512*1024**2},allow_new_sessions=allowed_sessions,
          requested_timeout_seconds=requested_seconds,effective_timeout_seconds=seconds,
          max_rss_bytes=rss,address_space_bytes=12*GIB,max_created_file_bytes=512*1024**2,name=name,argv=list(map(str,argv)),cwd=str(cwd or work),stdout_sha256=f.file_sha(out),stderr_sha256=f.file_sha(err));commands.append(r)
        with (work/'evidence/commands.jsonl').open('a') as h:h.write(json.dumps(r,sort_keys=True,separators=(',',':'))+'\n')
        result['command_count']=len(commands);result['complete_log_bytes']+=out.stat().st_size+err.stat().st_size
        f.need(result['complete_log_bytes']<=contract['aggregate_log_max_bytes'],'aggregate complete log bound exceeded')
        write_json(work/'evidence/last_command.json',r);write_json(work/'evidence/result.json',result)
        watchdog.check()
        safety_ok=not any(r[k] for k in ['timed_out','log_overflow','memory_exceeded','surviving_children']) and r['process_group_empty'] and r['descendants_empty'] and not (r['escaped_descendants'] and not r['new_sessions_explicitly_allowed'])
        f.need(safety_ok,'unsafe or incomplete diagnostic command: '+name)
        ok=r['exit_code']==0
        f.need(ok or not expect_success,'command failed/incomplete: '+name)
        return out,ok
    try:
        source_root=work/'source-input'
        source_receipt=extract_owned_sources(ROOT/'owned-sources.tar.gz',source_root,contract)
        write_json(work/'evidence/source-extraction.json',source_receipt)
        result['source_extraction_receipt_sha256']=f.file_sha(work/'evidence/source-extraction.json')
        result['source_archive_sha256']=contract['source_archive']['sha256']
        validate_owned_graph(contract,owned,required_lock,source_root)
        if a.runtime:
            f.need(a.runtime_inventory is not None,'existing runtime requires official inventory')
            runtime=a.runtime.absolute();f.need(f.file_sha(a.runtime_inventory)==RUNTIME_INVENTORY_SHA,'runtime inventory pin differs');inv=f.load_json(a.runtime_inventory)
            f.need(inv['archive_sha256']==f.TOOLCHAIN_SHA256,'runtime archive pin differs')
            for rel,row in inv['files'].items():
                p=runtime/rel;f.no_symlink_path(p)
                f.need(p.stat().st_size==row['bytes'] and f.file_sha(p)==row['sha256'],'runtime byte mismatch')
            for rel,target in inv['symlinks'].items():
                f.need((runtime/rel).is_symlink() and os.readlink(runtime/rel)==target and (runtime/rel).resolve().is_relative_to(runtime),'runtime symlink mismatch')
        else:
            archive=work/'lean.tar.zst';downloaded=0;start=time.monotonic()
            with urllib.request.urlopen(ARCHIVE_URL,timeout=60) as response,archive.open('xb') as out:
                while True:
                    block=response.read(1024**2)
                    if not block:break
                    downloaded+=len(block);f.need(downloaded<=ARCHIVE_BYTES and time.monotonic()-start<900,'release download bound');out.write(block)
            f.need(downloaded==ARCHIVE_BYTES,'official archive size differs')
            runtime=work/'runtime';inv=install_archive(archive,runtime);archive.unlink()
        f.need(f.sha(f.json_bytes(inv))==RUNTIME_INVENTORY_SHA,'canonical runtime inventory differs')
        actual={p.relative_to(runtime).as_posix() for p in runtime.rglob('*') if not p.is_dir() or p.is_symlink()}
        f.need(actual==set(inv['files'])|set(inv['symlinks']),'runtime has missing/extra entries')
        write_json(work/'evidence/runtime-inventory.json',inv)
        env=safe_env(runtime,work/'home',work/'tmp');env['MATHLIB_CACHE_DIR']=str(work/'cache')
        command('bwrap-preflight',sandbox(['/bin/true'],runtime=runtime,sources=[],writable=[work/'home',work/'tmp'],cwd=work/'tmp',env=env),seconds=30,env=env,allowed_sessions=True)
        readonly_boundary_preflight(runtime,work,env,command)
        curl,_=command('curl-version',['/usr/bin/curl','--disable','--version'],env=env,seconds=30)
        m=re.match(r'curl (\d+)\.(\d+)\.',curl.read_text());f.need(m and tuple(map(int,m.groups()))>=(7,81),'curl fallback download forbidden: approved system curl too old')
        pins=f.load_json(ROOT/'locks/dependencies.json')['packages'];validate_dependencies(pins);before={}
        for pin in pins:
            name=pin['name'];p=work/'packages'/name;p.mkdir()
            base=['/usr/bin/git','-c','core.hooksPath=/dev/null','-c','core.fsmonitor=false','-C',str(p)]
            command(name+'-init',base+['init','--quiet'],env=env,seconds=30)
            command(name+'-remote',base+['remote','add','origin',pin['url']],env=env,seconds=30)
            origin=str(a.local_dependencies/name) if a.local_dependencies else pin['url']
            if a.local_dependencies:source_snapshot(a.local_dependencies/name,pin)
            command(name+'-fetch',base+['fetch','--quiet','--depth=1','--no-tags',origin,pin['rev']],env=env,seconds=300,allowed_sessions=True)
            command(name+'-checkout',base+['checkout','--quiet','--detach',pin['rev']],env=env,seconds=60)
            before[name]=source_snapshot(p,pin)
            f.need(not (p/'.lake').exists(),'fresh checkout has prior Lake state')
            (p/'.lake/build').mkdir(parents=True);(p/'.lake/config').mkdir();(p/'.lake/packages').mkdir()
        mathlib=work/'packages/mathlib';manifest=f.load_json(mathlib/'lake-manifest.json')
        expected={p['name']:(p['url'],p['rev']) for p in pins if p['name']!='mathlib'}
        f.need({p['name']:(p['url'],p['rev']) for p in manifest['packages']}==expected,'Mathlib manifest differs from dependency allowlist')
        client=f.load_json(ROOT/'locks/cache-client.json')
        for row in client['files']:
            p=mathlib/row['path'];f.need(p.stat().st_size==row['bytes'] and f.file_sha(p)==row['sha256'],'cache client source pin differs')
        for pin in pins:
            p=work/'packages'/pin['name'];mp=p/'lake-manifest.json'
            if mp.exists():
                for dep in f.load_json(mp)['packages']:
                    f.need(dep['name'] in OFFICIAL_REPOS,'unexpected nested dependency')
                    (p/'.lake/packages'/dep['name']).symlink_to(work/'packages'/dep['name'],target_is_directory=True)
        write_json(work/'evidence/dependency-sources.json',before)
        writable=[work/'home',work/'tmp',work/'cache',*[work/'packages'/p['name']/'.lake' for p in pins]]
        kwargs=dict(runtime=runtime,sources=[work/'packages'],writable=writable,cwd=mathlib,env=env)
        # Bootstrap uses only authenticated source and runtime, with network off.
        command('cache-bootstrap',sandbox([runtime/'bin/lake','build','cache'],**kwargs),env=env,seconds=900,allowed_sessions=True)
        produced=mathlib/'.lake/build/bin/cache';f.need(produced.is_file(),'cache bootstrap did not produce executable')
        cache=work/'bootstrap/cache';shutil.copyfile(produced,cache);cache.chmod(0o555);cache_sha=f.file_sha(cache)
        kwargs['sources'].append(work/'bootstrap')
        write_json(work/'evidence/cache-client-binary.json',{'sha256':f.file_sha(cache),'bytes':cache.stat().st_size,'built_from_official_sources':True})
        roots=contract['cache_roots'];f.need(all(f.MODULE.fullmatch(x) for x in roots),'invalid cache root')
        f.need(shutil.disk_usage(work).free>=9*GIB,'insufficient measured disk for bounded cache acquisition')
        # Exact supported official trust chain. No forks, --unsafe, --scope, endpoint overrides.
        command('cache-get',sandbox([runtime/'bin/lake','env',cache,'get','--cache-from=master,legacy',*roots],network=True,**kwargs),env=env,seconds=1800,allowed_sessions=True)
        required=required_lock['modules']
        command('cache-lookup',sandbox([runtime/'bin/lake','env',cache,'lookup',*[x['module'] for x in required]],**kwargs),env=env,seconds=180,allowed_sessions=True)
        f.need(f.file_sha(cache)==cache_sha,'read-only bootstrap cache executable changed')
        cache_inv=checked_inventory(work/'cache',maximum=3*GIB)
        f.need(not any(Path(n).name.startswith('curl-') and not n.endswith('.cfg') for n in cache_inv['files']),'fallback curl executable is forbidden')
        write_json(work/'evidence/cache-downloads.json',cache_inv)
        inventories={};search=[]
        for pin in pins:
            name=pin['name'];p=work/'packages'/name
            f.need(source_snapshot(p,pin)==before[name],'official sources changed during cache acquisition')
            inventories[name]=checked_inventory(p/'.lake/build',maximum=4*GIB,allow_links=True)
            search.append(str(p/'.lake/build/lib/lean'))
        f.need(sum(i['bytes'] for i in inventories.values())<=5*GIB,'aggregate cached build bound')
        write_json(work/'evidence/cached-build-inventory.json',inventories)
        # Cache get can return zero on 404 misses. Admit the whole requested source closure.
        providers={}
        for pin in pins:
            lib=work/'packages'/pin['name']/'.lake/build/lib/lean'
            for obj in lib.rglob('*.olean'):
                m=obj.relative_to(lib).as_posix().removesuffix('.olean').replace('/','.')
                f.need(m not in providers,'duplicate cached module provider: '+m);providers[m]=pin['name']
        for row in required:
            name=row['package'];m=row['module'];rel=row['path']
            f.need(before[name]['files'][rel]['sha256']==row['sha256'],'required source closure differs')
            f.need(providers.get(m)==name,'missing or wrong cached module provider: '+m)
            stem=work/'packages'/name/'.lake/build/lib/lean'/m.replace('.','/')
            suffixes=['.olean','.ilean']+(['.olean.server','.olean.private','.ir.sig','.ir'] if row['modern_module'] else [])
            for suffix in suffixes:f.need(Path(str(stem)+suffix).is_file(),'missing required cached companion: '+m+suffix)
        for row in contract['modules']:f.need(row['module'] not in providers,'cached object shadows owned module')
        owners=namespace_providers([Path(s) for s in search]+[runtime/'lib/lean'])
        for row in required:
            f.need(owners.get(row['module'].split('.')[0])==str(work/'packages'/row['package']/'.lake/build/lib/lean'),'required namespace has wrong provider')
        f.exact_tree(source_root/'src',{name.removeprefix('src/') for name in contract['inputs'] if name.startswith('src/')})
        shutil.copytree(source_root/'src',work/'src');owned_before=checked_inventory(work/'src',maximum=contract['owned_source_max_bytes'])
        shutil.copytree(ROOT/'auditors',work/'auditors')
        auditor_before=checked_inventory(work/'auditors',maximum=1024**2)
        # Cached package builds stay read-only. Download archives are no longer inputs.
        shutil.rmtree(work/'cache');(work/'cache').mkdir()
        env['LEAN_PATH']=':'.join([str(work/'objects'),*search,str(runtime/'lib/lean')])
        prior={};checked=set();receipts=[];lineage=[]
        owned_rows={r['module']:r for r in owned['sources']};cache_rows={}
        for r in required:
            prefix='lib/lean/'+r['module'].replace('.','/')
            suffixes=['.olean','.ilean']+(['.olean.server','.olean.private','.ir.sig','.ir'] if r['modern_module'] else [])
            cache_rows[r['module']]={**r,'companions':{prefix+suffix:inventories[r['package']]['files'][prefix+suffix] for suffix in suffixes}}
        result['cached_build_inventory_sha256']=f.file_sha(work/'evidence/cached-build-inventory.json')
        result['runtime_inventory_sha256']=f.file_sha(work/'evidence/runtime-inventory.json')
        interface=cache_interface_identity(cache_rows,inventories,result['runtime_inventory_sha256'])
        write_json(work/'evidence/interface-identity.json',interface)
        result['interface_identity_sha256']=f.file_sha(work/'evidence/interface-identity.json')
        # Each profile has one exclusive committed namespace and one quarantine.
        # Neither profile can import the other profile's candidate objects.
        controls=work/'controls';shutil.copytree(PACKAGE/'controls',controls)
        controls_before=checked_inventory(controls,maximum=1024**2)
        auditor_objects=work/'auditor-objects';audit_prior={}
        core_env=safe_env(runtime,work/'home',work/'tmp');core_env['LEAN_PATH']=str(auditor_objects)+':'+str(runtime/'lib/lean')
        def build_core(name,extra,marker=None):
            require_profile_disk_and_output_budget(work,contract)
            staging=work/'quarantine'/name;staging.mkdir()
            argv=[runtime/'bin/lean','-j1','-M4096','-Dcompiler.postponeCompile=false',*extra,
                  '-o',staging/(name+'.olean'),'-i',staging/(name+'.ilean'),'-c',staging/(name+'.c'),controls/(name+'.lean')]
            kw=dict(runtime=runtime,sources=[controls,auditor_objects],writable=[staging,work/'home',work/'tmp'],cwd=controls,env=core_env)
            output,_=command('compile-control-'+name,sandbox(argv,**kw),env=core_env,seconds=180,rss=DIAGNOSTIC_RSS_BYTES,allowed_sessions=True)
            require_profile_disk_and_output_budget(work,contract)
            if marker is not None:f.need(output.read_text().splitlines().count(marker)==1,'actual CLI option marker differs')
            admitted=admit_quarantine(staging,auditor_objects,name,audit_prior,64*1024**2)
            audit_prior.clear();audit_prior.update(admitted);shutil.rmtree(staging)
            kw['writable']=[work/'home',work/'tmp']
            command('check-control-'+name,sandbox([runtime/'bin/leanchecker',name],**kw),env=core_env,seconds=120,rss=DIAGNOSTIC_RSS_BYTES,allowed_sessions=True)
            verify_owned_final(auditor_objects,audit_prior,64*1024**2)
        build_core('AuditAsyncTarget',[])
        for profile,extra in PROFILES:
            watchdog.check();require_profile_disk_and_output_budget(work,contract)
            cname='DefaultOptionControl' if profile=='default' else 'DisabledOptionControl'
            marker='ASYNC_OPTION_CONTROL_DEFAULT_TRUE' if profile=='default' else 'ASYNC_OPTION_CONTROL_DISABLED_FALSE'
            build_core(cname,extra,marker)
            require_profile_disk_and_output_budget(work,contract)
            objects=work/('profile-'+profile+'-objects');objects.mkdir()
            profile_env=dict(env);profile_env['LEAN_PATH']=':'.join([str(objects),*search,str(runtime/'lib/lean')])
            staging=work/'quarantine'/('target-'+profile);staging.mkdir()
            rel=TARGET.replace('.','/');target=staging/(rel+'.olean');target.parent.mkdir(parents=True)
            inputs=direct_import_receipt(owned_rows[TARGET],owned_rows,set(),{},cache_rows,runtime)
            profile_receipt={'profile':profile,'source_sha256':TARGET_SHA,'extra_lean_arguments':extra,'ordered_imports':inputs,
                'compiler_command':len(commands),'checker_command':None,'audit_command':None,'accepted':False,
                'source_unchanged':True,'missing_thread_virtual_memory_samples':True}
            result['current_profile']=profile;result['profiles'][profile]=profile_receipt;write_json(work/'evidence/result.json',result)
            argv=[runtime/'bin/lean','-j1','-M4096','-Dcompiler.postponeCompile=false',*extra,
                  '-o',target,'-i',staging/(rel+'.ilean'),'-c',staging/(rel+'.c'),work/'src'/(rel+'.lean')]
            kw=dict(runtime=runtime,sources=[work/'packages',work/'src',objects],writable=[staging,work/'home',work/'tmp'],cwd=work/'src',env=profile_env)
            namespace_providers([objects,*[Path(s) for s in search],runtime/'lib/lean'])
            output,ok=command('compile-profile-'+profile,sandbox(argv,**kw),env=profile_env,seconds=180,rss=DIAGNOSTIC_RSS_BYTES,allowed_sessions=True,expect_success=False)
            current=commands[-1];require_profile_disk_and_output_budget(work,contract)
            if not ok:
                # The one predeclared baseline abort is diagnostic data only.
                # No failed or partial output is admitted or passed to the checker.
                expected_error='libc++abi: terminating due to uncaught exception of type lean::exception: failed to create thread: Resource temporarily unavailable\n'
                safe_failure=(profile=='default' and current['exit_code']==134 and
                    not any(current[k] for k in ['timed_out','log_overflow','memory_exceeded','surviving_children']) and
                    current['process_group_empty'] and current['descendants_empty'] and
                    (not current['escaped_descendants'] or current['new_sessions_explicitly_allowed']) and
                    output.read_bytes()==b'' and (work/'logs'/('compile-profile-'+profile+'.stderr')).read_text()==expected_error)
                profile_receipt['status']='BASELINE_THREAD_ABORT_REPRODUCED' if safe_failure else 'FAILED_PROFILE'
                profile_receipt['partial_outputs']=checked_inventory(staging,maximum=512*1024**2)
                write_json(work/'evidence'/('profile-'+profile+'.json'),profile_receipt)
                f.need(safe_failure,'unexpected or unsafe profile failure: '+profile)
            else:
                prior_profile=admit_quarantine(staging,objects,TARGET,{},contract['owned_output_max_bytes']);shutil.rmtree(staging)
                profile_receipt['checker_command']=len(commands)
                kw['writable']=[work/'home',work/'tmp']
                command('check-profile-'+profile,sandbox([runtime/'bin/leanchecker',TARGET],**kw),env=profile_env,seconds=120,rss=DIAGNOSTIC_RSS_BYTES,allowed_sessions=True)
                verify_owned_final(objects,prior_profile,contract['owned_output_max_bytes'])
                profile_receipt['outputs']=prior_profile
                audit_env=dict(profile_env);audit_env['LEAN_PATH']=str(auditor_objects)+':'+profile_env['LEAN_PATH']
                akw=dict(runtime=runtime,sources=[controls,auditor_objects,objects,work/'packages'],writable=[work/'home',work/'tmp'],cwd=controls,env=audit_env)
                profile_receipt['audit_command']=len(commands)
                audit_out,_=command('audit-profile-'+profile,sandbox([runtime/'bin/lean','-j1','-M4096','--run',controls/'AuditAsyncTarget.lean'],**akw),env=audit_env,seconds=600,rss=DIAGNOSTIC_RSS_BYTES,allowed_sessions=True)
                f.need(audit_out.read_text().splitlines().count('ASYNC_TARGET_RAW_AUDIT_PASSED_NO_FINAL_THEOREM')==1,'target raw audit marker differs')
                final_profile=verify_owned_final(objects,prior_profile,contract['owned_output_max_bytes'])
                write_json(work/'evidence'/('profile-'+profile+'-final-objects.json'),final_profile)
                profile_receipt['final_output_inventory_sha256']=f.file_sha(work/'evidence'/('profile-'+profile+'-final-objects.json'))
                profile_receipt['status']='COMPILED_KERNEL_CHECKED_AND_AUDITED';profile_receipt['accepted']=True
                write_json(work/'evidence'/('profile-'+profile+'.json'),profile_receipt)
            # Freeze a host-side transcript checkpoint before proceeding to B.
            profile_receipt['receipt_sha256']=f.file_sha(work/'evidence'/('profile-'+profile+'.json'))
            profile_receipt['log_hashes']={str(p.relative_to(work/'logs')):f.file_sha(p) for p in sorted((work/'logs').glob('*-profile-'+profile+'.*'))}
            write_json(work/'evidence'/('profile-'+profile+'-frozen.json'),profile_receipt)
            result['profiles'][profile]=profile_receipt;write_json(work/'evidence/result.json',result)
        require_profile_disk_and_output_budget(work,contract)
        f.need(result['profiles']['async_off']['accepted'] is True,'disabled asynchronous profile did not pass')
        for profile,_ in PROFILES:
            rec=result['profiles'][profile]
            if rec['accepted']:verify_owned_final(work/('profile-'+profile+'-objects'),rec['outputs'],contract['owned_output_max_bytes'])
            f.need(f.file_sha(work/'evidence'/('profile-'+profile+'.json'))==rec['receipt_sha256'],'earlier profile receipt changed')
            for name,digest in rec['log_hashes'].items():f.need(f.file_sha(work/'logs'/name)==digest,'earlier profile transcript changed')
        verify_owned_final(auditor_objects,audit_prior,64*1024**2)
        f.need(checked_inventory(controls,maximum=1024**2)==controls_before,'control source changed')
        f.need(checked_inventory(work/'src',maximum=contract['owned_source_max_bytes'])==owned_before,'owned source changed')
        for pin in pins:
            name=pin['name'];p=work/'packages'/name
            f.need(source_snapshot(p,pin)==before[name],'dependency source changed')
            f.need(checked_inventory(p/'.lake/build',maximum=4*GIB,allow_links=True)==inventories[name],'cached dependency bytes changed')
        watchdog.check()
        result['status']='ASYNC_DIAGNOSTIC_GATES_PASSED_PENDING_EVIDENCE'
        result['baseline_reproduced']=result['profiles']['default']['status']=='BASELINE_THREAD_ABORT_REPRODUCED'
        result['cause_proven']=False
        terminal_ready=True
    except Exception as error:
        result['status']='FAILED_OR_INCOMPLETE';result['error']=str(error);terminal_ready=False;raise
    finally:
        try:
            write_json(work/'evidence/result.json',result)
            for p in sorted((work/'logs').glob('*')):
                f.need(p.is_file() and not p.is_symlink(),'unexpected log entry')
                q=work/'evidence/logs'/p.name;q.parent.mkdir(exist_ok=True);shutil.copyfile(p,q)
            checked_inventory(work/'evidence',maximum=diagnostic['evidence_max_bytes']-8192)
            if terminal_ready:
                watchdog.check()
                result['command_receipts_sha256']=f.file_sha(work/'evidence/commands.jsonl')
                result['status']='ONE_MODULE_ASYNC_DIAGNOSTIC_COMPLETED';result['complete_evidence']=True
                write_json(work/'evidence/result.json',result)
                watchdog.check()
                marker=work/'evidence/diagnostic-ready.pending';marker.write_bytes(f.json_bytes({'result_sha256':f.file_sha(work/'evidence/result.json'),'contract_sha256':a.contract_sha256}))
                watchdog.check();os.replace(marker,work/'evidence/diagnostic-ready.json');watchdog.check()
        except Exception as error:
            result['status']='FAILED_EVIDENCE_OR_DEADLINE';result['complete_evidence']=False;result['collection_error']=str(error)
            write_json(work/'evidence/result.json',result);raise
        finally:watchdog.close()

if __name__=='__main__':main()
