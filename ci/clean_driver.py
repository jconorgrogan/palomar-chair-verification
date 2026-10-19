#!/usr/bin/env python3
"""Clean-source hierarchy C driver. Exact release pins/review required."""
from __future__ import annotations
import argparse,copy,math,secrets,threading,hashlib,importlib.util,json,os,shutil,stat,subprocess,sys,time,types,urllib.request
from pathlib import Path
from datetime import datetime,timezone
ENTRY_MONOTONIC=time.monotonic()

# No package code executes before its caller-pinned contract and complete code
# table have been authenticated. The workflow authenticates all clean checkouts
# before invoking this entrypoint as an additional independent gate.
EXECUTION_RELEASED=True
CODE_FILES={'clean_final_semantics.py','export_retry_specs.py','conron_recovery_resources.py','four_context_final.py', 'three_context_policy.py', 'ci_transport.py', 'continuation_policy.py', 'clean_transport.py', 'toolchain_install.py', 'three_context_final.py', 'origin_transport.py', 'clean_io.py', 'clean_driver.py', 'FinalExportAudit.lean', 'clean_local.py', 'clean_policy.py', 'clean_runner.py', 'four_context_policy.py', 'fresh_stage.py'}

def bootstrap(code,contract_hash):
    def need(ok):
        if not ok:raise RuntimeError('driver bootstrap pin/path/schema mismatch')
    need(type(contract_hash) is str and len(contract_hash)==64 and all(c in '0123456789abcdef' for c in contract_hash))
    for x in (code,*code.parents):need(not x.is_symlink())
    path=code/'clean_contract.json';st=path.lstat();need(stat.S_ISREG(st.st_mode) and st.st_nlink==1 and st.st_size<4*1024**2)
    raw=path.read_bytes();need(hashlib.sha256(raw).hexdigest()==contract_hash)
    def pairs(rows):
        out={}
        for k,v in rows:need(k not in out);out[k]=v
        return out
    contract=json.loads(raw,object_pairs_hook=pairs,parse_constant=lambda _:(_ for _ in ()).throw(ValueError('nonfinite contract')))
    pins=contract.get('implementation_sha256');need(type(pins) is dict and set(pins)==CODE_FILES)
    for name,digest in pins.items():
        file=code/name;st=file.lstat();need(stat.S_ISREG(st.st_mode) and st.st_nlink==1 and hashlib.sha256(file.read_bytes()).hexdigest()==digest)
    need(contract.get('review_status')=='reviewed_for_execution' and contract.get('clean_integration_review_status')=='reviewed' and EXECUTION_RELEASED)
    reviews=contract.get('final_semantic_activation_requirements')
    need(contract.get('final_semantic_review_status')=='reviewed' and type(reviews)is dict and
         set(reviews)=={'production_conron_outcome_review'} and
         all(type(v)is str and len(v)==64 and all(c in '0123456789abcdef'for c in v)for v in reviews.values()))
    selected=contract.get('conron_resource_selection')
    need(type(selected)is dict and selected=={**contract.get('conron_resource_candidate',{}),
         'outcome_review_sha256':reviews['production_conron_outcome_review']})
    sys.path.insert(0,str(code));sys.dont_write_bytecode=True
    return contract

def git(root,*args):
    return subprocess.run(['/usr/bin/git','-C',str(root),*args],check=True,text=True,
                          stdout=subprocess.PIPE,stderr=subprocess.PIPE).stdout.strip()

def _safe_native_result(result):
 """Numeric/boolean result only; never argv, environment, logs or arbitrary repr."""
 booleans=('timed_out','log_overflow','memory_exceeded','surviving_children','escaped_descendants','new_sessions_explicitly_allowed','process_group_empty','descendants_empty')
 times=('cleanup_bound_seconds','cleanup_elapsed_seconds','elapsed_seconds')
 if type(result) is not dict or set(result)!={*booleans,*times,'exit_code','peak_sampled_tree_rss_bytes'}:return None
 if any(type(result[k]) is not bool for k in booleans):return None
 if type(result['exit_code']) is not int or not -255<=result['exit_code']<=255:return None
 if type(result['peak_sampled_tree_rss_bytes']) is not int or not 0<=result['peak_sampled_tree_rss_bytes']<2**63:return None
 if any(type(result[k]) not in (int,float) or not math.isfinite(result[k]) or not 0<=result[k]<=10**9 for k in times):return None
 return dict(result)

PHASES=('entry','transport_bootstrap','clean_checkouts','source_pins','runtime_download','runtime_install','runtime_inventory','runtime_verify','execution_context','prepare_authentication','stage_descriptor','stage_restore_build','stage_command','final_restore','final_command','final_pack','final_acquisition','verdict_reauthentication','verdict')
def mark(state,phase):
    if phase not in PHASES:raise RuntimeError('unknown fixed phase')
    if state.get('phase') in PHASES:
        state.setdefault('completed',[]).append(state['phase'])
        state['completed']=state['completed'][-256:]
    state['phase']=phase;state['position']='before'

def safe_native(f,state,*args,**kwargs):
    f.need('GH_TOKEN' not in os.environ and 'GITHUB_TOKEN' not in os.environ and
           not any('TOKEN' in k or 'SECRET' in k for k in kwargs['env']),'native credential separation changed')
    state.pop('native_result',None);state.pop('safe_captures',None)
    result=f.run_process(*args,**kwargs)
    projected=_safe_native_result(result)
    state['native_result']=projected;state.pop('safe_captures',None)
    allowed=kwargs.get('allow_new_sessions',False)
    f.need(projected is not None and projected['new_sessions_explicitly_allowed'] is allowed and
           not any(projected[k] for k in ('timed_out','log_overflow','memory_exceeded','surviving_children')) and
           (allowed or not projected['escaped_descendants']) and
           projected['process_group_empty'] and projected['descendants_empty'] and
           projected['peak_sampled_tree_rss_bytes']<=kwargs['limits']['rss_tree_bytes'] and
           projected['cleanup_elapsed_seconds']<=projected['cleanup_bound_seconds'],
           'native safety or cleanup rejected')
    state['safe_captures']=(Path(kwargs['stdout']),Path(kwargs['stderr']),kwargs['max_log_bytes'])
    return result


def write_failure(state,error):
    # Nothing from arbitrary exception arguments, responses, argv or environment.
    root=state.get('root')
    if type(root) is not type(Path('/')) or not root.is_dir() or root.is_symlink():return
    phase=state.get('phase');phase=phase if phase in PHASES else 'bootstrap'
    value={'schema':'clean-source-failure-v1','status':'incomplete','proof_pass_claimed':False,
           'phase':phase,'reason_code':'REQUIRED_GATE_FAILED','native_result':_safe_native_result(state.get('native_result'))}
    if type(error) is MemoryError:value['reason_code']='MEMORY_FAILURE'
    elif type(error) is TimeoutError:value['reason_code']='TIMEOUT'
    elif type(error) is PermissionError:value['reason_code']='FILESYSTEM_PERMISSION'
    elif type(error) is FileNotFoundError:value['reason_code']='MISSING_FILE'
    elif type(error) is OSError:value['reason_code']='OS_FAILURE'
    module=state.get('transport_module')
    if module is not None:
        record=module._diagnostic_record(error)
        if (type(record) is dict and set(record)=={'schema','phase','category','reason_code','http_status','quota'} and
            record['schema']=='clean-transport-failure-v2' and record['phase'] in module.DIAGNOSTIC_PHASES and
            (record['category'],record['reason_code']) in set(module.DIAGNOSTIC_MESSAGES.values())|set(module.DIAGNOSTIC_GENERIC.values()) and
            (record['http_status'] is None or type(record['http_status']) is int and 100<=record['http_status']<=599)):
            quota=record['quota']
            if quota is None or (type(quota) is dict and set(quota)=={'limit','remaining','used','reset','resource'} and
                all(type(quota[k]) is int and 0<=quota[k]<=9999999999 for k in ('limit','remaining','used','reset')) and quota['resource'] in ('CORE','OTHER')):
                value['transport']={**record,'quota':None if quota is None else dict(quota)}
    command=state.get('command')
    if type(command) is dict:
        if set(command)=={'kind','stage_id','module_index','phase'} and command['kind']=='stage' and command['stage_id'] in {f'build_{i:03}' for i in range(93)} and type(command['module_index']) is int and 0<=command['module_index']<6369 and command['phase'] in ('compile','check'):value['command']=dict(command)
        elif set(command)=={'kind','name'} and command['kind']=='final' and command['name'] in ('sandbox_preflight','target_export','exact_export_audit','fresh_whole_closure','lean_from_export','lake_export_axioms','nanoda','conron'):value['command']=dict(command)
    raw=(json.dumps(value,sort_keys=True,indent=2,allow_nan=False)+'\n').encode()
    if len(raw)>16384:raise RuntimeError('fixed failure packet exceeds bound')
    output=root/'failure'
    if output.exists():return
    output.mkdir(mode=0o700)
    (output/'FAILURE.json').write_bytes(raw)
    captures=state.get('safe_captures')
    if captures is None:return
    paths=captures[:2];cap=min(captures[2],32*1024**2)
    infos=[]
    for path in paths:
        if root not in path.parents:return
        if any(p.is_symlink() for p in (path,*path.parents)):return
        info=path.lstat()
        if not stat.S_ISREG(info.st_mode) or info.st_nlink!=1:return
        infos.append(info)
    if sum(x.st_size for x in infos)>cap:return
    for path,name in zip(paths,('native.stdout','native.stderr')):
        # Complete, already-clean captures only; never token-bearing acquisition.
        shutil.copyfile(path,output/name)

def main():
    token=os.environ.pop('GH_TOKEN','');os.environ.pop('GITHUB_TOKEN',None)
    state={'phase':'bootstrap','completed':[]}
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('role');ap.add_argument('--stage')
    ap.add_argument('--contract-sha256',required=True);ap.add_argument('--pipeline',type=Path,required=True);ap.add_argument('--source',type=Path,required=True)
    args=ap.parse_args();code=Path(__file__).absolute().parent;contract=bootstrap(code,args.contract_sha256)
    import fresh_stage as f
    import clean_policy as cf
    import clean_local as local
    import clean_io as dio
    import clean_transport as current
    from clean_runner import CleanRunner
    from toolchain_install import install_archive
    try:
        with dio.JobBudget(entry=ENTRY_MONOTONIC) as budget:
            execute(args,code,contract,budget,f,cf,local,dio,current,CleanRunner,install_archive,token=token,state=state)
    except BaseException as error:
        write_failure(state,error)
        raise SystemExit('clean verification rejected; bounded diagnostics retained') from None
    finally:token=None

def execute(args,code,contract,budget,f,cf,local,dio,current,Runner,install_archive,*,token,state):
    cf.require_latest_selection()
    semantic=cf.final_semantics
    if args.role=='lean_export':budget=semantic.SplitBudget(budget,ENTRY_MONOTONIC)
    budget.check();mark(state,'entry')
    pipeline=local.canonical(str(args.pipeline));source=local.canonical(str(args.source))
    f.need(code==pipeline/'ci','driver must be exact ci child of current checkout')
    f.need(args.role in {'prepare','build','export_target','fresh_kernel','lean_export','nanoda','conron','verdict'} and ((args.role=='build')==(args.stage is not None)),'role/stage mismatch')
    root=local.canonical(str(Path(os.environ['RUNNER_TEMP'])/('hierarchy-c-clean-'+args.role+(('-'+args.stage) if args.stage else ''))))
    f.need(not root.exists(),'job workspace must be new');root.mkdir(mode=0o700);(root/'upload').mkdir();(root/'logs').mkdir()
    upload=root/'upload';state['root']=root;state['transport_module']=current
    def observed_now():budget.check();return budget.last_wall
    mark(state,'transport_bootstrap')
    origins=current.CleanTransport(token=token,root=root/'download',budget=budget,now=observed_now)
    f.need(os.environ.get('GITHUB_REF')=='refs/heads/'+cf.CURRENT_WORKFLOW['head_branch'],'unreviewed clean branch')
    mark(state,'clean_checkouts')
    for checkout,expected in [(source,cf.FIXED_IDENTITY['source_commit']),(pipeline,origins.commit)]:
        budget.check();f.need(git(checkout,'rev-parse','HEAD')==expected and git(checkout,'status','--porcelain=v1','--untracked-files=all','--ignored')=='','checkout identity or clean tree mismatch')
    mark(state,'source_pins')
    for name,digest in contract['implementation_sha256'].items():local.read_pinned(code/name,digest)
    plan=f.pinned_load(code/'plan.json',cf.FIXED_IDENTITY['plan_sha256']);profiles=f.pinned_load(code/'profiles.json',cf.FIXED_IDENTITY['profiles_sha256'])
    manifest=f.pinned_load(source/'SOURCE_MANIFEST.json',cf.FIXED_IDENTITY['source_manifest_sha256'])
    identity={**cf.FIXED_IDENTITY,'pipeline_commit':origins.commit,'contract_sha256':args.contract_sha256,'run_id':origins.run_id,'run_started_at':origins.run['created_at']}
    cf.validate_identity(identity,args.contract_sha256,origins.commit)
    f.need(contract.get('final_evidence_profile_sha256')==semantic.PROFILE_SHA256 and
           f.pinned_load(code/'clean_final_profile.json',semantic.PROFILE_SHA256)==semantic.PROFILE,'current final evidence profile changed')
    workflow=current.current_workflow_from_run(origins,contract['current_workflow'],pipeline)
    origins.bind(identity=identity,workflow=workflow,plan=plan,consumer_roles=contract['current_consumer_roles'],consumer_role=args.stage if args.role=='build' else args.role,github_job=os.environ.get('GITHUB_JOB'))
    budget.tighten_wall(cf.check_deadline(identity,observed_now()).timestamp())
    def authenticate_current():
        budget.check();origins._run('CurrentOrigin');origins._verify_workflow_source('CurrentOrigin');budget.check()
    authenticate_current()
    if args.role!='prepare':
        mark(state,'prepare_authentication');origins.authenticate_prepare('CurrentOrigin',root/'download'/'prepare')
    authenticate_current()
    origins.authenticate_prepare('PriorCleanOrigin',root/'download'/'prior-clean-prepare')
    origins.authenticate_prepare('LatestCleanOrigin',root/'download'/'latest-clean-prepare')
    mark(state,'runtime_download')
    archive=root/'lean.tar.zst';start=time.monotonic();downloaded=0
    with urllib.request.urlopen('https://github.com/leanprover/lean4/releases/download/v4.35.0-rc2/lean-4.35.0-rc2-linux.tar.zst',timeout=60) as response,archive.open('xb') as out:
        while True:
            budget.check();block=response.read(1024**2)
            if not block:break
            downloaded+=len(block);f.need(downloaded<=595391556 and time.monotonic()-start<900,'official release download bound');out.write(block)
    f.need(downloaded==595391556,'official release archive length mismatch');authenticate_current()
    mark(state,'runtime_install')
    toolchain=root/'toolchain';inventory=install_archive(archive,toolchain);budget.check()
    mark(state,'runtime_inventory')
    inventory_path=root/'inventory.json';inventory_path.write_bytes(f.json_bytes(inventory));inventory_sha=f.file_sha(inventory_path)
    f.need(inventory_sha==identity['toolchain_inventory_sha256'],'canonical runtime inventory changed')
    mark(state,'runtime_verify')
    f.verify_toolchain(toolchain,archive,inventory_path,contract,derived_inventory_sha256=inventory_sha)
    mark(state,'execution_context')
    cf._inputs(plan,manifest,profiles,identity);f.validate_contract(contract,manifest,plan,profiles)
    env={'PATH':str(toolchain/'bin')+':/usr/bin:/bin','HOME':str(root),'TMPDIR':str(root),'LANG':'C.UTF-8','LC_ALL':'C.UTF-8',
        'LEAN_NUM_THREADS':'1','LEAN_SYSROOT':str(toolchain),'LEAN_PATH':str(toolchain/'lib/lean')}
    execution_paths={'toolchain_root':str(toolchain),'code_root':str(code),'export_path':str(root/'logs/target_export.stdout'),'nanoda_config_path':str(root/'nanoda.json')}
    results=[]
    def command(name,argv,seconds=18000,rss=8*1024**3,stdout_limit=32*1024**2,sandbox_sessions=False,environment=None):
        budget.check();mark(state,'final_command');state['command']={'kind':'final','name':name}
        spec={'name':name,'argv':argv,'timeout_seconds':seconds,'resource_limits':{'address_space_bytes':12*1024**3,'rss_tree_bytes':rss,'max_created_file_bytes':stdout_limit},'max_log_bytes':stdout_limit,'new_sessions_explicitly_allowed':sandbox_sessions}
        if args.role!='prepare':
            expected=[x for x in cf.final_command_specs(args.role,execution_paths) if x['name']==name]
            f.need(expected==[spec],'actual command differs from unchanged final specification')
        if args.role in ('lean_export','nanoda','conron'):f.need(f.file_sha(Path(execution_paths['export_path']))==receipt['export_sha256'],'export mutated before command')
        record,out=dio.run_final_command(spec=spec,root=root,environment=environment or env,budget=budget,final=cf,executor=lambda *a,**kw:safe_native(f,state,*a,**kw))
        results.append(record);(root/'last_command.json').write_bytes(f.json_bytes(record));budget.check()
        if args.role in ('lean_export','nanoda','conron'):f.need(f.file_sha(Path(execution_paths['export_path']))==receipt['export_sha256'],'export mutated during command')
        budget.check();return out
    if args.role=='prepare':
        command('sandbox_preflight',['/usr/bin/bwrap','--ro-bind','/','/','--tmpfs','/home','--tmpfs','/root',
            '--tmpfs','/run/user','--tmpfs','/tmp','--dir','/tmp/home','--dev','/dev','--proc','/proc',
            '--clearenv','--unshare-all','--die-with-parent','--new-session','--','/bin/true'],seconds=30,sandbox_sessions=True)
        f.extract_sources(source/'hierarchy-c-sources.tar.gz',root/'source',manifest);budget.check()
        shutil.copyfile(inventory_path,upload/'inventory.json');(upload/'identity.json').write_bytes(f.json_bytes(identity));budget.check();return
    stage_command_index=0
    def stage_executor(*a,**kw):
        nonlocal stage_command_index
        stage=next((s for s in plan['stages'] if s['stage_id']==args.stage),None)
        f.need(args.stage=='build_092' and stage is not None and stage_command_index<2*len(stage['modules']),'fixed clean command index changed')
        state['command']={'kind':'stage','stage_id':args.stage,'module_index':stage_command_index//2,'phase':('compile','check')[stage_command_index%2]}
        stage_command_index+=1;mark(state,'stage_command')
        return budget.process(lambda:safe_native(f,state,*a,**kw))
    runner=Runner(budget=budget,contract=contract,manifest=manifest,plan=plan,profiles=profiles,identity=identity,source_root=root/'source',toolchain_root=toolchain,toolchain_inventory=inventory,workspace=root/'stage',executor=stage_executor)
    raw_native={}
    def stage_descriptors(ids):
        wrappers=[];sizes={}
        for sid in ids:
            budget.check();mark(state,'stage_descriptor')
            w=origins.download_stage(cf.origin_for_stage(sid),sid,root/'download'/sid,contract['max_artifact_bytes']+1024**2)
            receipt_path=current.copy_native_receipt(origins,w);descriptor_path=Path(w['archive_path']).parent/'upload-candidate.json'
            raw_native[sid]={'descriptor':descriptor_path.read_bytes(),'receipt':receipt_path.read_bytes()}
            cf.p.validate_native_bytes(w,raw_native[sid]['descriptor'],raw_native[sid]['receipt'])
            cf._validate_wrapper(w,identity,sid,workflow=workflow)
            sizes[sid]=w['native_descriptor']['archive_bytes'];f.need(sum(sizes.values())<=contract['max_restored_bytes'],'clean raw aggregate cap exceeded')
            wrappers.append(w);budget.check()
        return wrappers
    def native_descriptors(wrappers):return [{**copy.deepcopy(w['native_descriptor']),'archive_path':w['archive_path']} for w in wrappers]
    def pack_final(role,extra,files):
        budget.check();mark(state,'final_pack');info={name:{'bytes':path.stat().st_size,'sha256':f.file_sha(path)} for name,path in files.items()}
        receipt={'schema':'fresh-final-evidence-v1','role':role,'status':'completed_check_only','proof_pass_claimed':False,
            'identity':identity,'commands':results,'files':info,'execution_paths':execution_paths,**extra}
        cf.validate_final_commands(receipt);payload=upload/'payload.tar';rh=f.write_tar(payload,files,receipt,cf.FINAL_ARTIFACT_LIMIT)
        desc={'schema':'fresh-final-upload-v1','role':role,'identity':identity,'archive_sha256':f.file_sha(payload),'archive_bytes':payload.stat().st_size,'receipt_sha256':rh,'retention_days':7}
        (upload/'upload-candidate.json').write_bytes(f.json_bytes(desc));budget.check()
    def get_final(role):
        budget.check();mark(state,'final_acquisition');w=origins.download_final(role,root/'download'/role,cf.FINAL_ARTIFACT_LIMIT+1024**2);d=w['native_descriptor'];expanded=root/'expanded'/role
        receipt=f.extract_verified_archive(Path(w['archive_path']),d,expanded,cf.FINAL_ARTIFACT_LIMIT)
        f.need(receipt['role']==role and receipt['identity']==identity and receipt['status']=='completed_check_only','current final receipt mismatch')
        cf.validate_final_commands(receipt);budget.check();return receipt,expanded,d,w
    if args.role=='build':
        sid=args.stage;f.need(cf.origin_for_stage(sid)=='CurrentOrigin','selected prior-clean stage cannot be rebuilt');f.need(sid in runner.stages and os.environ['GITHUB_JOB']==runner.stages[sid]['producer_job'],'stage/workflow binding mismatch')
        ids=runner.stages[sid]['required_predecessors'];f.extract_sources(source/'hierarchy-c-sources.tar.gz',root/'source',manifest)
        ds=stage_descriptors(ids);mark(state,'stage_restore_build')
        f.need(not (root/'stage').exists(),'initial project workspace must be absent')
        runner.run(sid,native_descriptors(ds),os.environ['GITHUB_JOB']);budget.check()
        f.need(stage_command_index==2*len(runner.stages[sid]['modules']),'clean compile/check command coverage incomplete')
        for name in ['delta.tar','upload-candidate.json']:shutil.move(str(root/'stage'/name),upload/name)
        budget.check();return
    TARGET_MODULE=cf.TARGET_MODULE;TARGET=cf.TARGET
    if args.role in ('export_target','fresh_kernel'):
        ids=list(runner.stages);f.extract_sources(source/'hierarchy-c-sources.tar.gz',root/'source',manifest)
        ds=stage_descriptors(ids);mark(state,'final_restore');runner.restore_final(args.role,native_descriptors(ds))
        before={name:f.file_sha(path) for name,path in f.regular_tree(root/'stage'/'objects').items()}
        env['LEAN_PATH']=str(root/'stage'/'objects')+':'+str(toolchain/'lib/lean')
        provenance=cf.validate_stage_map(plan,manifest,profiles,ds,raw_native,identity,workflow)
        context=cf.final_context(manifest=manifest,provenance=provenance,object_hashes=before,identity=identity)
        if args.role=='export_target':
            exported=command('target_export',[str(toolchain/'bin/leanexport'),TARGET_MODULE,'--',TARGET],stdout_limit=2*1024**3)
            audit_env={**env,'LEAN_PATH':str(toolchain/'lib/lean')}
            command('exact_export_audit',[str(toolchain/'bin/lean'),'-j1','-M4096','--run',str(code/'FinalExportAudit.lean'),str(exported)],seconds=1800,rss=4*1024**3,environment=audit_env)
            f.need((root/'logs/exact_export_audit.stdout').read_text()=='EXPORT_CONTRACT_AUDIT_PASSED\n','trusted audit output incomplete')
            context['export_sha256']=f.file_sha(exported)
            context['native_stage_receipts_utf8']=dio.native_receipts_to_text(plan,provenance,{s:v['receipt'] for s,v in raw_native.items()},cf)
            files={'target.ndjson':exported,'audit.stdout':root/'logs/exact_export_audit.stdout','audit.stderr':root/'logs/exact_export_audit.stderr','export.stderr':root/'logs/target_export.stderr'}
        else:
            command('fresh_whole_closure',[str(toolchain/'bin/leanchecker'),'--fresh',TARGET_MODULE],seconds=18000)
            files={p.name:p for p in (root/'logs').iterdir()}
        f.need(before=={name:f.file_sha(path) for name,path in f.regular_tree(root/'stage'/'objects').items()},'final command mutated restored objects')
        f.verify_sources(root/'source',manifest);runner.verify_checked_objects();runner.check_run_age();pack_final(args.role,context,files);return
    if args.role in ('lean_export','nanoda','conron'):
        receipt,expanded,export_descriptor,_=get_final('export_target');exported=expanded/'target.ndjson';execution_paths['export_path']=str(exported)
        context=cf.final_context(manifest=manifest,provenance={'rows':receipt['resolved_provenance'],'campaign_predecessor_transfers':receipt['campaign_predecessor_transfers'],'sha256':receipt['resolved_provenance_sha256']},object_hashes=receipt['restored_object_hashes'],identity=identity)
        f.need(f.file_sha(exported)==receipt['export_sha256'],'exact-target export changed')
        if args.role=='lean_export':
            semantic.validate_semantic_inventory(inventory)
            f.need('LAKE_CHECK_EXPORT' not in env and 'COMPARATOR_BWRAP' not in env,'fixed Lake semantic environment')
            budget.finish_setup();mark(state,'final_command');state['command']={'kind':'final','name':'lake_export_axioms'}
            result,lake_budget=semantic.run_lake_command(role='lake_export_axioms',root=root,paths=execution_paths,
                env=env,state=state,budget=budget,entry_monotonic=ENTRY_MONOTONIC,specs=semantic.specs,
                base=sys.modules[__name__],f=f,dio=dio,final=semantic.legacy)
            semantic.validate_retry_command(result,role='lake_export_axioms',paths=execution_paths,
                budget_record=lake_budget,specs=semantic.specs,final=semantic.legacy)
            captures={}
            for stream in ('stdout','stderr'):
                path=root/'logs'/('lake_export_axioms.'+stream);f.no_symlink_path(path);st=path.lstat()
                f.need(stat.S_ISREG(st.st_mode) and st.st_nlink==1 and st.st_size<=32*1024**2,'bounded Lake capture')
                captures[stream]=path.read_bytes()
                f.need({'bytes':len(captures[stream]),'sha256':f.sha(captures[stream])}==result[stream],'Lake capture mutated')
            lake_output=semantic.validate_success_output(captures['stdout'],captures['stderr'],semantic.legacy)
            results.append(result);context.update(evidence_contract=semantic.EVIDENCE_CONTRACT,lake_budget=lake_budget,
                lake_output=lake_output,standalone_native_receipt_emitted=False,inner_native_receipt_emitted=False,
                legacy_pair_receipt_emitted=False)
            final_records=semantic.retain_records(root,inventory_path,args.role,{'LAKE_BUDGET.json':lake_budget,'LAKE_OUTPUT.json':lake_output})
        elif args.role=='nanoda':
            config=cf.nanoda_configuration(execution_paths)
            cfg=root/'nanoda.json';cfg.write_bytes(f.json_bytes(config));context['nanoda_config']=config
            command('nanoda',[str(toolchain/'bin/nanoda_bin'),str(cfg)],rss=6*1024**3)
        else:
            mark(state,'final_command');state['command']={'kind':'final','name':'conron'}
            result,headroom=semantic.run_conron_command(root=root,toolchain=toolchain,exported=exported,
                env=env,state=state,budget=budget,resources=semantic.resources,base=sys.modules[__name__],f=f,dio=dio,final=semantic.legacy)
            semantic.validate_conron_command(result,toolchain_root=str(toolchain),export_path=str(exported),resources=semantic.resources,final=semantic.legacy)
            semantic.validate_headroom(headroom);results.append(result)
            context.update(evidence_contract=semantic.PROFILE['roles']['conron']['contract'],headroom=headroom,
                resource_source_sha256=semantic.PROFILE['roles']['conron']['resource_source_sha256'])
            final_records=semantic.retain_records(root,inventory_path,args.role,{'HEADROOM.json':headroom})
        if args.role in ('lean_export','conron'):
            f.need(f.file_sha(exported)==receipt['export_sha256'],'export mutated during semantic check')
            f.verify_toolchain(toolchain,archive,inventory_path,contract,derived_inventory_sha256=inventory_sha)
            if args.role=='lean_export':semantic.validate_semantic_inventory(inventory)
            budget.check();authenticate_current()
            final_records.update(semantic.retain_export_receipt(expanded,export_descriptor,identity))
            context['retained_export_descriptor']=copy.deepcopy(export_descriptor)
        files={p.name:p for p in (root/'logs').iterdir()}
        if args.role=='nanoda':files['nanoda.json']=root/'nanoda.json'
        else:files.update(final_records)
        runner.check_run_age();pack_final(args.role,{**context,'export_sha256':receipt['export_sha256']},files);return
    checked={}
    for role in cf.FINAL_ROLES:
        receipt,_,_,wrapper=get_final(role);checked[role]={'receipt':receipt,'wrapper':wrapper}
    export_receipt=checked['export_target']['receipt'];provenance={'rows':export_receipt['resolved_provenance'],'campaign_predecessor_transfers':export_receipt['campaign_predecessor_transfers'],'sha256':export_receipt['resolved_provenance_sha256']}
    mark(state,'verdict_reauthentication')
    for wrapper in provenance['rows']:
        budget.check();meta=origins.reauthenticate_wrapper(wrapper)
        f.need(meta==wrapper['authenticated_metadata'],'resolved producer metadata changed')
    raw_receipts=dio.native_receipts_from_text(plan,provenance,export_receipt.get('native_stage_receipts_utf8'),cf)
    mark(state,'verdict')
    verdict=cf.final_verdict(plan,manifest,profiles,identity,workflow,provenance,raw_receipts,checked,observed_now())
    budget.check();(upload/'verdict.json').write_bytes(f.json_bytes(verdict));budget.check();print(json.dumps(verdict,sort_keys=True));budget.check()

if __name__=='__main__':main()
