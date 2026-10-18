#!/usr/bin/env python3
"""INACTIVE four-context hierarchy C driver. Exact release pins/review required."""
from __future__ import annotations
import argparse,copy,math,secrets,threading,hashlib,importlib.util,json,os,shutil,stat,subprocess,sys,time,types,urllib.request
from pathlib import Path
from datetime import datetime,timezone
ENTRY_MONOTONIC=time.monotonic()

# No package code executes before its caller-pinned contract and complete code
# table have been authenticated. The workflow authenticates all clean checkouts
# before invoking this entrypoint as an additional independent gate.
CODE_FILES={'four_context_driver.py','four_context_runner.py','four_context_transfer.py','four_context_current_transport.py','four_context_policy.py','four_context_final.py','three_context_driver.py','three_context_io.py','three_context_runner.py','three_context_execution_policy.py',
 'three_context_current_transport.py','three_context_final.py','three_context_policy.py','three_context_local.py',
 'checked_transfer.py','fresh_stage.py','continuation_policy.py','ci_transport.py','origin_transport.py',
 'toolchain_install.py','FinalExportAudit.lean','admission_evidence.py','ci_failure.py'}

def bootstrap(code,contract_hash):
    def need(ok):
        if not ok:raise RuntimeError('driver bootstrap pin/path/schema mismatch')
    need(type(contract_hash) is str and len(contract_hash)==64 and all(c in '0123456789abcdef' for c in contract_hash))
    for x in (code,*code.parents):need(not x.is_symlink())
    path=code/'four_context_contract.json';st=path.lstat();need(stat.S_ISREG(st.st_mode) and st.st_nlink==1 and st.st_size<4*1024**2)
    raw=path.read_bytes();need(hashlib.sha256(raw).hexdigest()==contract_hash)
    def pairs(rows):
        out={}
        for k,v in rows:need(k not in out);out[k]=v
        return out
    contract=json.loads(raw,object_pairs_hook=pairs,parse_constant=lambda _:(_ for _ in ()).throw(ValueError('nonfinite contract')))
    pins=contract.get('implementation_sha256');need(type(pins) is dict and set(pins)==CODE_FILES)
    for name,digest in pins.items():
        file=code/name;st=file.lstat();need(stat.S_ISREG(st.st_mode) and st.st_nlink==1 and hashlib.sha256(file.read_bytes()).hexdigest()==digest)
    need(contract.get('review_status')=='reviewed_for_execution' and contract.get('four_context_integration_review_status')=='reviewed')
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

ACQUISITION_PAIRS=(('AUTHORIZATION', 'API_PATH_REJECTED'), ('AUTHORIZATION', 'API_QUOTA_OR_AUTHORIZATION'), ('AUTHORIZATION', 'API_SOURCE_BINDING'), ('AUTHORIZATION', 'STORAGE_CREDENTIAL_REJECTED'), ('AUTHORIZATION', 'STORAGE_REDIRECT_REJECTED'), ('AUTHORIZATION', 'TOKEN_MISSING_OR_INVALID'), ('CAPACITY', 'DISK_FULL'), ('CAPACITY', 'DISK_HEADROOM'), ('CAPACITY', 'FILE_DESCRIPTORS'), ('CAPACITY', 'GLOBAL_RAW_LEDGER'), ('CAPACITY', 'HISTORICAL_GLOBAL_LEDGER'), ('CAPACITY', 'INODE_HEADROOM'), ('CAPACITY', 'MEMORY_FAILURE'), ('CLEANUP', 'METADATA_ERROR_CLEANUP'), ('CLEANUP', 'METADATA_RESPONSE_CLEANUP'), ('CLEANUP', 'QUARANTINE_CLEANUP'), ('CLEANUP', 'QUOTA_RESPONSE_CLEANUP'), ('DEADLINE', 'METADATA_DEADLINE_EXPIRED'), ('DEADLINE', 'ORIGINAL_AGE_EXPIRED'), ('DEADLINE', 'QUOTA_CLOCK_INVALID'), ('DEADLINE', 'QUOTA_PACING_BUDGET'), ('DEADLINE', 'QUOTA_REQUEST_BUDGET'), ('DEADLINE', 'QUOTA_SLEEP_NO_PROGRESS'), ('DEADLINE', 'QUOTA_TIMEOUT_BUDGET'), ('DEADLINE', 'QUOTA_WAIT_BUDGET'), ('DEADLINE', 'REQUEST_TIMEOUT_INVALID'), ('DEADLINE', 'SHARED_DEADLINE_EXPIRED'), ('ENVELOPE', 'AFFINITY_REJECTED'), ('ENVELOPE', 'INTERPRETER_FLAGS'), ('FILESYSTEM', 'FILESYSTEM_PERMISSION'), ('FILESYSTEM', 'OS_FAILURE'), ('FILESYSTEM', 'QUARANTINE_CANONICAL'), ('FILESYSTEM', 'QUARANTINE_EMPTY'), ('FILESYSTEM', 'QUARANTINE_FRESH'), ('FILESYSTEM', 'QUARANTINE_MODE'), ('FILESYSTEM', 'QUARANTINE_OWNER'), ('HTTP', 'HTTP_STATUS_REJECTED'), ('IDENTITY', 'DUPLICATE_TERMINAL_JOB'), ('IDENTITY', 'PREPARE_METADATA_CHANGED'), ('IDENTITY', 'STAGE_METADATA_CHANGED'), ('IDENTITY', 'TERMINAL_SNAPSHOT_CHANGED'), ('NETWORK', 'NETWORK_DNS'), ('NETWORK', 'NETWORK_FAILURE'), ('NETWORK', 'NETWORK_TIMEOUT'), ('PAYLOAD', 'NATIVE_RECEIPT_PIN'), ('PAYLOAD', 'NATIVE_TAR_PIN'), ('PAYLOAD', 'ZIP_SIZE_DIGEST'), ('QUOTA_SCHEMA', 'QUOTA_DATE'), ('QUOTA_SCHEMA', 'QUOTA_HEADERS_UNAVAILABLE'), ('QUOTA_SCHEMA', 'QUOTA_HEADER_CONFLICT'), ('QUOTA_SCHEMA', 'QUOTA_HEADER_SHAPE'), ('QUOTA_SCHEMA', 'QUOTA_LIMIT_UNEXPECTED'), ('QUOTA_SCHEMA', 'QUOTA_METADATA'), ('QUOTA_SCHEMA', 'QUOTA_NUMERIC_HEADER'), ('QUOTA_SCHEMA', 'QUOTA_REMAINING_RANGE'), ('QUOTA_SCHEMA', 'QUOTA_RESOURCE_UNEXPECTED'), ('QUOTA_SCHEMA', 'QUOTA_USED_RANGE'), ('QUOTA_SCHEMA', 'QUOTA_USED_REMAINING_MISMATCH'), ('QUOTA_WINDOW', 'QUOTA_CLOCK_BACKWARD'), ('QUOTA_WINDOW', 'QUOTA_EXHAUSTED'), ('QUOTA_WINDOW', 'QUOTA_REMAINING_INCREASED'), ('QUOTA_WINDOW', 'QUOTA_RESET_EARLY'), ('QUOTA_WINDOW', 'QUOTA_RESET_WINDOW'), ('REJECTION', 'UNCLASSIFIED_REJECTION'), ('SOURCE', 'HISTORICAL_PINS_MISMATCH'), ('SOURCE', 'SPEC_PIN_MISMATCH'))
PHASES=('entry','acquisition_session','current_bootstrap','clean_checkouts','source_pins','admission_witness',
 'runtime_download','runtime_install','runtime_inventory','runtime_verify','execution_context','historical_acquisition',
 'stage_descriptor','stage_restore_build','stage_command','final_restore','final_command','final_pack',
 'final_acquisition','verdict_reauthentication','verdict')
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

def load_acquisition(root,contract,local,budget):
    root=local.canonical(str(root));base=root.parent
    pins=contract['production_acquisition_sha256']
    expected={'ci/production90_acquisition.py','ci/PRODUCTION90_ACQUISITION_SPEC.json',
              *('frozen_downloader/ci/'+n for n in ('historical_acquisition.py','historical_acquisition_pins.json',
                 'origin_transport.py','fresh_stage.py','continuation_policy.py','ci_transport.py'))}
    local.need(type(pins) is dict and set(pins)==expected,'production acquisition graph changed')
    for name,digest in pins.items():budget.check();local.read_pinned(base/name,digest)
    names=('fresh_stage','continuation_policy','ci_transport','origin_transport','historical_acquisition')
    saved={n:sys.modules.get(n) for n in names};oldpath=list(sys.path);bytecode=sys.dont_write_bytecode
    local.need(threading.active_count()==1 and threading.current_thread() is threading.main_thread(),'single owner import required')
    try:
        sys.dont_write_bytecode=True
        for n in names:sys.modules.pop(n,None)
        path=root/'production90_acquisition.py'
        spec=importlib.util.spec_from_file_location('_production90_fixed',path)
        module=importlib.util.module_from_spec(spec)
        exec(compile(local.read_pinned(path,pins['ci/production90_acquisition.py']),str(path),'exec'),module.__dict__)
        local.need(module.h.f is module.f and module.h.ot is module.ot,'production acquisition import graph changed')
    finally:
        for n,value in saved.items():
            if value is None:sys.modules.pop(n,None)
            else:sys.modules[n]=value
        sys.path[:]=oldpath;sys.dont_write_bytecode=bytecode
    for name,digest in pins.items():budget.check();local.read_pinned(base/name,digest)
    budget.check();return module

def authenticate_acquisition(result,session,module,deadline,nonce,budget,p,local,plan,selection,bundle):
    budget.check()
    root=session.root
    local.need(type(session) is module.BatchProduction90Acquisition and
               session._production_session_state=='consumed' and session.parent_deadline_monotonic==deadline and
               session.session_nonce==nonce and session.opener.transport is session,'live acquisition owner changed')
    local.need(type(result) is dict and set(result)=={'root','wrappers_path','transport_receipt_path','transport_receipt_sha256'} and
               result['root']==str(root) and result['wrappers_path']==str(root/'WRAPPERS.json') and
               result['transport_receipt_path']==str(root/'TRANSPORT_RECEIPT.json'),'acquisition output path changed')
    certificate=p.parse_json(local.read_pinned(root/'TRANSPORT_RECEIPT.json',result['transport_receipt_sha256']))
    local.need(certificate['schema']=='production90-historical-acquisition-v1' and
               certificate['status']=='transport_bytes_authenticated_only' and certificate['proof_pass_claimed'] is False and
               certificate['semantic_admission'] is False and certificate['session_nonce']==nonce and
               certificate['host_deadline_monotonic']==deadline and certificate['acquisition_spec_sha256']==module.SPEC_SHA256 and
               certificate['scope']==session.spec['scope'] and certificate['inputs']==session.spec['inputs'] and
               certificate['accounting']['charged_raw_bytes']==3438714880 and
               certificate['accounting']['aggregate_cap_bytes']==4*1024**3,'acquisition certificate binding changed')
    actual=module.h.retained_files(root);actual.pop('TRANSPORT_RECEIPT.json')
    local.need(actual==certificate['files'],'acquisition retained membership or bytes changed')
    rows=p.parse_json(local.read_pinned(root/'WRAPPERS.json',certificate['files']['WRAPPERS.json']['sha256']))
    local.need(type(rows) is list and len(rows)==90 and
               [r['wrapper'] for r in rows]==certificate['wrappers'] and
               [r['wrapper']['native_descriptor']['stage_id'] for r in rows]==session.spec['scope']['historical_stage_ids'],
               'acquisition wrapper scope changed')
    for row,record in zip(rows,certificate['stages']):
        budget.check();local.need(type(row) is dict and set(row)=={'wrapper','raw_descriptor_path','raw_receipt_path'},'acquisition row changed')
        w=row['wrapper'];sid=w['native_descriptor']['stage_id']
        local.need(record['stage_id']==sid and p._wrapper_pin(w,selection,bundle,plan)==selection.row(sid).pin,'acquisition selected pin changed')
        for key,recordkey in (('raw_descriptor_path','raw_descriptor'),('raw_receipt_path','raw_receipt')):
            expected=root/record[recordkey]['path']
            local.need(str(expected)==row[key] and record[recordkey]['path'] in certificate['files'],'acquisition raw path changed')
            local.read_pinned(expected,record[recordkey]['sha256'])
        p.validate_native_bytes(w,Path(row['raw_descriptor_path']).read_bytes(),Path(row['raw_receipt_path']).read_bytes())
        budget.check()
    local.need(len(certificate['stages'])==90,'acquisition stage map changed')
    budget.check();return {r['wrapper']['native_descriptor']['stage_id']:copy.deepcopy(r) for r in rows}

def write_failure(state,error):
    # Nothing from arbitrary exception arguments, responses, argv or environment.
    root=state.get('root')
    if type(root) is not type(Path('/')) or not root.is_dir() or root.is_symlink():return
    phase=state.get('phase');phase=phase if phase in PHASES else 'bootstrap'
    value={'schema':'four-context-failure-v1','status':'incomplete','proof_pass_claimed':False,
           'phase':phase,'reason_code':'REQUIRED_GATE_FAILED','native_result':_safe_native_result(state.get('native_result'))}
    if type(error) is MemoryError:value['reason_code']='MEMORY_FAILURE'
    elif type(error) is TimeoutError:value['reason_code']='TIMEOUT'
    elif type(error) is PermissionError:value['reason_code']='FILESYSTEM_PERMISSION'
    elif type(error) is FileNotFoundError:value['reason_code']='MISSING_FILE'
    elif type(error) is OSError:value['reason_code']='OS_FAILURE'
    module=state.get('acquisition_module')
    if phase in ('acquisition_session','historical_acquisition','verdict_reauthentication') and module is not None:
        record=module._diagnostic_record(error)
        # Exact source-fixed numeric projection, revalidated before serialization.
        if (type(record) is dict and set(record)=={'schema','phase','category','reason_code','http_status','quota'} and
            all(type(record[k]) is str for k in ('schema','phase','category','reason_code')) and
            record['schema']=='production90-acquisition-failure-v2' and record['phase'] in module.DIAGNOSTIC_PHASES and
            (record['category'],record['reason_code']) in ACQUISITION_PAIRS and
            (record['http_status'] is None or type(record['http_status']) is int and 100<=record['http_status']<=599)):
            quota=record['quota']
            if quota is None or (type(quota) is dict and set(quota)=={'limit','remaining','used','reset','resource'} and
                all(type(quota[k]) is int and 0<=quota[k]<=9999999999 for k in ('limit','remaining','used','reset')) and
                type(quota['resource']) is str and quota['resource'] in ('CORE','OTHER')):
                value['acquisition']={**record,'quota':None if quota is None else dict(quota)}
    command=state.get('command')
    if type(command) is dict:
        if set(command)=={'kind','stage_id','phase'} and command['kind']=='stage' and command['stage_id'] in ('build_087','build_091','build_092') and command['phase'] in ('compile','check'):value['command']=dict(command)
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
    state={'phase':'bootstrap','position':'before','completed':[]}
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('role');ap.add_argument('--stage')
    ap.add_argument('--contract-sha256',required=True);ap.add_argument('--pipeline',type=Path,required=True)
    ap.add_argument('--source',type=Path,required=True);ap.add_argument('--prior',type=Path,required=True);ap.add_argument('--latest',type=Path,required=True)
    args=ap.parse_args();code=Path(__file__).absolute().parent;contract=bootstrap(code,args.contract_sha256)
    import fresh_stage as f
    import four_context_policy as p
    import three_context_local as local
    import three_context_io as dio
    import four_context_final as cf
    import four_context_policy as ep
    import four_context_current_transport as current
    from four_context_runner import FourContextRunner
    from admission_evidence import load_verified_admission
    from toolchain_install import install_archive
    try:
        with dio.JobBudget(entry=ENTRY_MONOTONIC) as budget:
            execute(args,code,contract,budget,f,p,local,dio,cf,ep,current,FourContextRunner,load_verified_admission,install_archive,token=token,state=state)
    except BaseException as error:
        write_failure(state,error)
        raise SystemExit('four-context verification rejected; bounded diagnostics retained') from None
    finally: token=None

def execute(args,code,contract,budget,f,p,local,dio,cf,ep,current,Runner,load_verified_admission,install_archive,*,token,state):
    budget.check();mark(state,'entry')
    pipeline=local.canonical(str(args.pipeline));source=local.canonical(str(args.source));prior=local.canonical(str(args.prior));latest=local.canonical(str(args.latest))
    f.need(code==pipeline/'ci','driver must be exact ci child of current checkout')
    f.need(args.role in {'prepare','build','export_target','fresh_kernel','lean_export','nanoda','conron','verdict'} and
           ((args.role=='build')==(args.stage is not None)),'role/stage mismatch')
    root=local.canonical(str(Path(os.environ['RUNNER_TEMP'])/('hierarchy-c-'+args.role+(('-'+args.stage) if args.stage else ''))))
    f.need(not root.exists(),'job workspace must be new');root.mkdir(mode=0o700);(root/'upload').mkdir();(root/'logs').mkdir()
    upload=root/'upload';state['root']=root
    mark(state,'acquisition_session')
    historical_module=load_acquisition(pipeline/'acquisition/ci',contract,local,budget)
    state['acquisition_module']=historical_module
    nonce=secrets.token_hex(32)
    def observed_now():budget.check();return budget.last_wall
    historical=historical_module.create_session(root/'historical-downloads',token,deadline_monotonic=float(budget.deadline),session_nonce=nonce,now=observed_now)
    original_deadline=historical.parent_deadline_monotonic
    hroot=historical.root
    mark(state,'current_bootstrap')
    transport=current.Transport(token=token,opener=historical.opener)
    f.need(os.environ.get('GITHUB_REF')=='refs/heads/verify/hierarchy-c-production-continuation-20261018','unreviewed current branch')
    mark(state,'clean_checkouts')
    for checkout,expected in [(source,p.PRIOR_SOURCE),(prior,p.PRIOR_PIPELINE),(latest,p.LATEST_PIPELINE),(pipeline,transport.commit)]:
        budget.check();f.need(git(checkout,'rev-parse','HEAD')==expected and git(checkout,'status','--porcelain=v1','--untracked-files=all','--ignored')=='','checkout identity or clean tree mismatch')
    mark(state,'source_pins')
    for name,digest in contract['implementation_sha256'].items():local.read_pinned(code/name,digest)
    bundle_raw=local.read_pinned(code/'FOUR_CONTEXT_BUNDLE.json',p.BUNDLE_SHA256);bundle=p.validate_context_bundle(bundle_raw,p.BUNDLE_SHA256)
    selection_raw=local.read_pinned(code/'four_context_selection.json',contract['selection_sha256'])
    plan=f.pinned_load(code/'plan.json',p.PLAN_SHA256);profiles=f.pinned_load(code/'profiles.json',contract['profiles_sha256'])
    selection=p.parse_selection(selection_raw,contract['selection_sha256'],plan,bundle,require_payloads=True)
    manifest=f.pinned_load(source/'SOURCE_MANIFEST.json',p.PRIOR_MANIFEST)
    prior_files_raw=local.read_pinned(pipeline/'admission/inputs/PRIOR_FILES.json',cf.PRIOR_FILES_SHA256)
    prior_files=p.parse_json(prior_files_raw)
    with local.frozen_prior(prior,prior_files) as native:
        old_manifest=native.f.pinned_load(prior/'ci/original/SOURCE_MANIFEST.json',p.OLD_MANIFEST)
        prior_contract=native.f.pinned_load(prior/'ci/continuation_contract.json',bundle.prior_context['identity']['contract_sha256'])
        source_delta=native.f.pinned_load(prior/'ci/source_delta.json',p.SOURCE_DELTA)
    identity={**bundle.latest_context['identity'],'pipeline_commit':transport.commit,'contract_sha256':args.contract_sha256,
        'run_started_at':transport.run['created_at'],'run_id':transport.run_id,'run_attempt':transport.attempt,
        'selection_sha256':selection.raw_sha256,'prior_identity_sha256':p.PRIOR_IDENTITY,'context_bundle_sha256':bundle.raw_sha256,
        'latest_identity_sha256':p.LATEST_IDENTITY,'profiles_sha256':p.CURRENT_PROFILES}
    p.validate_current_identity(identity,selection,bundle,pipeline_commit=transport.commit,contract_sha256=args.contract_sha256)
    workflow=current.current_workflow_from_run(transport,contract['current_workflow'],pipeline)
    origins=current.CurrentOriginTransport(transport,bundle_bytes=bundle_raw,selection_bytes=selection_raw,
        selection_sha256=selection.raw_sha256,plan=plan,current_context={'identity':identity,'workflow':workflow},
        pipeline_commit=transport.commit,contract_sha256=args.contract_sha256,now=observed_now,
        consumer_roles=contract['current_consumer_roles'],consumer_role=args.stage if args.role=='build' else args.role,
        github_job=os.environ.get('GITHUB_JOB'),opener=historical.opener)
    pins={'current_pipeline_commit':transport.commit,'current_contract_sha256':args.contract_sha256,
        'selection_sha256':selection.raw_sha256,'admission_certificate_sha256':contract['admission_certificate_sha256'],
        'admission_reconciliation_sha256':contract['admission_reconciliation_sha256'],'current_workflow_id':workflow['workflow_id']}
    budget.tighten_wall(p.deadline_check(bundle,selection,observed_now(),current_identity=identity).timestamp())
    def authenticate_current():
        budget.check();origins._run('CurrentOrigin');origins._verify_workflow_source('CurrentOrigin');budget.check()
    authenticate_current()
    mark(state,'admission_witness')
    admission_pin=f.pinned_load(code/'ADMISSION_PIN.json',contract['admission_pin_sha256'])
    admitted=load_verified_admission(origins,admission_pin,root/'admission-evidence',budget.remaining)
    certificate=local.read_pinned(Path(admitted['completion_path']),pins['admission_certificate_sha256'])
    reconciliation=local.read_pinned(Path(admitted['reconciliation_path']),pins['admission_reconciliation_sha256'])
    f.need(local.read_pinned(Path(admitted['selection_path']),'e7565dcc7925d05aa44225bc916bfd1a18d50b75c5438b07b1ea67d376b33549')==cf.original_admission_context(selection,bundle,pins)[0].raw_bytes,'admission selected bytes differ')
    cf.validate_admission_certificate(certificate,selection=selection,bundle=bundle,current_identity=identity,integration_pins=pins)
    cf.validate_admission_reconciliation(reconciliation,certificate_bytes=certificate,current_identity=identity,integration_pins=pins,now=observed_now())
    if args.role!='prepare':
        authenticate_current()
        origins.authenticate_prepare('OldOrigin',root/'current-transport-original-prepare')
        origins.authenticate_prepare('CurrentOrigin',root/'prepare')
    authenticate_current()
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
    ep.validate_execution_context(plan=plan,profiles=profiles,current_contract=contract,current_manifest=manifest,
        old_manifest=old_manifest,prior_manifest=manifest,source_delta=source_delta,inventory=inventory,current_identity=identity,
        selection=selection,bundle=bundle,integration_pins=pins,prior_contract=prior_contract)
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
        f.need(args.stage in ('build_087','build_091','build_092') and stage_command_index<2,'fixed production command index changed')
        state['command']={'kind':'stage','stage_id':args.stage,'phase':('compile','check')[stage_command_index]}
        stage_command_index+=1
        mark(state,'stage_command')
        return budget.process(lambda:safe_native(f,state,*a,**kw))
    runner=Runner(selection=selection,bundle=bundle,integration_pins=pins,current_authority=origins,prior_root=prior,
        admission_root=pipeline/'admission',prior_files_bytes=prior_files_raw,old_manifest=old_manifest,prior_manifest=manifest,
        source_delta=source_delta,prior_contract=prior_contract,host_deadline_monotonic=budget.deadline,latest_root=latest,
        contract=contract,manifest=manifest,plan=plan,profiles=profiles,identity=identity,source_root=root/'source',
        toolchain_root=toolchain,toolchain_inventory=inventory,workspace=root/'stage',executor=stage_executor)
    raw_native={}
    historical_rows=None
    def stage_descriptors(ids):
        nonlocal historical_rows
        mark(state,'historical_acquisition')
        if historical_rows is None:
            acquired=historical_module.acquire_session(historical)
            historical_rows=authenticate_acquisition(acquired,historical,historical_module,original_deadline,nonce,budget,p,local,plan,selection,bundle)
        wrappers=[];sizes={}
        for sid in ids:
            budget.check();row=selection.row(sid);origin=type(row).__name__
            mark(state,'stage_descriptor')
            if origin=='CurrentOrigin':
                w=origins.download_stage(origin,sid,root/'download'/sid,contract['max_artifact_bytes']+1024**2)
                reader=types.SimpleNamespace(root=root,_check_age=lambda:(origins._check_age(),budget.check()))
                receipt_path=historical_module.h.copy_native_receipt(reader,w)
                descriptor_path=Path(w['archive_path']).parent/'upload-candidate.json'
            else:
                retained=historical_rows[sid];w=retained['wrapper']
                descriptor_path=Path(retained['raw_descriptor_path']);receipt_path=Path(retained['raw_receipt_path'])
                f.need(p._wrapper_pin(w,selection,bundle,plan)==row.pin,'historical admitted payload pin changed')
            raw_native[sid]={'descriptor':descriptor_path.read_bytes(),'receipt':Path(receipt_path).read_bytes()}
            p.validate_native_bytes(w,raw_native[sid]['descriptor'],raw_native[sid]['receipt'])
            sizes[sid]=w['native_descriptor']['archive_bytes'];p.cumulative_raw_budget(selection,sizes);wrappers.append(w);budget.check()
        return wrappers
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
        sid=args.stage;f.need(sid in runner.stages and os.environ['GITHUB_JOB']==runner.stages[sid]['producer_job'],'stage/workflow binding mismatch')
        ids,_,_=ep.scope_stage_ids(plan,selection,target_stage=sid);f.extract_sources(source/'hierarchy-c-sources.tar.gz',root/'source',manifest)
        ds=stage_descriptors(ids);mark(state,'stage_restore_build');runner.run(sid,ds,os.environ['GITHUB_JOB'],native_bytes=raw_native);budget.check()
        for name in ['delta.tar','upload-candidate.json']:shutil.move(str(root/'stage'/name),upload/name)
        budget.check();return
    TARGET_MODULE=cf.TARGET_MODULE;TARGET=cf.TARGET
    if args.role in ('export_target','fresh_kernel'):
        ids,_,_=ep.scope_stage_ids(plan,selection,final_role=args.role);f.extract_sources(source/'hierarchy-c-sources.tar.gz',root/'source',manifest)
        ds=stage_descriptors(ids);mark(state,'final_restore');runner.restore_final(args.role,ds,native_bytes=raw_native)
        before={name:f.file_sha(path) for name,path in f.regular_tree(root/'stage'/'objects').items()}
        env['LEAN_PATH']=str(root/'stage'/'objects')+':'+str(toolchain/'lib/lean')
        provenance=cf.resolve_provenance(plan=plan,selection=selection,bundle=bundle,wrappers=ds,current_identity=identity,integration_pins=pins)
        context=cf.final_context(manifest=manifest,provenance=provenance,object_hashes=before,current_identity=identity,integration_pins=pins)
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
        receipt,expanded,_,_=get_final('export_target');exported=expanded/'target.ndjson';execution_paths['export_path']=str(exported)
        context=cf.final_context(manifest=manifest,provenance={'rows':receipt['resolved_provenance'],'sha256':receipt['resolved_provenance_sha256']},object_hashes=receipt['restored_object_hashes'],current_identity=identity,integration_pins=pins)
        f.need(f.file_sha(exported)==receipt['export_sha256'],'exact-target export changed')
        if args.role=='lean_export':
            command('lean_from_export',[str(toolchain/'bin/leanchecker'),'--silent','--from-export',str(exported)],seconds=9000)
            command('lake_export_axioms',[str(toolchain/'bin/lake'),'check','--from-export',str(exported)],seconds=9000,sandbox_sessions=True)
        elif args.role=='nanoda':
            config=cf.nanoda_configuration(execution_paths)
            cfg=root/'nanoda.json';cfg.write_bytes(f.json_bytes(config));context['nanoda_config']=config
            command('nanoda',[str(toolchain/'bin/nanoda_bin'),str(cfg)],rss=6*1024**3)
        else:command('conron',[str(toolchain/'bin/con-ron'),'--verified','--jobs=2',str(exported)],rss=3*1024**3)
        files={p.name:p for p in (root/'logs').iterdir()}
        if args.role=='nanoda':files['nanoda.json']=root/'nanoda.json'
        runner.check_run_age();pack_final(args.role,{**context,'export_sha256':receipt['export_sha256']},files);return
    checked={}
    for role in cf.FINAL_ROLES:
        receipt,_,_,wrapper=get_final(role);checked[role]={'receipt':receipt,'wrapper':wrapper}
    export_receipt=checked['export_target']['receipt'];provenance={'rows':export_receipt['resolved_provenance'],'sha256':export_receipt['resolved_provenance_sha256']}
    mark(state,'verdict_reauthentication')
    historical.refresh_terminal_snapshots(final=False)
    for wrapper in provenance['rows']:
        budget.check();row=selection.row(wrapper['native_descriptor']['stage_id'])
        if type(row) is p.CurrentOrigin:
            meta=origins.reauthenticate_wrapper(wrapper)
            f.need(meta==wrapper['authenticated_metadata'],'resolved producer metadata changed')
        else:
            historical.reauthenticate_selected(wrapper)
    historical.refresh_terminal_snapshots(final=True)
    raw_receipts=dio.native_receipts_from_text(plan,provenance,export_receipt.get('native_stage_receipts_utf8'),cf)
    mark(state,'verdict')
    verdict=cf.final_verdict(plan=plan,manifest=manifest,prior_manifest=manifest,current_identity=identity,selection=selection,bundle=bundle,
        integration_pins=pins,admission_certificate_bytes=certificate,admission_reconciliation_bytes=reconciliation,
        resolved_provenance=provenance,native_receipt_bytes=raw_receipts,checked=checked,now=observed_now(),current_max_age_seconds=contract['max_run_age_seconds'])
    budget.check();(upload/'verdict.json').write_bytes(f.json_bytes(verdict));budget.check();print(json.dumps(verdict,sort_keys=True));budget.check()

if __name__=='__main__':main()
