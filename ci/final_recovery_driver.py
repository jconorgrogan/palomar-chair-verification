#!/usr/bin/env python3
"""One-job Conron recovery producer. Exact reviewed integration contract required."""
from __future__ import annotations
import time
ENTRY_MONOTONIC=time.monotonic()
import argparse
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import shutil
import stat
import sys
import urllib.request

ORIGINAL_CONTRACT_SHA256='e9ba3c36ace2ab45c42c1d1d30e5340ea8935d24b9e7e6b206707e476977db45'
ORIGINAL_DRIVER_SHA256='57c9c4e2b60dae710b4584ae074a7b55bba7a1111eb42d0850c1a828cb0a3878'
ADDITIONS={'final_recovery_driver.py','final_recovery_bridge.py',
           'final_recovery_transport.py','conron_recovery_resources.py',
           'ORIGINAL_PROOF_IDENTITY.json','FINAL_RECOVERY_ORIGINS.json'}


def need(ok,reason):
    if not ok:raise RuntimeError(reason)


def read_pinned(path,digest,maximum=32*1024**2):
    for p in (path,*path.parents):need(not p.is_symlink(),'BOOTSTRAP_PATH')
    st=path.lstat()
    need(stat.S_ISREG(st.st_mode) and st.st_nlink==1 and st.st_size<=maximum,'BOOTSTRAP_FILE')
    raw=path.read_bytes()
    need(type(digest) is str and len(digest)==64 and hashlib.sha256(raw).hexdigest()==digest,
         'BOOTSTRAP_PIN')
    return raw


def parse(raw):
    def pairs(rows):
        value={}
        for k,v in rows:need(k not in value,'DUPLICATE_KEY');value[k]=v
        return value
    return json.loads(raw,object_pairs_hook=pairs,
        parse_constant=lambda _:(_ for _ in ()).throw(RuntimeError('NONFINITE_JSON')))


def bootstrap(code,contract_sha):
    contract=parse(read_pinned(code/'final_recovery_contract.json',contract_sha,1024**2))
    need(contract.get('schema')=='c092-conron-retry-contract-v1' and
         contract.get('review_status')=='reviewed_for_execution' and
         contract.get('role')=='conron' and contract.get('aggregate_verdict')=='not_implemented',
         'REVIEWED_FIXED_CONRON_CONTRACT_REQUIRED')
    need(contract.get('original_contract_sha256')==ORIGINAL_CONTRACT_SHA256,
         'ORIGINAL_CONTRACT_CHANGED')
    original=parse(read_pinned(code/'four_context_contract.json',ORIGINAL_CONTRACT_SHA256))
    pins=contract.get('implementation_sha256')
    need(type(pins) is dict and set(pins)==set(original['implementation_sha256'])|ADDITIONS,
         'EXACT_RUNTIME_GRAPH_REQUIRED')
    for name,digest in original['implementation_sha256'].items():
        need(pins.get(name)==digest,'ORIGINAL_IMPLEMENTATION_CHANGED')
    for name,digest in pins.items():read_pinned(code/name,digest)
    need(pins['four_context_driver.py']==ORIGINAL_DRIVER_SHA256,'ORIGINAL_DRIVER_CHANGED')
    sys.dont_write_bytecode=True
    sys.path.insert(0,str(code))
    # This source is pinned before execution; the unchanged bootstrap independently
    # verifies the old complete implementation graph and contract review state.
    spec=importlib.util.spec_from_file_location('four_context_driver',code/'four_context_driver.py')
    base=importlib.util.module_from_spec(spec);sys.modules[spec.name]=base
    exec(compile(read_pinned(code/'four_context_driver.py',ORIGINAL_DRIVER_SHA256),
                 str(code/'four_context_driver.py'),'exec'),base.__dict__)
    need(base.bootstrap(code,ORIGINAL_CONTRACT_SHA256)==original,'ORIGINAL_BOOTSTRAP_CHANGED')
    return contract,original,base


HEADROOM_REASONS=frozenset(('HEADROOM_CGROUP_COVERING_MOUNT','HEADROOM_CGROUP_DEVICE',
    'HEADROOM_CGROUP_MOUNT','HEADROOM_CGROUP_PATH','HEADROOM_CGROUP_ROOT','HEADROOM_CONTROLLERS',
    'HEADROOM_CONTROLLERS_CHANGED','HEADROOM_CONTROLLER_INCONSISTENT','HEADROOM_FD_CLOSE',
    'HEADROOM_FILE_CHANGED','HEADROOM_FILE_TYPE','HEADROOM_INSUFFICIENT','HEADROOM_LAYOUT_CHANGED',
    'HEADROOM_LIMIT_CHANGED','HEADROOM_MEMINFO','HEADROOM_MOUNT_BOUND','HEADROOM_MOUNT_SCHEMA',
    'HEADROOM_NUMBER','HEADROOM_PATH','HEADROOM_PATH_CHANGED','HEADROOM_READ_BOUND',
    'HEADROOM_REPORT_BOUND','HEADROOM_REQUIRED_FILE','HEADROOM_REQUIRED_LIMIT','HEADROOM_TEXT',
    'HEADROOM_UNSUPPORTED_CGROUP'))


def headroom_failure_reason(error,resources):
    if (type(error) is resources.Rejected and len(error.args)==1 and
        type(error.args[0]) is str and error.args[0] in HEADROOM_REASONS):
        return {'category':'HEADROOM','reason_code':error.args[0]}
    return None


def write_retry_failure(base,state,error):
    base.write_failure(state,error)
    reason=state.get('headroom_failure')
    if (type(reason) is dict and set(reason)=={'category','reason_code'} and
        reason['category']=='HEADROOM' and reason['reason_code'] in HEADROOM_REASONS):
        path=state['root']/'failure/FAILURE.json'
        need(path.is_file() and not path.is_symlink() and path.stat().st_size<=16384,
             'BOUNDED_FAILURE_REQUIRED')
        value=parse(path.read_bytes());value['retry_headroom_failure']=dict(reason)
        raw=(json.dumps(value,sort_keys=True,indent=2,allow_nan=False)+'\n').encode()
        need(len(raw)<=16384,'BOUNDED_FAILURE_REQUIRED');path.write_bytes(raw)


def run_retry_command(*,root,toolchain,exported,env,state,budget,resources,base,f,dio,final):
    """Fixed production call chain; module arguments are fixed imports in execute.

    Tests disclose substitution of the native call and headroom reader only.
    """
    headroom=[];actual_timeout=[]
    def guarded_executor(*a,**kw):
        # run_final_command owns the sole entered Budget.process scope.
        need(budget.in_child and not headroom,'ONE_ORIGINAL_NATIVE_SCOPE')
        try:
            headroom.append(resources.require_headroom(budget))
        except resources.Rejected as error:
            reason=headroom_failure_reason(error,resources)
            if reason is not None:state['headroom_failure']=reason
            raise
        state['retry_headroom']=headroom[0]
        left=budget.remaining()-3
        need(left>0,'HEADROOM_SCAN_EXHAUSTED_CLEANUP_RESERVE')
        kw['timeout']=min(kw['timeout'],left);actual_timeout.append(kw['timeout'])
        return base.safe_native(f,state,*a,**kw)
    spec=resources.conron_spec(str(toolchain),str(exported))
    command,_=dio.run_final_command(spec=spec,root=root,environment=env,budget=budget,
        executor=guarded_executor,final=final)
    command['effective_timeout_seconds']=actual_timeout[0]
    final._successful_command(command,spec)
    return command,headroom[0]


def download_official_archive(archive,budget):
    started=time.monotonic();downloaded=0
    with urllib.request.urlopen('https://github.com/leanprover/lean4/releases/download/v4.35.0-rc2/lean-4.35.0-rc2-linux.tar.zst',timeout=60) as response,archive.open('xb') as out:
        while True:
            budget.check();block=response.read(1024**2)
            if not block:break
            downloaded+=len(block)
            need(downloaded<=595391556 and time.monotonic()-started<900,'OFFICIAL_RELEASE_DOWNLOAD_BOUND')
            out.write(block)
    need(downloaded==595391556,'OFFICIAL_RELEASE_LENGTH')


def execute(args,code,contract,original,base,budget,token,state):
    import fresh_stage as f
    import four_context_policy as p
    import four_context_final as final
    import three_context_local as local
    import three_context_io as dio
    import final_recovery_bridge as bridge
    import conron_recovery_resources as resources
    from final_recovery_transport import FinalRecoveryTransport
    from toolchain_install import install_archive
    budget.check()
    paths=[local.canonical(str(getattr(args,k))) for k in ('pipeline','source','prior','latest')]
    pipeline,source,prior,latest=paths
    need(len(set(paths))==4 and code==pipeline/'ci',
         'EXACT_FOUR_CHECKOUT_LAYOUT')
    need(args.role=='conron' and os.environ.get('GITHUB_JOB')=='conron', 'CONRON_ROLE_ONLY')
    need(os.environ.get('GITHUB_REF')=='refs/heads/'+bridge.WORKFLOW['head_branch'], 'RECOVERY_BRANCH')
    seed={'run_id':os.environ.get('GITHUB_RUN_ID'),'run_attempt':os.environ.get('GITHUB_RUN_ATTEMPT'),
          'pipeline_commit':os.environ.get('GITHUB_SHA')}
    root=local.canonical(str(Path(os.environ['RUNNER_TEMP'])/'hierarchy-c-conron'))
    need(not root.exists(),'FRESH_WORKSPACE_REQUIRED');root.mkdir(mode=0o700)
    (root/'upload').mkdir();(root/'logs').mkdir();state['root']=root
    base.mark(state,'clean_checkouts')
    for checkout,expected in ((pipeline,seed['pipeline_commit']),(source,p.PRIOR_SOURCE),
                              (prior,p.PRIOR_PIPELINE),(latest,p.LATEST_PIPELINE)):
        budget.check()
        need(base.git(checkout,'rev-parse','HEAD')==expected and
             base.git(checkout,'status','--porcelain=v1','--untracked-files=all','--ignored')=='',
             'CLEAN_EXACT_CHECKOUT_REQUIRED')
    base.mark(state,'source_pins')
    for name,digest in contract['implementation_sha256'].items():
        budget.check();local.read_pinned(code/name,digest)
    proof_raw=local.read_pinned(code/'ORIGINAL_PROOF_IDENTITY.json',bridge.PROOF_IDENTITY_SHA256)
    proof=bridge.proof_identity(proof_raw)
    pins=parse(local.read_pinned(code/'FINAL_RECOVERY_ORIGINS.json',
        contract['implementation_sha256']['FINAL_RECOVERY_ORIGINS.json']))
    workflow={**bridge.WORKFLOW,'source_sha256':local.file_sha(pipeline/bridge.WORKFLOW['path'])}
    base.mark(state,'acquisition_session')
    acquisition=base.load_acquisition(pipeline/'acquisition/ci',original,local,budget)
    state['acquisition_module']=acquisition
    def now():budget.check();return budget.last_wall
    transport=FinalRecoveryTransport(token,seed,workflow,pins,acquisition_module=acquisition,
        deadline_monotonic=float(budget.deadline),now=now)
    base.mark(state,'current_bootstrap')
    authenticated=transport.authenticate_execution()
    metadata=authenticated['identity'];workflow=authenticated['workflow']
    need(all(metadata[k]==v for k,v in seed.items()),'AUTHENTICATED_EXECUTION_SEED')
    execution={**metadata,'schema':'c092-final-retry-execution-identity-v1','role':'conron',
        'contract_sha256':args.contract_sha256,'proof_identity_sha256':bridge.PROOF_IDENTITY_SHA256,
        'resource_source_sha256':bridge.RESOURCE_SOURCE_SHA256,
        'workflow_id':workflow['workflow_id'],'workflow_source_sha256':workflow['source_sha256']}
    bridge.validate_execution(execution,proof,workflow)
    def authenticate_current():
        budget.check()
        need(transport.authenticate_execution()==authenticated,'CURRENT_EXECUTION_CHANGED')
        budget.check()
    base.mark(state,'final_acquisition')
    # Reuse the exact old measured allocator: 512 MiB residual, 64 MiB
    # metadata reserve, 256 spare inodes, allocation-unit rounding. No deletion
    # credit. Each next irreversible phase is checked against retained inputs.
    acquisition.h.disk_headroom(root,pins['prepare']['artifact_zip_bytes']+32*1024**2+
        pins['conron_failure']['artifact_zip_bytes']+1024**2+
        pins['export_target']['artifact_zip_bytes']+final.FINAL_ARTIFACT_LIMIT+1024**2,new_files=32)
    prepare=transport.authenticate_prior_prepare(root/'prior-prepare')
    need(local.read_pinned(Path(prepare['identity_path']),bridge.PROOF_IDENTITY_SHA256)==proof_raw,
         'ORIGINAL_PREPARE_IDENTITY')
    expected_inventory=parse(local.read_pinned(Path(prepare['inventory_path']),
        proof['toolchain_inventory_sha256'],8*1024**2))
    failure=transport.authenticate_failure()
    need(failure.get('failure_sha256')==bridge.FAILURE_SHA256,'EXACT_PRIOR_FAILURE_REQUIRED')
    wrapper=transport.download_prior_final('export_target',root/'download/export_target',
                                          final.FINAL_ARTIFACT_LIMIT+1024**2)
    budget.check()
    expanded=root/'expanded/export_target';descriptor=wrapper['native_descriptor']
    # Authenticated fixed export producer writes five flat members including
    # receipt.json; unchanged extractor still validates the full native archive.
    acquisition.h.disk_headroom(root,final.FINAL_ARTIFACT_LIMIT,new_files=16)
    receipt=f.extract_verified_archive(Path(wrapper['archive_path']),descriptor,expanded,
                                       final.FINAL_ARTIFACT_LIMIT)
    budget.check()
    bundle_raw=local.read_pinned(code/'FOUR_CONTEXT_BUNDLE.json',p.BUNDLE_SHA256)
    bundle=p.validate_context_bundle(bundle_raw,p.BUNDLE_SHA256)
    plan=f.pinned_load(code/'plan.json',p.PLAN_SHA256)
    selection_raw=local.read_pinned(code/'four_context_selection.json',original['selection_sha256'])
    selection=p.parse_selection(selection_raw,original['selection_sha256'],plan,bundle,require_payloads=True)
    manifest=f.pinned_load(source/'SOURCE_MANIFEST.json',p.PRIOR_MANIFEST)
    context=bridge.validate_export(receipt=receipt,wrapper=wrapper,proof=proof,manifest=manifest,
        plan=plan,selection=selection,bundle=bundle,integration_pins=pins['proof_integration'],
        now=now(),final=final,io=dio)
    budget.tighten_wall(final._timestamp(context['acceptance_deadline']).timestamp())
    exported=expanded/'target.ndjson'
    need(f.file_sha(exported)==receipt['export_sha256'],'EXACT_EXPORT_BYTES')
    transport.reauthenticate_prior_wrapper(wrapper);authenticate_current()
    acquisition.h.disk_headroom(root,595391556,new_files=1)
    base.mark(state,'runtime_download')
    archive=root/'lean.tar.zst';download_official_archive(archive,budget);authenticate_current()
    base.mark(state,'runtime_install')
    runtime_names=set(expected_inventory['files'])|set(expected_inventory['symlinks'])
    runtime_directories={str(parent) for name in runtime_names for parent in Path(name).parents}
    acquisition.h.disk_headroom(root,5*1024**3,
        new_files=len(runtime_names)+len(runtime_directories)+16)
    toolchain=root/'toolchain';inventory=install_archive(archive,toolchain);budget.check()
    base.mark(state,'runtime_inventory')
    inventory_path=root/'inventory.json';inventory_path.write_bytes(f.json_bytes(inventory))
    inventory_sha=f.file_sha(inventory_path)
    need(inventory_sha==proof['toolchain_inventory_sha256'],'EXACT_ORIGINAL_INVENTORY')
    base.mark(state,'runtime_verify')
    f.verify_toolchain(toolchain,archive,inventory_path,original,derived_inventory_sha256=inventory_sha)
    budget.check();authenticate_current();transport.reauthenticate_prior_wrapper(wrapper)
    paths={'toolchain_root':str(toolchain),'code_root':str(code),'export_path':str(exported),
           'nanoda_config_path':str(root/'nanoda.json')}
    env={'PATH':str(toolchain/'bin')+':/usr/bin:/bin','HOME':str(root),'TMPDIR':str(root),
         'LANG':'C.UTF-8','LC_ALL':'C.UTF-8','LEAN_NUM_THREADS':'1',
         'LEAN_SYSROOT':str(toolchain),'LEAN_PATH':str(toolchain/'lib/lean')}
    need(f.file_sha(exported)==receipt['export_sha256'],'EXPORT_MUTATED_BEFORE_CHECK')
    acquisition.h.disk_headroom(root,32*1024**2,new_files=2)
    base.mark(state,'final_command');state['command']={'kind':'final','name':'conron'}
    command,headroom=run_retry_command(root=root,toolchain=toolchain,exported=exported,
        env=env,state=state,budget=budget,resources=resources,base=base,f=f,dio=dio,final=final)
    # safe_native has already accepted cleanup before run_final_command reads logs.
    bridge.validate_retry_command(command,toolchain_root=str(toolchain),export_path=str(exported),
                                  resources=resources,final=final)
    need(f.file_sha(exported)==receipt['export_sha256'],'EXPORT_MUTATED_DURING_CHECK')
    authenticate_current();transport.reauthenticate_prior_wrapper(wrapper)
    need(transport.authenticate_failure()==failure,'PRIOR_FAILURE_CHANGED')
    context_after=bridge.validate_export(receipt=receipt,wrapper=wrapper,proof=proof,manifest=manifest,
        plan=plan,selection=selection,bundle=bundle,integration_pins=pins['proof_integration'],
        now=now(),final=final,io=dio)
    need(context_after==context,'ORIGINAL_PROOF_CONTEXT_CHANGED')
    base.mark(state,'final_pack')
    retained=root/'retained';retained.mkdir()
    records={'ORIGINAL_PROOF_IDENTITY.json':proof_raw,
        'ORIGINAL_EXPORT_WRAPPER.json':f.json_bytes(context['original_export']),
        'HEADROOM.json':f.json_bytes(headroom),'EXECUTION_IDENTITY.json':f.json_bytes(execution),
        'PRIOR_FAILURE.json':f.json_bytes(failure)}
    acquisition.h.disk_headroom(root,sum(map(len,records.values())),new_files=len(records)+2)
    files={name:root/'logs'/name for name in ('conron.stdout','conron.stderr')}
    for name,raw in records.items():
        budget.check();path=retained/name;path.write_bytes(raw);files[name]=path
    # Preserve the already-validated native receipt in place. Hash and pack it
    # by streaming; do not add a smaller in-memory read/copy cap.
    files['ORIGINAL_EXPORT_RECEIPT.json']=expanded/'receipt.json'
    need(f.file_sha(files['ORIGINAL_EXPORT_RECEIPT.json'])==descriptor['receipt_sha256'],
         'RETAINED_ORIGINAL_RECEIPT_CHANGED')
    files['inventory.json']=inventory_path
    infos={name:{'bytes':path.stat().st_size,'sha256':f.file_sha(path)} for name,path in files.items()}
    result=bridge.retry_receipt(proof_raw=proof_raw,execution=execution,workflow=workflow,
        context=context,command=command,headroom=headroom,files=infos,paths=paths,
        failure_binding=failure,resources=resources,final=final)
    sizes=[len(f.json_bytes(result)),*(path.stat().st_size for path in files.values())]
    tar_bytes=sum(512+((n+511)//512)*512 for n in sizes)+1024
    tar_bytes=((tar_bytes+10239)//10240)*10240
    # Retain payload and allow a separate uncompressed upload ZIP; do not spend
    # the helper's original residual reserve or credit any retained input deletion.
    acquisition.h.disk_headroom(root,2*tar_bytes+1024**2,new_files=4)
    payload=root/'upload/payload.tar'
    rh=f.write_tar(payload,files,result,final.FINAL_ARTIFACT_LIMIT)
    upload={'schema':'c092-final-retry-upload-v1','role':'conron',
        'proof_identity_sha256':bridge.PROOF_IDENTITY_SHA256,'execution_identity':execution,
        'archive_sha256':f.file_sha(payload),'archive_bytes':payload.stat().st_size,
        'receipt_sha256':rh,'retention_days':7}
    (root/'upload/upload-candidate.json').write_bytes(f.json_bytes(upload))
    budget.check();authenticate_current();transport.reauthenticate_prior_wrapper(wrapper);budget.check()


def main():
    token=os.environ.pop('GH_TOKEN','');os.environ.pop('GITHUB_TOKEN',None)
    need(sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode, 'ISOLATED_SOURCE_INTERPRETER')
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('role',choices=['conron'])
    parser.add_argument('--contract-sha256',required=True)
    for name in ('pipeline','source','prior','latest'):parser.add_argument('--'+name,type=Path,required=True)
    args=parser.parse_args();code=Path(__file__).absolute().parent
    contract,original,base=bootstrap(code,args.contract_sha256)
    import three_context_io as dio
    state={'phase':'entry','position':'before','completed':[]}
    try:
        with dio.JobBudget(entry=ENTRY_MONOTONIC) as budget:
            execute(args,code,contract,original,base,budget,token,state)
    except BaseException as error:
        write_retry_failure(base,state,error)
        if state.get('retry_headroom') is not None and state.get('root') is not None:
            import final_recovery_bridge as bridge
            bridge.validate_headroom(state['retry_headroom'])
            failure_root=state['root']/'failure'
            if failure_root.is_dir():
                (failure_root/'HEADROOM.json').write_bytes((json.dumps(state['retry_headroom'],sort_keys=True,indent=2,allow_nan=False)+'\n').encode())
        raise SystemExit('Conron recovery rejected; bounded diagnostics retained') from None
    finally:token=None

if __name__=='__main__':main()
