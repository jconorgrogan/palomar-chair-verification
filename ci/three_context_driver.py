#!/usr/bin/env python3
"""INACTIVE three-context hierarchy C driver. Exact release pins/review required."""
from __future__ import annotations
import argparse,hashlib,importlib.util,json,os,shutil,stat,subprocess,sys,time,types,urllib.request
from pathlib import Path
from datetime import datetime,timezone
ENTRY_MONOTONIC=time.monotonic()

# No package code executes before its caller-pinned contract and complete code
# table have been authenticated. The workflow authenticates all clean checkouts
# before invoking this entrypoint as an additional independent gate.
CODE_FILES={'three_context_driver.py','three_context_io.py','three_context_runner.py','three_context_execution_policy.py',
 'three_context_current_transport.py','three_context_final.py','three_context_policy.py','three_context_local.py',
 'checked_transfer.py','fresh_stage.py','continuation_policy.py','ci_transport.py','origin_transport.py',
 'toolchain_install.py','FinalExportAudit.lean','admission_evidence.py','ci_failure.py'}

def bootstrap(code,contract_hash):
    def need(ok):
        if not ok:raise RuntimeError('driver bootstrap pin/path/schema mismatch')
    need(type(contract_hash) is str and len(contract_hash)==64 and all(c in '0123456789abcdef' for c in contract_hash))
    for x in (code,*code.parents):need(not x.is_symlink())
    path=code/'three_context_contract.json';st=path.lstat();need(stat.S_ISREG(st.st_mode) and st.st_nlink==1 and st.st_size<4*1024**2)
    raw=path.read_bytes();need(hashlib.sha256(raw).hexdigest()==contract_hash)
    def pairs(rows):
        out={}
        for k,v in rows:need(k not in out);out[k]=v
        return out
    contract=json.loads(raw,object_pairs_hook=pairs,parse_constant=lambda _:(_ for _ in ()).throw(ValueError('nonfinite contract')))
    pins=contract.get('implementation_sha256');need(type(pins) is dict and set(pins)==CODE_FILES)
    for name,digest in pins.items():
        file=code/name;st=file.lstat();need(stat.S_ISREG(st.st_mode) and st.st_nlink==1 and hashlib.sha256(file.read_bytes()).hexdigest()==digest)
    need(contract.get('review_status')=='reviewed_for_execution' and contract.get('three_context_integration_review_status')=='reviewed')
    sys.path.insert(0,str(code));sys.dont_write_bytecode=True
    return contract

def git(root,*args):
    return subprocess.run(['/usr/bin/git','-C',str(root),*args],check=True,text=True,
                          stdout=subprocess.PIPE,stderr=subprocess.PIPE).stdout.strip()

def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('role');ap.add_argument('--stage')
    ap.add_argument('--contract-sha256',required=True);ap.add_argument('--pipeline',type=Path,required=True)
    ap.add_argument('--source',type=Path,required=True);ap.add_argument('--prior',type=Path,required=True)
    args=ap.parse_args();code=Path(__file__).absolute().parent;contract=bootstrap(code,args.contract_sha256)
    import fresh_stage as f
    import three_context_policy as p
    import three_context_local as local
    import three_context_io as dio
    import three_context_final as cf
    import three_context_execution_policy as ep
    import three_context_current_transport as current
    from three_context_runner import ThreeContextRunner
    from admission_evidence import load_verified_admission
    from toolchain_install import install_archive
    with dio.JobBudget(entry=ENTRY_MONOTONIC) as budget:
        execute(args,code,contract,budget,f,p,local,dio,cf,ep,current,ThreeContextRunner,load_verified_admission,install_archive)

def execute(args,code,contract,budget,f,p,local,dio,cf,ep,current,Runner,load_verified_admission,install_archive):
    budget.check()
    pipeline=local.canonical(str(args.pipeline));source=local.canonical(str(args.source));prior=local.canonical(str(args.prior))
    f.need(code==pipeline/'ci','driver must be exact ci child of current checkout')
    f.need(args.role in {'prepare','build','export_target','fresh_kernel','lean_export','nanoda','conron','verdict'} and
           ((args.role=='build')==(args.stage is not None)),'role/stage mismatch')
    transport=current.Transport()
    f.need(os.environ.get('GITHUB_REF')=='refs/heads/verify/hierarchy-c-three-context-20261016','unreviewed current branch')
    for root,expected in [(source,p.PRIOR_SOURCE),(prior,p.PRIOR_PIPELINE),(pipeline,transport.commit)]:
        budget.check();f.need(git(root,'rev-parse','HEAD')==expected and git(root,'status','--porcelain=v1','--untracked-files=all','--ignored')=='','checkout identity or clean tree mismatch')
    for name,digest in contract['implementation_sha256'].items():local.read_pinned(code/name,digest)
    bundle_raw=local.read_pinned(code/'CONTEXT_BUNDLE.json',p.BUNDLE_SHA256);bundle=p.validate_context_bundle(bundle_raw,p.BUNDLE_SHA256)
    selection_raw=local.read_pinned(code/'three_context_selection.json',contract['selection_sha256'])
    plan=f.pinned_load(code/'plan.json',p.PLAN_SHA256);profiles=f.pinned_load(code/'profiles.json',contract['profiles_sha256'])
    selection=p.parse_selection(selection_raw,contract['selection_sha256'],plan,bundle,require_payloads=True)
    manifest=f.pinned_load(source/'SOURCE_MANIFEST.json',p.PRIOR_MANIFEST)
    prior_files_raw=local.read_pinned(pipeline/'admission/inputs/PRIOR_FILES.json',cf.PRIOR_FILES_SHA256)
    prior_files=p.parse_json(prior_files_raw)
    with local.frozen_prior(prior,prior_files) as native:
        old_manifest=native.f.pinned_load(prior/'ci/original/SOURCE_MANIFEST.json',p.OLD_MANIFEST)
        prior_contract=native.f.pinned_load(prior/'ci/continuation_contract.json',bundle.prior_context['identity']['contract_sha256'])
        source_delta=native.f.pinned_load(prior/'ci/source_delta.json',p.SOURCE_DELTA)
    identity={**bundle.prior_context['identity'],'pipeline_commit':transport.commit,'contract_sha256':args.contract_sha256,
        'run_started_at':transport.run['created_at'],'run_id':transport.run_id,'run_attempt':transport.attempt,
        'selection_sha256':selection.raw_sha256,'prior_identity_sha256':p.PRIOR_IDENTITY,'context_bundle_sha256':bundle.raw_sha256}
    p.validate_current_identity(identity,selection,bundle,pipeline_commit=transport.commit,contract_sha256=args.contract_sha256)
    workflow=current.current_workflow_from_run(transport,contract['current_workflow'],pipeline)
    def observed_now():budget.check();return budget.last_wall
    origins=current.CurrentOriginTransport(transport,bundle_bytes=bundle_raw,selection_bytes=selection_raw,
        selection_sha256=selection.raw_sha256,plan=plan,current_context={'identity':identity,'workflow':workflow},
        pipeline_commit=transport.commit,contract_sha256=args.contract_sha256,now=observed_now)
    pins={'current_pipeline_commit':transport.commit,'current_contract_sha256':args.contract_sha256,
        'selection_sha256':selection.raw_sha256,'admission_certificate_sha256':contract['admission_certificate_sha256'],
        'admission_reconciliation_sha256':contract['admission_reconciliation_sha256'],'current_workflow_id':workflow['workflow_id']}
    budget.tighten_wall(p.deadline_check(bundle,selection,observed_now(),current_identity=identity).timestamp())
    def authenticate_current():
        budget.check();origins._run('CurrentOrigin');origins._verify_workflow_source('CurrentOrigin');budget.check()
    authenticate_current()
    root=local.canonical(str(Path(os.environ['RUNNER_TEMP'])/('hierarchy-c-'+args.role+(('-'+args.stage) if args.stage else ''))))
    f.need(not root.exists(),'job workspace must be new');root.mkdir(mode=0o700);(root/'upload').mkdir();(root/'logs').mkdir()
    upload=root/'upload'
    admission_pin=f.pinned_load(code/'ADMISSION_PIN.json',contract['admission_pin_sha256'])
    admitted=load_verified_admission(origins,admission_pin,root/'admission-evidence',budget.remaining)
    certificate=local.read_pinned(Path(admitted['completion_path']),pins['admission_certificate_sha256'])
    reconciliation=local.read_pinned(Path(admitted['reconciliation_path']),pins['admission_reconciliation_sha256'])
    f.need(local.read_pinned(Path(admitted['selection_path']),selection.raw_sha256)==selection_raw,'admission selected bytes differ')
    cf.validate_admission_certificate(certificate,selection=selection,bundle=bundle,current_identity=identity,integration_pins=pins)
    cf.validate_admission_reconciliation(reconciliation,certificate_bytes=certificate,current_identity=identity,integration_pins=pins,now=observed_now())
    historical_module=dio.historical_module(pipeline/'acquisition/ci')
    hroot=root/'historical-downloads';hroot.mkdir(mode=0o700)
    historical=historical_module.HistoricalAcquisition(transport.token,hroot,now=observed_now,deadline_monotonic=budget.deadline)
    authenticate_current()
    for origin in ('OldOrigin','CurrentOrigin'):historical.authenticate_prepare(origin,hroot/('prepare-'+origin))
    if args.role!='prepare':
        authenticate_current()
        origins.authenticate_prepare('OldOrigin',root/'current-transport-original-prepare')
        origins.authenticate_prepare('CurrentOrigin',root/'prepare')
    authenticate_current()
    archive=root/'lean.tar.zst';start=time.monotonic();downloaded=0
    with urllib.request.urlopen('https://github.com/leanprover/lean4/releases/download/v4.35.0-rc2/lean-4.35.0-rc2-linux.tar.zst',timeout=60) as response,archive.open('xb') as out:
        while True:
            budget.check();block=response.read(1024**2)
            if not block:break
            downloaded+=len(block);f.need(downloaded<=595391556 and time.monotonic()-start<900,'official release download bound');out.write(block)
    f.need(downloaded==595391556,'official release archive length mismatch');authenticate_current()
    toolchain=root/'toolchain';inventory=install_archive(archive,toolchain);budget.check()
    inventory_path=root/'inventory.json';inventory_path.write_bytes(f.json_bytes(inventory));inventory_sha=f.file_sha(inventory_path)
    f.need(inventory_sha==identity['toolchain_inventory_sha256'],'canonical runtime inventory changed')
    f.verify_toolchain(toolchain,archive,inventory_path,contract,derived_inventory_sha256=inventory_sha)
    ep.validate_execution_context(plan=plan,profiles=profiles,current_contract=contract,current_manifest=manifest,
        old_manifest=old_manifest,prior_manifest=manifest,source_delta=source_delta,inventory=inventory,current_identity=identity,
        selection=selection,bundle=bundle,integration_pins=pins,prior_contract=prior_contract)
    env={'PATH':str(toolchain/'bin')+':/usr/bin:/bin','HOME':str(root),'TMPDIR':str(root),'LANG':'C.UTF-8','LC_ALL':'C.UTF-8',
        'LEAN_NUM_THREADS':'1','LEAN_SYSROOT':str(toolchain),'LEAN_PATH':str(toolchain/'lib/lean')}
    execution_paths={'toolchain_root':str(toolchain),'code_root':str(code),'export_path':str(root/'logs/target_export.stdout'),'nanoda_config_path':str(root/'nanoda.json')}
    results=[]
    def command(name,argv,seconds=18000,rss=8*1024**3,stdout_limit=32*1024**2,sandbox_sessions=False,environment=None):
        budget.check()
        spec={'name':name,'argv':argv,'timeout_seconds':seconds,'resource_limits':{'address_space_bytes':12*1024**3,'rss_tree_bytes':rss,'max_created_file_bytes':stdout_limit},'max_log_bytes':stdout_limit,'new_sessions_explicitly_allowed':sandbox_sessions}
        if args.role!='prepare':
            expected=[x for x in cf.final_command_specs(args.role,execution_paths) if x['name']==name]
            f.need(expected==[spec],'actual command differs from unchanged final specification')
        if args.role in ('lean_export','nanoda','conron'):f.need(f.file_sha(Path(execution_paths['export_path']))==receipt['export_sha256'],'export mutated before command')
        record,out=dio.run_final_command(spec=spec,root=root,environment=environment or env,budget=budget,final=cf)
        results.append(record);(root/'last_command.json').write_bytes(f.json_bytes(record));budget.check()
        if args.role in ('lean_export','nanoda','conron'):f.need(f.file_sha(Path(execution_paths['export_path']))==receipt['export_sha256'],'export mutated during command')
        budget.check();return out
    if args.role=='prepare':
        command('sandbox_preflight',['/usr/bin/bwrap','--ro-bind','/','/','--tmpfs','/home','--tmpfs','/root',
            '--tmpfs','/run/user','--tmpfs','/tmp','--dir','/tmp/home','--dev','/dev','--proc','/proc',
            '--clearenv','--unshare-all','--die-with-parent','--new-session','--','/bin/true'],seconds=30,sandbox_sessions=True)
        f.extract_sources(source/'hierarchy-c-sources.tar.gz',root/'source',manifest);budget.check()
        shutil.copyfile(inventory_path,upload/'inventory.json');(upload/'identity.json').write_bytes(f.json_bytes(identity));budget.check();return
    def stage_executor(*a,**kw):return budget.process(lambda:f.run_process(*a,**kw))
    runner=Runner(selection=selection,bundle=bundle,integration_pins=pins,current_authority=origins,prior_root=prior,
        admission_root=pipeline/'admission',prior_files_bytes=prior_files_raw,old_manifest=old_manifest,prior_manifest=manifest,
        source_delta=source_delta,prior_contract=prior_contract,host_deadline_monotonic=budget.deadline,
        contract=contract,manifest=manifest,plan=plan,profiles=profiles,identity=identity,source_root=root/'source',
        toolchain_root=toolchain,toolchain_inventory=inventory,workspace=root/'stage',executor=stage_executor)
    raw_native={}
    def stage_descriptors(ids):
        wrappers=[];sizes={}
        for sid in ids:
            budget.check();row=selection.row(sid);origin=type(row).__name__
            if origin=='CurrentOrigin':w=origins.download_stage(origin,sid,root/'download'/sid,contract['max_artifact_bytes']+1024**2)
            else:
                native_origin='OldOrigin' if origin=='OldOrigin' else 'CurrentOrigin'
                fixed=next(x for x in historical.pins['stages'] if x['stage_id']==sid and x['origin']==native_origin)
                w=historical.download_stage(native_origin,sid,hroot/sid,contract['max_artifact_bytes']+1024**2,pin=fixed['pin']);w['origin']=origin
                f.need(p._wrapper_pin(w,selection,bundle,plan)==row.pin,'historical admitted payload pin changed')
            reader=types.SimpleNamespace(root=root,_check_age=lambda:(origins._check_age(),budget.check()))
            receipt_path=historical_module.copy_native_receipt(reader,w)
            raw_native[sid]={'descriptor':(Path(w['archive_path']).parent/'upload-candidate.json').read_bytes(),'receipt':Path(receipt_path).read_bytes()}
            p.validate_native_bytes(w,raw_native[sid]['descriptor'],raw_native[sid]['receipt'])
            sizes[sid]=w['native_descriptor']['archive_bytes'];p.cumulative_raw_budget(selection,sizes);wrappers.append(w);budget.check()
        return wrappers
    def pack_final(role,extra,files):
        budget.check();info={name:{'bytes':path.stat().st_size,'sha256':f.file_sha(path)} for name,path in files.items()}
        receipt={'schema':'fresh-final-evidence-v1','role':role,'status':'completed_check_only','proof_pass_claimed':False,
            'identity':identity,'commands':results,'files':info,'execution_paths':execution_paths,**extra}
        cf.validate_final_commands(receipt);payload=upload/'payload.tar';rh=f.write_tar(payload,files,receipt,cf.FINAL_ARTIFACT_LIMIT)
        desc={'schema':'fresh-final-upload-v1','role':role,'identity':identity,'archive_sha256':f.file_sha(payload),'archive_bytes':payload.stat().st_size,'receipt_sha256':rh,'retention_days':7}
        (upload/'upload-candidate.json').write_bytes(f.json_bytes(desc));budget.check()
    def get_final(role):
        budget.check();w=origins.download_final(role,root/'download'/role,cf.FINAL_ARTIFACT_LIMIT+1024**2);d=w['native_descriptor'];expanded=root/'expanded'/role
        receipt=f.extract_verified_archive(Path(w['archive_path']),d,expanded,cf.FINAL_ARTIFACT_LIMIT)
        f.need(receipt['role']==role and receipt['identity']==identity and receipt['status']=='completed_check_only','current final receipt mismatch')
        cf.validate_final_commands(receipt);budget.check();return receipt,expanded,d,w
    if args.role=='build':
        sid=args.stage;f.need(sid in runner.stages and os.environ['GITHUB_JOB']==runner.stages[sid]['producer_job'],'stage/workflow binding mismatch')
        ids,_,_=ep.scope_stage_ids(plan,selection,target_stage=sid);f.extract_sources(source/'hierarchy-c-sources.tar.gz',root/'source',manifest)
        ds=stage_descriptors(ids);runner.run(sid,ds,os.environ['GITHUB_JOB'],native_bytes=raw_native);budget.check()
        for name in ['delta.tar','upload-candidate.json']:shutil.move(str(root/'stage'/name),upload/name)
        budget.check();return
    TARGET_MODULE=cf.TARGET_MODULE;TARGET=cf.TARGET
    if args.role in ('export_target','fresh_kernel'):
        ids,_,_=ep.scope_stage_ids(plan,selection,final_role=args.role);f.extract_sources(source/'hierarchy-c-sources.tar.gz',root/'source',manifest)
        ds=stage_descriptors(ids);runner.restore_final(args.role,ds,native_bytes=raw_native)
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
    for wrapper in provenance['rows']:
        budget.check();row=selection.row(wrapper['native_descriptor']['stage_id'])
        if type(row) is p.CurrentOrigin:meta=origins.reauthenticate_wrapper(wrapper)
        else:
            native_wrapper=json.loads(json.dumps(wrapper));native_origin='OldOrigin' if type(row) is p.OldOrigin else 'CurrentOrigin';native_wrapper['origin']=native_origin
            fixed=next(x for x in historical.pins['stages'] if x['stage_id']==row.stage_id and x['origin']==native_origin)
            meta=historical.reauthenticate_wrapper(native_wrapper,pin=fixed['pin'])
        f.need(meta==wrapper['authenticated_metadata'],'resolved producer metadata changed')
    raw_receipts=dio.native_receipts_from_text(plan,provenance,export_receipt.get('native_stage_receipts_utf8'),cf)
    verdict=cf.final_verdict(plan=plan,manifest=manifest,prior_manifest=manifest,current_identity=identity,selection=selection,bundle=bundle,
        integration_pins=pins,admission_certificate_bytes=certificate,admission_reconciliation_bytes=reconciliation,
        resolved_provenance=provenance,native_receipt_bytes=raw_receipts,checked=checked,now=observed_now(),current_max_age_seconds=contract['max_run_age_seconds'])
    budget.check();(upload/'verdict.json').write_bytes(f.json_bytes(verdict));budget.check();print(json.dumps(verdict,sort_keys=True));budget.check()

if __name__=='__main__':main()
