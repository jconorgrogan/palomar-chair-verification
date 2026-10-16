#!/usr/bin/env python3
"""INACTIVE fixed-origin continuation driver. Requires terminal pinned selection and independent review."""
from __future__ import annotations
import argparse,json,os,shutil,subprocess,time,urllib.request
from pathlib import Path
import fresh_stage as f
from ci_transport import Transport,REPOSITORY
from toolchain_install import install_archive
import continuation_policy as cp
from continuation_runner import ContinuationRunner, mixed_storage_budget
import continuation_final as cf
from origin_transport import OriginTransport, validate_workflow
from datetime import datetime, timezone
MANIFEST_SHA='09b0371c9acc07b07355824e7a7302a810c4247bbbce20d1e497bd4a02a23392'
ARCHIVE_URL='https://github.com/leanprover/lean4/releases/download/v4.35.0-rc2/lean-4.35.0-rc2-linux.tar.zst'
ARCHIVE_BYTES=595391556
TARGET_MODULE='SpectreFinite.RadiusFivePruningHierarchy'
TARGET='SpectreFinite.HexSearch.RadiusFivePruning.certifiedParentOccurrenceTheorem'
TYPE='SpectreFinite.HexSearch.NativeHierarchy.ParentOccurrenceTheorem'
FINAL_ROLES=['export_target','fresh_kernel','lean_export','nanoda','conron']
FINAL_ARTIFACT_LIMIT=3*1024**3

def git(root,*args):
    return subprocess.run(['/usr/bin/git','-C',str(root),*args],check=True,text=True,
                          stdout=subprocess.PIPE,stderr=subprocess.PIPE).stdout.strip()

def successful(result,allow_new_sessions=False):
    f.need(result['exit_code']==0 and all(result.get(k) is False for k in
        ['timed_out','log_overflow','memory_exceeded','surviving_children']) and
        (allow_new_sessions or result.get('escaped_descendants') is False) and
        result.get('process_group_empty') is True and result.get('descendants_empty') is True,
        'checker failed, timed out, exceeded a limit, or lacked child-cleanup evidence')


def current_workflow_from_run(transport, template, pipeline):
    """Resolve only the current workflow ID from the authenticated current run.

    Contract fixes path/name/branch/roles. Numeric ID and source digest are
    deliberately null until authenticated run metadata and the pinned checkout
    provide them. Original-origin mapping is never passed through this helper.
    """
    f.need(isinstance(transport,Transport),'authenticated current Transport required')
    cp.keys(template,{'workflow_id','path','name','head_branch','source_sha256','roles'},'current workflow template')
    f.need(template['workflow_id'] is None and template['source_sha256'] is None,
           'current workflow ID/source must come from authenticated runtime context')
    fixed={'path':'.github/workflows/hierarchy-c-meta-continuation.yml',
           'name':'Continued modern hierarchy C verification (clean rebuild pending)',
           'head_branch':'verify/hierarchy-c-meta-continuation-20261016'}
    f.need(all(template[k]==v for k,v in fixed.items()),'current workflow path/name/branch changed')
    run=transport.run
    f.need(type(run) is dict and type(run.get('id')) is int and run['id']>0 and str(run['id'])==transport.run_id and
           type(run.get('run_attempt')) is int and run['run_attempt']==1 and str(run['run_attempt'])==transport.attempt and
           run.get('head_sha')==transport.commit and run.get('event')=='push',
           'authenticated current run identity changed')
    for key in ('repository','head_repository'):
        repo=run.get(key)
        f.need(type(repo) is dict and type(repo.get('id')) is int and repo['id']==cp.REPOSITORY_ID and
               repo.get('full_name')==REPOSITORY,'current repository/head repository changed')
    f.need(all(run.get(k)==v for k,v in fixed.items()),'current run workflow fields changed')
    cp.integer(run.get('workflow_id'),'authenticated current workflow ID')
    mapping=dict(template);mapping['workflow_id']=run['workflow_id']
    path=Path(pipeline)/f.safe_rel(mapping['path']);f.no_symlink_path(path)
    f.need(path.is_file(),'pinned current workflow source missing')
    mapping['source_sha256']=f.file_sha(path)
    validate_workflow(mapping)
    return mapping


def authenticate_current_workflow(origins):
    """Re-fetch run/workflow/source before any prepare artifact or toolchain I/O."""
    origins._run('CurrentOrigin')
    origins._verify_workflow_source('CurrentOrigin')


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('role');ap.add_argument('--stage');ap.add_argument('--contract-sha256',required=True)
    ap.add_argument('--pipeline',type=Path,required=True);ap.add_argument('--source',type=Path,required=True)
    args=ap.parse_args();pipeline=args.pipeline.absolute();source=args.source.absolute();code=Path(__file__).resolve().parent
    f.need(code.is_relative_to(pipeline),'driver must come from pipeline checkout')
    contract=f.pinned_load(code/'continuation_contract.json',args.contract_sha256)
    selection_data=f.load_json(code/'continuation_selection.json')
    cp.require_activation(contract,selection_data)
    f.need(contract['review_status']=='reviewed_for_execution','INACTIVE: integrated pipeline contract is not approved')
    source_commit=contract['source_commit']
    f.need(f.COMMIT.fullmatch(source_commit or '') and source_commit!=cp.SOURCE and contract['source_manifest_sha256']==MANIFEST_SHA,'fixed repaired source identity required')
    transport=Transport()
    f.need(os.environ.get('GITHUB_REF')=='refs/heads/verify/hierarchy-c-meta-continuation-20261016','unreviewed destination ref')
    for root,expected in [(source,source_commit),(pipeline,transport.commit)]:
        f.no_symlink_path(root)
        f.need(git(root,'rev-parse','HEAD')==expected and git(root,'status','--porcelain=v1','--untracked-files=all','--ignored')=='',
               'checkout identity or clean-tree mismatch')
    for name,digest in contract['implementation_sha256'].items():
        f.safe_rel(name);f.need(f.file_sha(code/name)==digest,'pipeline implementation hash mismatch: '+name)
    manifest=f.pinned_load(source/'SOURCE_MANIFEST.json',MANIFEST_SHA)
    plan=f.pinned_load(code/'plan.json',contract['plan_sha256']);profiles=f.pinned_load(code/'profiles.json',contract['profiles_sha256'])
    selection=cp.parse_selection((code/'continuation_selection.json').read_bytes(),contract['selection_sha256'],plan)
    old_contract=f.pinned_load(code/'original/contract.json',cp.OLD_CONTRACT)
    old_profiles=f.pinned_load(code/'original/profiles.json',cp.OLD_PROFILES)
    old_plan=f.pinned_load(code/'original/plan.json',cp.PLAN)
    f.need(old_plan==plan,'original plan changed')
    old_manifest=f.pinned_load(code/'original/SOURCE_MANIFEST.json',cp.MANIFEST)
    source_delta=f.pinned_load(code/'source_delta.json',contract['source_delta_sha256'])
    old_identity=selection.old_context['identity']
    f.validate_contract(contract,manifest,plan,profiles)
    f.need(contract['final_checks_review_status']=='reviewed','final checker adapter review is pending')
    root=Path(os.environ['RUNNER_TEMP'])/('hierarchy-c-'+args.role+(('-'+args.stage) if args.stage else ''))
    f.no_symlink_path(root);f.need(not root.exists(),'job workspace must be new');root.mkdir()
    upload=root/'upload';upload.mkdir();(root/'logs').mkdir()
    # Expected identity uses only pinned facts and the authenticated current event.
    # Every job still derives the official inventory independently and checks it.
    identity={'pipeline_commit':transport.commit,'source_commit':source_commit,'source_manifest_sha256':MANIFEST_SHA,
        'plan_sha256':contract['plan_sha256'],'profiles_sha256':contract['profiles_sha256'],
        'contract_sha256':args.contract_sha256,'runner_sha256':contract['runner_sha256'],
        'lean_archive_sha256':f.TOOLCHAIN_SHA256,'toolchain_inventory_sha256':cp.INVENTORY,
        'run_started_at':transport.run['created_at'],'run_id':transport.run_id,'run_attempt':transport.attempt,
        'evidence_mode':'verified_continuation','selection_sha256':selection.raw_sha256,
        'old_identity_sha256':cp.identity_hash(old_identity)}
    cp.check_deadline(old_identity,identity)
    workflow=current_workflow_from_run(transport,contract['current_workflow'],pipeline)
    origins=OriginTransport(transport,selection.old_context,{'identity':identity,'workflow':workflow})
    authenticate_current_workflow(origins)
    origins.authenticate_prepare('OldOrigin',root/'old-prepare')
    if args.role!='prepare':origins.authenticate_prepare('CurrentOrigin',root/'prepare')
    start=time.monotonic()
    archive=root/'lean.tar.zst';downloaded=0
    # Official vendor download: no authentication header and no existing cache.
    with urllib.request.urlopen(ARCHIVE_URL,timeout=60) as response,archive.open('xb') as out:
        while True:
            block=response.read(1024**2)
            if not block:break
            cp.check_deadline(old_identity,identity)
            downloaded+=len(block);f.need(downloaded<=ARCHIVE_BYTES and time.monotonic()-start<900,'release download bound')
            out.write(block)
    f.need(downloaded==ARCHIVE_BYTES,'official release archive length mismatch')
    toolchain=root/'toolchain';inventory=install_archive(archive,toolchain)
    inventory_path=root/'inventory.json';inventory_path.write_bytes(f.json_bytes(inventory));inventory_sha=f.file_sha(inventory_path)
    f.need(inventory_sha==identity['toolchain_inventory_sha256'],'canonical official inventory differs from both origins')
    f.verify_toolchain(toolchain,archive,inventory_path,contract,derived_inventory_sha256=inventory_sha)
    cp.check_deadline(old_identity,identity)
    old_context={'contract':old_contract,'manifest':old_manifest,'plan':old_plan,'profiles':old_profiles,
                 'identity':old_identity,'inventory':inventory}
    cp.validate_contexts(selection,old_context,{'contract':contract,'manifest':manifest,'plan':plan,
        'profiles':profiles,'identity':identity,'inventory':inventory,'source_delta':source_delta})
    env={'PATH':str(toolchain/'bin')+':/usr/bin:/bin','HOME':str(root),'TMPDIR':str(root),
         'LANG':'C.UTF-8','LC_ALL':'C.UTF-8','LEAN_NUM_THREADS':'1','LEAN_SYSROOT':str(toolchain),'LEAN_PATH':str(toolchain/'lib/lean')}
    results=[]
    def command(name,argv,seconds=18000,rss=8*1024**3,stdout_limit=32*1024**2,sandbox_sessions=False,environment=None):
        cp.check_deadline(old_identity,identity)
        if args.role in ('lean_export','nanoda','conron'):
            f.need(f.file_sha(Path(execution_paths['export_path']))==receipt['export_sha256'],'shared export mutated before command')
        out=root/'logs'/(name+'.stdout');err=root/'logs'/(name+'.stderr')
        r=f.run_process(argv,cwd=root,env=environment or env,timeout=seconds,stdout=out,stderr=err,
            max_log_bytes=stdout_limit,limits={'address_space_bytes':12*1024**3,'rss_tree_bytes':rss,
            'max_created_file_bytes':stdout_limit},allow_new_sessions=sandbox_sessions)
        r.update(argv=argv,name=name,timeout_seconds=seconds,
                 resource_limits={'address_space_bytes':12*1024**3,'rss_tree_bytes':rss,'max_created_file_bytes':stdout_limit},
                 max_log_bytes=stdout_limit,new_sessions_explicitly_allowed=sandbox_sessions,stdout={'bytes':out.stat().st_size,'sha256':f.file_sha(out)},
                 stderr={'bytes':err.stat().st_size,'sha256':f.file_sha(err)})
        results.append(r);(root/'last_command.json').write_bytes(f.json_bytes(r));successful(r,sandbox_sessions)
        cp.check_deadline(old_identity,identity)
        if args.role in ('lean_export','nanoda','conron'):
            f.need(f.file_sha(Path(execution_paths['export_path']))==receipt['export_sha256'],'shared export mutated during command')
        return out
    # Never disable bwrap or change security settings. A host restriction is a
    # failed preparation, not permission to use an unsandboxed substitute.
    if args.role=='prepare':
        command('sandbox_preflight',['/usr/bin/bwrap','--ro-bind','/','/','--tmpfs','/home','--tmpfs','/root',
            '--tmpfs','/run/user','--tmpfs','/tmp','--dir','/tmp/home','--dev','/dev','--proc','/proc',
            '--clearenv','--unshare-all','--die-with-parent','--new-session','--','/bin/true'],seconds=30,sandbox_sessions=True)
        f.extract_sources(source/'hierarchy-c-sources.tar.gz',root/'source',manifest)
        cp.check_deadline(old_identity,identity)
        shutil.copyfile(inventory_path,upload/'inventory.json');(upload/'identity.json').write_bytes(f.json_bytes(identity))
        print(json.dumps({'role':'prepare','status':'prepared_only','proof_pass_claimed':False,'inventory_sha256':inventory_sha}))
        return
    runner=ContinuationRunner(selection=selection,old_context=old_context,source_delta=source_delta,contract=contract,manifest=manifest,plan=plan,profiles=profiles,identity=identity,
        source_root=root/'source',toolchain_root=toolchain,toolchain_inventory=inventory,workspace=root/'stage')
    runner.check_run_age()
    def stage_descriptors(ids):
        wrappers=[];download_total=0
        for sid in ids:
            row=selection.row(sid);dest=root/'download'/sid
            wrapper=origins.download_stage(type(row).__name__,sid,dest,contract['max_artifact_bytes']+1024**2,
                pin=row.pin if isinstance(row,cp.OldOrigin) else None)
            download_total+=Path(wrapper['archive_path']).stat().st_size
            f.need(download_total<=contract['max_restored_bytes'],'aggregate mixed-origin transfer bound')
            wrappers.append(wrapper)
        return wrappers
    def restore_all():
        f.extract_sources(source/'hierarchy-c-sources.tar.gz',root/'source',manifest)
        descriptors=stage_descriptors([s['stage_id'] for s in plan['stages']])
        workspace=root/'stage';workspace.mkdir()
        for name in ['objects','scratch','logs','module-quarantine']: (workspace/name).mkdir()
        for name in ['home','tmp']: (workspace/'scratch'/name).mkdir()
        needed=mixed_storage_budget(descriptors,contract,stages=runner.stages,current_identity=identity,build=False,allocation_unit=os.statvfs(workspace).f_frsize)
        f.need(shutil.disk_usage(root).free>=needed,'insufficient measured final restore space')
        runner.read_artifacts([s['stage_id'] for s in plan['stages']],descriptors)
        f.need(set(runner.objects)==set(runner.entries),'final restore does not cover all selected modules')
        expected={path.removeprefix('objects/') for outputs in runner.objects.values() for path in outputs}
        f.exact_tree(workspace/'objects',expected)
        env['LEAN_PATH']=str(workspace/'objects')+':'+str(toolchain/'lib/lean')
        return descriptors
    def pack_final(role,extra,files):
        cp.check_deadline(old_identity,identity)
        info={name:{'bytes':path.stat().st_size,'sha256':f.file_sha(path)} for name,path in files.items()}
        receipt={'schema':'fresh-final-evidence-v1','role':role,'status':'completed_check_only','proof_pass_claimed':False,
            'identity':identity,'commands':results,'files':info,
            'execution_paths':execution_paths,**extra}
        cf.validate_final_commands(receipt)
        payload=upload/'payload.tar';receipt_sha=f.write_tar(payload,files,receipt,FINAL_ARTIFACT_LIMIT)
        desc={'schema':'fresh-final-upload-v1','role':role,'identity':identity,'archive_sha256':f.file_sha(payload),
            'archive_bytes':payload.stat().st_size,'receipt_sha256':receipt_sha,'retention_days':7}
        (upload/'upload-candidate.json').write_bytes(f.json_bytes(desc))
        cp.check_deadline(old_identity,identity)
    def get_final(role):
        dest=root/'download'/role
        wrapper=origins.download_final(role,dest,FINAL_ARTIFACT_LIMIT+1024**2)
        d=wrapper['native_descriptor']
        expanded=root/'expanded'/role
        receipt=f.extract_verified_archive(Path(wrapper['archive_path']),d,expanded,FINAL_ARTIFACT_LIMIT)
        f.need(receipt['role']==role and receipt['identity']==identity and receipt['status']=='completed_check_only','final receipt mismatch')
        cf.validate_final_commands(receipt)
        return receipt,expanded,d,wrapper
    execution_paths={'toolchain_root':str(toolchain),'code_root':str(code),
        'export_path':str(root/'logs/target_export.stdout'),'nanoda_config_path':str(root/'nanoda.json')}
    if args.role=='build':
        sid=args.stage;f.need(sid in runner.stages,'unlisted stage')
        f.need(os.environ['GITHUB_JOB']==runner.stages[sid]['producer_job'],'stage/workflow job mismatch')
        f.extract_sources(source/'hierarchy-c-sources.tar.gz',root/'source',manifest)
        ds=stage_descriptors(runner.stages[sid]['required_predecessors'])
        runner.run(sid,ds,os.environ['GITHUB_JOB'])
        for name in ['delta.tar','upload-candidate.json']:shutil.move(str(root/'stage'/name),upload/name)
        return
    if args.role in ('export_target','fresh_kernel'):
        ds=restore_all();before={name:f.file_sha(path) for name,path in f.regular_tree(root/'stage'/'objects').items()}
        provenance=cf.resolve_provenance(plan=plan,selection_rows=selection.json_rows(),wrappers=ds,
            old_identity=old_identity,current_identity=identity)
        context=cf.final_context(manifest=manifest,provenance=provenance,object_hashes=before,current_identity=identity)
        if args.role=='export_target':
            exported=command('target_export',[str(toolchain/'bin/leanexport'),TARGET_MODULE,'--',TARGET],stdout_limit=2*1024**3)
            audit_env={**env,'LEAN_PATH':str(toolchain/'lib/lean')}
            command('exact_export_audit',[str(toolchain/'bin/lean'),'-j1','-M4096','--run',str(code/'FinalExportAudit.lean'),str(exported)],seconds=1800,rss=4*1024**3,environment=audit_env)
            f.need((root/'logs/exact_export_audit.stdout').read_text()=='EXPORT_CONTRACT_AUDIT_PASSED\n','trusted audit output incomplete')
            context['export_sha256']=f.file_sha(exported)
            files={'target.ndjson':exported,'audit.stdout':root/'logs/exact_export_audit.stdout','audit.stderr':root/'logs/exact_export_audit.stderr','export.stderr':root/'logs/target_export.stderr'}
        else:
            command('fresh_whole_closure',[str(toolchain/'bin/leanchecker'),'--fresh',TARGET_MODULE],seconds=18000)
            files={p.name:p for p in (root/'logs').iterdir()}
        f.need(before=={name:f.file_sha(path) for name,path in f.regular_tree(root/'stage'/'objects').items()},'final command mutated restored objects')
        f.verify_sources(root/'source',manifest);runner.check_run_age();pack_final(args.role,context,files);return
    if args.role in ('lean_export','nanoda','conron'):
        receipt,expanded,_,_=get_final('export_target');exported=expanded/'target.ndjson'
        execution_paths['export_path']=str(exported)
        context=cf.final_context(manifest=manifest,provenance={'rows':receipt['resolved_provenance'],
            'sha256':receipt['resolved_provenance_sha256']},object_hashes=receipt['restored_object_hashes'],current_identity=identity)
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
    f.need(args.role=='verdict','unknown final role')
    checked={}
    for role in FINAL_ROLES:
        receipt,_,_,wrapper=get_final(role);checked[role]={'receipt':receipt,'wrapper':wrapper}
    export_receipt=checked['export_target']['receipt']
    provenance={'rows':export_receipt['resolved_provenance'],'sha256':export_receipt['resolved_provenance_sha256']}
    for wrapper in provenance['rows']:
        row=selection.row(wrapper['native_descriptor']['stage_id'])
        meta=origins.reauthenticate_wrapper(wrapper,pin=row.pin if isinstance(row,cp.OldOrigin) else None)
        f.need(meta==wrapper['authenticated_metadata'],'resolved producer/artifact metadata changed')
    runner.check_run_age()
    verdict=cf.final_verdict(plan=plan,manifest=manifest,current_identity=identity,old_identity=old_identity,
        selection_rows=selection.json_rows(),resolved_provenance=provenance,checked=checked,
        now=datetime.now(timezone.utc),current_max_age_seconds=contract['max_run_age_seconds'])
    runner.check_run_age()
    (upload/'verdict.json').write_bytes(f.json_bytes(verdict));print(json.dumps(verdict,sort_keys=True))

if __name__=='__main__':main()
