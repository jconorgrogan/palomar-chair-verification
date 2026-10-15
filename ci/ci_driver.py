#!/usr/bin/env python3
"""Inactive-contract-gated cloud pipeline driver. All outputs are same-run only."""
from __future__ import annotations
import argparse,json,os,shutil,subprocess,time,urllib.request
from pathlib import Path
import fresh_stage as f
from ci_transport import Transport,REPOSITORY
from toolchain_install import install_archive
SOURCE_COMMIT='c8e274d7833c9e2e1ede5aa61fc042fba8035715'
MANIFEST_SHA='492735d8eef3a672c32125da2caf13744f5ccbe6b198da5873a1204464794a61'
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

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('role');ap.add_argument('--stage');ap.add_argument('--contract-sha256',required=True)
    ap.add_argument('--pipeline',type=Path,required=True);ap.add_argument('--source',type=Path,required=True)
    args=ap.parse_args();pipeline=args.pipeline.absolute();source=args.source.absolute();code=Path(__file__).resolve().parent
    f.need(code.is_relative_to(pipeline),'driver must come from pipeline checkout')
    contract=f.pinned_load(code/'contract.json',args.contract_sha256)
    f.need(contract['review_status']=='reviewed_for_execution','INACTIVE: integrated pipeline contract is not approved')
    f.need(contract['source_commit']==SOURCE_COMMIT and contract['source_manifest_sha256']==MANIFEST_SHA,'fixed source identity changed')
    transport=Transport()
    f.need(os.environ.get('GITHUB_REF')=='refs/heads/verify/hierarchy-c-20261015','unreviewed destination ref')
    for root,expected in [(source,SOURCE_COMMIT),(pipeline,transport.commit)]:
        f.no_symlink_path(root)
        f.need(git(root,'rev-parse','HEAD')==expected and git(root,'status','--porcelain=v1','--untracked-files=all','--ignored')=='',
               'checkout identity or clean-tree mismatch')
    for name,digest in contract['implementation_sha256'].items():
        f.safe_rel(name);f.need(f.file_sha(code/name)==digest,'pipeline implementation hash mismatch: '+name)
    manifest=f.pinned_load(source/'SOURCE_MANIFEST.json',MANIFEST_SHA)
    plan=f.pinned_load(code/'plan.json',contract['plan_sha256']);profiles=f.pinned_load(code/'profiles.json',contract['profiles_sha256'])
    f.validate_contract(contract,manifest,plan,profiles)
    f.need(contract['final_checks_review_status']=='reviewed','final checker adapter review is pending')
    root=Path(os.environ['RUNNER_TEMP'])/('hierarchy-c-'+args.role+(('-'+args.stage) if args.stage else ''))
    f.no_symlink_path(root);f.need(not root.exists(),'job workspace must be new');root.mkdir()
    upload=root/'upload';upload.mkdir();(root/'logs').mkdir()
    # Only the prepare job derives the common immutable identity. Other jobs get
    # it via a digest-checked artifact from the successful same-run prepare job.
    identity=None;prep=None
    if args.role!='prepare':
        prep=root/'prepare';transport.download('prepare','prepare',prep,['identity.json','inventory.json'],32*1024**2)
        identity=f.load_json(prep/'identity.json')
        f.need(identity['pipeline_commit']==transport.commit and identity['source_commit']==SOURCE_COMMIT and
               identity['run_id']==transport.run_id and identity['run_attempt']==transport.attempt and
               identity['contract_sha256']==args.contract_sha256 and identity['source_manifest_sha256']==MANIFEST_SHA,
               'prepare identity mismatch')
        f.need(f.file_sha(prep/'inventory.json')==identity['toolchain_inventory_sha256'],'prepare inventory digest mismatch')
    start=time.monotonic()
    archive=root/'lean.tar.zst';downloaded=0
    # Official vendor download: no authentication header and no existing cache.
    with urllib.request.urlopen(ARCHIVE_URL,timeout=60) as response,archive.open('xb') as out:
        while True:
            block=response.read(1024**2)
            if not block:break
            downloaded+=len(block);f.need(downloaded<=ARCHIVE_BYTES and time.monotonic()-start<900,'release download bound')
            out.write(block)
    f.need(downloaded==ARCHIVE_BYTES,'official release archive length mismatch')
    toolchain=root/'toolchain';inventory=install_archive(archive,toolchain)
    inventory_path=root/'inventory.json';inventory_path.write_bytes(f.json_bytes(inventory));inventory_sha=f.file_sha(inventory_path)
    if identity is not None:f.need(inventory_sha==identity['toolchain_inventory_sha256'],'canonical toolchain inventory differs between jobs')
    f.verify_toolchain(toolchain,archive,inventory_path,contract,derived_inventory_sha256=inventory_sha)
    if identity is None:
        identity={'pipeline_commit':transport.commit,'source_commit':SOURCE_COMMIT,'source_manifest_sha256':MANIFEST_SHA,
            'plan_sha256':contract['plan_sha256'],'profiles_sha256':contract['profiles_sha256'],
            'contract_sha256':args.contract_sha256,'runner_sha256':contract['runner_sha256'],
            'lean_archive_sha256':f.TOOLCHAIN_SHA256,'toolchain_inventory_sha256':inventory_sha,
            'run_started_at':transport.run['created_at'],'run_id':transport.run_id,'run_attempt':transport.attempt}
    else:
        for name in ['plan_sha256','profiles_sha256','runner_sha256']:
            f.need(identity[name]==contract[name],'prepare contract field mismatch: '+name)
    env={'PATH':str(toolchain/'bin')+':/usr/bin:/bin','HOME':str(root),'TMPDIR':str(root),
         'LANG':'C.UTF-8','LC_ALL':'C.UTF-8','LEAN_NUM_THREADS':'1','LEAN_PATH':str(toolchain/'lib/lean')}
    results=[]
    def command(name,argv,seconds=18000,rss=8*1024**3,stdout_limit=32*1024**2,sandbox_sessions=False,environment=None):
        out=root/'logs'/(name+'.stdout');err=root/'logs'/(name+'.stderr')
        r=f.run_process(argv,cwd=root,env=environment or env,timeout=seconds,stdout=out,stderr=err,
            max_log_bytes=stdout_limit,limits={'address_space_bytes':12*1024**3,'rss_tree_bytes':rss,
            'max_created_file_bytes':stdout_limit},allow_new_sessions=sandbox_sessions)
        r.update(argv=argv,name=name,timeout_seconds=seconds,stdout={'bytes':out.stat().st_size,'sha256':f.file_sha(out)},
                 stderr={'bytes':err.stat().st_size,'sha256':f.file_sha(err)})
        results.append(r);(root/'last_command.json').write_bytes(f.json_bytes(r));successful(r,sandbox_sessions)
        return out
    # Never disable bwrap or change security settings. A host restriction is a
    # failed preparation, not permission to use an unsandboxed substitute.
    if args.role=='prepare':
        command('sandbox_preflight',['/usr/bin/bwrap','--ro-bind','/','/','--tmpfs','/home','--tmpfs','/root',
            '--tmpfs','/run/user','--tmpfs','/tmp','--dir','/tmp/home','--dev','/dev','--proc','/proc',
            '--clearenv','--unshare-all','--die-with-parent','--new-session','--','/bin/true'],seconds=30,sandbox_sessions=True)
        f.extract_sources(source/'hierarchy-c-sources.tar.gz',root/'source',manifest)
        shutil.copyfile(inventory_path,upload/'inventory.json');(upload/'identity.json').write_bytes(f.json_bytes(identity))
        print(json.dumps({'role':'prepare','status':'prepared_only','proof_pass_claimed':False,'inventory_sha256':inventory_sha}))
        return
    runner=f.StageRunner(contract=contract,manifest=manifest,plan=plan,profiles=profiles,identity=identity,
        source_root=root/'source',toolchain_root=toolchain,toolchain_inventory=inventory,workspace=root/'stage')
    runner.check_run_age()
    def stage_descriptors(ids):
        ds=[];download_total=0
        for sid in ids:
            dest=root/'download'/sid
            meta=transport.download(sid,'stage '+sid,dest,['delta.tar','upload-candidate.json'],contract['max_artifact_bytes']+1024**2)
            d=f.load_json(dest/'upload-candidate.json');f.need(d['stage_id']==sid and d['identity']==identity,'stage descriptor identity mismatch')
            f.need(d['retention_days']==7,'unexpected stage artifact retention')
            d.update(meta);d['archive_path']=str(dest/'delta.tar');download_total+=d['archive_bytes']
            f.need(download_total<=contract['max_restored_bytes'],'total predecessor transfer budget exceeded');ds.append(d)
        return ds
    def restore_all():
        f.extract_sources(source/'hierarchy-c-sources.tar.gz',root/'source',manifest)
        descriptors=stage_descriptors([s['stage_id'] for s in plan['stages']])
        workspace=root/'stage';workspace.mkdir()
        for name in ['deps','objects','scratch','logs']: (workspace/name).mkdir()
        needed=2*sum(d['archive_bytes'] for d in descriptors)+contract['minimum_free_disk_bytes']
        f.need(shutil.disk_usage(root).free>=needed,'insufficient measured final restore space')
        runner.read_artifacts([s['stage_id'] for s in plan['stages']],descriptors)
        f.need(set(runner.objects)==set(runner.entries),'final restore does not cover all selected modules')
        expected={path.removeprefix('objects/') for outputs in runner.objects.values() for path in outputs}
        f.exact_tree(workspace/'deps',expected)
        env['LEAN_PATH']=str(workspace/'deps')+':'+str(toolchain/'lib/lean')
        return descriptors
    def pack_final(role,extra,files):
        info={name:{'bytes':path.stat().st_size,'sha256':f.file_sha(path)} for name,path in files.items()}
        receipt={'schema':'fresh-final-evidence-v1','role':role,'status':'completed_check_only','proof_pass_claimed':False,
            'identity':identity,'commands':results,'files':info,**extra}
        payload=upload/'payload.tar';receipt_sha=f.write_tar(payload,files,receipt,FINAL_ARTIFACT_LIMIT)
        desc={'schema':'fresh-final-upload-v1','role':role,'identity':identity,'archive_sha256':f.file_sha(payload),
            'archive_bytes':payload.stat().st_size,'receipt_sha256':receipt_sha,'retention_days':7}
        (upload/'upload-candidate.json').write_bytes(f.json_bytes(desc))
    def get_final(role):
        dest=root/'download'/role
        meta=transport.download(role,role,dest,['payload.tar','upload-candidate.json'],FINAL_ARTIFACT_LIMIT+1024**2)
        d=f.load_json(dest/'upload-candidate.json');f.need(d['role']==role and d['identity']==identity and d['retention_days']==7,'final descriptor mismatch')
        expanded=root/'expanded'/role
        receipt=f.extract_verified_archive(dest/'payload.tar',d,expanded,FINAL_ARTIFACT_LIMIT)
        f.need(receipt['role']==role and receipt['identity']==identity and receipt['status']=='completed_check_only','final receipt mismatch')
        f.need(receipt['commands'] and all(c['exit_code']==0 for c in receipt['commands']),'missing final command evidence')
        for c in receipt['commands']:successful(c,c.get('new_sessions_explicitly_allowed') is True)
        return receipt,expanded,d,meta
    if args.role=='build':
        sid=args.stage;f.need(sid in runner.stages,'unlisted stage')
        f.need(os.environ['GITHUB_JOB']==runner.stages[sid]['producer_job'],'stage/workflow job mismatch')
        f.extract_sources(source/'hierarchy-c-sources.tar.gz',root/'source',manifest)
        ds=stage_descriptors(runner.stages[sid]['required_predecessors'])
        runner.run(sid,ds,os.environ['GITHUB_JOB'])
        for name in ['delta.tar','upload-candidate.json']:shutil.move(str(root/'stage'/name),upload/name)
        return
    if args.role in ('export_target','fresh_kernel'):
        ds=restore_all();before={name:f.file_sha(path) for name,path in f.regular_tree(root/'stage'/'deps').items()}
        context={'target':TARGET,'expected_type':TYPE,'source_manifest_sha256':MANIFEST_SHA,
            'defining_source':{'module':'SpectreFinite.NativeCoarsening','sha256':'657fa4144fa715098c5ba3f46af79fac981fdd0638f3fd948da88b512f812501'},
            'checked_source_count':len(runner.entries),'restored_object_hashes':before,
            'stage_artifacts':[{k:v for k,v in d.items() if k!='archive_path'} for d in ds]}
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
        f.need(before=={name:f.file_sha(path) for name,path in f.regular_tree(root/'stage'/'deps').items()},'final command mutated restored objects')
        f.verify_sources(root/'source',manifest);runner.check_run_age();pack_final(args.role,context,files);return
    if args.role in ('lean_export','nanoda','conron'):
        receipt,expanded,_,_=get_final('export_target');exported=expanded/'target.ndjson'
        f.need(f.file_sha(exported)==receipt['export_sha256'],'exact-target export changed')
        if args.role=='lean_export':
            command('lean_from_export',[str(toolchain/'bin/leanchecker'),'--silent','--from-export',str(exported)],seconds=9000)
            command('lake_export_axioms',[str(toolchain/'bin/lake'),'check','--from-export',str(exported)],seconds=9000,sandbox_sessions=True)
        elif args.role=='nanoda':
            config={'use_stdin':False,'export_file_path':str(exported),'permitted_axioms':['propext','Classical.choice','Quot.sound'],
                'unpermitted_axiom_hard_error':False,'num_threads':2,'nat_extension':True,'string_extension':True}
            cfg=root/'nanoda.json';cfg.write_bytes(f.json_bytes(config))
            command('nanoda',[str(toolchain/'bin/nanoda_bin'),str(cfg)],rss=6*1024**3)
        else:command('conron',[str(toolchain/'bin/con-ron'),'--verified','--jobs=2',str(exported)],rss=3*1024**3)
        runner.check_run_age();pack_final(args.role,{'export_sha256':receipt['export_sha256']},{p.name:p for p in (root/'logs').iterdir()});return
    f.need(args.role=='verdict','unknown final role')
    checked={role:get_final(role)[0] for role in FINAL_ROLES}
    export_hash=checked['export_target']['export_sha256']
    f.need(all(checked[role]['export_sha256']==export_hash for role in ('lean_export','nanoda','conron')),'checker exports disagree')
    f.need(checked['export_target']['restored_object_hashes']==checked['fresh_kernel']['restored_object_hashes'],'fresh/export object closures disagree')
    f.need(checked['export_target']['checked_source_count']==manifest['source_count'],'source closure coverage mismatch')
    for stage in plan['stages']:transport.successful_job('stage '+stage['stage_id'])
    runner.check_run_age()
    verdict={'schema':'fresh-hierarchy-c-verdict-v1','status':'verified_exact_finite_hierarchy_c','identity':identity,
        'target':TARGET,'exact_type':TYPE,'allowed_axioms':['propext','Classical.choice','Quot.sound'],
        'source_count':manifest['source_count'],'export_sha256':export_hash,'checks':{role:'passed' for role in FINAL_ROLES},
        'scope':'Exact finite hierarchy C only. No unconditional downstream 2D/4D or Palomar-acceptance claim.'}
    (upload/'verdict.json').write_bytes(f.json_bytes(verdict));print(json.dumps(verdict,sort_keys=True))

if __name__=='__main__':main()
