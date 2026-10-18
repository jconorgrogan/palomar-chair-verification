#!/usr/bin/env python3
"""One-shot admission of fixed historical payloads. No proof execution or resume."""
from __future__ import annotations
import argparse, copy, json, os, shutil, sys, tarfile, time
from datetime import datetime, timezone
from pathlib import Path
# -I excludes the script directory; only these adjacent, pinned helper files load.
import importlib.util, hashlib
_here=Path(__file__).resolve().parent
BOOTSTRAP_PINS={'three_context_local.py': '0ea2d6be51208e03248f5dd062b57c85bbc6b5768d156b27032891c15d10a06a', 'three_context_policy.py': 'edc4852bcfe3cd8ca980733229859c98ca20fb7120edddaa61f0c55ed19f53d4'}
for _name in ('three_context_local','three_context_policy'):
    _path=_here/(_name+'.py')
    if _path.is_symlink() or hashlib.sha256(_path.read_bytes()).hexdigest()!=BOOTSTRAP_PINS[_name+'.py']:raise RuntimeError('bootstrap helper pin mismatch')
    _spec=importlib.util.spec_from_file_location(_name,_here/(_name+'.py'))
    _mod=importlib.util.module_from_spec(_spec);sys.modules[_name]=_mod;_spec.loader.exec_module(_mod)
import three_context_local as l
import three_context_policy as p


def load_spec(path,digest):
    path=l.canonical(str(path));spec=l.parse(l.read_pinned(path,digest))
    l.need(set(spec)=={'schema','review_status','inputs','implementation_sha256','max_seconds','max_evidence_bytes','raw_archive_cap','runtime_installed','proof_pass_claimed'},'unknown/missing admission spec fields')
    l.need(spec['schema']=='fixed-historical-semantic-admission-v1' and spec['review_status']=='reviewed_for_admission_only','inactive or wrong admission spec')
    l.need(spec['max_seconds']==19800 and spec['max_evidence_bytes']==64*1024**2 and spec['raw_archive_cap']==4*1024**3 and spec['runtime_installed'] is False and spec['proof_pass_claimed'] is False,'admission bounds or claims changed')
    l.need(set(spec['implementation_sha256'])=={'three_context_policy.py', 'three_context_local.py', 'three_context_job.py', 'three_context_evidence.py', 'three_context_admit.py'},'exact admission implementation set required')
    for name,sha in spec['implementation_sha256'].items():
        l.need('/' not in name and name.endswith('.py'),'invalid implementation name')
        l.need(l.file_sha(_here/name)==sha,'admission implementation pin mismatch')
    expected={'PRIOR_FILES.json','CONTEXT_BUNDLE.json','CANDIDATE_SELECTION.json','EXPECTED_PRIOR_IDENTITY.json'}
    l.need(set(spec['inputs'])==expected,'unknown admission input')
    inputs={name:l.parse(l.read_pinned(path.parent/name,sha)) for name,sha in spec['inputs'].items()}
    return spec,inputs


def verify_transport(root,receipt_sha):
    root=l.canonical(str(root));raw=l.read_pinned(root/'TRANSPORT_RECEIPT.json',receipt_sha)
    receipt=l.parse(raw)
    l.need(receipt.get('schema')=='historical-origin-acquisition-v1' and receipt.get('status')=='transport_bytes_authenticated_only' and receipt.get('proof_pass_claimed') is False,'transport receipt claim/schema')
    files=receipt.get('files');l.need(type(files) is dict and 'TRANSPORT_RECEIPT.json' not in files,'invalid transport file inventory')
    actual=l.tree(root);actual.pop('TRANSPORT_RECEIPT.json',None)
    l.need(actual==files,'retained transport tree differs from authenticated inventory')
    def inside(relative):
        l.need(type(relative) is str and relative and not relative.startswith('/') and '..' not in Path(relative).parts and str(Path(relative))==relative,'invalid transport relative path')
        l.need(relative in files,'transport file missing from inventory');return root/relative
    contexts=receipt.get('contexts');l.need(type(contexts) is dict and set(contexts)=={'OldOrigin','PriorSuccessorOrigin'},'transport contexts differ')
    identities={};inventories={}
    for origin,ctx in contexts.items():
        l.need(type(ctx) is dict and set(ctx)=={'identity_path','inventory_path'},'transport prepare path schema')
        identities[origin]=l.parse(inside(ctx['identity_path']).read_bytes())
        inventories[origin]=l.parse(inside(ctx['inventory_path']).read_bytes())
    rows=l.parse(inside(receipt['wrappers_path']).read_bytes());l.need(type(rows) is list,'wrapper rows must be a list')
    wrappers=[];native_bytes={}
    for row in rows:
        l.need(type(row) is dict and set(row)=={'wrapper','raw_descriptor_path','raw_receipt_path'},'wrapper row schema')
        w=row['wrapper'];sid=w['native_descriptor']['stage_id'];l.need(sid not in native_bytes,'duplicate raw stage')
        tar=l.canonical(w['archive_path']);l.need(tar.is_relative_to(root),'tar outside authenticated acquisition root')
        l.need(tar.relative_to(root).as_posix() in files,'tar not authenticated')
        for key in ('raw_descriptor_path','raw_receipt_path'):
            path=l.canonical(row[key]);l.need(path.is_relative_to(root) and path.relative_to(root).as_posix() in files,'raw native bytes outside authenticated transport tree')
        native_bytes[sid]={'descriptor':Path(row['raw_descriptor_path']).read_bytes(),'receipt':Path(row['raw_receipt_path']).read_bytes()}
        wrappers.append(w)
    return receipt,identities,inventories,wrappers,native_bytes


def admit_native(native,*,selection,old_context,source_delta,contract,manifest,plan,profiles,identity,inventory,source_root,workspace,wrappers,check_budget):
    """Exact native semantic call; also directly exercised by offline toy fixtures."""
    l.need(not workspace.exists(),'admission workspace must be new')
    workspace.mkdir();runtime=workspace/'empty-runtime';runtime.mkdir()
    stage=workspace/'validation';stage.mkdir()
    for name in ('objects','scratch','logs','module-quarantine'):(stage/name).mkdir()
    for name in ('home','tmp'):(stage/'scratch'/name).mkdir()
    runner=native.runner.ContinuationRunner(selection=selection,old_context=old_context,source_delta=source_delta,
        contract=contract,manifest=manifest,plan=plan,profiles=profiles,identity=identity,
        source_root=source_root,toolchain_root=runtime,toolchain_inventory=inventory,workspace=stage,executor=l.executor_refused)
    required=native.runner.mixed_storage_budget(wrappers,contract,stages=runner.stages,current_identity=identity,build=False,allocation_unit=os.statvfs(workspace).f_frsize)+64*1024**2
    l.need(shutil.disk_usage(workspace).free>=required,'insufficient measured full-closure admission space')
    # Conservative inode ceiling includes all payloads, original transient copy,
    # quarantine directories and receipts/journals; no future cleanup credit.
    members=directories=0
    for wrapper in wrappers:
        with tarfile.open(wrapper['archive_path'],'r:') as archive:
            names=[m.name for m in archive]
        members+=len(names);directories+=len({str(p) for name in names for p in Path(name).parents if str(p)!='.'})
    required_inodes=3*(members+directories)+16*len(wrappers)+1024
    l.need(os.statvfs(workspace).f_favail>=required_inodes,'insufficient measured full-closure admission inodes')
    check_budget()
    with l.admission_only_guard(runtime,[native.f,native.old,native.runner],check_budget):
        runner.read_artifacts([w['native_descriptor']['stage_id'] for w in wrappers],wrappers)
        runner.verify_checked_objects();native.f.verify_sources(source_root,manifest);check_budget()
        expected_modules=[m for s in plan['stages'] if s['stage_id'] in {w['native_descriptor']['stage_id'] for w in wrappers} for m in s['modules']]
        l.need(set(runner.objects)==set(expected_modules) and len(expected_modules)==len(set(expected_modules)),'complete historical module map mismatch')
        objects={name.removeprefix('objects/'):digest for outputs in runner.objects.values() for name,digest in outputs.items()}
        actual={name:info['sha256'] for name,info in l.tree(stage/'objects').items()}
        l.need(actual==objects,'retained full companion tree mismatch')
        evidence=l.tree(stage/'restore-evidence')
        l.need(runner.predecessor_descriptors==[w['native_descriptor'] for w in wrappers],'native predecessor map changed')
        for w in wrappers:l.need(l.file_sha(Path(w['archive_path']))==w['native_descriptor']['archive_sha256'],'retained original tar mutated')
        check_budget()
    l.need(not list(runtime.iterdir()),'runtime placeholder acquired content')
    return {'objects':runner.objects,'native_descriptors':runner.predecessor_descriptors,'restore_evidence':evidence,
            'required_additional_free_bytes':required,'required_free_inodes':required_inodes,'runtime_installed':False,'runtime_opened':False,'executor_calls':0}


def execute(args):
    spec,inputs=load_spec(args.spec,args.spec_sha256)
    workspace=l.canonical(str(args.workspace));output=l.canonical(str(args.output));prior=l.canonical(str(args.prior_root));source=l.canonical(str(args.source_root));transport=l.canonical(str(args.transport_root))
    roots=(workspace,output,prior,source,transport)
    l.need(all(a!=b and a not in b.parents and b not in a.parents for i,a in enumerate(roots) for b in roots[i+1:]),'roots overlap')
    l.need(not workspace.exists() and not output.exists(),'admission cannot resume or overwrite')
    l.need(type(args.deadline_monotonic) is float and 0<args.deadline_monotonic-time.monotonic()<=spec['max_seconds'],'invalid shared admission deadline')
    bundle=p.validate_context_bundle(l.json_bytes(inputs['CONTEXT_BUNDLE.json']),spec['inputs']['CONTEXT_BUNDLE.json'])
    start_wall=datetime.now(timezone.utc);last_wall=[start_wall]
    deadline=[args.deadline_monotonic]
    with l.frozen_prior(prior,inputs['PRIOR_FILES.json']) as native:
        ci=prior/'ci';f=native.f;cp=native.p
        plan=f.pinned_load(ci/'plan.json',cp.PLAN);profiles=f.pinned_load(ci/'profiles.json',cp.OLD_PROFILES)
        candidate=p.parse_selection(l.json_bytes(inputs['CANDIDATE_SELECTION.json']),spec['inputs']['CANDIDATE_SELECTION.json'],plan,bundle)
        receipt,identities,inventories,wrappers,raws=verify_transport(transport,args.transport_receipt_sha256)
        for origin in ('OldOrigin','PriorSuccessorOrigin'):
            context_paths=receipt['contexts'][origin]
            p.validate_prepare_bytes(bundle,origin,(transport/context_paths['identity_path']).read_bytes(),(transport/context_paths['inventory_path']).read_bytes())
            l.need(identities[origin]==bundle.context(origin)['identity'],'authenticated prepare identity differs')
            l.need(l.sha(l.json_bytes(inventories[origin]))==cp.INVENTORY,'authenticated inventory differs')
        l.need(inventories['OldOrigin']==inventories['PriorSuccessorOrigin'],'historical inventory mismatch')
        l.need(identities['PriorSuccessorOrigin']==inputs['EXPECTED_PRIOR_IDENTITY.json'],'actual prior prepare differs from derived identity')
        selected=p.derive_pinned_inactive_selection(candidate,bundle,plan,[w for w in wrappers if w['origin']=='PriorSuccessorOrigin'])
        native_view=p.native_prior_invocation_view(wrappers,selected,bundle,plan,native_bytes=raws)
        ledger=p.cumulative_raw_budget(selected,{w['native_descriptor']['stage_id']:Path(w['archive_path']).stat().st_size for w in wrappers})
        # Freeze the already validated minimum once; repeated file guards need
        # not repeatedly parse the immutable full context/selection JSON.
        fixed=p.deadline_check(bundle,selected,datetime.now(timezone.utc),previous_now=last_wall[0])
        def budget():
            now=datetime.now(timezone.utc)
            l.need(last_wall[0]<=now<fixed,'backward clock or historical expiry reached');last_wall[0]=now
            deadline[0]=min(deadline[0],time.monotonic()+(fixed-now).total_seconds())
            l.need(time.monotonic()<deadline[0],'shared job or original age deadline exceeded')
            return fixed
        budget()
        prior_identity=identities['PriorSuccessorOrigin'];contract=f.pinned_load(ci/'continuation_contract.json',prior_identity['contract_sha256'])
        manifest=f.pinned_load(args.source_manifest,cp.NEW_MANIFEST)
        oldctx={key:f.pinned_load(ci/'original'/filename,digest) for key,filename,digest in [('contract','contract.json',cp.OLD_CONTRACT),('manifest','SOURCE_MANIFEST.json',cp.MANIFEST),('plan','plan.json',cp.PLAN),('profiles','profiles.json',cp.OLD_PROFILES)]}
        oldctx.update(identity=identities['OldOrigin'],inventory=inventories['OldOrigin'])
        prior_selection=cp.parse_selection((ci/'continuation_selection.json').read_bytes(),prior_identity['selection_sha256'],plan)
        result=admit_native(native,selection=prior_selection,old_context=oldctx,source_delta=f.pinned_load(ci/'source_delta.json',cp.SOURCE_DELTA),
            contract=contract,manifest=manifest,plan=plan,profiles=profiles,identity=prior_identity,inventory=inventories['PriorSuccessorOrigin'],source_root=source,workspace=workspace,wrappers=native_view,check_budget=budget)
        # Re-authenticate every retained transport byte and frozen input after semantic admission.
        verify_transport(transport,args.transport_receipt_sha256);budget()
        l.need(len(result['objects'])==3153 and len(wrappers)==48,'fixed historical coverage differs')
        output.mkdir()
        l.durable(output/'SELECTED_CANDIDATE.json',selected.raw_bytes)
        l.durable(output/'NATIVE_VALIDATION.json',l.json_bytes(result))
        complete={'schema':'fixed-three-context-historical-admission-v1','status':'historical_payloads_native_validated_only','proof_pass_claimed':False,'clean_replay_claimed':False,
            'runtime_installed':False,'kernel_executed':False,'semantic_scope':'Unchanged original and prior readonly receipt/payload validators; authenticated inventory only.',
            'spec_sha256':args.spec_sha256,'context_bundle_sha256':bundle.raw_sha256,'candidate_selection_sha256':candidate.raw_sha256,'selection_sha256':selected.raw_sha256,
            'transport_receipt_sha256':args.transport_receipt_sha256,'prior_identity_sha256':l.sha(l.json_bytes(prior_identity)),
            'prior_files_sha256':spec['inputs']['PRIOR_FILES.json'],'native_validation_sha256':l.file_sha(output/'NATIVE_VALIDATION.json'),
            'stage_count':48,'module_count':3153,'companion_count':sum(len(x) for x in result['objects'].values()),
            'raw_archive_bytes':ledger.total_bytes,'raw_archive_cap':spec['raw_archive_cap'],'remaining_raw_bytes':ledger.remaining_bytes,
            'original_deadline':fixed.isoformat(),'started_at':start_wall.isoformat(),'completed_at':datetime.now(timezone.utc).isoformat(),
            'activation_allowed':False,'independent_reconciliation_required':True,'future_current_execution_adapter_reviewed':False}
        budget();raw=l.json_bytes(complete);l.need(sum(p.stat().st_size for p in output.iterdir())+len(raw)<=spec['max_evidence_bytes'],'evidence cap exceeded')
    # The frozen loader has now rehashed every historical source before success.
    budget();l.durable(output/'COMPLETION.json',raw);budget()
    return complete


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    for name in ('spec','prior-root','source-root','source-manifest','transport-root','workspace','output'):ap.add_argument('--'+name,type=Path,required=True)
    for name in ('spec-sha256','transport-receipt-sha256'):ap.add_argument('--'+name,required=True)
    ap.add_argument('--deadline-monotonic',type=float,required=True);args=ap.parse_args()
    try:
        result=execute(args);print(json.dumps({'status':result['status'],'stages':result['stage_count'],'proof_pass_claimed':False}))
    except BaseException:
        # No deletion: the output may predate this invocation. A certificate is
        # usable only with the separately checked successful process/job result.
        raise
if __name__=='__main__':main()
