"""Pure clean-run receipt policy; no I/O, downloads, execution or activation.

The authenticated clean driver must use the unchanged StageRunner.run and
StageRunner.read_artifacts on fresh owned roots. Those native validators remain
mandatory. This module checks their retained, authenticated receipt projection;
a caller-supplied dictionary is never authentication or native admission.
"""
from __future__ import annotations
from copy import deepcopy
from datetime import datetime, timezone, timedelta
import re
import fresh_stage as f
import four_context_policy as p
import four_context_final as shared

TARGET_MODULE=shared.TARGET_MODULE
TARGET=shared.TARGET
TYPE=shared.TYPE
ALLOWED_AXIOMS=shared.ALLOWED_AXIOMS
DEFINING_SOURCE=shared.DEFINING_SOURCE
AUDIT_SHA256=shared.AUDIT_SHA256
AUDIT_OUTPUT=shared.AUDIT_OUTPUT
FINAL_ROLES=shared.FINAL_ROLES
FINAL_ARTIFACT_LIMIT=shared.FINAL_ARTIFACT_LIMIT
REPOSITORY=shared.REPOSITORY
REPOSITORY_ID=shared.REPOSITORY_ID
ACTIVATION_ALLOWED=False
MAX_AGE=518400
MAX_RESTORED=4*1024**3
ORIGINS=('CurrentOrigin',)
CURRENT_WORKFLOW={'head_branch':'verify/hierarchy-c-clean-replay-20261018',
    'path':'.github/workflows/hierarchy-c-clean-replay.yml','name':'Verify hierarchy C clean replay'}
FIXED_IDENTITY={'source_commit':p.PRIOR_SOURCE,'source_manifest_sha256':p.PRIOR_MANIFEST,
    'plan_sha256':p.PLAN_SHA256,'profiles_sha256':p.CURRENT_PROFILES,
    'runner_sha256':'9085c9eea092c270fbd6952834839103c66519a7b4716fe09147001c7d96355d',
    'lean_archive_sha256':'b67d0e0ba959fc74e186f1b44aebca32d6ecb6a28f8e9a029fc4e9f73398a049',
    'toolchain_inventory_sha256':'42bd268b1ca3e9bf89f4149ac427d6c0e76f735233b092a6df4ca27a2c2db7ea',
    'evidence_mode':'clean_source_rebuild','run_attempt':'1'}
IDENTITY_KEYS=set(FIXED_IDENTITY)|{'pipeline_commit','contract_sha256','run_id','run_started_at'}
FORBIDDEN_RUNS={str(x) for x in (p.OLD_RUN,p.PRIOR_RUN,p.LATEST_RUN,p.EXCLUDED_RUN,39089923663)}
_digest=shared._digest
_positive=shared._positive
_timestamp=shared._timestamp
# Use the existing exact command/configuration/axiom acceptance functions.
final_command_specs=shared.final_command_specs
validate_final_commands=shared.validate_final_commands
nanoda_configuration=shared.nanoda_configuration
_successful_command=shared._successful_command


def validate_identity(identity, contract_sha256, pipeline_commit):
    p.keys(identity,IDENTITY_KEYS,'clean identity')
    p.digest(contract_sha256,'clean contract')
    f.need(type(pipeline_commit) is str and f.COMMIT.fullmatch(pipeline_commit) and
        pipeline_commit not in {p.OLD_PIPELINE,p.PRIOR_PIPELINE,p.LATEST_PIPELINE},'new clean pipeline commit required')
    expected={**FIXED_IDENTITY,'contract_sha256':contract_sha256,'pipeline_commit':pipeline_commit}
    f.need(all(type(identity.get(k)) is type(v) and identity[k]==v for k,v in expected.items()),'clean fixed identity changed')
    f.need(type(identity['run_id']) is str and re.fullmatch('[1-9][0-9]*',identity['run_id']) and
        identity['run_id'] not in FORBIDDEN_RUNS,'distinct initial clean run required')
    _timestamp(identity['run_started_at'])
    return p.object_sha(identity)


def _inputs(plan,manifest,profiles,identity):
    validate_identity(identity,identity.get('contract_sha256'),identity.get('pipeline_commit'))
    p.validate_plan(plan)
    f.need(p.object_sha(manifest)==FIXED_IDENTITY['source_manifest_sha256'],'exact clean source manifest required')
    f.need(p.object_sha(profiles)==FIXED_IDENTITY['profiles_sha256'],'exact clean profile bytes required')
    entries=f.manifest_index(manifest)
    modules=[m for stage in plan['stages'] for m in stage['modules']]
    f.need(len(modules)==len(set(modules))==6369 and set(modules)==set(entries)==set(profiles['module_profiles']),
        'all 6369 clean source/profile modules required')
    return entries


def validate_workflow(workflow,plan):
    p.validate_plan(plan)
    p.keys(workflow,{'head_branch','name','path','workflow_id','source_sha256','roles'},'clean workflow')
    _positive(workflow['workflow_id'],'clean workflow ID');_digest(workflow['source_sha256'],'clean workflow source')
    f.need(all(workflow[k]==v for k,v in CURRENT_WORKFLOW.items()),'clean workflow identity changed')
    stages={s['stage_id']:s for s in plan['stages']}
    f.need(type(workflow['roles']) is dict and set(workflow['roles'])==set(stages)|set(FINAL_ROLES)|{'prepare'},
        'exact clean provider role set required')
    for role,mapping in workflow['roles'].items():
        expected={'producer_job':stages[role]['producer_job'] if role in stages else role,
            'job_name':'stage '+role if role in stages else role,'upload_locations':1,
            'verifier_step':{'number':6,'name':'Run fail-closed verifier'},
            'upload_step':{'number':7,'name':"Upload only this job's new evidence"}}
        f.need(mapping==expected and p.object_sha(mapping)==p.object_sha(expected),'clean producer/upload binding changed')
    return workflow


def check_deadline(identity,now,*,artifact_expiries=(),previous_now=None,max_age_seconds=MAX_AGE):
    validate_identity(identity,identity.get('contract_sha256'),identity.get('pipeline_commit'))
    p.integer(max_age_seconds,'clean maximum age',MAX_AGE)
    f.need(type(now) is datetime and now.tzinfo is not None,'aware trusted clean clock required')
    if previous_now is not None:f.need(type(previous_now) is datetime and previous_now.tzinfo is not None and now>=previous_now,'clean clock moved backward')
    start=_timestamp(identity['run_started_at']);f.need(start<=now,'future clean run')
    deadline=min([start+timedelta(seconds=max_age_seconds)]+[_timestamp(x) for x in artifact_expiries])
    f.need(now<deadline,'clean age/artifact expiry reached')
    return deadline


def _validate_wrapper(wrapper, identity, role, *, workflow, final=False):
    current_workflow_id=workflow['workflow_id']
    """Recheck complete producer metadata, never treating descriptor IDs as authority."""
    required = {'origin', 'native_descriptor', 'authenticated_metadata', 'raw_descriptor_sha256'}
    f.need(type(wrapper) is dict and set(wrapper) in (required, required | {'archive_path'}),
           'invalid origin wrapper fields')
    f.need(wrapper['origin'] in ORIGINS, 'unknown origin')
    if final:
        f.need(wrapper['origin'] == 'CurrentOrigin', 'historical final evidence forbidden')
    _digest(wrapper['raw_descriptor_sha256'], 'raw upload descriptor hash')
    d = wrapper['native_descriptor']
    f.need(type(d) is dict and 'archive_path' not in d and 'origin' not in d,
           'native descriptor rewritten with wrapper fields')
    f.need(d.get('identity') == identity and d.get('retention_days') == 7, 'descriptor origin/retention mismatch')
    f.need(d.get('schema') == ('fresh-final-upload-v1' if final else 'fresh-stage-upload-candidate-v1'),
           'descriptor schema mismatch')
    f.need(d.get('role' if final else 'stage_id') == role, 'descriptor role mismatch')
    _positive(d.get('artifact_id'), 'artifact ID')
    _positive(d.get('producer_job_id'), 'producer job ID')
    _positive(d.get('archive_bytes'), 'archive bytes')
    f.need(d['archive_bytes'] <= (FINAL_ARTIFACT_LIMIT if final else 1024**3), 'archive byte ceiling')
    for key in ('archive_sha256', 'receipt_sha256', 'artifact_zip_sha256'):
        _digest(d.get(key), key)
    f.need(d.get('producer_conclusion') == 'success', 'descriptor producer unsuccessful')
    meta = wrapper['authenticated_metadata']
    f.need(type(meta) is dict and set(meta) == {'run', 'job', 'artifact', 'role'}, 'authenticated metadata shape mismatch')
    run, job, artifact, mapping = (meta[k] for k in ('run', 'job', 'artifact', 'role'))
    f.need(type(run.get('id')) is int and str(run['id']) == identity['run_id'] and
           type(run.get('run_attempt')) is int and str(run['run_attempt']) == identity['run_attempt'] and
           run.get('head_sha') == identity['pipeline_commit'] and run.get('event') == 'push' and
           run.get('created_at') == identity['run_started_at'], 'authenticated producer run mismatch')
    for key in ('repository', 'head_repository'):
        repository = run.get(key, {})
        f.need(type(repository.get('id')) is int and repository['id'] == REPOSITORY_ID,
               'authenticated repository numeric identity mismatch')
    f.need(run['repository'].get('full_name') == REPOSITORY, 'authenticated repository name mismatch')
    if wrapper['origin'] == 'CurrentOrigin':
        # OriginTransport._metadata omits run.name; its authenticated _run
        # boundary validates that name before producing this exact projection.
        _positive(current_workflow_id, 'reviewed current workflow ID')
        f.need(type(run.get('workflow_id')) is int and run['workflow_id'] == current_workflow_id
               and all(run.get(key) == CURRENT_WORKFLOW[key] for key in ('path', 'head_branch')),
               'current workflow identity mismatch')
    f.need(type(mapping) is dict and set(mapping) == {'producer_job', 'job_name', 'verifier_step', 'upload_step', 'upload_locations'}
           and type(mapping['upload_locations']) is int and mapping['upload_locations'] == 1,
           'unreviewed producer/upload mapping')
    f.need(job.get('id') == d['producer_job_id'] and type(job.get('id')) is int and
           job.get('status') == 'completed' and job.get('conclusion') == 'success' and
           job.get('head_sha') == identity['pipeline_commit'] and job.get('name') == mapping['job_name'] and
           type(job.get('run_attempt')) is int and str(job['run_attempt']) == identity['run_attempt'] and
           str(job.get('run_id')) == identity['run_id'], 'actual successful producer mismatch')
    expected_name = role if final else 'stage '+role
    f.need(mapping['job_name'] == expected_name and
           (final or d.get('producer_job') == mapping['producer_job']), 'producer role mapping mismatch')
    steps = job.get('steps')
    f.need(type(steps) is list, 'producer step evidence absent')
    for key in ('verifier_step', 'upload_step'):
        step = mapping[key]
        f.need(type(step) is dict and set(step) == {'number', 'name'}, 'producer step mapping invalid')
        _positive(step['number'], 'producer step number')
        matches = [s for s in steps if s.get('number') == step['number'] and s.get('name') == step['name']]
        f.need(len(matches) == 1 and matches[0].get('status') == 'completed' and
               matches[0].get('conclusion') == 'success', 'verifier/upload step unsuccessful or missing')
    workflow_run = artifact.get('workflow_run', {})
    f.need(artifact.get('id') == d['artifact_id'] and type(artifact.get('id')) is int and
           artifact.get('expired') is False and artifact.get('digest') == 'sha256:'+d['artifact_zip_sha256'] and
           artifact.get('name') == 'hierarchy-c-'+identity['run_id']+'-'+identity['run_attempt']+'-'+role,
           'authenticated artifact identity/digest mismatch')
    _positive(artifact.get('size_in_bytes'), 'authoritative ZIP bytes')
    f.need(type(workflow_run.get('id')) is int and str(workflow_run['id']) == identity['run_id'] and
           workflow_run.get('head_sha') == identity['pipeline_commit'] and
           workflow_run.get('repository_id') == REPOSITORY_ID and workflow_run.get('head_repository_id') == REPOSITORY_ID,
           'artifact workflow/repository mismatch')
    f.need(mapping==workflow['roles'][role],'wrapper differs from fixed clean workflow role')
    return d


def _provenance(plan,wrappers,identity,workflow):
    validate_workflow(workflow,plan)
    f.need(type(wrappers) is list and len(wrappers)==len(plan['stages'])==93,'all 93 clean stage wrappers required')
    rows=[];total=0
    for stage,wrapper in zip(plan['stages'],wrappers):
        d=_validate_wrapper(wrapper,identity,stage['stage_id'],workflow=workflow)
        f.need(d['producer_job']==stage['producer_job'],'clean stage producer differs from original plan')
        total+=d['archive_bytes']
        rows.append(deepcopy({k:v for k,v in wrapper.items() if k!='archive_path'}))
    f.need(total<=MAX_RESTORED,'clean global 4GiB raw archive budget exceeded')
    return rows


def _seal(rows,transfers):
    value={'rows':deepcopy(rows),'same_run_predecessor_transfers':deepcopy(transfers)}
    return {**value,'sha256':p.object_sha(value)}


def _unseal(provenance):
    p.keys(provenance,{'rows','same_run_predecessor_transfers','sha256'},'clean provenance')
    f.need(provenance==_seal(provenance['rows'],provenance['same_run_predecessor_transfers']),'clean provenance byte binding changed')
    return provenance['rows']


def validate_native_predecessor_order(*,plan,provenance,native_receipt_bytes):
    """Raw native bytes and exact same-clean-run chain; no semantic substitute."""
    p.validate_plan(plan);rows=_unseal(provenance)
    ids=[s['stage_id'] for s in plan['stages']]
    f.need(type(rows) is list and len(rows)==93 and type(native_receipt_bytes) is dict and set(native_receipt_bytes)==set(ids),
        'all 93 raw clean stage receipts required')
    transfers={};seen={};hashes={};identity=None
    for stage,wrapper in zip(plan['stages'],rows):
        sid=stage['stage_id'];d=wrapper['native_descriptor'];raw=native_receipt_bytes[sid]
        f.need(wrapper['origin']=='CurrentOrigin' and d.get('stage_id')==sid,'clean native order/origin changed')
        validate_identity(d['identity'],d['identity'].get('contract_sha256'),d['identity'].get('pipeline_commit'))
        if identity is None:identity=d['identity']
        f.need(d['identity']==identity,'cross-run clean descriptor forbidden')
        f.need(type(raw) is bytes and p.sha(raw)==d['receipt_sha256'],'exact raw clean receipt changed')
        r=p.parse_json(raw)
        f.need(type(r) is dict and r.get('schema')=='fresh-stage-receipt-v1' and r.get('receipt_protocol')==f.READONLY_PROTOCOL and
            r.get('status')=='fresh_compile_check_pairs_only' and r.get('proof_pass_claimed') is False and
            r.get('identity')==identity and r.get('stage_id')==sid and r.get('producer_job')==stage['producer_job'],
            'clean native receipt envelope changed')
        predecessors=stage['required_predecessors']
        f.need(r.get('predecessors')==[seen[x] for x in predecessors],'clean same-run predecessor chain changed')
        transfers[sid]=list(predecessors);seen[sid]=d;hashes[sid]=p.sha(raw)
    f.need(provenance['same_run_predecessor_transfers']==transfers,'clean predecessor transfer ledger changed')
    return hashes


def _stage_map(plan,manifest,profiles,wrappers,native_receipt_bytes,identity,workflow):
    entries=_inputs(plan,manifest,profiles,identity);rows=_provenance(plan,wrappers,identity,workflow)
    transfers={s['stage_id']:list(s['required_predecessors']) for s in plan['stages']}
    provenance=_seal(rows,transfers)
    validate_native_predecessor_order(plan=plan,provenance=provenance,native_receipt_bytes=native_receipt_bytes)
    all_modules=[]
    for stage in plan['stages']:
        r=p.parse_json(native_receipt_bytes[stage['stage_id']]);records=r.get('modules')
        f.need(type(records) is list and [v.get('module') for v in records]==stage['modules'],'clean compiled module order/coverage changed')
        files=r.get('files');f.need(type(files) is dict,'native file map missing')
        for record in records:
            module=record['module'];all_modules.append(module);profile_id=profiles['module_profiles'][module]
            f.need(record.get('source_sha256')==entries[module]['sha256'] and record.get('profile')==profile_id,
                'clean source/profile record changed')
            outputs=record.get('outputs');expected=f.object_paths(module,f.MODERN_SUFFIXES)
            f.need(type(outputs) is dict and set(outputs)==set(expected),'six clean companions required')
            for name,digest in outputs.items():
                _digest(digest,'clean companion hash')
                f.need(name in files and files[name].get('sha256')==digest,'clean companion file binding changed')
                p.integer(files[name].get('bytes'),'clean companion bytes',1024**3,minimum=0)
            # This is the unchanged native success predicate. Full native file,
            # import, command-layout and sandbox checks still run in StageRunner.
            for phase in ('compile','check'):
                command=record.get(phase);f.need(type(command) is dict,'clean compile/check record missing')
                f.need(type(command.get('exit_code')) is int and command['exit_code']==0 and
                    command.get('timed_out') is False and command.get('log_overflow') is False and
                    command.get('memory_exceeded') is False and command.get('surviving_children') is False and
                    command.get('escaped_descendants') is False and command.get('process_group_empty') is True and
                    command.get('descendants_empty') is True,'unsuccessful clean native compile/check pair')
                expected_spec={'tool':'lean' if phase=='compile' else 'leanchecker',
                    'flags':profiles['profiles'][profile_id][phase+'_flags'],'module':module,
                    'source':entries[module]['path'] if phase=='compile' else None}
                f.need(command.get('spec')==expected_spec,'clean native command specification changed')
    f.need(len(all_modules)==len(set(all_modules))==6369 and set(all_modules)==set(entries),'clean compiled closure incomplete')
    return provenance


def validate_stage_map(plan,manifest,profiles,wrappers,native_bytes,identity,workflow):
    """Validate the full live-restored clean map, preserving every raw native byte."""
    ids={s['stage_id'] for s in p.validate_plan(plan)}
    f.need(type(native_bytes) is dict and set(native_bytes)==ids,'all93 raw native descriptor/receipt pairs required')
    receipts={}
    f.need(type(wrappers) is list and len(wrappers)==93,'all93 wrapper pairs required')
    for wrapper in wrappers:
        sid=wrapper['native_descriptor']['stage_id'];p.keys(native_bytes[sid],{'descriptor','receipt'},'clean native pair')
        p.validate_native_bytes(wrapper,native_bytes[sid]['descriptor'],native_bytes[sid]['receipt'])
        receipts[sid]=native_bytes[sid]['receipt']
    return _stage_map(plan,manifest,profiles,wrappers,receipts,identity,workflow)


def final_context(manifest,provenance,object_hashes,identity):
    """Context for an actual clean full-closure restore; final_verdict revalidates."""
    validate_identity(identity,identity.get('contract_sha256'),identity.get('pipeline_commit'))
    f.need(p.object_sha(manifest)==FIXED_IDENTITY['source_manifest_sha256'],'clean source manifest changed')
    rows=_unseal(provenance);entries=f.manifest_index(manifest)
    ids=[f'build_{i:03}' for i in range(93)]
    f.need(len(rows)==93 and [w['native_descriptor']['stage_id'] for w in rows]==ids and
        all(w['origin']=='CurrentOrigin' and w['native_descriptor']['identity']==identity for w in rows),'clean full native provenance required')
    f.need(set(provenance['same_run_predecessor_transfers'])==set(ids),'full clean predecessor ledger required')
    expected={name.removeprefix('objects/') for m in entries for name in f.object_paths(m,f.MODERN_SUFFIXES)}
    f.need(type(object_hashes) is dict and set(object_hashes)==expected,'all38214 clean companion hashes required')
    for digest in object_hashes.values():_digest(digest,'clean restored object hash')
    f.need(entries[DEFINING_SOURCE['module']]['sha256']==DEFINING_SOURCE['sha256'],'defining source mismatch')
    return {'target':TARGET,'expected_type':TYPE,'allowed_axioms':list(ALLOWED_AXIOMS),
        'defining_source':dict(DEFINING_SOURCE),'final_export_audit_sha256':AUDIT_SHA256,
        'source_manifest_sha256':identity['source_manifest_sha256'],'checked_source_count':manifest['source_count'],
        'checked_sources':{m:e['sha256'] for m,e in entries.items()},'restored_object_hashes':deepcopy(object_hashes),
        'resolved_provenance':deepcopy(rows),'resolved_provenance_sha256':provenance['sha256'],
        'same_run_predecessor_transfers':deepcopy(provenance['same_run_predecessor_transfers']),
        'initial_project_object_trees_empty':True,'project_artifact_imports':[],'compiled_source_count':6369}


def final_verdict(plan,manifest,profiles,identity,workflow,provenance,native_receipt_bytes,checked,now):
    """Clean-only result after native admission and authenticated final checks.

    The authenticated driver, not these dictionaries, establishes empty roots and
    permitted input routes. Same-run predecessor imports are recorded explicitly;
    project_artifact_imports lists only external/prior-run project seed artifacts.
    """
    actual=_stage_map(plan,manifest,profiles,provenance['rows'],native_receipt_bytes,identity,workflow)
    f.need(actual==provenance,'clean full provenance/ledger changed')
    f.need(type(checked) is dict and set(checked)==set(FINAL_ROLES),'allfive clean final evidence roles required')
    # Bind final restore hashes to the exact accepted native receipt outputs.
    receipt_objects={name.removeprefix('objects/'):digest
        for sid in native_receipt_bytes
        for record in p.parse_json(native_receipt_bytes[sid])['modules']
        for name,digest in record['outputs'].items()}
    context=final_context(manifest,provenance,receipt_objects,identity)
    export_hash=_digest(checked['export_target']['receipt'].get('export_sha256'),'clean export hash')
    expiries=[w['authenticated_metadata']['artifact']['expires_at'] for w in provenance['rows']];artifacts={}
    for role in FINAL_ROLES:
        evidence=checked[role];p.keys(evidence,{'receipt','wrapper'},'clean final evidence')
        r=evidence['receipt'];w=evidence['wrapper']
        f.need(not (set(r)&{'selection_sha256','old_identity_sha256','prior_identity_sha256','latest_identity_sha256',
            'context_bundle_sha256','admission_certificate_sha256','admission_reconciliation_sha256'}),'continuation lineage in clean final receipt')
        d=_validate_wrapper(w,identity,role,workflow=workflow,final=True)
        f.need(d['receipt_sha256']==p.object_sha(r),'clean final receipt byte hash changed')
        f.need(r.get('schema')=='fresh-final-evidence-v1' and r.get('role')==role and
            r.get('status')=='completed_check_only' and r.get('proof_pass_claimed') is False and
            r.get('identity')==identity,'clean final receipt envelope changed')
        for key,value in context.items():f.need(type(r.get(key)) is type(value) and r[key]==value,'clean final context mismatch: '+key)
        if role!='fresh_kernel' or 'export_sha256' in r:f.need(r.get('export_sha256')==export_hash,'clean final export disagreement')
        validate_final_commands(r)
        expiries.append(w['authenticated_metadata']['artifact']['expires_at'])
        artifacts[role]=deepcopy({k:v for k,v in w.items() if k!='archive_path'})
    deadline=check_deadline(identity,now,artifact_expiries=expiries)
    return {'schema':'clean-source-hierarchy-c-verdict-v1','status':'clean_source_rebuild_checks_passed',
        'identity':deepcopy(identity),**context,'exact_type':TYPE,'source_count':manifest['source_count'],
        'export_sha256':export_hash,'checks':{role:'passed' for role in FINAL_ROLES},'final_artifacts':artifacts,
        'acceptance_deadline':deadline.isoformat(),'clean_source_rebuild':'checks_passed',
        'bit_reproducibility_claim':False,'overall_task_complete':False,'activation_allowed':False,
        'scope':'Exact finite hierarchy C clean-source checks only. Independent continuation byte comparison remains required.'}
