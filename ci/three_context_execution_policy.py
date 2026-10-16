"""Inactive pure policy for exact target-specific three-context restores.

Raw bytes and transport metadata must be authenticated by the caller. These
checks do not execute either historical native validator or the current runner.
"""
from __future__ import annotations
import copy
from dataclasses import dataclass
import fresh_stage as f
import three_context_policy as p
import three_context_final as final

ACTIVATION_ALLOWED=False
NUMERIC_AND_PROTOCOL_FIELDS=(
 'lean_release','lean_archive_sha256','runner','maximum_parallel_jobs','retention_days',
 'job_timeout_seconds','max_artifact_bytes','max_log_bytes','max_restored_bytes',
 'max_stage_output_bytes','max_run_age_seconds','minimum_free_disk_bytes','module_interface',
 'output_suffixes','reserved_final_jobs','receipt_protocol','toolchain_inventory_mode')
REVIEW_FIELDS=('review_status','storage_adapter_review_status','readonly_commit_review_status',
 'transport_review_status','process_containment_review_status','compiler_adapter_review_status',
 'final_checks_review_status')

@dataclass(frozen=True)
class RestoreScope:
    raw_bytes: bytes
    @property
    def data(self):return p.parse_json(self.raw_bytes)
    @property
    def sha256(self):return p.sha(self.raw_bytes)

def validate_execution_context(*,plan,profiles,current_contract,current_manifest,old_manifest,prior_manifest,
        source_delta,inventory,current_identity,selection,bundle,integration_pins,prior_contract):
    # The exact final-component seam binds current identities and independently
    # reviewed selection/admission pins. Actual admission records are required by
    # the driver before this pure context is used.
    selection=final._selection_context(plan,selection,bundle,current_identity,integration_pins)
    p.need(p.object_sha(prior_contract)==bundle.prior_context['identity']['contract_sha256'],'historical prior contract changed')
    p.need(p.object_sha(current_contract)==integration_pins['current_contract_sha256'],'current contract hash changed')
    p.need(p.object_sha(profiles)==current_identity['profiles_sha256'],'profile bytes changed')
    p.need(p.object_sha(inventory)==current_identity['toolchain_inventory_sha256'],'canonical runtime inventory changed')
    p.validate_prior_current_sources(prior_manifest,current_manifest,bundle.prior_context['identity'],current_identity)
    p.validate_original_repair(old_manifest,prior_manifest,source_delta,plan)
    for key in NUMERIC_AND_PROTOCOL_FIELDS:
        p.need(key in current_contract and key in prior_contract and type(current_contract[key]) is type(prior_contract[key]) and current_contract[key]==prior_contract[key],
               'numeric/protocol contract field changed: '+key)
    for key in REVIEW_FIELDS:
        expected='reviewed_for_execution' if key=='review_status' else 'reviewed'
        p.need(current_contract.get(key)==expected,'inactive execution gate: '+key)
    fixed={'source_commit':p.PRIOR_SOURCE,'source_manifest_sha256':p.PRIOR_MANIFEST,'plan_sha256':p.PLAN_SHA256,
      'profiles_sha256':current_identity['profiles_sha256'],'source_delta_sha256':p.SOURCE_DELTA,
      'runner_sha256':bundle.prior_context['identity']['runner_sha256'],'selection_sha256':selection.raw_sha256,
      'old_identity_sha256':p.OLD_IDENTITY,'prior_identity_sha256':p.PRIOR_IDENTITY,'context_bundle_sha256':bundle.raw_sha256}
    p.need(all(type(current_contract.get(k)) is type(v) and current_contract[k]==v for k,v in fixed.items()),'execution contract identity binding changed')
    f.validate_contract(current_contract,current_manifest,plan,profiles)
    p.need(current_contract['max_restored_bytes']==p.MAX_RESTORED and current_contract['max_run_age_seconds']==p.MAX_AGE,'aggregate cap/deadline changed')
    return selection


def scope_stage_ids(plan,selection,*,target_stage=None,final_role=None):
    p.validate_plan(plan);p.validate_provider_dag(selection,plan)
    p.need((target_stage is None)!=(final_role is None),'exactly one stage/final scope required')
    stages={s['stage_id']:s for s in plan['stages']}
    if target_stage is not None:
        p.need(type(target_stage) is str and target_stage in stages and type(selection.row(target_stage)) is p.CurrentOrigin,'fresh current target required')
        expected=stages[target_stage]['required_predecessors']
    else:
        p.need(final_role in ('export_target','fresh_kernel'),'only full-closure final roles allowed')
        expected=list(stages)
    historical=[sid for sid in expected if type(selection.row(sid)) is not p.CurrentOrigin]
    current=[sid for sid in expected if type(selection.row(sid)) is p.CurrentOrigin]
    for sid in historical:p.need(set(stages[sid]['required_predecessors'])<=set(historical),'historical subset not transitively closed')
    for sid in expected:p.need(set(stages[sid]['required_predecessors'])<=set(expected),'restore scope not transitively closed')
    return list(expected),historical,current


def validate_restore_scope(*,plan,selection,bundle,wrappers,native_bytes,current_identity,integration_pins,
                           target_stage=None,final_role=None):
    """Validate all native bytes before passing an exact subset to native validators.

    The historical invocation view changes only the outer prior label. Hashes,
    identities, descriptors, receipts and predecessor chains are never rewritten.
    """
    selection=final._selection_context(plan,selection,bundle,current_identity,integration_pins)
    expected,historical,current=scope_stage_ids(plan,selection,target_stage=target_stage,final_role=final_role)
    p.need(type(wrappers) is list and [w.get('native_descriptor',{}).get('stage_id') for w in wrappers]==expected,'wrong/missing/duplicate/unordered restore wrappers')
    p.need(type(native_bytes) is dict and set(native_bytes)==set(expected),'exact native byte map required')
    stages={s['stage_id']:s for s in plan['stages']};admitted={};objects={};view=[];sizes={};all_receipts={}
    for wrapper in wrappers:
        p.keys(wrapper,p.WRAPPER_KEYS,'restore wrapper');d=wrapper['native_descriptor'];sid=d['stage_id'];row=selection.row(sid);origin=type(row).__name__
        p.need(wrapper['origin']==origin,'selected provider label changed')
        identity=current_identity if origin=='CurrentOrigin' else bundle.context(origin)['identity']
        final._validate_wrapper(wrapper,identity,sid,current_workflow_id=integration_pins['current_workflow_id'] if origin=='CurrentOrigin' else None)
        if origin!='CurrentOrigin':p.need(p._wrapper_pin(wrapper,selection,bundle,plan)==row.pin,'historical payload pin changed')
        p.keys(native_bytes[sid],{'descriptor','receipt'},'native byte pair')
        receipt=p.validate_native_bytes(wrapper,native_bytes[sid]['descriptor'],native_bytes[sid]['receipt'])
        p.need(receipt.get('schema')=='fresh-stage-receipt-v1' and receipt.get('status')=='fresh_compile_check_pairs_only' and receipt.get('proof_pass_claimed') is False,'native receipt scope/status changed')
        if origin=='OldOrigin':p.need('receipt_protocol' not in receipt,'original receipt protocol rewritten')
        else:p.need(receipt.get('receipt_protocol')=='readonly_committed_v1','readonly receipt protocol missing')
        p.need(receipt.get('predecessors')==[admitted[x] for x in stages[sid]['required_predecessors']],'exact original native predecessor chain changed')
        modules=receipt.get('modules');p.need(type(modules) is list and [x.get('module') for x in modules]==stages[sid]['modules'],'native stage module order/coverage changed')
        files=receipt.get('files');p.need(type(files) is dict,'native receipt files map missing')
        for entry in modules:
            module=entry['module'];outputs=entry.get('outputs');prefix='objects/'+module.replace('.','/')
            p.need(type(outputs) is dict and set(outputs)=={prefix+s for s in p.SUFFIXES},'exact six companions required')
            for name,digest in outputs.items():
                p.digest(digest,'native output hash');p.need(name in files and files[name].get('sha256')==digest,'native module/file output hash mismatch')
                p.integer(files[name].get('bytes'),'native companion byte count',p.MAX_ARTIFACT,minimum=0)
            if origin!='CurrentOrigin':
                p.need(module not in objects,'duplicate historical object provider');objects[module]=copy.deepcopy(outputs)
        if origin!='CurrentOrigin':
            native=copy.deepcopy(wrapper)
            if origin=='PriorSuccessorOrigin':native['origin']='CurrentOrigin'
            view.append(native)
        admitted[sid]=copy.deepcopy(d);all_receipts[sid]=receipt;sizes[sid]=d['archive_bytes']
    ledger=p.cumulative_raw_budget(selection,sizes)
    value={'schema':'exact-three-context-restore-scope-v1','target_stage':target_stage,'final_role':final_role,
        'expected_stage_ids':expected,'historical_stage_ids':historical,'current_stage_ids':current,
        'native_descriptors':[admitted[s] for s in expected],'historical_native_view':view,
        'historical_objects':objects,'raw_archive_bytes':ledger.total_bytes,'remaining_raw_bytes':ledger.remaining_bytes,
        'selection_sha256':selection.raw_sha256,'context_bundle_sha256':bundle.raw_sha256,
        'current_identity':current_identity,'semantic_admission_claimed':False,'activation_allowed':False}
    p.need([w['native_descriptor'] for w in view]==[admitted[s] for s in historical],'historical native mapping mutated')
    return RestoreScope(p.json_bytes(value))


def canonical_native_order(plan,descriptors):
    """Order only; never normalize descriptor identity or content."""
    stages=p.validate_plan(plan);p.need(type(descriptors) is list,'descriptor list required')
    by={d['stage_id']:d for d in descriptors};p.need(len(by)==len(descriptors) and set(by)<={s['stage_id'] for s in stages},'duplicate or unknown native descriptor')
    return [copy.deepcopy(by[s['stage_id']]) for s in stages if s['stage_id'] in by]


def archive_ledger_after_build(selection,scope_sizes,stage_id,raw_bytes):
    p.need(type(selection.row(stage_id)) is p.CurrentOrigin and stage_id not in scope_sizes,'new current stage must be distinct')
    sizes=copy.deepcopy(scope_sizes);sizes[stage_id]=raw_bytes
    return p.cumulative_raw_budget(selection,sizes)
