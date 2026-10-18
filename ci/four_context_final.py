"""Pure, fail-closed FOUR-context final candidate. ACTIVATION IS ALWAYS FALSE.

No network, process execution or filesystem mutation occurs here. Inputs must
come from OriginTransport and extract_verified_archive, after the policy and
stage validators have checked source, profiles, receipt chains and byte bounds.
Authentication is that caller's responsibility; a dictionary is not authority.
The original same-run driver and its receipt format are deliberately unchanged.
"""
from __future__ import annotations

from copy import deepcopy
from datetime import datetime, timezone
import math
from pathlib import PurePosixPath
import fresh_stage as f
import four_context_policy as p
import three_context_policy as original_policy
import three_context_final as original_final

TARGET_MODULE = 'SpectreFinite.RadiusFivePruningHierarchy'
TARGET = 'SpectreFinite.HexSearch.RadiusFivePruning.certifiedParentOccurrenceTheorem'
TYPE = 'SpectreFinite.HexSearch.NativeHierarchy.ParentOccurrenceTheorem'
ALLOWED_AXIOMS = ['propext', 'Classical.choice', 'Quot.sound']
DEFINING_SOURCE = {'module': 'SpectreFinite.NativeCoarsening',
    'sha256': '7a880be093b4c4b82004e94cfa4484d5fbe35fe606033bf6912f5072f6e42659'}
AUDIT_SHA256 = '594df90549cc67c2708d7950a3df43e76e2f46348009903226aced8afd9e9859'
AUDIT_OUTPUT = b'EXPORT_CONTRACT_AUDIT_PASSED\n'
FINAL_ROLES = ('export_target', 'fresh_kernel', 'lean_export', 'nanoda', 'conron')
ORIGINAL_MAX_AGE_SECONDS = 518400
CONTINUATION_STATUS = 'continued_hierarchy_c_checks_passed_clean_rebuild_pending'
REPOSITORY = 'jconorgrogan/palomar-chair-verification'
REPOSITORY_ID = 1407290933
FINAL_ARTIFACT_LIMIT = 3 * 1024**3
ORIGINS = p.ORIGINS
ACTIVATION_ALLOWED = False
ORIGINAL_DEADLINE = '2026-10-22T06:15:54Z'
CANDIDATE_SELECTION_SHA256 = '362d0324b33ace062795c53b2c94ffc3752c87d7baeedc26299942482ee9d223'
PRIOR_FILES_SHA256 = '9618bc2900517a9234254ddf2a2ea6fb3c78f643bd12f11967f986f49e7dde1d'
INTEGRATION_PIN_FIELDS = frozenset({'current_pipeline_commit', 'current_contract_sha256',
    'selection_sha256', 'admission_certificate_sha256', 'admission_reconciliation_sha256',
    'current_workflow_id'})
CURRENT_WORKFLOW = {'head_branch': 'verify/hierarchy-c-production-recovery-20261018',
    'path': '.github/workflows/hierarchy-c-production-recovery.yml',
    'name': 'Verify hierarchy C production recovery'}


def _digest(value, label):
    f.need(isinstance(value, str) and f.SHA256.fullmatch(value), 'invalid '+label)
    return value


def _positive(value, label):
    f.need(type(value) is int and value > 0, 'invalid '+label)
    return value


def _timestamp(value):
    f.need(isinstance(value, str), 'missing trusted timestamp')
    try:
        result = datetime.fromisoformat(value.replace('Z', '+00:00'))
    except ValueError as error:
        raise f.Rejected('invalid trusted timestamp') from error
    f.need(result.tzinfo is not None, 'timestamp must include timezone')
    return result


def check_deadline(bundle, selection, current_identity, *, now,
                   current_max_age_seconds=518400, previous_now=None, artifact_expiries=()):
    """Retain the original clock across all four fixed contexts and expiries."""
    deadline = p.deadline_check(bundle, selection, now, current_identity=current_identity,
        max_age_seconds=current_max_age_seconds, previous_now=previous_now,
        artifact_expiries=artifact_expiries)
    f.need(deadline <= _timestamp(ORIGINAL_DEADLINE), 'original deadline reset')
    return deadline.isoformat()


def activation_status():
    """No supplied dictionary or review flag can activate this draft."""
    return {'active': False, 'activation_allowed': False,
        'status': 'inactive_four_context_final_gate_candidate',
        'clean_source_rebuild': 'pending', 'proof_pass_claimed': False,
        'required': ['actual_authenticated_90_payload_native_admission',
                     'separately_reviewed_current_runner_driver_transport_workflow',
                     'independently_sealed_current_identity_and_evidence_pins']}


def _integration_pins(integration_pins):
    f.need(type(integration_pins) is dict and set(integration_pins) == INTEGRATION_PIN_FIELDS,
           'exact reviewed integration pins required')
    commit = integration_pins['current_pipeline_commit']
    f.need(type(commit) is str and f.COMMIT.fullmatch(commit), 'unresolved current pipeline commit')
    _positive(integration_pins['current_workflow_id'], 'unresolved current workflow ID')
    for key in INTEGRATION_PIN_FIELDS - {'current_pipeline_commit', 'current_workflow_id'}:
        _digest(integration_pins[key], 'unresolved integration pin: '+key)


def _selection_context(plan, selection, bundle, current_identity, integration_pins):
    _integration_pins(integration_pins)
    bundle = p.validate_context_bundle(bundle.raw_bytes, bundle.raw_sha256)
    selection = p.parse_selection(selection.raw_bytes, integration_pins['selection_sha256'],
                                  plan, bundle, require_payloads=True)
    providers = p.validate_provider_dag(selection, plan)
    f.need(tuple(len(providers[o]) for o in ORIGINS) == (37, 11, 42, 1, 2),
           'exact 37 original, 11 prior, 42 latest, 1 production and 2 fresh stages required')
    p.validate_current_identity(current_identity, selection, bundle,
        pipeline_commit=integration_pins['current_pipeline_commit'],
        contract_sha256=integration_pins['current_contract_sha256'])
    f.need(tuple(f.MODERN_SUFFIXES) == p.SUFFIXES, 'six modern companion suffixes changed')
    return selection


def original_admission_context(selection, bundle, integration_pins):
    """Recover the exact original 48-stage authority; never broaden its claim.

    The new static selection extends the original provider map. Reconstructing
    canonical original bytes is accepted only if both frozen native hashes match.
    The actual certificate remains unchanged and is checked by its original API.
    """
    _integration_pins(integration_pins)
    bundle=p._bundle(bundle);p._selection_consistent(selection)
    f.need(selection.bundle_sha256==bundle.raw_sha256,'admission selection bundle mismatch')
    value=bundle.data
    old_bundle={'schema':'fixed-three-context-bundle-v1',
        'contexts':{name:value['contexts'][name] for name in p.ORIGINS[:2]},
        'old_stage_rows':value['old_stage_rows'],'prior_candidate_rows':value['prior_candidate_rows']}
    old_bundle['contexts']['CurrentOrigin']={'rank':2,'parents':['OldOrigin','PriorSuccessorOrigin'],
        'source_commit':p.PRIOR_SOURCE,'source_manifest_sha256':p.PRIOR_MANIFEST}
    raw=p.json_bytes(old_bundle)
    original_bundle=original_policy.validate_context_bundle(raw,original_policy.BUNDLE_SHA256)
    old_selection=selection.data
    old_selection.pop('latest_origin');old_selection.pop('production_origin')
    old_selection.update(schema='verified-continuation-selection-v2',context_bundle_sha256=original_bundle.raw_sha256)
    rows=[]
    for row in old_selection['stages']:
        if row['origin'] in ('LatestSuccessorOrigin','ProductionSuccessOrigin'):
            row.clear();row.update(stage_id=selection.rows[len(rows)].stage_id,origin='CurrentOrigin')
        cls=getattr(original_policy,row['origin'])
        rows.append(cls(row['stage_id'],p.json_bytes(row['pin'])) if 'pin' in row else cls(row['stage_id']))
    raw=p.json_bytes(old_selection)
    latest=bundle.latest_context['identity']
    f.need(p.sha(raw)==latest['selection_sha256'],'original admission selection byte hash changed')
    original_selection=original_policy.Selection(raw,original_bundle.raw_sha256,tuple(rows),original_bundle.raw_bytes)
    original_policy._selection_consistent(original_selection)
    pins={**integration_pins,'current_pipeline_commit':latest['pipeline_commit'],
        'current_contract_sha256':latest['contract_sha256'],'selection_sha256':latest['selection_sha256'],
        'current_workflow_id':bundle.latest_context['workflow']['workflow_id']}
    return original_selection,original_bundle,latest,pins


def validate_admission_certificate(certificate_bytes, *, selection, bundle,
                                   current_identity, integration_pins):
    original_selection,original_bundle,latest,pins=original_admission_context(selection,bundle,integration_pins)
    p.validate_current_identity(current_identity,selection,bundle,
        pipeline_commit=integration_pins['current_pipeline_commit'],contract_sha256=integration_pins['current_contract_sha256'])
    return original_final.validate_admission_certificate(certificate_bytes,selection=original_selection,
        bundle=original_bundle,current_identity=latest,integration_pins=pins)


def validate_admission_reconciliation(reconciliation_bytes, *, certificate_bytes,
                                      current_identity, integration_pins, now):
    # The original reconciliation API does not need selection/bundle. Its pinned
    # latest identity is recovered from the unchanged raw certificate context by
    # the caller through the explicit original context helper. This compatibility
    # entrypoint requires the immutable latest identity supplied in the module's
    # reviewed literal below, rather than substituting the new current identity.
    _integration_pins(integration_pins)
    latest=p.latest_native_identity()
    pins={**integration_pins,'current_pipeline_commit':latest['pipeline_commit'],
        'current_contract_sha256':latest['contract_sha256'],'selection_sha256':latest['selection_sha256'],
        'current_workflow_id':p.LATEST_WORKFLOW_ID}
    f.need(current_identity.get('latest_identity_sha256')==p.LATEST_IDENTITY,'latest admission lineage missing')
    return original_final.validate_admission_reconciliation(reconciliation_bytes,certificate_bytes=certificate_bytes,
        current_identity=latest,integration_pins=pins,now=now)


def _canonical_path(value):
    f.need(isinstance(value, str) and value and '\\' not in value and '\x00' not in value,
           'invalid execution path')
    path = PurePosixPath(value)
    f.need(path.is_absolute() and str(path) == value and '..' not in path.parts,
           'noncanonical execution path')
    return value


def nanoda_configuration(paths):
    return {'use_stdin': False, 'export_file_path': _canonical_path(paths['export_path']),
        'permitted_axioms': list(ALLOWED_AXIOMS), 'unpermitted_axiom_hard_error': False,
        'num_threads': 2, 'nat_extension': True, 'string_extension': True}


def final_command_specs(role, paths):
    """Exact existing checker argv and budgets, for both execution and checking.

    The driver records each returned specification on the actual run_process
    result. No options are inferred from a self-reported command receipt.
    """
    f.need(role in FINAL_ROLES, 'unknown final role')
    f.need(set(paths) == {'toolchain_root', 'code_root', 'export_path', 'nanoda_config_path'},
           'execution path fields mismatch')
    for value in paths.values():
        _canonical_path(value)
    tool = paths['toolchain_root'] + '/bin/'
    exported = paths['export_path']

    def spec(name, argv, seconds=18000, rss=8*1024**3, logs=32*1024**2, sessions=False):
        return {'name': name, 'argv': argv, 'timeout_seconds': seconds,
            'resource_limits': {'address_space_bytes': 12*1024**3,
                'rss_tree_bytes': rss, 'max_created_file_bytes': logs},
            'max_log_bytes': logs, 'new_sessions_explicitly_allowed': sessions}

    return {
        'export_target': [
            spec('target_export', [tool+'leanexport', TARGET_MODULE, '--', TARGET], logs=2*1024**3),
            spec('exact_export_audit', [tool+'lean', '-j1', '-M4096', '--run',
                paths['code_root']+'/FinalExportAudit.lean', exported], seconds=1800, rss=4*1024**3)],
        'fresh_kernel': [spec('fresh_whole_closure', [tool+'leanchecker', '--fresh', TARGET_MODULE])],
        'lean_export': [
            spec('lean_from_export', [tool+'leanchecker', '--silent', '--from-export', exported], seconds=9000),
            spec('lake_export_axioms', [tool+'lake', 'check', '--from-export', exported], seconds=9000, sessions=True)],
        'nanoda': [spec('nanoda', [tool+'nanoda_bin', paths['nanoda_config_path']], rss=6*1024**3)],
        'conron': [spec('conron', [tool+'con-ron', '--verified', '--jobs=2', exported], rss=3*1024**3)],
    }[role]


def _successful_command(command, spec):
    effective = command.get('effective_timeout_seconds')
    f.need(type(effective) is int and 0 < effective <= spec['timeout_seconds'],
           'invalid or enlarged effective shared-deadline timeout')
    for key, expected in spec.items():
        f.need(command.get(key) == expected and type(command.get(key)) is type(expected),
               'final command specification mismatch: '+key)
    f.need(type(command.get('exit_code')) is int and command['exit_code'] == 0,
           'unsuccessful final command')
    for key in ('timed_out', 'log_overflow', 'memory_exceeded', 'surviving_children'):
        f.need(command.get(key) is False, 'failed command or missing limit evidence: '+key)
    f.need(type(command.get('escaped_descendants')) is bool and
           (spec['new_sessions_explicitly_allowed'] or command['escaped_descendants'] is False),
           'unexpected escaped descendants')
    for key in ('process_group_empty', 'descendants_empty'):
        f.need(command.get(key) is True, 'missing command cleanup evidence: '+key)
    peak = command.get('peak_sampled_tree_rss_bytes')
    f.need(type(peak) is int and 0 <= peak <= spec['resource_limits']['rss_tree_bytes'],
           'invalid/excessive measured RSS')
    elapsed = command.get('elapsed_seconds')
    f.need(type(elapsed) in (int, float) and math.isfinite(elapsed) and elapsed >= 0,
           'invalid elapsed command time')


def _file_info(value):
    f.need(type(value) is dict and set(value) == {'bytes', 'sha256'}, 'invalid final file metadata')
    f.need(type(value['bytes']) is int and value['bytes'] >= 0, 'invalid final file size')
    _digest(value['sha256'], 'final file hash')


def validate_final_commands(receipt):
    """Require exact complete command sequence, cleanup, limits and log bindings."""
    role = receipt['role']
    specs = final_command_specs(role, receipt['execution_paths'])
    commands = receipt.get('commands')
    f.need(type(commands) is list and len(commands) == len(specs), 'missing/extra final command')
    files = receipt.get('files')
    f.need(type(files) is dict, 'missing final files')
    for path, info in files.items():
        f.safe_rel(path)
        _file_info(info)
    expected_files = set()
    for command, spec in zip(commands, specs):
        _successful_command(command, spec)
        for stream in ('stdout', 'stderr'):
            name = spec['name']+'.'+stream
            if role == 'export_target':
                name = {'target_export.stdout': 'target.ndjson', 'target_export.stderr': 'export.stderr',
                    'exact_export_audit.stdout': 'audit.stdout', 'exact_export_audit.stderr': 'audit.stderr'}[name]
            expected_files.add(name)
            f.need(name in files and command.get(stream) == files[name], 'final command log binding mismatch')
        f.need(sum(command[stream]['bytes'] for stream in ('stdout', 'stderr')) <= spec['max_log_bytes'],
               'combined final command logs exceed bound')
    if role == 'export_target':
        f.need(files['audit.stdout'] == {'bytes': len(AUDIT_OUTPUT), 'sha256': f.sha(AUDIT_OUTPUT)},
               'exact export audit output incomplete')
        f.need(files['target.ndjson']['sha256'] == receipt.get('export_sha256'), 'export file hash mismatch')
    if role == 'nanoda':
        config = nanoda_configuration(receipt['execution_paths'])
        f.need(receipt.get('nanoda_config') == config, 'NanoDa audited configuration mismatch')
        payload = f.json_bytes(config)
        f.need(files.get('nanoda.json') == {'bytes': len(payload), 'sha256': f.sha(payload)},
               'NanoDa configuration byte binding mismatch')
        expected_files.add('nanoda.json')
    f.need(set(files) == expected_files, 'missing/unexpected final files')



def _validate_wrapper(wrapper, identity, role, *, final=False, current_workflow_id=None):
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
    if wrapper['origin'] in ORIGINS[:4]:
        f.need(run.get('status') == 'completed' and run.get('conclusion') == 'failure', 'historical run not terminal failure')
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
    workflow = artifact.get('workflow_run', {})
    f.need(artifact.get('id') == d['artifact_id'] and type(artifact.get('id')) is int and
           artifact.get('expired') is False and artifact.get('digest') == 'sha256:'+d['artifact_zip_sha256'] and
           artifact.get('name') == 'hierarchy-c-'+identity['run_id']+'-'+identity['run_attempt']+'-'+role,
           'authenticated artifact identity/digest mismatch')
    _positive(artifact.get('size_in_bytes'), 'authoritative ZIP bytes')
    f.need(type(workflow.get('id')) is int and str(workflow['id']) == identity['run_id'] and
           workflow.get('head_sha') == identity['pipeline_commit'] and
           workflow.get('repository_id') == REPOSITORY_ID and workflow.get('head_repository_id') == REPOSITORY_ID,
           'artifact workflow/repository mismatch')
    return d


def resolve_provenance(*, plan, selection, bundle, wrappers, current_identity,
                       integration_pins):
    """Freeze all 93 native providers without relabeling historical descriptors.

    Actual archives/native receipt bytes and native predecessor chains must have
    passed the correct historical or current validator before this pure seam.
    """
    selection = _selection_context(plan, selection, bundle, current_identity, integration_pins)
    stages = plan['stages']
    f.need(type(wrappers) is list and len(wrappers) == len(stages),
           'full plan provenance coverage/order mismatch')
    rows = []
    for stage, choice, wrapper in zip(stages, selection.rows, wrappers):
        origin = type(choice).__name__
        f.need(type(wrapper) is dict and wrapper.get('origin') == origin, 'provenance origin mismatch')
        identity = current_identity if origin == 'CurrentOrigin' else bundle.context(origin)['identity']
        d = _validate_wrapper(wrapper, identity, stage['stage_id'],
                              current_workflow_id=integration_pins['current_workflow_id'])
        f.need(d['producer_job'] == stage['producer_job'], 'producer differs from original plan')
        if origin != 'CurrentOrigin':
            # The prior native validator's invocation view is NOT used here: the
            # outward registry must retain PriorSuccessorOrigin and native IDs.
            full = deepcopy(wrapper)
            full.setdefault('archive_path', '/pure-projection/never-opened')
            f.need(p._wrapper_pin(full, selection, bundle, plan) == choice.pin,
                   'frozen historical artifact pin mismatch')
        rows.append(deepcopy({key: value for key, value in wrapper.items() if key != 'archive_path'}))
    p.cumulative_raw_budget(selection,
        {row['native_descriptor']['stage_id']: row['native_descriptor']['archive_bytes'] for row in rows})
    return {'rows': rows, 'sha256': f.sha(f.json_bytes(rows))}


def validate_native_predecessor_order(*, plan, provenance, native_receipt_bytes):
    """Recheck all exact raw receipt digests and plan-filtered native chains.

    Original receipts have the historical v1 envelope with no receipt_protocol.
    Prior/current receipts must retain readonly_committed_v1. This is additional
    chain checking, never a substitute for native archive/semantic validation.
    """
    p.validate_plan(plan)
    f.need(type(provenance) is dict and set(provenance) == {'rows', 'sha256'}
           and provenance['sha256'] == f.sha(f.json_bytes(provenance['rows'])),
           'native chain provenance digest mismatch')
    rows = provenance['rows']
    ids = [stage['stage_id'] for stage in plan['stages']]
    f.need(type(rows) is list and len(rows) == len(ids), 'native chain provenance count mismatch')
    f.need(type(native_receipt_bytes) is dict and set(native_receipt_bytes) == set(ids),
           'all 93 exact raw native stage receipts required')
    seen = {}
    hashes = {}
    for stage, wrapper in zip(plan['stages'], rows):
        sid = stage['stage_id']; d = wrapper['native_descriptor']; origin = wrapper['origin']
        f.need(origin in ORIGINS and d.get('stage_id') == sid, 'native chain origin/order mismatch')
        raw = native_receipt_bytes[sid]
        f.need(type(raw) is bytes and f.sha(raw) == d.get('receipt_sha256'),
               'native chain exact receipt byte hash mismatch')
        receipt = p.parse_json(raw)
        f.need(type(receipt) is dict and receipt.get('schema') == 'fresh-stage-receipt-v1'
               and receipt.get('status') == 'fresh_compile_check_pairs_only'
               and receipt.get('proof_pass_claimed') is False
               and receipt.get('stage_id') == sid and receipt.get('producer_job') == stage['producer_job']
               and receipt.get('identity') == d['identity'], 'native stage receipt envelope mismatch')
        if origin == 'OldOrigin':
            f.need('receipt_protocol' not in receipt, 'original native receipt protocol rewritten')
        else:
            f.need(receipt.get('receipt_protocol') == f.READONLY_PROTOCOL,
                   'prior/current readonly native receipt protocol missing')
        expected = [seen[ancestor] for ancestor in stage['required_predecessors']]
        f.need(receipt.get('predecessors') == expected, 'native plan-filtered predecessor chain/order mismatch')
        seen[sid] = d; hashes[sid] = f.sha(raw)
    return hashes


def final_context(*, manifest, provenance, object_hashes, current_identity, integration_pins):
    _integration_pins(integration_pins)
    f.need(current_identity.get('selection_sha256') == integration_pins['selection_sha256'],
           'final context selection binding mismatch')
    f.need(f.sha(f.json_bytes(manifest)) == p.PRIOR_MANIFEST == current_identity.get('source_manifest_sha256')
           and current_identity.get('source_commit') == p.PRIOR_SOURCE, 'exact prior/current source required')
    entries = f.manifest_index(manifest)
    f.need(type(object_hashes) is dict, 'restored object hashes missing')
    expected = {name.removeprefix('objects/') for m in entries for name in f.object_paths(m,f.MODERN_SUFFIXES)}
    f.need(set(object_hashes) == expected, 'exact full-manifest object coverage mismatch')
    for value in object_hashes.values():
        _digest(value, 'restored object hash')
    f.need(provenance.get('sha256') == f.sha(f.json_bytes(provenance.get('rows'))), 'resolved provenance digest mismatch')
    return {'target': TARGET, 'expected_type': TYPE, 'allowed_axioms': list(ALLOWED_AXIOMS),
        'defining_source': dict(DEFINING_SOURCE), 'final_export_audit_sha256': AUDIT_SHA256,
        'source_manifest_sha256': current_identity['source_manifest_sha256'],
        'checked_source_count': manifest['source_count'],
        'checked_sources': {module: entry['sha256'] for module, entry in entries.items()},
        'restored_object_hashes': deepcopy(object_hashes),
        'resolved_provenance': deepcopy(provenance['rows']), 'resolved_provenance_sha256': provenance['sha256'],
        'selection_sha256': current_identity['selection_sha256'],
        'context_bundle_sha256': p.BUNDLE_SHA256, 'prior_identity_sha256': p.PRIOR_IDENTITY,
        'latest_identity_sha256': p.LATEST_IDENTITY, 'production_identity_sha256':p.PRODUCTION_IDENTITY,
        'admission_certificate_sha256': integration_pins['admission_certificate_sha256'],
        'admission_reconciliation_sha256': integration_pins['admission_reconciliation_sha256']}


def final_verdict(*, plan, manifest, prior_manifest, current_identity, selection, bundle,
                  integration_pins, admission_certificate_bytes, admission_reconciliation_bytes,
                  resolved_provenance, native_receipt_bytes, checked, now,
                  current_max_age_seconds=518400, previous_now=None):
    """Return only a continuation result. A separate clean rebuild remains mandatory.

    checked maps every FINAL_ROLES entry to {'receipt': verified extracted receipt,
    'wrapper': OriginTransport wrapper}. Both restore jobs independently supply
    full provenance/object/source maps; every downstream check binds that context.
    """
    selection = _selection_context(plan, selection, bundle, current_identity, integration_pins)
    p.validate_prior_current_sources(prior_manifest, manifest, bundle.prior_context['identity'], current_identity)
    validate_admission_certificate(admission_certificate_bytes, selection=selection, bundle=bundle,
        current_identity=current_identity, integration_pins=integration_pins)
    validate_admission_reconciliation(admission_reconciliation_bytes, certificate_bytes=admission_certificate_bytes,
        current_identity=current_identity, integration_pins=integration_pins, now=now)
    deadline = check_deadline(bundle, selection, current_identity, now=now,
        current_max_age_seconds=current_max_age_seconds, previous_now=previous_now)
    f.need(type(checked) is dict and set(checked) == set(FINAL_ROLES), 'complete fresh final role set required')
    provenance = resolve_provenance(plan=plan, selection=selection, bundle=bundle,
        wrappers=resolved_provenance['rows'], current_identity=current_identity, integration_pins=integration_pins)
    f.need(provenance == resolved_provenance, 'resolved full provenance/hash mismatch')
    validate_native_predecessor_order(plan=plan, provenance=provenance, native_receipt_bytes=native_receipt_bytes)
    entries = f.manifest_index(manifest)
    modules = [m for stage in plan['stages'] for m in stage['modules']]
    f.need(len(modules) == len(set(modules)) and set(modules) == set(entries), 'full plan source coverage mismatch')
    context = final_context(manifest=manifest, provenance=provenance,
        object_hashes=checked['export_target']['receipt']['restored_object_hashes'], current_identity=current_identity,
        integration_pins=integration_pins)
    f.need(context['checked_sources'].get(DEFINING_SOURCE['module']) == DEFINING_SOURCE['sha256'],
           'defining source not in exact source manifest')
    export_hash = _digest(checked['export_target']['receipt'].get('export_sha256'), 'exact export hash')
    final_artifacts = {}
    for role in FINAL_ROLES:
        evidence = checked[role]
        f.need(type(evidence) is dict and set(evidence) == {'receipt', 'wrapper'}, 'final evidence fields mismatch')
        receipt = evidence['receipt']
        d = _validate_wrapper(evidence['wrapper'], current_identity, role, final=True,
                              current_workflow_id=integration_pins['current_workflow_id'])
        f.need(d['receipt_sha256'] == f.sha(f.json_bytes(receipt)), 'final receipt bytes/digest mismatch')
        f.need(receipt.get('schema') == 'fresh-final-evidence-v1' and receipt.get('role') == role and
               receipt.get('status') == 'completed_check_only' and receipt.get('proof_pass_claimed') is False and
               receipt.get('identity') == current_identity, 'stale/relabelled final receipt')
        for key, expected in context.items():
            f.need(receipt.get(key) == expected and type(receipt.get(key)) is type(expected),
                   'final context/provenance mismatch: '+key)
        if role != 'fresh_kernel' or 'export_sha256' in receipt:
            f.need(receipt.get('export_sha256') == export_hash, 'checker exports disagree')
        validate_final_commands(receipt)
        for wrapper in (evidence['wrapper'],):
            expiry = _timestamp(wrapper['authenticated_metadata']['artifact'].get('expires_at'))
            f.need(now < expiry, 'final artifact expired')
        final_artifacts[role] = deepcopy({key: value for key, value in evidence['wrapper'].items() if key != 'archive_path'})
    for row in provenance['rows']:
        f.need(now < _timestamp(row['authenticated_metadata']['artifact'].get('expires_at')), 'stage artifact expired')
    counts = {origin: {'stages': 0, 'modules': 0} for origin in ORIGINS}
    for stage, row in zip(plan['stages'], provenance['rows']):
        counts[row['origin']]['stages'] += 1
        counts[row['origin']]['modules'] += len(stage['modules'])
    return {'schema': 'verified-continuation-hierarchy-c-verdict-v4', 'status': CONTINUATION_STATUS,
        'identity': deepcopy(current_identity), **context, 'exact_type': TYPE,
        'source_count': manifest['source_count'], 'export_sha256': export_hash,
        'checks': {role: 'passed' for role in FINAL_ROLES}, 'final_artifacts': final_artifacts,
        'origin_counts': counts, 'origins': {'OldOrigin': deepcopy(bundle.old_context['identity']),
            'PriorSuccessorOrigin': deepcopy(bundle.prior_context['identity']),
            'LatestSuccessorOrigin': deepcopy(bundle.latest_context['identity']),
            'ProductionSuccessOrigin':deepcopy(bundle.production_context['identity']), 'CurrentOrigin': deepcopy(current_identity)},
        'acceptance_deadline': deadline, 'clean_source_rebuild': 'pending',
        'activation_allowed': False, 'admission_kernel_executed': False,
        'bit_reproducibility_claim': False, 'overall_task_complete': False,
        'scope': 'Exact finite hierarchy C continuation checks only. Clean-source rebuild pending. '
                 'No unconditional downstream 2D/4D or Palomar-acceptance claim.'}


def compare_clean_reproduction(continuation, clean):
    """Compare an independently validated clean-gate verdict; never run/authorize it.

    The caller must authenticate the clean verdict through its own separate gate.
    This is a comparison helper, not a replacement for validating clean receipts.
    Object/export byte differences always block a bit-reproducibility claim.
    """
    f.need(continuation.get('status') == CONTINUATION_STATUS, 'not a continuation verdict')
    f.need(clean.get('status') == 'clean_source_rebuild_checks_passed' and
           clean.get('initial_project_object_trees_empty') is True and
           clean.get('project_artifact_imports') == [] and
           type(clean.get('compiled_source_count')) is int and
           clean['compiled_source_count'] == continuation['source_count'] and
           clean.get('checks') == {role: 'passed' for role in FINAL_ROLES},
           'complete empty-tree clean-source gate missing')
    clean_identity = clean.get('identity', {})
    f.need(clean_identity.get('evidence_mode') == 'clean_source_rebuild' and
           'selection_sha256' not in clean_identity and 'old_identity_sha256' not in clean_identity and
           clean_identity.get('run_id') not in {identity['run_id'] for identity in continuation['origins'].values()}
           and 'prior_identity_sha256' not in clean_identity and 'latest_identity_sha256' not in clean_identity and 'production_identity_sha256' not in clean_identity and 'context_bundle_sha256' not in clean_identity,
           'clean rebuild reused continuation identity')
    for key in ('target', 'exact_type', 'allowed_axioms', 'defining_source', 'final_export_audit_sha256',
                'source_manifest_sha256', 'checked_sources', 'source_count'):
        f.need(clean.get(key) == continuation.get(key), 'clean theorem/type/axiom/source closure identity mismatch: '+key)
    for key in ('source_commit', 'source_manifest_sha256', 'plan_sha256', 'profiles_sha256',
                'lean_archive_sha256', 'toolchain_inventory_sha256'):
        f.need(clean.get('identity', {}).get(key) == continuation['identity'].get(key) and
               continuation['identity'].get(key) is not None, 'clean source/profile/toolchain mismatch: '+key)
    objects = clean.get('restored_object_hashes')
    expected = continuation['restored_object_hashes']
    f.need(type(objects) is dict and set(objects) == set(expected), 'clean object coverage mismatch')
    for value in objects.values():
        _digest(value, 'clean object hash')
    _digest(clean.get('export_sha256'), 'clean export hash')
    differences = [path for path in sorted(expected) if objects[path] != expected[path]]
    export_equal = clean['export_sha256'] == continuation['export_sha256']
    reproducible = not differences and export_equal
    return {'schema': 'continuation-clean-byte-comparison-v1',
        'status': 'byte_reproduction_verified' if reproducible else 'reproduction_difference_claim_blocked',
        'clean_source_rebuild': 'checks_passed', 'object_byte_differences': differences,
        'export_bytes_equal': export_equal, 'bit_reproducibility_claim': reproducible,
        'overall_task_complete': reproducible}
