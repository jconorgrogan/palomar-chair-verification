"""Pure, fail-closed final gates for the inactive verified-continuation adapter.

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
import continuation_policy as cp

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
ORIGINS = ('OldOrigin', 'CurrentOrigin')


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


def check_deadline(old_identity, current_identity, *, now, current_max_age_seconds=518400):
    """Check both trusted starts; a successor can never restart the old clock."""
    f.need(isinstance(now, datetime) and now.tzinfo is not None, 'aware current time required')
    _positive(current_max_age_seconds, 'current age bound')
    f.need(current_max_age_seconds <= ORIGINAL_MAX_AGE_SECONDS, 'current age bound enlarged')
    deadlines = []
    for identity, bound in ((old_identity, ORIGINAL_MAX_AGE_SECONDS),
                            (current_identity, current_max_age_seconds)):
        start = _timestamp(identity.get('run_started_at'))
        age = (now - start).total_seconds()
        f.need(0 <= age <= bound, 'original/current six-day deadline exceeded or future start')
        deadlines.append(start.timestamp() + bound)
    return datetime.fromtimestamp(min(deadlines), timezone.utc).isoformat()


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


def _identity_context(identity, current=False):
    f.need(type(identity) is dict, 'missing origin identity')
    for name in ('run_id', 'run_attempt'):
        value = identity.get(name)
        f.need(isinstance(value, str) and value.isdigit() and value == str(int(value)) and int(value) > 0,
               'invalid identity '+name)
    f.need(isinstance(identity.get('pipeline_commit'), str) and f.COMMIT.fullmatch(identity['pipeline_commit']),
           'invalid pipeline commit')
    _timestamp(identity.get('run_started_at'))
    if current:
        f.need(identity.get('evidence_mode') == 'verified_continuation', 'successor lacks continuation identity')
        _digest(identity.get('selection_sha256'), 'selection hash')
        _digest(identity.get('old_identity_sha256'), 'old identity hash')
    else:
        f.need(identity.get('evidence_mode') in (None, 'same_run'), 'chained continuation forbidden')


def _validate_wrapper(wrapper, identity, role, *, final=False):
    """Recheck complete producer metadata, never treating descriptor IDs as authority."""
    required = {'origin', 'native_descriptor', 'authenticated_metadata', 'raw_descriptor_sha256'}
    f.need(type(wrapper) is dict and set(wrapper) in (required, required | {'archive_path'}),
           'invalid origin wrapper fields')
    f.need(wrapper['origin'] in ORIGINS, 'unknown origin')
    if final:
        f.need(wrapper['origin'] == 'CurrentOrigin', 'old final evidence forbidden')
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
    if wrapper['origin'] == 'OldOrigin':
        f.need(run.get('status') == 'completed' and run.get('conclusion') == 'failure', 'old run not terminal failure')
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


def resolve_provenance(*, plan, selection_rows, wrappers, old_identity, current_identity):
    """Freeze complete ordered path-free native descriptors and authenticated metadata."""
    _identity_context(old_identity)
    _identity_context(current_identity, current=True)
    f.need(current_identity['old_identity_sha256'] == f.sha(f.json_bytes(old_identity)), 'old identity binding mismatch')
    f.need(old_identity['run_id'] == '38860226136' and old_identity['run_attempt'] == '1' and
           old_identity['pipeline_commit'] == 'f8c7028dd80232ac522b7cf223052921fca396fa', 'wrong fixed old origin')
    f.need(current_identity['run_id'] != old_identity['run_id'], 'successor is not a distinct run')
    cp.validate_identity_pair(old_identity,current_identity)
    stages = plan['stages']
    ids = [s['stage_id'] for s in stages]
    f.need(len(ids) == len(set(ids)) and len(ids) == plan['stage_count'], 'plan stage count/duplicates')
    f.need([r['stage_id'] for r in selection_rows] == ids and len(wrappers) == len(ids),
           'full plan provenance coverage/order mismatch')
    origin_by_stage = {choice['stage_id']: choice['origin'] for choice in selection_rows}
    for stage in stages:
        if origin_by_stage[stage['stage_id']] == 'OldOrigin':
            f.need(all(origin_by_stage.get(predecessor) == 'OldOrigin'
                       for predecessor in stage['required_predecessors']), 'old child of fresh ancestor')
    rows = []
    for stage, choice, wrapper in zip(stages, selection_rows, wrappers):
        origin = choice['origin']
        f.need(origin in ORIGINS and wrapper.get('origin') == origin, 'provenance origin mismatch')
        f.need(set(choice) == ({'stage_id', 'origin', 'pin'} if origin == 'OldOrigin' else {'stage_id', 'origin'}),
               'origin selection fields mismatch')
        identity = old_identity if origin == 'OldOrigin' else current_identity
        d = _validate_wrapper(wrapper, identity, stage['stage_id'])
        f.need(d['producer_job'] == stage['producer_job'], 'producer differs from original plan')
        if origin == 'OldOrigin':
            pin = choice['pin']
            artifact = wrapper['authenticated_metadata']['artifact']
            expected_pin = {key: d[key] for key in ('artifact_id', 'producer_job_id', 'artifact_zip_sha256',
                'archive_sha256', 'archive_bytes', 'receipt_sha256')}
            expected_pin.update(artifact_name=artifact['name'], artifact_zip_bytes=artifact['size_in_bytes'],
                raw_descriptor_sha256=wrapper['raw_descriptor_sha256'], expires_at=artifact['expires_at'],
                identity_sha256=f.sha(f.json_bytes(old_identity)))
            f.need(pin == expected_pin, 'frozen old artifact pin mismatch')
            for key in ('artifact_id', 'producer_job_id', 'artifact_zip_bytes', 'archive_bytes'):
                _positive(pin[key], 'old pin '+key)
        rows.append(deepcopy({key: value for key, value in wrapper.items() if key != 'archive_path'}))
    f.need(sum(row['native_descriptor']['archive_bytes'] for row in rows) <= 4*1024**3,
           'aggregate mixed-origin restored archive bound exceeded')
    return {'rows': rows, 'sha256': f.sha(f.json_bytes(rows))}


def final_context(*, manifest, provenance, object_hashes, current_identity):
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
        'selection_sha256': current_identity['selection_sha256']}


def final_verdict(*, plan, manifest, current_identity, old_identity, selection_rows,
                  resolved_provenance, checked, now, current_max_age_seconds=518400):
    """Return only a continuation result. A separate clean rebuild remains mandatory.

    checked maps every FINAL_ROLES entry to {'receipt': verified extracted receipt,
    'wrapper': OriginTransport wrapper}. Both restore jobs independently supply
    full provenance/object/source maps; every downstream check binds that context.
    """
    deadline = check_deadline(old_identity, current_identity, now=now,
                              current_max_age_seconds=current_max_age_seconds)
    f.need(type(checked) is dict and set(checked) == set(FINAL_ROLES), 'complete fresh final role set required')
    provenance = resolve_provenance(plan=plan, selection_rows=selection_rows,
        wrappers=resolved_provenance['rows'], old_identity=old_identity, current_identity=current_identity)
    f.need(provenance == resolved_provenance, 'resolved full provenance/hash mismatch')
    entries = f.manifest_index(manifest)
    modules = [m for stage in plan['stages'] for m in stage['modules']]
    f.need(len(modules) == len(set(modules)) and set(modules) == set(entries), 'full plan source coverage mismatch')
    context = final_context(manifest=manifest, provenance=provenance,
        object_hashes=checked['export_target']['receipt']['restored_object_hashes'], current_identity=current_identity)
    f.need(context['checked_sources'].get(DEFINING_SOURCE['module']) == DEFINING_SOURCE['sha256'],
           'defining source not in exact source manifest')
    export_hash = _digest(checked['export_target']['receipt'].get('export_sha256'), 'exact export hash')
    final_artifacts = {}
    for role in FINAL_ROLES:
        evidence = checked[role]
        f.need(type(evidence) is dict and set(evidence) == {'receipt', 'wrapper'}, 'final evidence fields mismatch')
        receipt = evidence['receipt']
        d = _validate_wrapper(evidence['wrapper'], current_identity, role, final=True)
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
    return {'schema': 'verified-continuation-hierarchy-c-verdict-v1', 'status': CONTINUATION_STATUS,
        'identity': deepcopy(current_identity), **context, 'exact_type': TYPE,
        'source_count': manifest['source_count'], 'export_sha256': export_hash,
        'checks': {role: 'passed' for role in FINAL_ROLES}, 'final_artifacts': final_artifacts,
        'origin_counts': counts, 'origins': {'OldOrigin': deepcopy(old_identity), 'CurrentOrigin': deepcopy(current_identity)},
        'acceptance_deadline': deadline, 'clean_source_rebuild': 'pending',
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
           clean_identity.get('run_id') not in {continuation['identity']['run_id'],
                                                continuation['origins']['OldOrigin']['run_id']},
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
