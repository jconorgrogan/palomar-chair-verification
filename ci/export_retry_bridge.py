"""Inactive Lake kernel/used-axiom semantic receipt and pure property join.

The caller authenticates remote producer/artifact metadata, validates complete
archive/member bytes, and obtains original_context through validate_export.
A supplied dictionary alone is not authentication or execution authority.
The join covers source-bound kernel/used-axiom properties; it is not a C verdict.
"""
from __future__ import annotations
import copy
import hashlib
import math
import re
import final_recovery_bridge as original_bridge

PROOF_IDENTITY_SHA256 = original_bridge.PROOF_IDENTITY_SHA256
ORIGINAL_CONTRACT_SHA256 = original_bridge.ORIGINAL_CONTRACT_SHA256
ORIGINAL_DEADLINE = original_bridge.ORIGINAL_DEADLINE
SPEC_SOURCE_SHA256 = 'c46a5c309381ab60e73826c47c3a937d887d922f8288972ebd3f25367b7a36fc'
WORKFLOW = {'head_branch': 'verify/hierarchy-c-export-check-recovery-20261018',
    'path': '.github/workflows/hierarchy-c-export-check-recovery.yml',
    'name': 'Verify hierarchy C export check recovery'}
ROLES = ('lake_export_axioms',)
EXECUTION_FIELDS = {'schema', 'role', 'run_id', 'run_attempt', 'run_started_at',
    'pipeline_commit', 'contract_sha256', 'proof_identity_sha256',
    'spec_source_sha256', 'workflow_id', 'workflow_source_sha256',
    'producer_job_id', 'producer_job_name'}
FAILURE_BINDING = {
    'failure_sha256': '1ff3cfff44b04ce15b53fa5fafcf0e275ea0b160df51315f59a8efdd6ead4138',
    'artifact_id': 12140768075, 'producer_job_id': 117678357698,
    'original_run_id': 39120636576, 'original_run_attempt': 1,
    'original_pipeline_commit': '1c74c8a1b664b7e704c625a598441846401d8834',
    'artifact_zip_sha256': '4f025ffd83eaf6bf8cf5730ce2523619ba311ed847b57131d6eb202e585e32c6'}

SEMANTIC_SOURCE_REVIEW_SHA256 = 'a82f5f572d3b0365eba58afaad9bb659aeb549c4cb7903a94bad560b5e17b8c1'
SEMANTIC_SOURCES = {
    'src/lean/lake/Lake/CLI/Main.lean': {'bytes': 58018, 'sha256': '330d8ebde227bee7234892dabe2191fcd387c8d582559537baca1e207f9196d3'},
    'src/lean/lake/Lake/CLI/Check.lean': {'bytes': 30904, 'sha256': '55daf430e5adea38453b21798cbdf4cd099f66ec969494022a566a8ae098c00b'},
    'src/lean/lake/Lake/Check/Axioms.lean': {'bytes': 3359, 'sha256': '261fa54494a6a17c23b8588d788ab1080e5c39af2143948f8e140cfa295560d1'}}
EVIDENCE_CONTRACT = 'single_lake_kernel_and_used_axioms_v1'
STANDARD_AXIOMS = ('propext', 'Classical.choice', 'Quot.sound')

class Rejected(RuntimeError): pass

def need(value, reason):
    if not value: raise Rejected(reason)

def digest(raw): return hashlib.sha256(raw).hexdigest()
def proof_identity(raw): return original_bridge.proof_identity(raw)
def validate_export(**kwargs): return original_bridge.validate_export(**kwargs)

def _digest(value):
    need(type(value) is str and re.fullmatch('[0-9a-f]{64}', value), 'DIGEST')

def _positive(value): need(type(value) is int and value > 0, 'POSITIVE_INTEGER')

def validate_execution(identity, proof, workflow, *, role):
    need(role in ROLES and type(identity) is dict and set(identity) == EXECUTION_FIELDS,
         'EXECUTION_FIELDS')
    need(identity['schema'] == 'c092-lake-export-retry-execution-identity-v1' and
         identity['role'] == role and identity['producer_job_name'] == role and
         identity['run_id'] != proof['run_id'] and
         identity['pipeline_commit'] != proof['pipeline_commit'] and
         identity['run_attempt'] == '1', 'NEW_DISTINCT_CHECKER_EXECUTION')
    need(type(identity['run_id']) is str and re.fullmatch('[1-9][0-9]*', identity['run_id']) and
         type(identity['pipeline_commit']) is str and
         re.fullmatch('[0-9a-f]{40}', identity['pipeline_commit']), 'EXECUTION_IDENTITY')
    for name in ('contract_sha256', 'workflow_source_sha256'): _digest(identity[name])
    need(identity['proof_identity_sha256'] == PROOF_IDENTITY_SHA256 and
         identity['spec_source_sha256'] == SPEC_SOURCE_SHA256, 'EXECUTION_PINS')
    _positive(identity['workflow_id']); _positive(identity['producer_job_id'])
    need(type(workflow) is dict and set(workflow) == set(WORKFLOW) | {'workflow_id', 'source_sha256'} and
         all(workflow.get(k) == v for k, v in WORKFLOW.items()) and
         workflow.get('workflow_id') == identity['workflow_id'] and
         workflow.get('source_sha256') == identity['workflow_source_sha256'], 'EXECUTION_WORKFLOW')
    from datetime import datetime, timezone
    need(type(identity['run_started_at']) is str, 'EXECUTION_TIME')
    started = datetime.strptime(identity['run_started_at'], '%Y-%m-%dT%H:%M:%SZ').replace(tzinfo=timezone.utc)
    need(proof['run_started_at'] < identity['run_started_at'] < ORIGINAL_DEADLINE,
         'ORIGINAL_DEADLINE')
    return copy.deepcopy(identity)

def validate_budget(record, command, specs):
    keys = {'schema', 'job_timeout_seconds', 'setup_allocation_seconds', 'closeout_reserve_seconds',
            'setup_elapsed_seconds', 'dispatch_remaining_seconds', 'effective_timeout_seconds'}
    need(type(record) is dict and set(record) == keys and
         record['schema'] == 'c092-lake-export-retry-budget-v1', 'BUDGET_FIELDS')
    for name, expected in (('job_timeout_seconds', specs.JOB_SECONDS),
                           ('setup_allocation_seconds', specs.SETUP_SECONDS),
                           ('closeout_reserve_seconds', specs.CLOSEOUT_SECONDS)):
        need(type(record[name]) is int and record[name] == expected, 'FIXED_BUDGET')
    elapsed = record['setup_elapsed_seconds']
    need(type(elapsed) in (int, float) and math.isfinite(elapsed) and
         0 <= elapsed <= specs.SETUP_SECONDS, 'SETUP_ALLOCATION')
    left = record['dispatch_remaining_seconds']
    need(type(left) is int and specs.CLOSEOUT_SECONDS < left <= specs.JOB_SECONDS,
         'DISPATCH_REMAINING')
    effective = record['effective_timeout_seconds']
    need(type(effective) is int and effective == min(command['timeout_seconds'], left - specs.CLOSEOUT_SECONDS)
         and command.get('effective_timeout_seconds') == effective, 'ACTUAL_EFFECTIVE_TIMEOUT')

def validate_retry_command(record, *, role, paths, budget_record, specs, final):
    spec = specs.checker_spec(role, paths, final)
    final._successful_command(record, spec)
    need(record.get('cleanup_bound_seconds') == 3.0 and
         type(record.get('cleanup_elapsed_seconds')) in (int, float) and
         math.isfinite(record['cleanup_elapsed_seconds']) and
         0 <= record['cleanup_elapsed_seconds'] <= 3.0, 'UNCHANGED_CLEANUP_BOUND')
    for name in ('stdout', 'stderr'): final._file_info(record.get(name))
    need(sum(record[name]['bytes'] for name in ('stdout', 'stderr')) <= 32 * 1024**2,
         'COMBINED_LOG_BOUND')
    validate_budget(budget_record, record, specs)
    need(record['elapsed_seconds'] <= record['effective_timeout_seconds'] + 3.0,
         'NATIVE_TIME_WITHIN_EFFECTIVE_CAP_AND_CLEANUP')

def validate_semantic_inventory(inventory):
    need(type(inventory) is dict and type(inventory.get('files')) is dict, 'SEMANTIC_INVENTORY')
    for name, expected in SEMANTIC_SOURCES.items():
        row = inventory['files'].get(name)
        need(type(row) is dict and all(type(row.get(k)) is type(v) and row[k] == v
             for k, v in expected.items()), 'EXACT_SEMANTIC_SOURCE_INVENTORY')

def validate_success_output(stdout, stderr, final):
    """Require all outer captures and exactly the source-defined success grammar.

    Export order determines the unique standard-axiom order; no lexical ordering
    or requirement that all standard axioms are used is invented here.
    """
    need(type(stdout) is bytes and type(stderr) is bytes and
         len(stdout) + len(stderr) <= 32 * 1024**2, 'COMPLETE_BOUNDED_CAPTURES')
    need(stderr == b'', 'UNEXPECTED_LAKE_STDERR')
    try: text = stdout.decode('utf-8', 'strict')
    except UnicodeDecodeError: raise Rejected('LAKE_STDOUT_UTF8') from None
    lines = text.split('\n')
    need(len(lines) == 4 and lines[-1] == '' and
         lines[0] == 'Running Lean default kernel on solution' and
         lines[1] == 'Lean default kernel accepts the solution', 'EXACT_KERNEL_SUCCESS_OUTPUT')
    if lines[2] == 'Uses no axioms': used = []
    else:
        prefix = 'Uses axioms: '
        need(lines[2].startswith(prefix), 'STANDARD_AXIOM_OUTPUT')
        used = lines[2][len(prefix):].split(', ')
        need(bool(used) and len(used) == len(set(used)) and
             all(x in STANDARD_AXIOMS for x in used) and
             lines[2] == prefix + ', '.join(used), 'CANONICAL_UNIQUE_STANDARD_AXIOMS')
    return {'schema': 'c092-lake-kernel-used-axioms-output-v1',
        'evidence_contract': EVIDENCE_CONTRACT,
        'semantic_source_review_sha256': SEMANTIC_SOURCE_REVIEW_SHA256,
        'runtime_source_bindings': copy.deepcopy(SEMANTIC_SOURCES),
        'kernel_success_observed': True, 'used_axioms': used,
        'stdout_utf8': text,
        'stdout': {'bytes': len(stdout), 'sha256': digest(stdout)},
        'stderr': {'bytes': len(stderr), 'sha256': digest(stderr)},
        'inner_native_receipt_present': False}


def retry_receipt(*, proof_raw, execution, workflow, original_context, command,
                  budget_record, output_evidence, files, paths, failure_binding, specs, final):
    proof = proof_identity(proof_raw); role = execution.get('role')
    validate_execution(execution, proof, workflow, role=role)
    validate_retry_command(command, role=role, paths=paths, budget_record=budget_record,
                           specs=specs, final=final)
    need(type(output_evidence) is dict and type(output_evidence.get('stdout_utf8')) is str, 'OUTPUT_EVIDENCE')
    expected_output = validate_success_output(output_evidence['stdout_utf8'].encode('utf-8'), b'', final)
    need(output_evidence == expected_output and final.f.json_bytes(output_evidence) == final.f.json_bytes(expected_output),
         'SOURCE_BOUND_OUTPUT_EVIDENCE')
    need(command['stdout'] == output_evidence['stdout'] and command['stderr'] == output_evidence['stderr'],
         'COMPLETE_OUTPUT_HASH_BINDING')
    need(type(failure_binding) is dict and set(failure_binding) == set(FAILURE_BINDING) and
         all(type(failure_binding[k]) is type(v) and failure_binding[k] == v
             for k, v in FAILURE_BINDING.items()), 'EXACT_ORIGINAL_LEAN_FAILURE')
    need(type(original_context) is dict and original_context.get('acceptance_deadline') and
         final._timestamp(original_context['acceptance_deadline']) <= final._timestamp(ORIGINAL_DEADLINE),
         'ORIGINAL_CONTEXT_DEADLINE')
    _digest(original_context.get('export_sha256'))
    wrapper = original_context.get('original_export')
    need(type(wrapper) is dict and wrapper.get('native_descriptor', {}).get('role') == 'export_target' and
         wrapper['native_descriptor'].get('identity') == proof, 'ORIGINAL_EXPORT_IDENTITY')
    expected = {role + '.stdout', role + '.stderr', 'ORIGINAL_PROOF_IDENTITY.json',
        'ORIGINAL_EXPORT_RECEIPT.json', 'ORIGINAL_EXPORT_WRAPPER.json', 'EXECUTION_IDENTITY.json',
        'PRIOR_FAILURE.json', 'BUDGET.json', 'OUTPUT_EVIDENCE.json', 'inventory.json'}
    need(type(files) is dict and set(files) == expected, 'EXACT_SPLIT_MEMBERS')
    for value in files.values(): final._file_info(value)
    need(files[role + '.stdout'] == command['stdout'] and files[role + '.stderr'] == command['stderr'],
         'NATIVE_LOG_BINDING')
    need(files['ORIGINAL_PROOF_IDENTITY.json'] == {'bytes': 1574, 'sha256': PROOF_IDENTITY_SHA256},
         'ORIGINAL_PROOF_BYTES')
    for name, value in (('EXECUTION_IDENTITY.json', execution), ('PRIOR_FAILURE.json', failure_binding),
                        ('ORIGINAL_EXPORT_WRAPPER.json', wrapper), ('BUDGET.json', budget_record),
                        ('OUTPUT_EVIDENCE.json', output_evidence)):
        raw = final.f.json_bytes(value)
        need(files[name] == {'bytes': len(raw), 'sha256': digest(raw)}, 'RECORD_FILE_BINDING')
    need(files['ORIGINAL_EXPORT_RECEIPT.json']['sha256'] == wrapper['native_descriptor']['receipt_sha256'],
         'RETAINED_NATIVE_EXPORT_RECEIPT')
    need(files['inventory.json'] == {'bytes': 3292808, 'sha256': proof['toolchain_inventory_sha256']},
         'EXACT_RUNTIME_INVENTORY')
    return {'schema': 'c092-lake-export-retry-evidence-v1', 'role': role,
        'status': 'completed_check_only', 'proof_pass_claimed': False,
        'overall_task_complete': False, 'aggregate_verdict': 'not_implemented',
        'proof_identity': proof, 'execution_identity': copy.deepcopy(execution),
        'evidence_contract': EVIDENCE_CONTRACT,
        'semantic_source_review_sha256': SEMANTIC_SOURCE_REVIEW_SHA256,
        'output_evidence': copy.deepcopy(output_evidence),
        'old_standalone_lean_result': 'failed_timeout',
        'standalone_native_receipt_emitted': False, 'inner_native_receipt_emitted': False,
        'execution_workflow': copy.deepcopy(workflow), 'spec_source_sha256': SPEC_SOURCE_SHA256,
        'original_deadline': ORIGINAL_DEADLINE, 'commands': [copy.deepcopy(command)],
        'execution_paths': copy.deepcopy(paths), 'files': copy.deepcopy(files),
        'budget': copy.deepcopy(budget_record), 'prior_failure': copy.deepcopy(failure_binding),
        'proof_context': copy.deepcopy(original_context)}

def validate_receipt(receipt, *, proof_raw, original_context, specs, final):
    need(type(receipt) is dict and receipt.get('schema') == 'c092-lake-export-retry-evidence-v1' and
         receipt.get('role') in ROLES and type(receipt.get('commands')) is list and
         len(receipt['commands']) == 1, 'SPLIT_RECEIPT_ONLY')
    need(receipt.get('proof_context') == original_context, 'AUTHENTICATED_ORIGINAL_CONTEXT')
    expected = retry_receipt(proof_raw=proof_raw, execution=receipt['execution_identity'],
        workflow=receipt['execution_workflow'], original_context=original_context,
        command=receipt['commands'][0], budget_record=receipt['budget'], output_evidence=receipt['output_evidence'], files=receipt['files'],
        paths=receipt['execution_paths'], failure_binding=receipt['prior_failure'], specs=specs, final=final)
    need(receipt == expected and final.f.json_bytes(receipt) == final.f.json_bytes(expected),
         'EXACT_SPLIT_RECEIPT')
    return expected

AUTHENTICATION_FIELDS = {'schema', 'role', 'execution_identity', 'execution_workflow',
    'producer_conclusion', 'artifact_id', 'artifact_zip_sha256', 'archive_sha256', 'receipt_sha256'}

def property_join(*, receipt, authentication, proof_raw, original_context, specs, final):
    """Pure Lake-only property coverage after reviewed output authentication.

    The caller binds complete native artifact/member bytes and authenticated
    successful producer/upload identities before supplying this summary.
    A structurally valid dictionary alone does not authenticate anything.
    """
    accepted = validate_receipt(receipt, proof_raw=proof_raw, original_context=original_context,
                                specs=specs, final=final)
    auth = authentication
    need(type(auth) is dict and set(auth) == AUTHENTICATION_FIELDS and
         auth['schema'] == 'c092-lake-export-retry-authentication-v1' and
         auth['role'] == 'lake_export_axioms' and auth['producer_conclusion'] == 'success' and
         auth['execution_identity'] == accepted['execution_identity'] and
         auth['execution_workflow'] == accepted['execution_workflow'], 'AUTHENTICATED_EXECUTION_BINDING')
    for name in ('artifact_zip_sha256', 'archive_sha256', 'receipt_sha256'): _digest(auth[name])
    need(auth['receipt_sha256'] == digest(final.f.json_bytes(accepted)), 'AUTHENTICATED_RECEIPT_BYTES')
    _positive(auth['artifact_id'])
    return {'schema': 'c092-lake-kernel-used-axioms-coverage-v1',
        'status': 'source_bound_kernel_and_used_axioms_completed_only',
        'evidence_contract': EVIDENCE_CONTRACT,
        'semantic_source_review_sha256': SEMANTIC_SOURCE_REVIEW_SHA256,
        'properties': ['builtin_lean_kernel_on_original_export', 'standard_used_axioms_on_original_export'],
        'proof_identity_sha256': PROOF_IDENTITY_SHA256,
        'export_sha256': original_context['export_sha256'],
        'original_export_wrapper_sha256': digest(final.f.json_bytes(original_context['original_export'])),
        'original_context_sha256': digest(final.f.json_bytes(original_context)),
        'original_deadline': ORIGINAL_DEADLINE, 'outer_lake_check': copy.deepcopy(auth),
        'used_axioms': copy.deepcopy(accepted['output_evidence']['used_axioms']),
        'old_standalone_lean_result': 'failed_timeout',
        'standalone_native_receipt_emitted': False, 'inner_native_receipt_emitted': False,
        'legacy_receipt_emitted': False, 'proof_pass_claimed': False,
        'overall_task_complete': False, 'aggregate_verdict': 'not_implemented'}
