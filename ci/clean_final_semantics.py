"""Inactive finite clean final property adapter. No selector, transport or release authority.
Reviewed source-bound functions are copied verbatim (only collision names differ).
The original final validator remains unchanged and rejects these changed commands.
"""
from __future__ import annotations
import copy,hashlib,json,math,re,stat,time
from pathlib import Path
import fresh_stage as f
import four_context_final as legacy
import export_retry_specs as specs
import conron_recovery_resources as resources
class Rejected(f.Rejected):pass
def need(value,reason):
    if not value:raise Rejected(reason)
def digest(raw):return hashlib.sha256(raw).hexdigest()


SEMANTIC_SOURCE_REVIEW_SHA256 = 'a82f5f572d3b0365eba58afaad9bb659aeb549c4cb7903a94bad560b5e17b8c1'


SEMANTIC_SOURCES = {
    'src/lean/lake/Lake/CLI/Main.lean': {'bytes': 58018, 'sha256': '330d8ebde227bee7234892dabe2191fcd387c8d582559537baca1e207f9196d3'},
    'src/lean/lake/Lake/CLI/Check.lean': {'bytes': 30904, 'sha256': '55daf430e5adea38453b21798cbdf4cd099f66ec969494022a566a8ae098c00b'},
    'src/lean/lake/Lake/Check/Axioms.lean': {'bytes': 3359, 'sha256': '261fa54494a6a17c23b8588d788ab1080e5c39af2143948f8e140cfa295560d1'}}


EVIDENCE_CONTRACT = 'single_lake_kernel_and_used_axioms_v1'


STANDARD_AXIOMS = ('propext', 'Classical.choice', 'Quot.sound')


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


class SplitBudget:
    """Keep the original controller; reject setup past its fixed allocation.

    These checks do not renew the original deadline or interrupt arbitrary host
    I/O atomically. The existing host/controller watchdogs remain authoritative.
    """
    def __init__(self, shared, entry):
        self.shared=shared;self.entry=entry;self.setup_complete=False
    @property
    def deadline(self): return self.shared.deadline
    @property
    def last_wall(self): return self.shared.last_wall
    @property
    def in_child(self): return self.shared.in_child
    def check(self):
        self.shared.check()
        if not self.setup_complete:
            need(0<=time.monotonic()-self.entry<=1800,'SETUP_ALLOCATION_EXCEEDED')
    def remaining(self):
        self.check();return self.shared.remaining()
    def tighten_wall(self, deadline):
        self.shared.tighten_wall(deadline);self.check()
    def finish_setup(self):
        self.check();need(not self.setup_complete,'SETUP_ALREADY_CLOSED');self.setup_complete=True
    def process(self, call):
        need(self.setup_complete,'SETUP_NOT_CLOSED');self.check()
        try:return self.shared.process(call)
        finally:self.check()


def run_lake_command(*,role,root,paths,env,state,budget,entry_monotonic,base,f,dio,final,specs):
    """One original native process scope with a measured, fixed closeout reserve."""
    observed=[]
    def guarded_executor(*a,**kw):
        need(budget.in_child and not observed,'ONE_ORIGINAL_NATIVE_SCOPE')
        # Evaluate after all setup and immediately before safe_native dispatch.
        elapsed=time.monotonic()-entry_monotonic
        need(0<=elapsed<=specs.SETUP_SECONDS,'SETUP_ALLOCATION_EXCEEDED')
        remaining=budget.remaining()
        left=remaining-specs.CLOSEOUT_SECONDS
        need(left>0,'CLOSEOUT_RESERVE_EXHAUSTED')
        effective=min(kw['timeout'],left)
        need(type(effective) is int and effective>0,'POSITIVE_EFFECTIVE_TIMEOUT')
        kw['timeout']=effective
        record={'schema':'c092-lake-export-retry-budget-v1',
            'job_timeout_seconds':specs.JOB_SECONDS,'setup_allocation_seconds':specs.SETUP_SECONDS,
            'closeout_reserve_seconds':specs.CLOSEOUT_SECONDS,
            'setup_elapsed_seconds':elapsed,'dispatch_remaining_seconds':remaining,
            'effective_timeout_seconds':effective}
        observed.append(record);state['split_budget']=record
        result=base.safe_native(f,state,*a,**kw)
        # Frozen native code uses exactly three seconds; refuse any contradictory
        # result before run_final_command hashes/reads captures.
        if not (result.get('cleanup_bound_seconds')==3.0 and
                type(result.get('cleanup_elapsed_seconds')) in (int,float) and
                0<=result['cleanup_elapsed_seconds']<=3.0 and
                type(result.get('elapsed_seconds')) in (int,float) and
                0<=result['elapsed_seconds']<=effective+3.0):
            state.pop('safe_captures',None)
            raise RuntimeError('NATIVE_TIME_OR_CLEANUP_BOUND')
        return result
    spec=specs.checker_spec(role,paths,final)
    command,_=dio.run_final_command(spec=spec,root=root,environment=env,budget=budget,
        executor=guarded_executor,final=final)
    need(len(observed)==1,'ONE_NATIVE_DISPATCH')
    command['effective_timeout_seconds']=observed[0]['effective_timeout_seconds']
    final._successful_command(command,spec)
    return command,observed[0]


def validate_headroom(record):
    need(type(record) is dict and record.get('schema')=='conron-host-headroom-v1' and
         record.get('status')=='observed' and record.get('required_bytes')==8*1024**3 and
         type(record.get('minimum_available_bytes')) is int and
         record['minimum_available_bytes']>=8*1024**3 and
         record.get('exclusive_reservation') is False and
         record.get('sufficient_checker_memory_proved') is False and
         record.get('host_initial_cgroup_namespace_is_trusted_environment_assumption') is True,
         'HEADROOM_RECORD')
    need(type(record.get('samples')) is list and len(record['samples'])==2,
         'HEADROOM_SAMPLES')
    need(len(json.dumps(record,sort_keys=True,allow_nan=False).encode())<=128*1024,
         'HEADROOM_RECORD_BOUND')


def validate_conron_command(record, *, toolchain_root, export_path, resources, final):
    spec=resources.conron_spec(toolchain_root,export_path)
    final._successful_command(record,spec)
    need(record.get('cleanup_bound_seconds')==3.0 and
         type(record.get('cleanup_elapsed_seconds')) in (int,float) and
         math.isfinite(record['cleanup_elapsed_seconds']) and
         0<=record['cleanup_elapsed_seconds']<=3.0, 'UNCHANGED_CLEANUP_BOUND')
    for name in ('stdout','stderr'): final._file_info(record.get(name))
    need(sum(record[name]['bytes'] for name in ('stdout','stderr'))<=32*1024**2,
         'COMBINED_LOG_BOUND')


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


def run_conron_command(*,root,toolchain,exported,env,state,budget,resources,base,f,dio,final):
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


PROFILE = {'schema': 'clean-final-property-profile-v1', 'evidence_contract': 'clean_single_lake_and_conron_jobs1_v1', 'legacy_two_command_lean_receipt_emitted': False, 'standalone_native_lean_receipt_emitted': False, 'inner_native_receipt_emitted': False, 'roles': {'export_target': {'contract': 'unchanged_exact_target_export_and_audit'}, 'fresh_kernel': {'contract': 'unchanged_fresh_whole_closure'}, 'lean_export': {'contract': 'single_lake_kernel_and_used_axioms_v1', 'properties': ['builtin_lean_kernel_on_same_clean_export', 'standard_used_axioms_on_same_clean_export'], 'semantic_source_review_sha256': 'a82f5f572d3b0365eba58afaad9bb659aeb549c4cb7903a94bad560b5e17b8c1', 'spec_source_sha256': 'c46a5c309381ab60e73826c47c3a937d887d922f8288972ebd3f25367b7a36fc', 'job_seconds': 19800, 'setup_seconds': 1800, 'closeout_seconds': 300, 'command_seconds': 17700}, 'nanoda': {'contract': 'unchanged_nanoda_exact_export'}, 'conron': {'contract': 'conron_jobs1_rss6_as24_headroom8_v1', 'resource_source_sha256': 'b91ffe78701b6c16289b55a6f6afdf03a9ee932d1facc7ca5cb939c2d9dd8710', 'jobs': 1, 'rss_tree_bytes': 6442450944, 'address_space_bytes': 25769803776, 'required_headroom_bytes': 8589934592, 'command_seconds': 18000}}}
PROFILE_SHA256 = '35cb829b34d99a2925a4e12cceb276be335cda89af8d97640d650520e6eb7ae7'
INVENTORY_BYTES = 3292808
INVENTORY_SHA256 = '42bd268b1ca3e9bf89f4149ac427d6c0e76f735233b092a6df4ca27a2c2db7ea'



def final_command_specs(role,paths):
    original=legacy.final_command_specs(role,paths)
    if role=='lean_export':return [specs.checker_spec('lake_export_axioms',paths,legacy)]
    if role=='conron':return [resources.conron_spec(paths['toolchain_root'],paths['export_path'])]
    return original

def _info(value):
    raw=f.json_bytes(value);return {'bytes':len(raw),'sha256':f.sha(raw)}

def validate_final_commands(receipt):
    role=receipt.get('role');need(role in PROFILE['roles'],'EXACT_FINAL_ROLE')
    need(receipt.get('final_evidence_profile')==PROFILE and
         receipt.get('final_evidence_profile_sha256')==PROFILE_SHA256 and
         receipt.get('identity',{}).get('final_evidence_profile_sha256')==PROFILE_SHA256,
         'EXACT_CURRENT_FINAL_PROFILE')
    if role not in ('lean_export','conron'):
        legacy.validate_final_commands(receipt);return
    commands=receipt.get('commands');need(type(commands)is list and len(commands)==1,'ONE_EXACT_OUTER_COMMAND')
    command=commands[0];paths=receipt['execution_paths'];files=receipt.get('files')
    need(type(files)is dict,'EXACT_FINAL_FILES')
    for name,info in files.items():f.safe_rel(name);legacy._file_info(info)
    validate_retained_export(receipt)
    common={'EVIDENCE_PROFILE.json','inventory.json','ORIGINAL_EXPORT_RECEIPT.json'}
    need(files.get('EVIDENCE_PROFILE.json')==_info(PROFILE) and
         files.get('inventory.json')=={'bytes':INVENTORY_BYTES,'sha256':INVENTORY_SHA256} and
         receipt['identity'].get('toolchain_inventory_sha256')==INVENTORY_SHA256,'FINAL_PROFILE_INVENTORY_BYTES')
    need(receipt.get('evidence_contract')==PROFILE['roles'][role]['contract'],'EXACT_PROPERTY_CONTRACT')
    if role=='lean_export':
        validate_retry_command(command,role='lake_export_axioms',paths=paths,
            budget_record=receipt.get('lake_budget'),specs=specs,final=legacy)
        output=receipt.get('lake_output');need(type(output)is dict and type(output.get('stdout_utf8'))is str,'EXACT_LAKE_OUTPUT')
        expected=validate_success_output(output['stdout_utf8'].encode('utf-8'),b'',legacy)
        need(output==expected and f.json_bytes(output)==f.json_bytes(expected),'SOURCE_BOUND_LAKE_OUTPUT')
        need(command['stdout']==output['stdout'] and command['stderr']==output['stderr'],'COMPLETE_LAKE_CAPTURES')
        need(receipt.get('standalone_native_receipt_emitted') is False and
             receipt.get('inner_native_receipt_emitted') is False and
             receipt.get('legacy_pair_receipt_emitted') is False,'NO_FICTITIOUS_LEAN_RECEIPT')
        need(files.get('LAKE_BUDGET.json')==_info(receipt['lake_budget']) and
             files.get('LAKE_OUTPUT.json')==_info(output),'LAKE_RECORD_BYTE_BINDINGS')
        extra={'LAKE_BUDGET.json','LAKE_OUTPUT.json'}
    else:
        validate_conron_command(command,toolchain_root=paths['toolchain_root'],export_path=paths['export_path'],resources=resources,final=legacy)
        validate_headroom(receipt.get('headroom'))
        need(receipt.get('resource_source_sha256')==PROFILE['roles']['conron']['resource_source_sha256'] and
             files.get('HEADROOM.json')==_info(receipt['headroom']),'EXACT_CONRON_RESOURCE_RECORD')
        extra={'HEADROOM.json'}
    for stream in ('stdout','stderr'):
        name=command['name']+'.'+stream;need(files.get(name)==command[stream],'COMMAND_CAPTURE_BINDING');common.add(name)
    need(set(files)==common|extra,'EXACT_CURRENT_FINAL_MEMBERS')

def retain_records(root,inventory_path,role,values):
    retained=root/'retained-final';need(not retained.exists(),'NEW_FINAL_RECORD_ROOT');retained.mkdir()
    files={'inventory.json':inventory_path}
    for name,value in {'EVIDENCE_PROFILE.json':PROFILE,**values}.items():
        f.safe_rel(name);path=retained/name;path.write_bytes(f.json_bytes(value));files[name]=path
    return files


RETAINED_EXPORT_MEMBER='ORIGINAL_EXPORT_RECEIPT.json'

def validate_retained_export(receipt):
    """Supplemental retention only; actual export still requires native admission."""
    descriptor=receipt.get('retained_export_descriptor')
    need(type(descriptor)is dict and set(descriptor)=={
        'schema','role','identity','archive_sha256','archive_bytes','receipt_sha256',
        'retention_days','artifact_id','producer_job_id','producer_conclusion','artifact_zip_sha256'},
        'RETAINED_EXPORT_DESCRIPTOR_FIELDS')
    need(descriptor['schema']=='fresh-final-upload-v1' and descriptor['role']=='export_target' and
         descriptor['identity']==receipt.get('identity') and type(descriptor['retention_days'])is int and
         descriptor['retention_days']==7 and descriptor['producer_conclusion']=='success',
         'RETAINED_EXPORT_SAME_RUN_IDENTITY')
    for name in ('archive_sha256','receipt_sha256','artifact_zip_sha256'):legacy._digest(descriptor[name],'retained export '+name)
    for name in ('artifact_id','producer_job_id','archive_bytes'):legacy._positive(descriptor[name],'retained export '+name)
    need(descriptor['archive_bytes']<=legacy.FINAL_ARTIFACT_LIMIT,'RETAINED_EXPORT_ARCHIVE_BOUND')
    info=receipt.get('files',{}).get(RETAINED_EXPORT_MEMBER);legacy._file_info(info)
    need(0<info['bytes']<=descriptor['archive_bytes']<=legacy.FINAL_ARTIFACT_LIMIT and
         info['sha256']==descriptor['receipt_sha256'],'RETAINED_EXPORT_RECEIPT_BINDING')

def retain_export_receipt(expanded,descriptor,identity):
    """Return the exact already-admitted file for streaming by the native packer.

    No serialization, copy, read_bytes, acquisition or new per-receipt cap.
    """
    path=expanded/'receipt.json';f.no_symlink_path(path);info=path.lstat()
    need(stat.S_ISREG(info.st_mode) and info.st_nlink==1 and
         0<info.st_size<=legacy.FINAL_ARTIFACT_LIMIT,'RETAINED_EXPORT_RECEIPT_PATH_BOUND')
    value={'retained_export_descriptor':copy.deepcopy(descriptor),'identity':identity,
           'files':{RETAINED_EXPORT_MEMBER:{'bytes':info.st_size,'sha256':f.file_sha(path)}}}
    validate_retained_export(value)
    return {RETAINED_EXPORT_MEMBER:path}
