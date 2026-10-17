"""Inactive modern route A: one frozen origin, exact leaf repair, one successor.

No network, process launch, source compilation or receipt mutation is performed here.
All inherited limits, profile/plan bytes and runtime identity remain fixed.
"""
from __future__ import annotations
from dataclasses import dataclass
from datetime import datetime, timezone, timedelta
from pathlib import Path
import copy
import fresh_stage as f

REPOSITORY = 'jconorgrogan/palomar-chair-verification'
REPOSITORY_ID = 1407290933
OLD_RUN = 38860226136
OLD_ATTEMPT = 1
OLD_PIPELINE = 'f8c7028dd80232ac522b7cf223052921fca396fa'
SOURCE = '4a0cbd71ba9cd318620e11694037d956d2393d06'
MANIFEST = '401320e96ea5a511678892c359af43131fae75494a55d8ea1df0e1dc606a326f'
OLD_CONTRACT = 'a0ad861b7f8b9eb857d8a44ce811dcae7149ffc1f81bd9cdd7a788536ce15555'
PLAN = 'c25336bffaf3ada115c7642840675f445cc3cef145fa1d70e9eec8988567a7ed'
OLD_PROFILES = '0af17b85b2b469be445bdcb68acbc07bb38507382fc818ffc4bd2bac5e3ce1ee'
OLD_RUNNER = 'a8cbd69f9904b6f2645177de722f3466cb762045a7cd8c3e6230f1ceaa9c9c1d'
INVENTORY = '42bd268b1ca3e9bf89f4149ac427d6c0e76f735233b092a6df4ca27a2c2db7ea'
CURRENT_RUNNER = '9085c9eea092c270fbd6952834839103c66519a7b4716fe09147001c7d96355d'
NEW_MANIFEST = '09b0371c9acc07b07355824e7a7302a810c4247bbbce20d1e497bd4a02a23392'
SOURCE_DELTA = '12541d2a57fac6c4e6a2e36e849d1bf400d284f968d77c2d43580d40aa7696ef'
REPAIRED_MODULE = 'SpectreFinite.RadiusFivePrivateFamilyExport'
REPAIRED_PATH = 'SpectreFinite/RadiusFivePrivateFamilyExport.lean'
REPAIRED_DEPENDENCY = 'SpectreFinite.RadiusFiveFamilyData'
REBUILD_STAGE = 'build_054'
SOURCE_COUNT = 6369
STAGE_COUNT = 93
OLD_SOURCE_SHA256 = 'f94f3e7685129d131944d064b99a2de41342b102d1332f12328e89204b5065af'
NEW_SOURCE_SHA256 = 'fae623a710e5888f41a37adcb5016e640e39688cfb199186895369afefce05a5'
INSERTION = b'meta import SpectreFinite.RadiusFiveFamilyData\n'
INSERTION_OFFSET = 57
NEW_STATUS = 'source_only_header_repair_pending_real_compile_and_full_verification'
REPAIR_DESCRIPTION = 'Add a plain meta import alongside the unchanged public runtime import; preserve the #eval body and all 93 stages.'
NEW_ARCHIVE_SHA256 = '0275377e3a3dfb2bc757606334326b327569d8c164c234bb42d5ea9242f51446'
NEW_ARCHIVE_BYTES = 4684110
CONTRACT_CHANGED_FIELDS = {'source_commit', 'source_manifest_sha256', 'runner_sha256',
    'implementation_sha256', 'review_status', 'note'}
CONTRACT_NEW_FIELDS = {'evidence_mode', 'continuation_review_status', 'selection_sha256',
    'old_identity_sha256', 'source_delta_sha256', 'current_workflow',
    'storage_adapter_review_status', 'readonly_commit_review_status', 'receipt_protocol'}
IMPLEMENTATION_KEYS = {
    'fresh_stage.py', 'ci_transport.py', 'ci_failure.py', 'toolchain_install.py', 'FinalExportAudit.lean',
    'continuation_policy.py', 'continuation_runner.py', 'continuation_final.py', 'continuation_driver.py',
    'continuation_workflow.py', 'origin_transport.py', 'source_delta.json',
    'original/fresh_stage.py', 'original/ci_driver.py', 'original/ci_transport.py', 'original/ci_failure.py',
    'original/toolchain_install.py', 'original/FinalExportAudit.lean', 'original/contract.json',
    'original/profiles.json', 'original/plan.json', 'original/SOURCE_MANIFEST.json'}
MAX_AGE = 518400
MAX_ARTIFACT = 1024**3
MAX_RESTORED = 4*1024**3
IDENTITY_KEYS = {'pipeline_commit','source_commit','source_manifest_sha256','plan_sha256','profiles_sha256',
    'contract_sha256','runner_sha256','lean_archive_sha256','toolchain_inventory_sha256','run_started_at','run_id','run_attempt'}
PIN_KEYS = {'artifact_id','producer_job_id','artifact_name','artifact_zip_sha256','artifact_zip_bytes',
    'archive_sha256','archive_bytes','receipt_sha256','raw_descriptor_sha256','expires_at','identity_sha256'}
NATIVE_KEYS = {'schema','stage_id','producer_job','identity','archive_sha256','receipt_sha256','archive_bytes',
    'artifact_id','producer_job_id','producer_conclusion','retention_days','artifact_zip_sha256'}


def keys(value, expected, label):
    f.need(type(value) is dict and set(value)==set(expected), 'unknown/missing '+label+' fields')


def integer(value, label, maximum=2**63-1):
    f.need(type(value) is int and 0 < value <= maximum, 'invalid '+label)


def digest(value, label):
    f.need(type(value) is str and f.SHA256.fullmatch(value), 'invalid '+label)


def timestamp(value):
    f.need(type(value) is str, 'invalid timestamp type')
    try: result=datetime.fromisoformat(value.replace('Z','+00:00'))
    except ValueError as e: raise f.Rejected('invalid timestamp') from e
    f.need(result.tzinfo is not None, 'timestamp timezone missing')
    return result.astimezone(timezone.utc)


def identity_hash(identity): return f.sha(f.json_bytes(identity))


def validate_old_identity(identity):
    keys(identity, IDENTITY_KEYS, 'original identity')
    expected={'pipeline_commit':OLD_PIPELINE,'source_commit':SOURCE,'source_manifest_sha256':MANIFEST,
        'plan_sha256':PLAN,'profiles_sha256':OLD_PROFILES,'contract_sha256':OLD_CONTRACT,
        'runner_sha256':OLD_RUNNER,'lean_archive_sha256':f.TOOLCHAIN_SHA256,
        'toolchain_inventory_sha256':INVENTORY,'run_id':str(OLD_RUN),'run_attempt':'1'}
    f.need(all(identity[k]==v for k,v in expected.items()), 'not the fixed original identity')
    timestamp(identity['run_started_at'])


def validate_identity_pair(old_identity, current_identity):
    """Shared transport/final identity seam; full contexts remain mandatory."""
    validate_old_identity(old_identity)
    keys(current_identity, IDENTITY_KEYS | {'evidence_mode', 'selection_sha256', 'old_identity_sha256'},
         'successor identity')
    ci = current_identity
    fixed = {'source_manifest_sha256': NEW_MANIFEST, 'plan_sha256': PLAN, 'profiles_sha256': OLD_PROFILES,
             'runner_sha256': CURRENT_RUNNER, 'lean_archive_sha256': f.TOOLCHAIN_SHA256,
             'toolchain_inventory_sha256': INVENTORY, 'run_attempt': '1',
             'evidence_mode': 'verified_continuation', 'old_identity_sha256': identity_hash(old_identity)}
    f.need(all(ci[k] == value for k, value in fixed.items()), 'successor identity fixed facts changed')
    f.need(type(ci['source_commit']) is str and f.COMMIT.fullmatch(ci['source_commit']) and
           ci['source_commit'] != SOURCE, 'distinct immutable successor source commit required')
    f.need(type(ci['pipeline_commit']) is str and f.COMMIT.fullmatch(ci['pipeline_commit']) and
           ci['pipeline_commit'] != OLD_PIPELINE, 'distinct immutable successor pipeline required')
    run_id = ci['run_id']
    f.need(type(run_id) is str and run_id.isascii() and run_id.isdecimal() and
           str(int(run_id)) == run_id and int(run_id) > 0 and run_id != str(OLD_RUN),
           'distinct canonical successor run required')
    for field in ('contract_sha256', 'selection_sha256'):
        digest(ci[field], field)
    f.need(timestamp(old_identity['run_started_at']) <= timestamp(ci['run_started_at']),
           'successor precedes original run')


def validate_pin(pin, stage_id, old_identity_sha256):
    keys(pin, PIN_KEYS, 'old stage pin')
    for k in ('artifact_id','producer_job_id'): integer(pin[k], k)
    integer(pin['artifact_zip_bytes'],'ZIP bytes',MAX_ARTIFACT+1024**2)
    integer(pin['archive_bytes'],'archive bytes',MAX_ARTIFACT)
    for k in ('artifact_zip_sha256','archive_sha256','receipt_sha256','raw_descriptor_sha256','identity_sha256'): digest(pin[k],k)
    f.need(pin['identity_sha256']==old_identity_sha256,'old pin identity mismatch')
    f.need(pin['artifact_name']==f'hierarchy-c-{OLD_RUN}-1-{stage_id}','old artifact name mismatch')
    timestamp(pin['expires_at'])


@dataclass(frozen=True)
class OldOrigin:
    stage_id: str
    # Canonical bytes make origin choices immutable, even to caller dictionary changes.
    pin_bytes: bytes
    @property
    def pin(self): return f.parse_json(self.pin_bytes)


@dataclass(frozen=True)
class CurrentOrigin:
    stage_id: str


@dataclass(frozen=True)
class Selection:
    raw_sha256: str
    old_context_bytes: bytes
    rows: tuple[OldOrigin|CurrentOrigin,...]
    @property
    def old_context(self): return f.parse_json(self.old_context_bytes)
    def row(self, sid):
        found=[r for r in self.rows if r.stage_id==sid]
        f.need(len(found)==1,'unselected stage');return found[0]
    def json_rows(self):
        return [dict(stage_id=r.stage_id,origin=type(r).__name__,**({'pin':r.pin} if isinstance(r,OldOrigin) else {})) for r in self.rows]


def parse_selection(data: bytes, expected_sha256: str, plan: dict) -> Selection:
    validate_plan(plan)
    digest(expected_sha256,'selection hash')
    f.need(f.sha(data)==expected_sha256,'selection bytes changed')
    obj=f.parse_json(data);keys(obj,{'schema','old_origin','stages'},'selection')
    f.need(obj['schema']=='verified-continuation-selection-v1','selection schema mismatch')
    old=obj['old_origin']
    keys(old,{'repository','repository_id','run_id','run_attempt','pipeline_commit','identity','identity_sha256','prepare','workflow'},'old origin')
    for k in ('repository_id','run_id','run_attempt'): integer(old[k],k)
    f.need((old['repository'],old['repository_id'],old['run_id'],old['run_attempt'],old['pipeline_commit'])==
        (REPOSITORY,REPOSITORY_ID,OLD_RUN,OLD_ATTEMPT,OLD_PIPELINE),'second/aliased old origin forbidden')
    validate_old_identity(old['identity']);digest(old['identity_sha256'],'old identity hash')
    f.need(old['identity_sha256']==identity_hash(old['identity']),'old identity hash mismatch')
    f.need(type(old['prepare']) is dict and old['prepare'] and type(old['workflow']) is dict and old['workflow'],
        'authenticated prepare/workflow pins are required')
    f.need(type(obj['stages']) is list and len(obj['stages'])==len(plan['stages']),'selection must cover every plan stage')
    rows=[];old_set=set()
    for stage, row in zip(plan['stages'],obj['stages']):
        f.need(type(row) is dict and row.get('stage_id')==stage['stage_id'],'missing/duplicate/unordered selection row')
        origin=row.get('origin')
        if origin=='OldOrigin':
            f.need(row['stage_id'] != REBUILD_STAGE, 'repaired diagnostic stage must be CurrentOrigin')
            keys(row,{'stage_id','origin','pin'},'old row');validate_pin(row['pin'],row['stage_id'],old['identity_sha256'])
            f.need(set(stage['required_predecessors'])<=old_set,'old child has a rebuilt/non-old ancestor')
            old_set.add(row['stage_id']);rows.append(OldOrigin(row['stage_id'],f.json_bytes(row['pin'])))
        else:
            keys(row,{'stage_id','origin'},'current row');f.need(origin=='CurrentOrigin','unknown origin alias')
            rows.append(CurrentOrigin(row['stage_id']))
    f.need(old_set and len(old_set)<len(rows),'continuation requires both old and fresh stages')
    return Selection(expected_sha256,f.json_bytes(old),tuple(rows))


def validate_plan(plan):
    f.need(type(plan) is dict and f.sha(f.json_bytes(plan)) == PLAN, 'original plan bytes changed')
    f.need(type(plan.get('stages')) is list and len(plan['stages']) == STAGE_COUNT,
           'all original stages must remain')
    repaired = [stage for stage in plan['stages'] if stage['stage_id'] == REBUILD_STAGE]
    f.need(len(repaired) == 1 and repaired[0]['modules'] == [REPAIRED_MODULE],
           'diagnostic rebuild stage ownership changed')


def validate_profiles(old, current):
    """Every profile, module assignment and resource limit is unchanged."""
    f.need(f.sha(f.json_bytes(old)) == OLD_PROFILES and current == old,
           'profile bytes or module assignments changed')


def source_content_hash(files):
    """The original manifest's exact canonical source-tree hash encoding."""
    return f.sha(b''.join(row['path'].encode('utf-8') + b'\0' + bytes.fromhex(row['sha256']) +
                         row['bytes'].to_bytes(8, 'big') for row in sorted(files, key=lambda x: x['path'])))


def validate_source_reconciliation(old, current, delta, plan):
    """Pinned whole manifests plus exact constructive leaf-only reconciliation.

    This validates identities and source bytes stated in the frozen delta. The
    caller must still run verify_sources against the actual current source tree.
    No general source, import or metadata exception is accepted.
    """
    validate_plan(plan)
    for value, pin, label in ((old, MANIFEST, 'old manifest'), (current, NEW_MANIFEST, 'new manifest'),
                              (delta, SOURCE_DELTA, 'source delta')):
        f.need(type(value) is dict and f.sha(f.json_bytes(value)) == pin, 'unpinned ' + label)
    expected_delta_keys = {'schema', 'module', 'stage_id', 'old_manifest_sha256', 'new_manifest_sha256',
        'old_source_sha256', 'new_source_sha256', 'old_bytes', 'new_bytes', 'old_source_utf8',
        'new_source_utf8', 'inserted_utf8', 'insertion_offset', 'source_count', 'stage_count',
        'all_other_source_records_unchanged', 'research_declaration_bodies_unchanged',
        'affected_module_has_no_owned_importers', 'actual_real_diagnostic_compiled'}
    keys(delta, expected_delta_keys, 'source delta')
    fixed = {'schema': 'one-diagnostic-meta-import-delta-v1', 'module': REPAIRED_MODULE,
        'stage_id': REBUILD_STAGE, 'old_manifest_sha256': MANIFEST, 'new_manifest_sha256': NEW_MANIFEST,
        'old_source_sha256': OLD_SOURCE_SHA256, 'new_source_sha256': NEW_SOURCE_SHA256,
        'inserted_utf8': INSERTION.decode('utf-8'), 'insertion_offset': INSERTION_OFFSET,
        'source_count': SOURCE_COUNT, 'stage_count': STAGE_COUNT,
        'all_other_source_records_unchanged': True, 'research_declaration_bodies_unchanged': True,
        'affected_module_has_no_owned_importers': True, 'actual_real_diagnostic_compiled': False}
    f.need(all(type(delta[k]) is type(v) and delta[k] == v for k, v in fixed.items()),
           'source delta statement changed')
    f.need(type(delta['old_source_utf8']) is str and type(delta['new_source_utf8']) is str,
           'source delta bytes must be UTF-8 text')
    old_bytes = delta['old_source_utf8'].encode('utf-8')
    new_bytes = delta['new_source_utf8'].encode('utf-8')
    f.need(type(delta['old_bytes']) is int and type(delta['new_bytes']) is int and
           len(old_bytes) == delta['old_bytes'] and len(new_bytes) == delta['new_bytes'] and
           f.sha(old_bytes) == OLD_SOURCE_SHA256 and f.sha(new_bytes) == NEW_SOURCE_SHA256,
           'source delta body/hash/length mismatch')
    f.need(new_bytes == old_bytes[:INSERTION_OFFSET] + INSERTION + old_bytes[INSERTION_OFFSET:],
           'source change is not the exact plain-meta insertion')
    f.need(old_bytes[:INSERTION_OFFSET] == b'module\n\npublic import ' +
           REPAIRED_DEPENDENCY.encode('utf-8') + b'\n', 'insertion moved outside exact header')
    f.need(len(old['files']) == len(current['files']) == SOURCE_COUNT and
           old['source_count'] == current['source_count'] == SOURCE_COUNT, 'source closure count changed')
    f.need(len({row['module'] for row in old['files']}) == SOURCE_COUNT and
           len({row['path'] for row in old['files']}) == SOURCE_COUNT, 'duplicate source record')
    affected = [i for i, row in enumerate(old['files']) if row['module'] == REPAIRED_MODULE]
    f.need(len(affected) == 1, 'missing or duplicate diagnostic module')
    idx = affected[0]
    expected_old = {'module': REPAIRED_MODULE, 'path': REPAIRED_PATH, 'bytes': len(old_bytes),
                    'sha256': OLD_SOURCE_SHA256, 'implicit_Init': True,
                    'ordered_imports': [REPAIRED_DEPENDENCY]}
    f.need(old['files'][idx] == expected_old, 'original diagnostic source record differs')
    expected = copy.deepcopy(old)
    expected['files'][idx] = dict(expected_old, bytes=len(new_bytes), sha256=NEW_SOURCE_SHA256,
                                 ordered_imports=[REPAIRED_DEPENDENCY, REPAIRED_DEPENDENCY])
    f.need(all(REPAIRED_MODULE not in row['ordered_imports'] for row in old['files']),
           'diagnostic has an owned importer; leaf-only reuse no longer valid')
    f.need(old['source_bytes'] == sum(row['bytes'] for row in old['files']) and
           old['source_content_sha256'] == source_content_hash(old['files']), 'old source inventory incoherent')
    expected['source_bytes'] += len(INSERTION)
    expected['source_content_sha256'] = source_content_hash(expected['files'])
    expected['archive'] = dict(old['archive'], bytes=NEW_ARCHIVE_BYTES, sha256=NEW_ARCHIVE_SHA256)
    expected['status'] = NEW_STATUS
    expected['diagnostic_meta_import_repair'] = {'change': REPAIR_DESCRIPTION, 'module': REPAIRED_MODULE,
                                               'old_source_sha256': OLD_SOURCE_SHA256,
                                               'new_source_sha256': NEW_SOURCE_SHA256}
    f.need(current == expected, 'only the exact diagnostic record and derived manifest metadata may change')
    f.need(current['proof_pass_claimed'] is False, 'source preparation cannot claim proof success')
    owned = [module for stage in plan['stages'] for module in stage['modules']]
    f.need(len(owned) == SOURCE_COUNT and len(set(owned)) == SOURCE_COUNT and
           set(owned) == {row['module'] for row in current['files']}, 'source/stage ownership changed')
    return REPAIRED_MODULE


def validate_implementation(old, current):
    """Exact named implementation map, with original validator bytes frozen."""
    # The driver additionally verifies these map entries against actual files
    # from the independently reviewed and hash-pinned pipeline checkout.
    f.need(type(current) is dict and set(current) == IMPLEMENTATION_KEYS,
           'unknown/missing continuation implementation file')
    for name, value in current.items():
        f.safe_rel(name); digest(value, 'implementation digest')
    for name, value in old.items():
        f.need(current['original/' + name] == value, 'frozen original implementation changed: ' + name)
        if name not in {'fresh_stage.py', 'ci_driver.py'}:
            f.need(current[name] == value, 'unchanged implementation helper changed: ' + name)
    f.need(current['fresh_stage.py'] == CURRENT_RUNNER, 'unreviewed readonly runner')
    for name, pin in [('original/contract.json', OLD_CONTRACT), ('original/plan.json', PLAN),
                      ('original/profiles.json', OLD_PROFILES), ('original/SOURCE_MANIFEST.json', MANIFEST),
                      ('source_delta.json', SOURCE_DELTA)]:
        f.need(current[name] == pin, 'implementation data pin changed: ' + name)


def validate_contexts(selection, old, current):
    """Validate both immutable origins and exactly one leaf-source successor."""
    keys(old, {'contract', 'manifest', 'plan', 'profiles', 'identity', 'inventory'}, 'old context')
    keys(current, {'contract', 'manifest', 'plan', 'profiles', 'identity', 'inventory', 'source_delta'}, 'current context')
    f.need(isinstance(selection, Selection), 'typed selection required')
    old_identity = selection.old_context['identity']
    f.need(old['identity'] == old_identity, 'old receipts must use original identity')
    validate_old_identity(old_identity)
    for key, expected in [('contract', OLD_CONTRACT), ('plan', PLAN), ('profiles', OLD_PROFILES),
                          ('manifest', MANIFEST), ('inventory', INVENTORY)]:
        f.need(f.sha(f.json_bytes(old[key])) == expected, 'unpinned original ' + key)
    keys(current['identity'], IDENTITY_KEYS | {'evidence_mode', 'selection_sha256', 'old_identity_sha256'},
         'successor identity')
    ci, cc = current['identity'], current['contract']
    validate_identity_pair(old_identity, ci)
    require_activation(cc, {'schema': 'verified-continuation-selection-v1',
                           'old_origin': selection.old_context, 'stages': selection.json_rows()})
    f.need(set(cc) == set(old['contract']) | CONTRACT_NEW_FIELDS, 'unknown/missing successor contract fields')
    for key in set(old['contract']) - CONTRACT_CHANGED_FIELDS:
        f.need(cc[key] == old['contract'][key], 'contract policy changed: ' + key)
    for key, field in [('contract', 'contract_sha256'), ('profiles', 'profiles_sha256'), ('plan', 'plan_sha256'),
                       ('manifest', 'source_manifest_sha256'), ('inventory', 'toolchain_inventory_sha256')]:
        f.need(f.sha(f.json_bytes(current[key])) == ci[field], 'successor ' + key + ' hash mismatch')
    f.need(ci['evidence_mode'] == 'verified_continuation' and
           cc['selection_sha256'] == ci['selection_sha256'] == selection.raw_sha256 and
           cc['old_identity_sha256'] == ci['old_identity_sha256'] == identity_hash(old_identity),
           'successor selection/origin binding mismatch')
    f.need(type(ci['run_id']) is str and ci['run_id'].isdigit() and int(ci['run_id']) > 0 and
           ci['run_id'] != str(OLD_RUN) and ci['run_attempt'] == '1' and
           type(ci['pipeline_commit']) is str and f.COMMIT.fullmatch(ci['pipeline_commit']) and
           ci['pipeline_commit'] != OLD_PIPELINE, 'successor must be one distinct initial run/pipeline')
    timestamp(ci['run_started_at'])
    f.need(ci['source_commit'] == cc['source_commit'] and ci['source_manifest_sha256'] == NEW_MANIFEST and
           cc['source_manifest_sha256'] == NEW_MANIFEST and cc['source_delta_sha256'] == SOURCE_DELTA,
           'successor source/delta identity mismatch')
    f.need(ci['runner_sha256'] == cc['runner_sha256'] == CURRENT_RUNNER, 'successor readonly runner mismatch')
    for name in ('plan_sha256', 'profiles_sha256', 'lean_archive_sha256', 'toolchain_inventory_sha256'):
        f.need(ci[name] == old_identity[name], 'plan/profile/toolchain identity changed')
    f.need(old['plan'] == current['plan'] and old['inventory'] == current['inventory'],
           'stage/order/toolchain facts changed')
    validate_profiles(old['profiles'], current['profiles'])
    validate_source_reconciliation(old['manifest'], current['manifest'], current['source_delta'], current['plan'])
    validate_implementation(old['contract']['implementation_sha256'], cc['implementation_sha256'])
    f.need([row.stage_id for row in selection.rows] == [stage['stage_id'] for stage in current['plan']['stages']],
           'typed selection does not exactly cover current plan')
    f.need(isinstance(selection.row(REBUILD_STAGE), CurrentOrigin), 'repaired diagnostic stage must be CurrentOrigin')
    old_entries = {row['module']: row for row in old['manifest']['files']}
    new_entries = {row['module']: row for row in current['manifest']['files']}
    old_set = set()
    for row, stage in zip(selection.rows, current['plan']['stages']):
        f.need(type(row) in (OldOrigin, CurrentOrigin), 'unknown typed origin')
        if isinstance(row, OldOrigin):
            validate_pin(row.pin, row.stage_id, identity_hash(old_identity))
            f.need(set(stage['required_predecessors']) <= old_set, 'old child has a rebuilt/non-old ancestor')
            old_set.add(row.stage_id)
            for module in stage['modules']:
                f.need(old_entries[module] == new_entries[module], 'reused source/import metadata changed')
    f.need(old_set and len(old_set) < len(selection.rows), 'continuation requires old and fresh stages')


def check_deadline(old_identity,current_identity,now=None,current_max_age=MAX_AGE):
    integer(current_max_age,'successor age',MAX_AGE)
    now=now or datetime.now(timezone.utc)
    f.need(now.tzinfo is not None,'current time must be trusted/timezone-aware')
    old_start=timestamp(old_identity['run_started_at']);new_start=timestamp(current_identity['run_started_at'])
    f.need(old_start<=now and new_start<=now,'run timestamp is in future')
    deadline=min(old_start+timedelta(seconds=MAX_AGE),new_start+timedelta(seconds=current_max_age))
    f.need(now<=deadline,'original or successor six-day deadline expired')
    return deadline


def validate_wrappers(selection, expected, wrappers, *, old_identity, current_identity, plan):
    ordered=[s['stage_id'] for s in plan['stages']]
    f.need(expected==[sid for sid in ordered if sid in set(expected)],'noncanonical restore request')
    f.need([w['native_descriptor']['stage_id'] for w in wrappers]==expected,'wrong/duplicate/missing wrapper set')
    stages={s['stage_id']:s for s in plan['stages']};requested=set(expected)
    total=0
    for wrapper in wrappers:
        keys(wrapper,{'origin','native_descriptor','archive_path','authenticated_metadata','raw_descriptor_sha256'},'artifact wrapper')
        d=wrapper['native_descriptor'];keys(d,NATIVE_KEYS,'native descriptor')
        sid=d['stage_id'];row=selection.row(sid)
        f.need(wrapper['origin']==type(row).__name__,'origin differs from frozen selection')
        f.need(set(stages[sid]['required_predecessors'])<=requested,'restore set not predecessor-closed')
        f.need(d['identity']==(old_identity if isinstance(row,OldOrigin) else current_identity),'descriptor origin identity mismatch')
        f.need(d['schema']=='fresh-stage-upload-candidate-v1' and d['producer_job']==stages[sid]['producer_job'] and
               d['producer_conclusion']=='success' and type(d['retention_days']) is int and d['retention_days']==7,'native descriptor role/status mismatch')
        for k in ('artifact_id','producer_job_id'):integer(d[k],k)
        integer(d['archive_bytes'],'archive bytes',MAX_ARTIFACT)
        for k in ('archive_sha256','receipt_sha256','artifact_zip_sha256'):digest(d[k],k)
        digest(wrapper['raw_descriptor_sha256'],'raw descriptor hash')
        if isinstance(row,OldOrigin):
            for k in ('artifact_id','producer_job_id','archive_sha256','archive_bytes','receipt_sha256','artifact_zip_sha256'):
                f.need(d[k]==row.pin[k],'old native descriptor differs from frozen pin: '+k)
            f.need(wrapper['raw_descriptor_sha256']==row.pin['raw_descriptor_sha256'],'raw old descriptor changed')
        path=Path(wrapper['archive_path']);f.no_symlink_path(path)
        f.need(path.is_file() and path.stat().st_size==d['archive_bytes'],'actual tar size differs from descriptor')
        total+=path.stat().st_size
        f.need(total<=MAX_RESTORED,'aggregate mixed-origin restore budget exceeded')
    return total


def nonempty_waves(selection,plan):
    """Schedule original numeric waves, not first appearance in the stage list.

    The frozen stage list is topological but interleaves independent lanes. A
    late-listed stage can belong to an earlier wave than already-listed stages.
    Keep original stage order within each wave; all cross-stage dependencies
    must be in strictly earlier original waves, including restored predecessors.
    """
    validate_plan(plan)
    stages={stage['stage_id']:stage for stage in plan['stages']}
    f.need(len(stages)==len(plan['stages']), 'duplicate scheduled stage')
    for stage in plan['stages']:
        wave=stage.get('wave')
        f.need(type(wave) is int and wave>=0, 'invalid original numeric wave')
        f.need(stage.get('producer_job')==f'wave_{wave:02d}', 'producer job/numeric wave mismatch')
        f.need(type(stage.get('needs_stages')) is list and
               all(type(sid) is str for sid in stage['needs_stages']) and
               len(set(stage['needs_stages']))==len(stage['needs_stages']), 'invalid direct stage dependencies')
    groups={}
    for stage in plan['stages']:
        for predecessor in stage['needs_stages']:
            f.need(predecessor in stages and stages[predecessor]['wave']<stage['wave'],
                   'direct stage dependency must be in a strictly earlier original wave')
        row=selection.row(stage['stage_id'])
        f.need(type(row) in (OldOrigin,CurrentOrigin), 'unknown scheduled stage origin')
        if isinstance(row,CurrentOrigin):groups.setdefault(stage['wave'],[]).append(stage['stage_id'])
    result=[];previous='prepare'
    for wave,ids in sorted(groups.items()):
        job=f'wave_{wave:02d}'
        result.append({'job_id':job,'stage_ids':ids,'needs':['prepare'] if previous=='prepare' else ['prepare',previous],
                       'max_parallel':4,'runner':'ubuntu-22.04','timeout_minutes':350})
        previous=job
    return result


def require_activation(contract, selection_data):
    f.need(type(contract) is dict and contract.get('review_status') == 'reviewed_for_execution' and
           contract.get('continuation_review_status') == 'independently_reviewed' and
           type(selection_data) is dict and selection_data,
           'INACTIVE: terminal selection and independent continuation review required')
    f.need(contract.get('evidence_mode') == 'verified_continuation', 'continuation contract mode missing')
    for key, expected in [('storage_adapter_review_status', 'reviewed'),
                          ('readonly_commit_review_status', 'reviewed'),
                          ('compiler_adapter_review_status', 'reviewed'),
                          ('final_checks_review_status', 'reviewed'),
                          ('process_containment_review_status', 'reviewed'),
                          ('transport_review_status', 'reviewed'),
                          ('receipt_protocol', 'readonly_committed_v1'),
                          ('source_manifest_sha256', NEW_MANIFEST),
                          ('source_delta_sha256', SOURCE_DELTA), ('runner_sha256', CURRENT_RUNNER)]:
        f.need(contract.get(key) == expected, 'INACTIVE: missing or changed ' + key)
    source = contract.get('source_commit')
    f.need(type(source) is str and f.COMMIT.fullmatch(source) and source != SOURCE,
           'INACTIVE: distinct immutable successor source commit required')
    digest(contract.get('selection_sha256'), 'selection hash')
    digest(contract.get('old_identity_sha256'), 'old identity hash')
    f.need(type(contract.get('current_workflow')) is dict and contract['current_workflow'],
           'reviewed current workflow mapping missing')
