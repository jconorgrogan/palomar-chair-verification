"""Strict higher-only schema. Legacy contracts and native receipts retain their identity."""
from pathlib import Path
import hashlib,json,re
SCHEMA='higher-dimension-staged-replay-v1'
SUCCESS='HIGHER_DIMENSIONS_THREE_AND_GE_FIVE_RAW_AUDITED'
STAGE_SUCCESS='CHECKED_HIGHER_DIMENSION_STAGE_COMPLETED'
HSTAGES=['H0_common','H1_coarse_contacts','H2_forward_contacts','H3_contact_binding','H4_product_geometry','H5_higher_assembly']
OLD=['F0_common','F3_product_geometry']
RECOVERY_MODE='exact-historical-H4-v1'
H4_STAGE='H4_product_geometry'
H4_PRODUCER_SHA='36e9d007ca11bf79dcd2841b3023c4ecf40b170503a4c484661d6b1e33049aa5'
CONTROL_LAYOUT_REVIEW_SHA='8aca4fc5f247cfe7ba5cab59e5f876cfcb3166784d50fd05c5912a58ee689d93'
H4_IDENTITY={'repository':'jconorgrogan/palomar-chair-verification','run_id':'38982023996','run_attempt':'1','workflow_commit':'31e580fd4246e2d60dd6393ac8571abfe1cd2ba0'}
def recovery(c):return c.get('higher_recovery_mode')==RECOVERY_MODE
H5_RETRY_MODE='exact-historical-H0-H3-for-H5-read-diagnostic-v1'
H5_PRODUCER_SHA='29e3b7dddbd52d782a9489b2394080ed48e9c361a46c8b3315f202119d715d21'
H5_PRODUCER_IDENTITY={'repository':'jconorgrogan/palomar-chair-verification','run_id':'39134139440','run_attempt':'1','workflow_commit':'db18549f7ad64d5d62c4f9432f8f804ab375375c'}
def h5_retry(c):return c.get('higher_h5_retry_mode')==H5_RETRY_MODE
def raw_as24(c):return 'higher_h5_raw_auditor_address_space_gib' in c
def raw_heap5120(c):return 'higher_h5_raw_auditor_heap_mib' in c
def command_address_space_bytes(c,name,a):
    if raw_as24(c):
        a.f.need(h5_retry(c) and type(c['higher_h5_raw_auditor_address_space_gib']) is int and c['higher_h5_raw_auditor_address_space_gib']==24,'unapproved raw-auditor AS profile')
        if name=='audit-AuditHigherPhysicalEndpoints':return 24*a.GIB
    return 12*a.GIB
def producer_cache_role(c,sid,a):
    a.f.need(sid in OLD+HSTAGES,'unknown native cache role')
    if sid in OLD:
        expected=a.ORIGINAL_STAGE_CONTRACT_SHA if sid==OLD[0] else a.CONTINUATION_PRODUCER_SHA
        a.f.need(digest(c)==expected,'legacy stage producer contract differs');return 'base'
    a.f.need(c.get('schema')==SCHEMA,'higher stage lacks higher producer profile');return 'extended'
COUNTS=[44,221,82,460,304,27]
CHECKS={'SparseMonotiles.CoarseContactCertificates5PackedRows':(240,'914a3ddef7a5674a9bb2f7a5725b30521c80bdb1f988663b1a167e89bf5660bf',163.708),'SparseMonotiles.CoarseContactCertificates5SymmetryCoverage':(720,'283a5e1d00ead57526fd7bb70227b1cb1b77d12aba41bdee54d8d0236e592816',572.843)}
CONTROL_LABELS=['exact mapped model definition', 'renamed native model constant rejected', 'extra reference model constant rejected', 'nested extra reference model constant rejected', 'changed HasTiling predicate rejected', 'changed HasTiling existential universe rejected', 'missing HasTiling existential rejected', 'exact collection-period surrogate', 'collection period changed to union period rejected', 'model extra universe rejected', 'unsafe model rejected', 'open model body rejected', 'exact quantified endpoint surrogate', 'dimension quantifier removed rejected', 'dimension binder renamed rejected', 'dimension binder visibility changed rejected', 'dimension lower bound changed rejected', 'extra hypothesis rejected', 'axiom substituted for theorem rejected', 'three standard axioms accepted', 'sorryAx rejected', 'extra axiom rejected', 'fixed seven model names and two endpoints']
TARGETS=['ClarkSeed.exists_physical_aperiodic_monotile_of_ge_five','ClarkSeed.exists_physical_aperiodic_monotile_of_ge_three_ne_four']
def digest(value):return hashlib.sha256((json.dumps(value,sort_keys=True,indent=2)+'\n').encode()).hexdigest()
def profile(c,a):
    a.f.need('higher_recovery_mode' not in c or recovery(c),'unknown higher recovery mode')
    a.f.need('higher_h5_retry_mode' not in c or (h5_retry(c) and recovery(c)),'unknown H5-only retry mode')
    if raw_heap5120(c):validate_raw_heap5120_scope(c,a)
    else:a.f.need('higher_h5_heap5120' not in c,'heap5120 scope lacks fixed profile')
    if raw_as24(c):validate_raw_as24_scope(c,a)
    else:a.f.need('higher_h5_as24' not in c,'AS24 scope lacks fixed resource profile')
    if h5_retry(c):validate_h5_retry_scope(c,a)
    expected={'schema':SCHEMA,'owned_module_count':1433,'fresh_higher_module_count':1138,'retained_historical_module_count':295,'higher_mathematical_closure_count':1154,'retained_context_outside_higher_closure_count':279,'lean_heap_mib':4096,'diagnostic_rss_gib':8,'diagnostic_timeout_seconds':180,'check_timeout_seconds':120,'outer_timeout_minutes':330,'aggregate_command_deadline_seconds':19200,'maximum_parallel_jobs':4,'stage_count':8,'workflow_job_count':6,'workflow_aggregate_seconds':115200,'workflow_outer_runner_minutes':1980,'object_artifact_max_bytes':4*a.GIB,'object_artifact_zip_max_bytes':4*a.GIB+4*1024**2,'producer_job_log_max_bytes':16*1024**2,'transport_timeout_seconds':1800,'failure_evidence_grace_seconds':5,'owned_output_max_bytes':6*a.GIB,'owned_source_max_bytes':32*1024**2,'evidence_max_bytes':124*1024**2,'aggregate_log_max_bytes':64*1024**2,'per_command_log_max_bytes':1024**2,'minimum_free_disk_bytes':1536*1024**2,'auditor_timeout_seconds':600,'cache_module_count':2805}
    if recovery(c):expected.update(workflow_job_count=5,workflow_aggregate_seconds=96000,workflow_outer_runner_minutes=1650,fresh_execution_module_count=834,retained_higher_module_count=304)
    else:a.f.need('fresh_execution_module_count' not in c and 'retained_higher_module_count' not in c,'legacy higher profile asserts recovery counts')
    if h5_retry(c):expected.update(workflow_job_count=1,workflow_aggregate_seconds=19200,workflow_outer_runner_minutes=330,fresh_execution_module_count=27,retained_higher_module_count=1111)
    for k,v in expected.items():a.f.need(type(c.get(k)) is type(v) and c[k]==v,'higher profile differs: '+k)
    for k,v in {'all_dimension_uniform_proof_certified':False,'final_C_proof_certified':False,'unconditional_monotile_proof_certified':False,'higher_endpoints_have_no_C_premise':True,'fresh_external_source_rebuild':False,'owned_objects_from_prior_runs_allowed':True,'owned_objects_from_same_run_checked_stages_allowed':True,'fresh_research_modules_exactly_once':True}.items():a.f.need(c.get(k) is v,'higher claim/trust differs: '+k)
    a.f.need(c.get('proof_scope')=='higher-dimension-sources-and-c-free-endpoints' and c.get('independent_auditor_preflight_stages')==['H0_common','H5_higher_assembly'],'higher proof/preflight scope differs')
    a.f.need(c.get('higher_reference_static_review_sha256')=='392e108004b6feb0726e0de8d48e84debb5d666be280fe6a00d484510f2688dd','higher reference review differs')
    for name,pin in {'AuditHigherPhysicalEndpoints':(10780,'ba9a502d5f121719b7fff10c73d3bf9cfa6857a0f2a42e99b36d39051b64af13'),'HigherPhysicalReference':(2138,'bcf383a13467b15ce7b55e1e4a171bab4f86439e696b0a30ebd13769236c15ea'),'HigherInspectorControl':((7009,'c19d8b660c981e205956b092775b6c8f44f7c6eabae795e9278f316530ca1fe4') if recovery(c) else (6975,'017aadfea7927f7957a5143bcfa8f93af37214ef56f62881e8bddb05af34e482'))}.items():
        a.f.need(c['inputs'].get('auditors/'+name+'.lean')=={'bytes':pin[0],'sha256':pin[1]},'higher independent source pin differs')
    a.f.need(c.get('higher_visibility_variant_lock_sha256')=='3621fde9a869de3f0fc4f3f312c142e13df0d5672f34b1402b10cf9b99f475be' and c.get('higher_visibility_independent_review_sha256')=='a583afc1d571b60f41a349d0797fd8f373ac190b92598ec35ee85d2777338373' and c.get('higher_visibility_actual_elaboration_pending') is True,'higher visibility provenance differs')
    a.f.need(c['execution_stages']==([HSTAGES[-1]] if h5_retry(c) else [s for s in HSTAGES if s!=H4_STAGE] if recovery(c) else HSTAGES) and c['locked_origin_stages']==(OLD+HSTAGES[:-1] if h5_retry(c) else OLD+[H4_STAGE] if recovery(c) else OLD) and c['higher_endpoints']==TARGETS and c['higher_target']=='ClarkSeed.PhysicalDimensions','higher execution or theorem scope differs')
    a.f.need('module_compile_arguments' not in c and 'conditional_C_remains_explicit' not in c,'higher replay has an unapproved compiler option or misleading C premise field')
    wanted={m:{'proposed_check_timeout_seconds':v[0],'source_sha256':v[1],'observed_historical_checker_seconds':v[2]} for m,v in CHECKS.items()}
    a.f.need(c.get('module_checker_timeout_exceptions')==wanted,'checker exceptions differ')
    for m,v in CHECKS.items():a.f.need(c['inputs']['src/'+m.replace('.','/')+'.lean']['sha256']==v[1],'checker exception source differs')
    if recovery(c):validate_control_layout(c,a)
def validate_h5_retry_scope(c,a):
    expected={'schema':'higher-h5-read-diagnostic-retry-v1','producer_contract_sha256':H5_PRODUCER_SHA,
      'producer_identity':H5_PRODUCER_IDENTITY,'retained_stages':HSTAGES[:4],
      'diagnostic_source_review_sha256':'e9d1d4c8d7cc7f6ccb4d3a86fb478cfc3d10913c2179318b6ad1ae0e0f2516cc',
      'diagnostic_proposal_sha256':'bbfdaf39e91bc7de9d7f4b24ba1922c4746b646f9f1babc59da16ec203d94eaa',
      'failed_h5_terminal_review_sha256':'b3316faad3cda79182e2eca04ac0a8630fc9bd17fb496f5644d340bbcd834a01',
      'failed_h5_objects_reused':False,'fresh_h5_module_count':27,'all_per_command_and_per_job_caps_unchanged':not raw_as24(c)}
    a.f.need(c.get('higher_h5_retry')==expected,'H5 retry scope/provenance differs')
    a.f.need(c['publication_branch']==('verify/higher-h5-heap5120-20261018' if raw_heap5120(c) else 'verify/higher-h5-as24-20261018' if raw_as24(c) else 'verify/higher-h5-read-diagnostic-20261018'),'H5 retry branch differs')
    for path,sha in [('origin/higher-h5-diagnostic-independent-review.json',expected['diagnostic_source_review_sha256']),
                     ('origin/higher-h5-diagnostic-proposal-review.json',expected['diagnostic_proposal_sha256']),
                     ('origin/failed-h5-terminal-review.json',expected['failed_h5_terminal_review_sha256'])]:
        a.f.need(c['inputs'][path]['sha256']==sha and a.f.file_sha(a.ROOT/path)==sha,'H5 retry source evidence changed')

def validate_raw_as24_scope(c,a):
    command_address_space_bytes(c,'audit-AuditHigherPhysicalEndpoints',a)
    expected={'schema': 'higher-h5-raw-auditor-as24-v1', 'previous_contract_sha256': 'aa6ae7a64d5e8b00e358887ad5d085127b1e318bd8b291ef7ba8ac59886c9369', 'failed_run_identity': {'repository': 'jconorgrogan/palomar-chair-verification', 'run_id': '39150122418', 'run_attempt': '1', 'workflow_commit': '31143d79da8970f60dec6227cb97fd5470321209'}, 'failed_h5_terminal_review_sha256': 'ed35605dbb4a4ea88ab9e0c1a8e2a9bf8775ec9c712c5aa3c5015ed11f656837', 'raw_auditor_command': 'audit-AuditHigherPhysicalEndpoints', 'previous_address_space_bytes': 12884901888, 'address_space_bytes': 25769803776, 'rss_tree_bytes': 8589934592, 'other_commands_address_space_bytes': 12884901888, 'other_command_and_job_limits_unchanged': True, 'failed_h5_objects_reused': False, 'fresh_h5_module_count': 27}
    a.f.need(c.get('higher_h5_as24')==expected,'raw-auditor AS24 scope/provenance differs')
    for path,sha in [('origin/higher-h5-as12-contract.json',expected['previous_contract_sha256']),('origin/failed-h5-as12-terminal-review.json',expected['failed_h5_terminal_review_sha256'])]:
        a.f.need(c['inputs'][path]['sha256']==sha and a.f.file_sha(a.ROOT/path)==sha,'AS24 prior source/evidence changed')

def validate_raw_heap5120_scope(c,a):
    a.f.need(h5_retry(c) and raw_as24(c) and type(c['higher_h5_raw_auditor_heap_mib']) is int and c['higher_h5_raw_auditor_heap_mib']==5120,'unapproved raw-auditor heap profile')
    expected={'schema': 'higher-h5-raw-auditor-heap5120-v1', 'previous_contract_sha256': '3e38bbd56e30868f63be4f8ff68485c0b4a643117bf78b763472c245b07f6630', 'failed_run_identity': {'repository': 'jconorgrogan/palomar-chair-verification', 'run_id': '39156079183', 'run_attempt': '1', 'workflow_commit': 'f20a3135ad6f49dd3a8050053d1affd885891016'}, 'failed_h5_terminal_review_sha256': '3a86ac46a3edd66af0839c47d08e3571c80839dbea014e5b22ff22eadf7ccd95', 'official_memory_source_binding_sha256': 'b1d83132919f10e8768975536d8423b4099e760458265ad9107c5e15a9a53608', 'raw_auditor_command': 'audit-AuditHigherPhysicalEndpoints', 'previous_lean_heap_mib': 4096, 'lean_heap_mib': 5120, 'address_space_bytes': 25769803776, 'rss_tree_bytes': 8589934592, 'all_other_command_arguments_and_limits_unchanged': True, 'failed_h5_objects_reused': False, 'fresh_h5_module_count': 27}
    a.f.need(c.get('higher_h5_heap5120')==expected,'raw-auditor heap5120 scope/provenance differs')
    for path,sha in [('origin/higher-h5-as24-contract.json',expected['previous_contract_sha256']),('origin/failed-h5-as24-terminal-review.json',expected['failed_h5_terminal_review_sha256']),('origin/lean-memory/SOURCE_BINDING.json',expected['official_memory_source_binding_sha256'])]:
        a.f.need(c['inputs'][path]['sha256']==sha and a.f.file_sha(a.ROOT/path)==sha,'heap5120 prior source/evidence changed')

def validate_control_layout(c,a):
    old_path='origin/HigherInspectorControl.original.lean';new_path='auditors/HigherInspectorControl.lean';lock_path='locks/higher-control-layout-repair.json'
    before=b'  let native := { refDefinition with name := `SparseMonotiles.HasTiling,\n'
    after=b'  let native := { refDefinition with\n    name := `SparseMonotiles.HasTiling,\n'
    expected={'schema':'higher-control-layout-repair-v1','old_bytes':6975,'new_bytes':6979,'old_sha256':'017aadfea7927f7957a5143bcfa8f93af37214ef56f62881e8bddb05af34e482','new_sha256':'bc8ecd03848123d85f6afc77ff42bd7b4627bffc00bae6989cbefa8e43863992','byte_offset':2629,'old_exact_utf8':before.decode(),'new_exact_utf8':after.decode(),'preserved_control_count':23,'independent_review_sha256':CONTROL_LAYOUT_REVIEW_SHA,'actual_corrected_control_elaboration_pending':True}
    a.f.need(a.f.SHA256.fullmatch(CONTROL_LAYOUT_REVIEW_SHA) and c.get('higher_control_layout_review_sha256')==CONTROL_LAYOUT_REVIEW_SHA,'control layout review is missing or changed')
    a.f.need(a.f.load_json(a.ROOT/lock_path)==expected,'control layout lineage differs')
    for path,size,sha in [(old_path,6975,expected['old_sha256']),(new_path,7009,'c19d8b660c981e205956b092775b6c8f44f7c6eabae795e9278f316530ca1fe4')]:
        a.f.need(c['inputs'][path]=={'bytes':size,'sha256':sha} and (a.ROOT/path).stat().st_size==size and a.f.file_sha(a.ROOT/path)==sha,'control layout source pin differs')
    old=(a.ROOT/old_path).read_bytes();new=(a.ROOT/new_path).read_bytes()
    meta=b'meta import Lean.Elab.Command\n'
    a.f.need(new.count(meta)==1 and new.count(b'meta import AuditHigherPhysicalEndpoints\n'+meta)==1,'higher green meta import differs')
    new=new.replace(meta,b'',1)
    a.f.need(len(new)==6979 and hashlib.sha256(new).hexdigest()==expected['new_sha256'],'historical layout intermediate differs')
    a.f.need(c.get('higher_control_green_prefix')=={'run_id':38988960060,'run_attempt':1,'commit':'6954395491fc254b31dd40e77789b45410fc6cc4','control_sha256':'c19d8b660c981e205956b092775b6c8f44f7c6eabae795e9278f316530ca1fe4','review_sha256':'2b87c220aed18b5c44514ad9c18854b58d6ce57161e6132f5fb66d68c819b229'},'higher green prefix provenance differs')
    a.f.need(old.count(before)==1 and old.index(before)==2629 and new==old.replace(before,after,1),'control correction is not the sole reviewed whitespace edit')
def checker_seconds(c,m):return CHECKS[m][0] if c.get('schema')==SCHEMA and m in CHECKS else c['check_timeout_seconds']
def stage_plan(c,a):
    a.f.need(c['stage_order']==OLD+HSTAGES and set(c['stages'])==set(OLD+HSTAGES) and c['final_stage']==HSTAGES[-1],'higher stage set differs')
    owned=a.f.load_json(a.ROOT/'locks/owned-sources.json');rows={r['module']:r for r in owned['sources']};owner={};seen=[]
    needmap={'H0_common':['F3_product_geometry'],'H1_coarse_contacts':['F3_product_geometry','H0_common'],'H2_forward_contacts':['F3_product_geometry','H0_common'],'H3_contact_binding':['F3_product_geometry','H0_common'],'H4_product_geometry':['F3_product_geometry'],'H5_higher_assembly':['F3_product_geometry',*HSTAGES[:-1]]}
    for sid,count in zip(OLD+HSTAGES,[186,109,*COUNTS]):
        row=c['stages'][sid];names=row['modules'];a.f.need(len(names)==len(set(names))==count,'higher stage count differs')
        needs=[] if sid==OLD[0] else [OLD[0]] if sid==OLD[1] else needmap[sid]
        a.f.need(row['needs']==needs,'higher stage dependencies differ')
        ancestors=set(needs)
        for dep in needs:ancestors.update(c['stages'][dep]['admitted_stages'])
        a.f.need(row['admitted_stages']==[s for s in seen if s in ancestors],'higher ancestor order differs')
        available={m for dep in row['admitted_stages'] for m in c['stages'][dep]['modules']}
        for m in names:
            a.f.need(m not in owner and m in rows,'higher duplicate/unlisted source')
            for dep in rows[m]['ordered_imports']:a.f.need(dep not in rows or dep in available,'higher stage import not accepted: '+m+' -> '+dep)
            owner[m]=sid;available.add(m)
        seen.append(sid)
    a.f.need(set(owner)==set(rows)=={r['module'] for r in c['modules']} and len(rows)==1433,'higher stage exact union differs')
    a.f.need(set(m for sid in HSTAGES for m in c['stages'][sid]['modules'])==set(owned['fresh_higher_modules']),'fresh higher partition differs')
def owned_graph(c,owned,required,source_root,a):
    rows=owned['sources'];names=[r['module'] for r in rows];order=owned['module_order'];graph={r['module']:r['ordered_imports'] for r in rows}
    a.f.need(len(names)==len(set(names))==1433 and names==order==[r['module'] for r in c['modules']],'higher owned order differs')
    cache={r['module'] for r in required['modules']};runtime=set(c['runtime_roots'])
    a.f.need(len(cache)==len(required['modules'])==2805 and not cache.intersection(names),'higher cache union differs')
    a.f.need(runtime==set(owned['runtime_roots'])==set(required['runtime_roots'])=={'Init','Init.Data.Rat'},'higher runtime boundary differs')
    a.f.need(required['roots']==c['cache_roots'] and set(required['roots'])<=cache,'higher cache roots differ')
    seen=set();paths=set();external=set()
    for r in rows:
        m=r['module'];p='src/'+m.replace('.','/')+'.lean';a.f.need(a.f.MODULE.fullmatch(m) and r['path']==p,'higher source path/name differs')
        a.f.need(c['inputs'][p]=={'bytes':r['bytes'],'sha256':r['sha256']},'higher source pin differs')
        parsed=a.header_parser.header((source_root/p).read_bytes())
        a.f.need(parsed['modern'] and not parsed['prelude'] and [x['module'] for x in parsed['imports']]==r['ordered_imports'],'higher source header differs')
        for dep in r['ordered_imports']:
            a.f.need(dep in seen or dep in cache or dep in runtime,'higher unresolved import: '+m+' -> '+dep)
            if dep in cache:external.add(dep)
        seen.add(m);paths.add(p)
    needed=set()
    def visit(m):
        if m in needed or m not in graph:return
        needed.add(m)
        for dep in graph[m]:visit(dep)
    visit('ClarkSeed.PhysicalDimensions')
    historical={m for sid in OLD for m in c['stages'][sid]['modules']};fresh=set(owned['fresh_higher_modules'])
    a.f.need(len(needed)==1154 and len(needed&historical)==16 and needed-historical==fresh and len(fresh)==1138,'higher mathematical closure differs')
    validate_visibility_sources(c,source_root,fresh,a)
    a.f.need(historical==set(owned['historical_context_modules']) and len(historical)==295 and len(historical-needed)==279,'higher admitted context differs')
    a.f.need(paths=={p for p in c['inputs'] if p.startswith('src/')},'higher source extras')
    base=a.f.load_json(a.ROOT/'origin/base-required-modules.json')
    a.f.need(set(required['roots'])==set(base['roots'])|external,'higher direct external boundary differs')
    a.f.need(not {'SpectreFinite.RadiusFivePruningHierarchy','NativeFinalAssembly.AllDimensions','NativeFinalAssembly.AllDimensionsOfParent'}&set(names),'unreviewed uniform/C assembly present in higher-only run')
def origins(c,a):
    a.f.need(c['schema']==SCHEMA,'higher origin schema differs')
    paths={a.ORIGINAL_STAGE_CONTRACT_SHA:'origin/producer-contract.json',a.CONTINUATION_PRODUCER_SHA:'origin/continuation-producer-contract.json'};producers={}
    if recovery(c):paths[H4_PRODUCER_SHA]='origin/higher-producer-contract.json'
    if h5_retry(c):paths[H5_PRODUCER_SHA]='origin/higher-h0-h3-producer-contract.json'
    original_owned=a.f.load_json(a.ROOT/'origin/producer-owned-sources.json');oldrows={r['module']:r for r in original_owned['sources']};current={r['module']:r for r in a.f.load_json(a.ROOT/'locks/owned-sources.json')['sources']}
    for sha,path in paths.items():
        p=c['producer_contracts'][sha];a.f.need(p=={'path':path,'sha256':sha,'bytes':(a.ROOT/path).stat().st_size} and c['inputs'][path]=={'bytes':p['bytes'],'sha256':sha},'higher producer pointer differs')
        producer=a.f.pinned_load(a.ROOT/path,sha);a.validate_diagnostic_profile(producer);a.validate_stage_plan(producer);producers[sha]=producer
        for name in ['lean-toolchain','locks/dependencies.json','locks/cache-client.json']:a.f.need(c['inputs'][name]==producer['inputs'][name],'higher immutable runtime/cache pin differs')
        if sha in (H4_PRODUCER_SHA,H5_PRODUCER_SHA):
            a.f.need((not recovery(producer)) if sha==H4_PRODUCER_SHA else (recovery(producer) and not h5_retry(producer)),'historical higher producer recovery role differs')
            for name in ['locks/owned-sources.json','locks/required-modules.json','locks/cache-extension.json','origin/base-interface-identity.json','origin/base-required-modules.json']:
                a.f.need(c['inputs'][name]==producer['inputs'][name],'historical H4 source/cache lock changed')
            a.f.need(c['source_archive']==producer['source_archive'],'historical H4 source archive changed')
        else:
            a.f.need(a.f.file_sha(a.ROOT/'origin/producer-owned-sources.json')==producer['inputs']['locks/owned-sources.json']['sha256'],'original source graph changed')
            a.f.need(a.f.file_sha(a.ROOT/'origin/base-required-modules.json')==producer['inputs']['locks/required-modules.json']['sha256'],'original cache graph changed')
    a.f.need(set(c['producer_contracts'])==set(paths),'higher unknown producer contract')
    p=c['origin_lock'];a.f.need(p['path']=='origin/locked-origins.json' and c['inputs'][p['path']]=={'bytes':p['bytes'],'sha256':p['sha256']},'higher origin pointer differs')
    lock=a.f.pinned_load(a.ROOT/p['path'],p['sha256']);a.f.need(lock['schema']==('higher-exact-mixed-origin-lock-v3' if h5_retry(c) else 'higher-exact-mixed-origin-lock-v2' if recovery(c) else 'higher-exact-mixed-origin-lock-v1') and lock['producer_contracts']==list(paths) and set(lock['stages'])==set(c['locked_origin_stages']),'higher origin set differs')
    selected={}
    for sid in OLD:
        row=lock['stages'][sid];a.transport.validate_origin_lock(row['origin']);sha=a.CONTINUATION_PRODUCER_SHA if sid==OLD[1] else a.ORIGINAL_STAGE_CONTRACT_SHA
        a.f.need(row['producer_contract_sha256']==sha and set(row)=={'origin','producer_contract_sha256','receipt_sha256','checked_module_receipts_sha256','descriptor_sha256','stage_tar_sha256','stage_tar_bytes','independent_review_sha256'},'higher origin role differs')
        expected={'repository':'jconorgrogan/palomar-chair-verification','run_id':'38944907835' if sid==OLD[1] else '38914223883','run_attempt':'1','workflow_commit':'3a2ec654097b5259679816e81ccfab6fe3948d41' if sid==OLD[1] else '318a6900eabfec550b4adf1b0f4bd634c20d67c5'}
        a.f.need(row['origin']['identity']==expected and row['origin']['stage_id']==sid and row['origin']['workflow_id']==386423911,'higher exact historical identity differs')
        producer=producers[sha];a.f.need(c['stages'][sid]==producer['stages'][sid],'higher native stage schedule changed')
        for m in producer['stages'][sid]['modules']:a.f.need(current[m]==oldrows[m] and c['inputs'][current[m]['path']]==producer['inputs'][current[m]['path']],'retained source row differs')
        for k in ['receipt_sha256','checked_module_receipts_sha256','descriptor_sha256','stage_tar_sha256','independent_review_sha256']:a.f.need(a.f.SHA256.fullmatch(row[k]),'higher missing origin digest')
        selected[sid]=producer
    native=c['native_continuation_origin_lock'];a.f.need(native['path']=='origin/continuation-producer-origins.json' and a.f.file_sha(a.ROOT/native['path'])==native['sha256']==producers[a.CONTINUATION_PRODUCER_SHA]['origin_lock']['sha256'],'native F3 predecessor certificate changed')
    if recovery(c):
        row=lock['stages'][H4_STAGE];producer=producers[H4_PRODUCER_SHA]
        validate_h4_origin_row(row,c,producer,current,a)
        native=c['native_higher_origin_lock'];path='origin/higher-producer-origins.json'
        a.f.need(native=={'path':path,'bytes':producer['origin_lock']['bytes'],'sha256':producer['origin_lock']['sha256']} and c['inputs'][path]=={'bytes':native['bytes'],'sha256':native['sha256']},'native H4 predecessor lock pointer differs')
        native_lock=a.f.pinned_load(a.ROOT/path,native['sha256'])
        a.f.need((a.ROOT/path).stat().st_size==native['bytes'] and native_lock=={'schema':'higher-exact-mixed-origin-lock-v1','producer_contracts':list(paths)[:2],'stages':{sid:lock['stages'][sid] for sid in OLD}},'native H4 predecessor origins changed')
        pointer=c['native_higher_interface'];path='origin/higher-interface-identity.json'
        a.f.need(set(pointer)=={'path','bytes','sha256'} and pointer['path']==path and c['inputs'][path]=={'bytes':pointer['bytes'],'sha256':pointer['sha256']} and (a.ROOT/path).stat().st_size==pointer['bytes'],'native H4 interface pointer differs')
        interface=a.f.pinned_load(a.ROOT/path,pointer['sha256'])
        fields={'schema','runtime_inventory_sha256','required_cache_companion_rows_sha256','all_package_native_library_files_sha256','approved_bootstrap_companion_rows_sha256'}
        a.f.need(set(interface)==fields and interface['schema']=='higher-external-interface-v1' and interface['runtime_inventory_sha256']==a.RUNTIME_INVENTORY_SHA and interface['all_package_native_library_files_sha256']==digest({}),'native H4 extended interface scope differs')
        for k in fields-{'schema'}:a.f.need(a.f.SHA256.fullmatch(interface[k]),'native H4 interface digest differs')
        selected[H4_STAGE]=producer
    if h5_retry(c):
        producer=producers[H5_PRODUCER_SHA];pointer=c['native_h0_h3_origin_lock'];path='origin/higher-h0-h3-producer-origins.json'
        a.f.need(pointer=={'path':path,'bytes':producer['origin_lock']['bytes'],'sha256':producer['origin_lock']['sha256']} and c['inputs'][path]=={'bytes':pointer['bytes'],'sha256':pointer['sha256']},'native H0-H3 origin pointer differs')
        native=a.f.pinned_load(a.ROOT/path,pointer['sha256'])
        a.f.need((a.ROOT/path).stat().st_size==pointer['bytes'] and native=={'schema':'higher-exact-mixed-origin-lock-v2','producer_contracts':list(paths)[:3],'stages':{sid:lock['stages'][sid] for sid in OLD+[H4_STAGE]}},'native H0-H3 predecessor origins changed')
        for sid in HSTAGES[:4]:
            validate_h0_h3_origin_row(lock['stages'][sid],sid,c,producer,current,a);selected[sid]=producer
    return selected,lock['stages']
def validate_h4_origin_row(row,c,producer,current,a):
    """Pinned metadata policy only; Transport separately authenticates the API and every payload byte."""
    a.transport.validate_origin_lock(row['origin'])
    a.f.need(set(row)=={'origin','producer_contract_sha256','receipt_sha256','checked_module_receipts_sha256','descriptor_sha256','stage_tar_sha256','stage_tar_bytes','independent_review_sha256'},'H4 origin fields differ')
    a.f.need(row['producer_contract_sha256']==H4_PRODUCER_SHA and row['origin']['identity']==H4_IDENTITY and row['origin']['stage_id']==H4_STAGE and row['origin']['workflow_id']==386423911,'historical H4 identity or contract differs')
    a.f.need(c['stages'][H4_STAGE]==producer['stages'][H4_STAGE],'native H4 stage schedule changed')
    for m in producer['stages'][H4_STAGE]['modules']:
        a.f.need(c['inputs'][current[m]['path']]==producer['inputs'][current[m]['path']],'native H4 source changed')
    for k in ['receipt_sha256','checked_module_receipts_sha256','descriptor_sha256','stage_tar_sha256','independent_review_sha256']:a.f.need(a.f.SHA256.fullmatch(row[k]),'missing H4 origin digest')
    a.f.need(type(row['stage_tar_bytes']) is int and 0<row['stage_tar_bytes']<=c['object_artifact_max_bytes'],'H4 tar bound differs')

def validate_h0_h3_origin_row(row,sid,c,producer,current,a):
    """Four exact original producers; full native byte/receipt admission remains mandatory."""
    a.f.need(h5_retry(c) and sid in HSTAGES[:4],'unselected H0-H3 retained stage')
    a.transport.validate_origin_lock(row['origin'])
    a.f.need(set(row)=={'origin','producer_contract_sha256','receipt_sha256','checked_module_receipts_sha256','descriptor_sha256','stage_tar_sha256','stage_tar_bytes','independent_review_sha256'},'H0-H3 origin fields differ')
    a.f.need(row['producer_contract_sha256']==H5_PRODUCER_SHA and row['origin']['identity']==H5_PRODUCER_IDENTITY and row['origin']['stage_id']==sid and row['origin']['workflow_id']==386423911,'original H0-H3 identity or contract differs')
    a.f.need(c['stages'][sid]==producer['stages'][sid],'native H0-H3 stage schedule changed')
    for m in producer['stages'][sid]['modules']:
        a.f.need(c['inputs'][current[m]['path']]==producer['inputs'][current[m]['path']],'native H0-H3 source changed')
    for k in ['receipt_sha256','checked_module_receipts_sha256','descriptor_sha256','stage_tar_sha256','independent_review_sha256']:
        a.f.need(isinstance(row[k],str) and a.f.SHA256.fullmatch(row[k]),'missing H0-H3 origin digest')
    a.f.need(type(row['stage_tar_bytes']) is int and 0<row['stage_tar_bytes']<=c['object_artifact_max_bytes'],'H0-H3 tar bound differs')

def require_native_interface(c,sid,interface,a):
    if recovery(c) and (sid==H4_STAGE or (h5_retry(c) and sid in HSTAGES[:4])):
        pointer=c['native_higher_interface'];path='origin/higher-interface-identity.json'
        a.f.need(set(pointer)=={'path','bytes','sha256'} and pointer['path']==path and c['inputs'][path]=={'bytes':pointer['bytes'],'sha256':pointer['sha256']},'native H4 interface pointer differs')
        a.f.need((a.ROOT/path).stat().st_size==pointer['bytes'],'native H4 interface byte size differs')
        expected=a.f.pinned_load(a.ROOT/path,pointer['sha256'])
        a.f.need(interface==expected,'native H4 extended interface changed')
    return interface

def cache_extension(c,cache_rows,inventories,runtime_sha,a):
    lock=a.f.load_json(a.ROOT/'locks/cache-extension.json');base_lock=a.f.load_json(a.ROOT/'origin/base-required-modules.json');base_names={r['module'] for r in base_lock['modules']};extra=lock['extension_modules']
    a.f.need(lock['schema']=='exact-official-cache-extension-v1' and lock['base_module_count']==2786 and lock['full_module_count']==2805 and len(extra)==19 and not base_names.intersection(extra),'cache extension exact count differs')
    a.f.need(set(cache_rows)==base_names|set(extra) and lock['native_libraries_must_be_empty'] is True,'cache extension module union differs')
    a.f.need(lock['base_required_modules_sha256']==a.f.file_sha(a.ROOT/'origin/base-required-modules.json') and lock['base_interface_sha256']==a.f.file_sha(a.ROOT/'origin/base-interface-identity.json'),'cache extension base pins differ')
    a.f.need(lock['official_runtime_inventory_sha256']==runtime_sha==a.RUNTIME_INVENTORY_SHA and lock['official_mathlib_commit']==c['official_mathlib_commit'],'cache extension runtime/source commit differs')
    suffixes=['.olean','.ilean','.olean.server','.olean.private','.ir.sig','.ir'];a.f.need(lock['cached_modern_companion_suffixes']==suffixes,'cache companion convention differs')
    for m,r in extra.items():
        a.f.need({k:cache_rows[m][k] for k in ['module','package','path','sha256','modern_module']}=={k:r[k] for k in ['module','package','path','sha256','modern_module']},'cache extension source row differs')
        a.f.need(set(cache_rows[m]['companions'])=={'lib/lean/'+m.replace('.','/')+s for s in suffixes},'cache extension companion set differs')
        for value in cache_rows[m]['companions'].values():
            a.f.need(set(value)=={'bytes','sha256'} and type(value['bytes']) is int and 0<=value['bytes']<=512*1024**2 and isinstance(value['sha256'],str) and a.f.SHA256.fullmatch(value['sha256']),'extension companion is not exact regular byte/hash metadata')
        a.f.need(set(r['ordered_imports'])<=set(cache_rows)|{'Init'},'cache extension has unresolved import')
    base={m:cache_rows[m] for m in sorted(base_names)};old=a.cache_interface_identity(base,inventories,runtime_sha);full=a.cache_interface_identity(cache_rows,inventories,runtime_sha)
    bootstrap=bootstrap_companions(c,cache_rows,inventories,a)
    full={**full,'schema':'higher-external-interface-v1','approved_bootstrap_companion_rows_sha256':digest(bootstrap)}
    a.f.need(old==a.f.load_json(a.ROOT/'origin/base-interface-identity.json'),'old cache companions/runtime/native interface changed')
    a.f.need(old['all_package_native_library_files_sha256']==full['all_package_native_library_files_sha256']==digest({}),'native library addition is forbidden')
    cert={'schema':'verified-official-cache-extension-v1','base_interface_sha256':digest(old),'full_interface_sha256':digest(full),'base_interface':old,'full_interface':full,'runtime_inventory_sha256':runtime_sha,'official_mathlib_commit':c['official_mathlib_commit'],'extension_lock_sha256':a.f.file_sha(a.ROOT/'locks/cache-extension.json'),'base_module_count':2786,'extension_module_count':19,'full_module_count':2805,'extension_companion_rows':{m:cache_rows[m] for m in sorted(extra)},'all_old_companions_identical':True,'native_library_rows':{},'approved_bootstrap_companions':bootstrap}
    return base,old,full,cert
def validate_cache_sources(c,work,before,a):
    lock=a.f.load_json(a.ROOT/'locks/cache-extension.json')
    for m,row in lock['approved_bootstrap_modules'].items():
        actual=before[row['package']]['files'][row['source_path']]
        a.f.need(actual['kind']=='regular' and actual['bytes']==row['source_bytes'] and actual['sha256']==row['source_sha256'] and actual['git_blob']==row['source_git_blob'],'bootstrap source differs from approved official pin')
    for m,row in lock['extension_modules'].items():
        actual=before['mathlib']['files'][row['path']]
        a.f.need(actual['kind']=='regular' and actual['bytes']==row['bytes'] and actual['sha256']==row['sha256'] and actual['git_blob']==row['official_git_blob'],'extension source differs from official commit')
        parsed=a.header_parser.header((work/'packages/mathlib'/row['path']).read_bytes())
        a.f.need(parsed['modern'] and not parsed['prelude'] and [x['module'] for x in parsed['imports']]==row['ordered_imports'],'extension actual import header differs')
def terminal_receipt(result,commands,rows,receipts,audits,final,a):
    a.f.need(result.get('proof_scope')=='higher-dimension-sources-and-c-free-endpoints' and 'conditional_C_remains_explicit' not in result and result['higher_endpoints_have_no_C_premise'] is True and result['all_dimension_uniform_proof_certified'] is False and result['final_C_proof_certified'] is False and result['unconditional_monotile_proof_certified'] is False,'higher terminal scope differs')
    a.require_success_commands(commands)
    names=[r['module'] for r in rows];expected=[phase+'-'+m for m in names for phase in ['compile','check']]
    actual=[r['name'] for r in commands if r['name'].startswith(('compile-','check-')) and not r['name'].startswith(('compile-auditor-','check-auditor-'))]
    a.f.need(actual==expected and [r['module'] for r in receipts]==names and all(r['checker_passed'] is True for r in receipts),'higher ordered checker coverage differs')
    a.f.need(audits==({'higher_physical_endpoints':True} if final else {}),'higher raw audit missing or premature')
def validate_current_evidence(c,evidence,result,commands,a):
    """Reconstruct the same complete argv profiles used for transported stages."""
    work=evidence.parent;runtime=work/'runtime';owned=a.f.load_json(a.ROOT/'locks/owned-sources.json');rows={r['module']:r for r in owned['sources']};required=a.f.load_json(a.ROOT/'locks/required-modules.json')['modules'];cached=a.f.load_json(evidence/'cached-build-inventory.json');cache_rows={}
    for r in required:
        prefix='lib/lean/'+r['module'].replace('.','/');suffixes=['.olean','.ilean']+(['.olean.server','.olean.private','.ir.sig','.ir'] if r['modern_module'] else [])
        cache_rows[r['module']]={**r,'companions':{prefix+s:cached[r['package']]['files'][prefix+s] for s in suffixes}}
    _,_,_,extension=cache_extension(c,cache_rows,cached,result['runtime_inventory_sha256'],a)
    a.f.need(a.f.file_sha(evidence/'cache-extension-admission.json')==result['cache_extension_receipt_sha256'] and a.f.load_json(evidence/'cache-extension-admission.json')==extension,'collector cache extension certificate differs')
    pins=a.f.load_json(a.ROOT/'locks/dependencies.json')['packages'];sid=result['stage_id']
    expected={'producer_work':str(work),'runtime':runtime,'contract':c,'dependency_pins':pins,'cache_rows':cache_rows,'cache_search':[str(work/'packages'/p['name']/'.lake/build/lib/lean') for p in pins],'stage_rows':[rows[m] for m in c['stages'][sid]['modules']],'stage_id':sid}
    a.transport.validate_commands(commands,evidence,expected,a)
    validate_audit_evidence(c,evidence,result,a)
    final=a.f.load_json(evidence/'fresh-owned-objects.json')['files'];stage=c['stages'][sid]
    receipts=a.transport._json_lines(evidence/'owned-modules.jsonl')
    validate_current_imports(c,sid,receipts,final,rows,cache_rows,runtime,a)

def auditor_specs(c,work,runtime,search,a):
    specs=[]
    def add(name,argv,env,sources,writable,cwd,seconds):
        specs.append({'name':name,'argv':a.sandbox(argv,runtime=runtime,sources=sources,writable=writable,cwd=cwd,env=env),'cwd':str(work),'requested_timeout_seconds':seconds,'max_rss_bytes':8*a.GIB,'allow_new_sessions':True})
    for name,object_root,is_reference in [('AuditHigherPhysicalEndpoints',work/'auditor-objects',False),('HigherInspectorControl',work/'auditor-objects',False),('HigherPhysicalReference',work/'reference-objects',True)]:
        env=a.safe_env(runtime,work/'home',work/'tmp');env['LEAN_PATH']=':'.join([str(object_root),*(list(map(str,search)) if is_reference else []),str(runtime/'lib/lean')])
        sources=[work/'auditors',object_root]+([work/'packages'] if is_reference else [])
        staging=work/'quarantine'/name
        argv=[runtime/'bin/lean','-j1','-M4096','-Dcompiler.postponeCompile=false','-o',staging/(name+'.olean'),'-i',staging/(name+'.ilean'),'-c',staging/(name+'.c'),work/'auditors'/(name+'.lean')]
        add('compile-auditor-'+name,argv,env,sources,[staging,work/'home',work/'tmp'],work/'auditors',180)
        add('check-auditor-'+name,[runtime/'bin/leanchecker',name],env,sources,[work/'home',work/'tmp'],work/'auditors',120)
    env=a.safe_env(runtime,work/'home',work/'tmp');env['MATHLIB_CACHE_DIR']=str(work/'cache');env['LEAN_PATH']=':'.join(map(str,[work/'auditor-objects',work/'reference-objects',work/'objects',*map(Path,search),runtime/'lib/lean']))
    add('audit-AuditHigherPhysicalEndpoints',[runtime/'bin/lean','-j1','-M5120' if raw_heap5120(c) else '-M4096','--run',work/'auditors/AuditHigherPhysicalEndpoints.lean'],env,[work/'auditors',work/'auditor-objects',work/'reference-objects',work/'objects',work/'packages'],[work/'home',work/'tmp'],work/'auditors',c['auditor_timeout_seconds'])
    if raw_as24(c):specs[-1]['address_space_bytes']=command_address_space_bytes(c,specs[-1]['name'],a)
    for row in specs:row['argv']=list(map(str,row['argv']))
    return specs

def audit_output(transcript,a):
    lines=transcript.splitlines();a.f.need(len(lines)==3 and lines[-1]=='HIGHER_PHYSICAL_ENDPOINT_AUDIT_PASSED','higher auditor output missing, extra or incomplete')
    records=[];models=['SparseMonotiles.'+n for n in ['Point','IsTiling','translate','IsPeriod','HasTiling','IsAperiodic','IsAperiodicMonotile']]
    for i,line in enumerate(lines[:2]):
        row=a.f.parse_json(line.encode());expected={'schema':'higher-physical-endpoint-audit-v1','status':'pass','mode':'higher-only','target':TARGETS[i],'module':'ClarkSeed.PhysicalDimensions','reference_module':'HigherPhysicalReference','reference_template':'HigherPhysicalReference.'+('ExpectedGeFive' if i==0 else 'ExpectedGeThreeNeFour'),'model_module':'SparseMonotiles.Model','model_definitions':models,'level_params':[],'explicit_binders':['d','hd'] if i==0 else ['d','hd','hne'],'explicit_hypotheses':['5 ≤ d'] if i==0 else ['3 ≤ d','d ≠ 4'],'raw_type_equal':True,'raw_model_equal':True,'closed_type_and_proof':True,'selected_declaration_ownership':True,'exact_reference_owned_set':True,'trust_level':0,'plugins_enabled':False,'extensions_loaded':False}
        a.f.need(set(row)==set(expected)|{'axioms'},'higher audit record fields differ')
        for k,v in expected.items():a.f.need(type(row[k]) is type(v) and row[k]==v,'higher audit field differs: '+k)
        xs=row['axioms'];a.f.need(isinstance(xs,list) and all(isinstance(x,str) for x in xs) and len(xs)==len(set(xs)) and set(xs)<=a.ALLOWED_AXIOMS,'higher axiom set differs')
        records.append(row)
    return records

def prepare_auditors(c,work,runtime,search,command,a):
    import shutil
    specs=auditor_specs(c,work,runtime,search,a);maps={'auditor-objects':{},'reference-objects':{}}
    for index,(name,root) in enumerate([('AuditHigherPhysicalEndpoints',work/'auditor-objects'),('HigherInspectorControl',work/'auditor-objects'),('HigherPhysicalReference',work/'reference-objects')]):
        a.f.need(shutil.disk_usage(work).free>=c['minimum_free_disk_bytes'],'insufficient disk before independent audit source')
        staging=work/'quarantine'/name;staging.mkdir()
        spec=specs[index*2];out,_=command(spec['name'],spec['argv'],seconds=spec['requested_timeout_seconds'],rss=spec['max_rss_bytes'],allowed_sessions=True)
        if name=='HigherInspectorControl':
            validate_control_output(out.read_text(),a)
        maps[root.name]=a.admit_quarantine(staging,root,name,maps[root.name],64*1024**2);shutil.rmtree(staging)
        spec=specs[index*2+1];command(spec['name'],spec['argv'],seconds=spec['requested_timeout_seconds'],rss=spec['max_rss_bytes'],allowed_sessions=True)
        a.verify_owned_final(root,maps[root.name],64*1024**2)
    verify_auditor_maps(work,maps,a)
    a.write_json(work/'evidence/independent-auditor-objects.json',maps)
    return maps

def run_auditors(c,work,runtime,search,env,command,a):
    spec=auditor_specs(c,work,runtime,search,a)[-1]
    ir_path='objects/SparseMonotiles/CoarseContactCertificates5SymmetryData.ir'
    expected={'bytes':1054344,'sha256':'c23815bcc4aa90a6789c65b76c996848cab3178cde51504fe42b3d352f1c858d'}
    observation={'schema':'higher-h5-ir-predispatch-observation-v1','path':ir_path,'expected_h0':expected,
      'observation_phase':'immediately_before_raw_audit_dispatch','monotonic_started_seconds':a.time.monotonic(),
      'observed':None,'matches_expected_h0':None,'refusal_reason':None}
    watchdog=a._ACTIVE_WATCHDOG;reason='watchdog_unavailable'
    observation['aggregate_deadline_monotonic_seconds']=watchdog.deadline if watchdog is not None else None
    identity=lambda st:(st.st_dev,st.st_ino,st.st_mode,st.st_nlink,st.st_size,st.st_mtime_ns,st.st_ctime_ns)
    try:
        if watchdog is None:raise ValueError(reason)
        reason='aggregate_deadline_expired';watchdog.check()
        ir=work/ir_path;reason='path_alias_refused';a.f.no_symlink_path(ir)
        reason='not_regular_single_link';before=ir.lstat()
        if not a.stat.S_ISREG(before.st_mode) or before.st_nlink!=1:raise ValueError(reason)
        observation['observed']={'bytes':before.st_size,'sha256':None}
        reason='size_mismatch'
        if before.st_size!=expected['bytes']:
            observation['matches_expected_h0']=False;raise ValueError(reason)
        reason='open_refused';fd=a.os.open(ir,a.os.O_RDONLY|a.os.O_NOFOLLOW|a.os.O_NONBLOCK|a.os.O_CLOEXEC)
        try:
            reason='identity_changed'
            if identity(a.os.fstat(fd))!=identity(before):raise ValueError(reason)
            reason='aggregate_deadline_expired';watchdog.check()
            reason='bounded_read_failed';data=a.os.read(fd,expected['bytes']+1)
            reason='read_size_mismatch'
            if len(data)!=expected['bytes']:raise ValueError(reason)
            reason='identity_changed'
            if identity(a.os.fstat(fd))!=identity(before):raise ValueError(reason)
            reason='aggregate_deadline_expired';watchdog.check()
        finally:
            try:a.os.close(fd)
            except OSError:reason='close_failed';raise
        reason='path_alias_refused';a.f.no_symlink_path(ir)
        reason='identity_changed'
        if identity(ir.lstat())!=identity(before):raise ValueError(reason)
        reason='aggregate_deadline_expired';watchdog.check()
        observation['observed']['sha256']=hashlib.sha256(data).hexdigest()
        watchdog.check();observation['matches_expected_h0']=observation['observed']==expected
    except (OSError,ValueError):
        observation['refusal_reason']=reason
    observation['monotonic_ended_seconds']=a.time.monotonic()
    if watchdog is not None and (watchdog.expired or observation['monotonic_ended_seconds']>=watchdog.deadline):
        observation['refusal_reason']='aggregate_deadline_expired';observation['matches_expected_h0']=None
    a.write_json(work/'evidence/higher-h5-ir-predispatch-observation.json',observation)
    out,_=command(spec['name'],spec['argv'],seconds=spec['requested_timeout_seconds'],rss=spec['max_rss_bytes'],allowed_sessions=True)
    records=audit_output(out.read_text(),a);a.write_json(work/'evidence/higher-physical-endpoints-raw-audit.json',records)
    return {'higher_physical_endpoints':True}
def validate_extension_companion_files(c,work,a):
    import stat
    lock=a.f.load_json(a.ROOT/'locks/cache-extension.json')
    packages=a.f.load_json(a.ROOT/'locks/dependencies.json')['packages']
    required=a.f.load_json(a.ROOT/'locks/required-modules.json')['modules']
    provider_packages={r['package'] for r in required}|{r['package'] for r in lock['approved_bootstrap_modules'].values()}
    a.f.need(provider_packages<={p['name'] for p in packages},'cache provider package is not pinned')
    for pin in packages:
        root=work/'packages'/pin['name']/'.lake/build/lib/lean';a.f.no_symlink_path(root)
        for parent in root.parents:
            a.f.need(not parent.exists() or parent.is_dir(),'cache search root ancestor is not a directory: '+str(parent))
        if root.exists():
            a.f.need(root.is_dir(),'cache search root is not a directory: '+pin['name'])
        else:
            a.f.need(pin['name'] not in provider_packages,'required cache search root is absent: '+pin['name'])
    for m,r in {**lock['extension_modules'],**lock['approved_bootstrap_modules']}.items():
        for suffix in r.get('companion_suffixes',lock['cached_modern_companion_suffixes']):
            path=work/'packages'/r['package']/'.lake/build/lib/lean'/(m.replace('.','/')+suffix)
            a.f.no_symlink_path(path);st=path.lstat()
            a.f.need(stat.S_ISREG(st.st_mode) and st.st_nlink==1,'new cache companion must be a confined regular single-link file')

def bootstrap_companions(c,cache_rows,inventories,a):
    lock=a.f.load_json(a.ROOT/'locks/cache-extension.json');approved=lock['approved_bootstrap_modules']
    expected={'Cache.'+name for name in ['Cli','Env','Hashing','IO','Infra','Lean','Main','Marker','Query','Requests','Upload','Upload.Azure','Upload.Curl','Upload.Defs','Upload.Dest','Upload.Rclone','Upload.S3','Warning']}
    a.f.need(set(approved)==expected and all(row['package']=='mathlib' and row['source_path']==m.replace('.','/')+'.lean' and row['companion_suffixes']==['.olean','.ilean'] for m,row in approved.items()),'approved bootstrap provider set differs')
    providers={}
    for package,inv in inventories.items():
        for path,row in inv['files'].items():
            a.f.need(not ((path=='lib/lean' or path.startswith('lib/lean/')) and 'symlink' in row),'symlink below a cache search root is forbidden')
            if path.startswith('lib/lean/') and path.endswith('.olean'):
                m=path[len('lib/lean/'):].removesuffix('.olean').replace('/','.')
                a.f.need(m not in providers,'duplicate cached bootstrap/research provider');providers[m]=package
    wanted={m:r['package'] for m,r in cache_rows.items()}|{m:r['package'] for m,r in approved.items()}
    a.f.need(providers==wanted,'unlisted or missing cache/bootstrap .olean provider')
    result={}
    for m,r in approved.items():
        prefix='lib/lean/'+m.replace('.','/');companions={prefix+s:inventories[r['package']]['files'][prefix+s] for s in r['companion_suffixes']}
        for row in companions.values():a.f.need(set(row)=={'bytes','sha256'} and type(row['bytes']) is int and 0<=row['bytes']<=512*1024**2 and isinstance(row['sha256'],str) and a.f.SHA256.fullmatch(row['sha256']),'bootstrap companion must be regular byte/hash metadata')
        result[m]={'source_pin':r,'companions':companions}
    return result

def validate_audit_evidence(c,evidence,result,a):
    sid=result['stage_id'];preflight=sid in ['H0_common','H5_higher_assembly']
    a.f.need(result.get('independent_auditor_preflight_passed') is preflight,'higher helper preflight scope differs')
    if preflight:
        maps=a.f.load_json(evidence/'independent-auditor-objects.json')
        a.f.need(set(maps)=={'auditor-objects','reference-objects'} and set(maps['auditor-objects'])==a.module_outputs('AuditHigherPhysicalEndpoints')|a.module_outputs('HigherInspectorControl') and set(maps['reference-objects'])==a.module_outputs('HigherPhysicalReference'),'higher helper companion inventory differs')
        for rows in maps.values():
            for row in rows.values():a.f.need(set(row)=={'bytes','sha256'} and type(row['bytes']) is int and 0<=row['bytes']<=512*1024**2 and isinstance(row['sha256'],str) and a.f.SHA256.fullmatch(row['sha256']),'invalid helper companion metadata')
        a.f.need(sum(row['bytes'] for rows in maps.values() for row in rows.values())<=64*1024**2,'aggregate independent helper output exceeds unchanged cap')
        a.f.need(a.f.file_sha(evidence/'independent-auditor-objects.json')==result['independent_auditor_inventory_sha256'],'higher helper inventory digest differs')
        text=(evidence/'logs/compile-auditor-HigherInspectorControl.stdout').read_text()
        validate_control_output(text,a)
    if sid==c['final_stage']:
        records=audit_output((evidence/'logs/audit-AuditHigherPhysicalEndpoints.stdout').read_text(),a)
        a.f.need(records==a.f.load_json(evidence/'higher-physical-endpoints-raw-audit.json'),'higher raw audit receipt differs from complete stdout')

def validate_current_imports(c,sid,receipts,final,rows,cache_rows,runtime,a):
    stage=c['stages'][sid];ancestors={m for dep in stage['admitted_stages'] for m in c['stages'][dep]['modules']}
    prior={name:final[name] for m in ancestors for name in a.module_outputs(m)};accepted=set(ancestors)
    a.f.need([r['module'] for r in receipts]==stage['modules'],'current import receipt coverage differs')
    for record,m in zip(receipts,stage['modules']):
        a.f.need(set(record)=={'module','source_sha256','ordered_imports','outputs','compiler_command','checker_command','checker_passed','proof_scope'} and record['proof_scope']=='higher-dimension-sources-and-c-free-endpoints','higher module receipt scope/fields differ')
        imports=a.direct_import_receipt(rows[m],rows,accepted,prior,cache_rows,runtime)
        a.f.need(record['ordered_imports']==imports,'current higher import receipt differs')
        accepted.add(m);prior.update(record['outputs'])
    a.f.need(prior==final,'current higher accepted inventory differs')

def validate_control_output(text,a):
    a.f.need(text.splitlines()==['PASS '+label for label in CONTROL_LABELS]+['HIGHER_INSPECTOR_CORE_CONTROL_PASSED'],'exact core inspector control output differs')

def verify_auditor_maps(work,maps,a):
    a.f.need(set(maps)=={'auditor-objects','reference-objects'},'independent helper roots differ')
    a.f.need(sum(row['bytes'] for rows in maps.values() for row in rows.values())<=64*1024**2,'aggregate independent helper output exceeds unchanged cap')
    for name,expected in maps.items():a.verify_owned_final(work/name,expected,64*1024**2)

VISIBILITY_MODULES={'SparseMonotiles.CarrierHierarchyParent','SparseMonotiles.CarrierHierarchyCoarsening'}
def reconstruct_visibility_source(data,row,a):
    a.f.need(len(data)==row['variant_bytes'] and a.f.sha(data)==row['variant_sha256'],'visibility variant bytes differ')
    expected=b'set_option backward.privateInPublic true in\n';insertions=row['insertions'];a.f.need(len(insertions)==2,'visibility scope count differs')
    current=data
    for i,r in reversed(list(enumerate(insertions))):
        offset=r['original_byte_offset']+i*len(expected)
        a.f.need(r['insert_utf8'].encode()==expected and current[offset:offset+len(expected)]==expected,'visibility insertion position/bytes differ')
        current=current[:offset]+current[offset+len(expected):]
    a.f.need(len(current)==row['baseline_bytes'] and a.f.sha(current)==row['baseline_sha256'],'visibility original body does not reconstruct exactly')
    for r in insertions:
        offset=r['original_byte_offset'];a.f.need(current[offset:].startswith(r['anchor'].encode()) and current[:offset].count(b'\n')+1==r['original_line'],'visibility declaration anchor differs')
    return current

def validate_visibility_sources(c,source_root,fresh,a):
    path=a.ROOT/'locks/higher-visibility-variants.json';a.f.need(a.f.file_sha(path)==c['higher_visibility_variant_lock_sha256'],'visibility lock differs')
    lock=a.f.load_json(path);variants={r['module']:r for r in lock['files']};lineage={r['module']:r for r in a.f.load_json(a.ROOT/'locks/higher-source-lineage.json')['sources']}
    a.f.need(set(variants)==VISIBILITY_MODULES and set(lineage)==fresh and lock['added_commands']==4 and lock['added_bytes']==176 and lock['global_option_enabled'] is False and lock['private_keywords_removed'] is False,'visibility exact scope differs')
    for m in sorted(fresh):
        data=(source_root/'src'/(m.replace('.','/')+'.lean')).read_bytes()
        if m in variants:data=reconstruct_visibility_source(data,variants[m],a)
        a.f.need(a.f.sha(data)==lineage[m]['proposed_modern_sha256'],'higher source differs from frozen port plus exact visibility overlay')
