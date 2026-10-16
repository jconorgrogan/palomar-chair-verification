"""Strict higher-only schema. Legacy contracts and native receipts retain their identity."""
from pathlib import Path
import hashlib,json,re
SCHEMA='higher-dimension-staged-replay-v1'
SUCCESS='HIGHER_DIMENSIONS_THREE_AND_GE_FIVE_RAW_AUDITED'
STAGE_SUCCESS='CHECKED_HIGHER_DIMENSION_STAGE_COMPLETED'
HSTAGES=['H0_common','H1_coarse_contacts','H2_forward_contacts','H3_contact_binding','H4_product_geometry','H5_higher_assembly']
OLD=['F0_common','F3_product_geometry']
COUNTS=[44,221,82,460,304,27]
CHECKS={'SparseMonotiles.CoarseContactCertificates5PackedRows':(240,'914a3ddef7a5674a9bb2f7a5725b30521c80bdb1f988663b1a167e89bf5660bf',163.708),'SparseMonotiles.CoarseContactCertificates5SymmetryCoverage':(720,'283a5e1d00ead57526fd7bb70227b1cb1b77d12aba41bdee54d8d0236e592816',572.843)}
CONTROL_LABELS=['exact mapped model definition', 'renamed native model constant rejected', 'extra reference model constant rejected', 'nested extra reference model constant rejected', 'changed HasTiling predicate rejected', 'changed HasTiling existential universe rejected', 'missing HasTiling existential rejected', 'exact collection-period surrogate', 'collection period changed to union period rejected', 'model extra universe rejected', 'unsafe model rejected', 'open model body rejected', 'exact quantified endpoint surrogate', 'dimension quantifier removed rejected', 'dimension binder renamed rejected', 'dimension binder visibility changed rejected', 'dimension lower bound changed rejected', 'extra hypothesis rejected', 'axiom substituted for theorem rejected', 'three standard axioms accepted', 'sorryAx rejected', 'extra axiom rejected', 'fixed seven model names and two endpoints']
TARGETS=['ClarkSeed.exists_physical_aperiodic_monotile_of_ge_five','ClarkSeed.exists_physical_aperiodic_monotile_of_ge_three_ne_four']
def digest(value):return hashlib.sha256((json.dumps(value,sort_keys=True,indent=2)+'\n').encode()).hexdigest()
def profile(c,a):
    expected={'schema':SCHEMA,'owned_module_count':1433,'fresh_higher_module_count':1138,'retained_historical_module_count':295,'higher_mathematical_closure_count':1154,'retained_context_outside_higher_closure_count':279,'lean_heap_mib':4096,'diagnostic_rss_gib':8,'diagnostic_timeout_seconds':180,'check_timeout_seconds':120,'outer_timeout_minutes':330,'aggregate_command_deadline_seconds':19200,'maximum_parallel_jobs':4,'stage_count':8,'workflow_job_count':6,'workflow_aggregate_seconds':115200,'workflow_outer_runner_minutes':1980,'object_artifact_max_bytes':4*a.GIB,'object_artifact_zip_max_bytes':4*a.GIB+4*1024**2,'producer_job_log_max_bytes':16*1024**2,'transport_timeout_seconds':1800,'failure_evidence_grace_seconds':5,'owned_output_max_bytes':6*a.GIB,'owned_source_max_bytes':32*1024**2,'evidence_max_bytes':124*1024**2,'aggregate_log_max_bytes':64*1024**2,'per_command_log_max_bytes':1024**2,'minimum_free_disk_bytes':1536*1024**2,'auditor_timeout_seconds':600,'cache_module_count':2805}
    for k,v in expected.items():a.f.need(type(c.get(k)) is type(v) and c[k]==v,'higher profile differs: '+k)
    for k,v in {'all_dimension_uniform_proof_certified':False,'final_C_proof_certified':False,'unconditional_monotile_proof_certified':False,'higher_endpoints_have_no_C_premise':True,'fresh_external_source_rebuild':False,'owned_objects_from_prior_runs_allowed':True,'owned_objects_from_same_run_checked_stages_allowed':True,'fresh_research_modules_exactly_once':True}.items():a.f.need(c.get(k) is v,'higher claim/trust differs: '+k)
    a.f.need(c.get('proof_scope')=='higher-dimension-sources-and-c-free-endpoints' and c.get('independent_auditor_preflight_stages')==['H0_common','H5_higher_assembly'],'higher proof/preflight scope differs')
    a.f.need(c.get('higher_reference_static_review_sha256')=='392e108004b6feb0726e0de8d48e84debb5d666be280fe6a00d484510f2688dd','higher reference review differs')
    for name,pin in {'AuditHigherPhysicalEndpoints':(10780,'ba9a502d5f121719b7fff10c73d3bf9cfa6857a0f2a42e99b36d39051b64af13'),'HigherPhysicalReference':(2138,'bcf383a13467b15ce7b55e1e4a171bab4f86439e696b0a30ebd13769236c15ea'),'HigherInspectorControl':(6975,'017aadfea7927f7957a5143bcfa8f93af37214ef56f62881e8bddb05af34e482')}.items():
        a.f.need(c['inputs'].get('auditors/'+name+'.lean')=={'bytes':pin[0],'sha256':pin[1]},'higher independent source pin differs')
    a.f.need(c.get('higher_visibility_variant_lock_sha256')=='3621fde9a869de3f0fc4f3f312c142e13df0d5672f34b1402b10cf9b99f475be' and c.get('higher_visibility_independent_review_sha256')=='a583afc1d571b60f41a349d0797fd8f373ac190b92598ec35ee85d2777338373' and c.get('higher_visibility_actual_elaboration_pending') is True,'higher visibility provenance differs')
    a.f.need(c['execution_stages']==HSTAGES and c['locked_origin_stages']==OLD and c['higher_endpoints']==TARGETS and c['higher_target']=='ClarkSeed.PhysicalDimensions','higher execution or theorem scope differs')
    a.f.need('module_compile_arguments' not in c and 'conditional_C_remains_explicit' not in c,'higher replay has an unapproved compiler option or misleading C premise field')
    wanted={m:{'proposed_check_timeout_seconds':v[0],'source_sha256':v[1],'observed_historical_checker_seconds':v[2]} for m,v in CHECKS.items()}
    a.f.need(c.get('module_checker_timeout_exceptions')==wanted,'checker exceptions differ')
    for m,v in CHECKS.items():a.f.need(c['inputs']['src/'+m.replace('.','/')+'.lean']['sha256']==v[1],'checker exception source differs')
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
    original_owned=a.f.load_json(a.ROOT/'origin/producer-owned-sources.json');oldrows={r['module']:r for r in original_owned['sources']};current={r['module']:r for r in a.f.load_json(a.ROOT/'locks/owned-sources.json')['sources']}
    for sha,path in paths.items():
        p=c['producer_contracts'][sha];a.f.need(p=={'path':path,'sha256':sha,'bytes':(a.ROOT/path).stat().st_size} and c['inputs'][path]=={'bytes':p['bytes'],'sha256':sha},'higher producer pointer differs')
        producer=a.f.pinned_load(a.ROOT/path,sha);a.validate_diagnostic_profile(producer);a.validate_stage_plan(producer);producers[sha]=producer
        for name in ['lean-toolchain','locks/dependencies.json','locks/cache-client.json']:a.f.need(c['inputs'][name]==producer['inputs'][name],'higher immutable runtime/cache pin differs')
        a.f.need(a.f.file_sha(a.ROOT/'origin/producer-owned-sources.json')==producer['inputs']['locks/owned-sources.json']['sha256'],'original source graph changed')
        a.f.need(a.f.file_sha(a.ROOT/'origin/base-required-modules.json')==producer['inputs']['locks/required-modules.json']['sha256'],'original cache graph changed')
    a.f.need(set(c['producer_contracts'])==set(paths),'higher unknown producer contract')
    p=c['origin_lock'];a.f.need(p['path']=='origin/locked-origins.json' and c['inputs'][p['path']]=={'bytes':p['bytes'],'sha256':p['sha256']},'higher origin pointer differs')
    lock=a.f.pinned_load(a.ROOT/p['path'],p['sha256']);a.f.need(lock['schema']=='higher-exact-mixed-origin-lock-v1' and lock['producer_contracts']==list(paths) and set(lock['stages'])==set(OLD),'higher origin set differs')
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
    return selected,lock['stages']
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
    add('audit-AuditHigherPhysicalEndpoints',[runtime/'bin/lean','-j1','-M4096','--run',work/'auditors/AuditHigherPhysicalEndpoints.lean'],env,[work/'auditors',work/'auditor-objects',work/'reference-objects',work/'objects',work/'packages'],[work/'home',work/'tmp'],work/'auditors',c['auditor_timeout_seconds'])
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
    out,_=command(spec['name'],spec['argv'],seconds=spec['requested_timeout_seconds'],rss=spec['max_rss_bytes'],allowed_sessions=True)
    records=audit_output(out.read_text(),a);a.write_json(work/'evidence/higher-physical-endpoints-raw-audit.json',records)
    return {'higher_physical_endpoints':True}
def validate_extension_companion_files(c,work,a):
    import stat
    lock=a.f.load_json(a.ROOT/'locks/cache-extension.json')
    for pin in a.f.load_json(a.ROOT/'locks/dependencies.json')['packages']:
        root=work/'packages'/pin['name']/'.lake/build/lib/lean';a.f.no_symlink_path(root)
        a.f.need(root.is_dir(),'cache search root is not a directory')
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
