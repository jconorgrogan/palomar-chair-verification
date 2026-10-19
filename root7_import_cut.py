#!/usr/bin/env python3
"""Inactive two-file import-cut experiment; source-reviewed only until authorized."""
from __future__ import annotations
import time
ENTRY_TIME=time.monotonic()
import argparse,hashlib,importlib.util,json,os,re,shutil,stat,sys
from pathlib import Path
ROOT=Path(__file__).absolute().parent
PRIMITIVE_SHA='87c6c61f67bdf42cf7b8dece9ac343021942fb3c7e750668c2aba253d7687932'
p=ROOT/'inherited_primitives.py'
for q in [p,*p.parents]:
    if q.is_symlink():raise RuntimeError('symlink trusted helper ancestry')
if p.stat().st_size>50000 or hashlib.sha256(p.read_bytes()).hexdigest()!=PRIMITIVE_SHA:raise RuntimeError('inherited primitive pin differs')
spec=importlib.util.spec_from_file_location('root7_inherited',p);d=importlib.util.module_from_spec(spec);sys.modules[spec.name]=d;spec.loader.exec_module(d)
a=d.a;f=d.f;VENDOR=d.VENDOR;GIB=1024**3
SCHEMA='palomar-root7-import-cut-smoke-v1';SUCCESS='ROOT7_IMPORT_CUT_FOCUSED_TEST_PASSED'
PART32='SpectreFinite.RadiusFiveRoot7Part32';COVER='SpectreFinite.RadiusFiveRoot7Cover'
FIXTURES=['baseline','identical','value','type','axiom','inventory','native']
FIXTURE_CASES=['identical','value','type','inventory','axiom','native']
FIXTURE_REJECTIONS={'value':'DECLARATION_FIELDS_DIFFER','type':'TYPE_OR_KIND_DIFFERS','inventory':'INTRODUCED_INVENTORY_DIFFERS','axiom':'UNPERMITTED_AXIOM','native':'ENVIRONMENT_SUBTRACTION_SIZE'}
LIMITS={'aggregate_command_deadline_seconds':7200,'outer_timeout_minutes':130,
 'diagnostic_timeout_seconds':180,'check_timeout_seconds':120,'lean_heap_mib':4096,
 'address_space_bytes':12*GIB,'rss_tree_bytes':8*GIB,'max_created_file_bytes':512*1024**2,
 'per_command_log_max_bytes':1024**2,'aggregate_log_max_bytes':64*1024**2,'evidence_max_bytes':124*1024**2,
 'upload_max_bytes':128*1024**2,'collection_reserve_bytes':4*1024**2,'owned_source_max_bytes':32*1024**2,
 'owned_output_max_bytes':6*GIB,'minimum_free_disk_bytes':1536*1024**2,'failure_evidence_grace_seconds':5}
EVIDENCE_NAMES={'result.json','commands.jsonl','last_command.json','source-extraction.json','runtime-inventory.json',
 'read-only-boundary-preflight.json','owned-modules.jsonl','fresh-owned-objects.json','capture-collection-scope.json',
 'part32-views.json','interface-comparison.json','cover-axioms.json','early-fixtures.json'}
TERMINAL=EVIDENCE_NAMES-{'result.json','last_command.json','capture-collection-scope.json'}


def validate_contract(c,reviewed=False):
 f.need(c['schema']==SCHEMA and c['limits']==LIMITS,'profile differs')
 f.need(c['owned_module_count']==388 and len(c['module_order'])==len(set(c['module_order']))==388,'source count differs')
 f.need(c['runtime_roots']==['Init','Init.Data.List.OfFn'] and c['cache_roots']==[],'runtime-only boundary differs')
 f.need(c['publication_branch']=='verify/palomar-root7-import-cut-generated-20261019','branch differs')
 f.need(c['full_official_verification_claimed'] is False and c['restore_project_objects'] is False,'scope differs')
 f.need(c['owned_source_max_bytes']==LIMITS['owned_source_max_bytes'],'source bound differs')
 v=c['prerequisite_views'];f.need(len(v['original'])==len(set(v['original']))==325 and len(v['candidate'])==len(set(v['candidate']))==286,'view cardinality differs')
 f.need(set(v['candidate'])<=set(v['original']) and PART32 not in v['original'],'view set differs')
 f.need(c['module_order'][:325]==v['original'] and c['module_order'][325]==PART32 and c['module_order'][-1]==COVER,'fresh prefix ordering differs')
 f.need(len(c['explicit_part32_declarations'])==239 and sum(r['kind']=='def' for r in c['explicit_part32_declarations'])==10 and sum(r['kind']=='theorem' for r in c['explicit_part32_declarations'])==229,'explicit declaration inventory differs')
 f.need(len(c['explicit_cover_declarations'])==213 and all(r['kind']=='theorem' for r in c['explicit_cover_declarations']) and any(r['name']=='SpectreFinite.HexSearch.RadiusFive.root7_table_cover' for r in c['explicit_cover_declarations']),'explicit Cover inventory differs')
 f.need(c['fixture_cases']==FIXTURE_CASES,'fixture case plan differs')
 f.need(c['recorded_command_count']==796 and c['sum_command_timeout_seconds']==119580,'finite envelope differs')
 if reviewed:
  f.need(c['review_status']=='reviewed_for_execution','INACTIVE: independent review required')
  f.need(type(c.get('independent_driver_review_sha256')) is str and f.SHA256.fullmatch(c['independent_driver_review_sha256']),'driver review pin missing')


def validate_workflow(c,contract_sha):
 data=(ROOT/'.github/workflows/palomar-root7-import-cut-smoke.yml').read_bytes()
 active=c['review_status']=='reviewed_for_execution';token=contract_sha.encode() if active else b'0'*64
 guard=b'    if: ${{ true }}\n' if active else b'    if: ${{ false }}\n'
 f.need(data.count(b'--contract-sha256 '+token)==2 and data.count(guard)==1,'workflow slots differ')
 normalized=data.replace(b'--contract-sha256 '+token,b'--contract-sha256 '+b'0'*64).replace(guard,b'    if: ${{ false }}\n')
 f.need(c['workflow_template_sha256']=='95ad46508ed59173158f8b90750ae988c9f013efc484082897c4b6b83f0bfe63' and f.sha(normalized)==c['workflow_template_sha256'],'normalized workflow differs')


def validate_inputs(c):
 expected=set(c['distribution_files']);files={}
 f.need(expected==(set(c['inputs'])-{p for p in c['inputs'] if p.startswith('src/')})|{'smoke-contract.json','owned-sources.tar.gz','.github/workflows/palomar-root7-import-cut-smoke.yml'},'distribution lock differs')
 for parent,dirs,names in os.walk(ROOT,followlinks=False):
  if Path(parent)==ROOT and '.git' in dirs:dirs.remove('.git')
  for n in dirs:f.need(not (Path(parent)/n).is_symlink(),'distribution symlink')
  for n in names:
   p=Path(parent)/n;s=p.lstat();f.need(stat.S_ISREG(s.st_mode) and s.st_nlink==1,'nonregular input');files[p.relative_to(ROOT).as_posix()]=p
 f.need(set(files)==expected,'unexpected or missing distribution file')
 validate_workflow(c,f.sha(f.json_bytes(c)))
 for rel,row in c['inputs'].items():
  f.safe_rel(rel)
  if rel.startswith('src/'):continue
  p=files[rel];f.need(p.stat().st_size==row['bytes'] and f.file_sha(p)==row['sha256'],'protected input differs: '+rel)


def validate_graph(c,work):
 rows=c['modules'];owned={r['module']:r for r in rows};seen=set();external=set()
 f.need([r['module'] for r in rows]==c['module_order'],'graph order differs')
 for row in rows:
  m=row['module'];path='src/'+m.replace('.','/')+'.lean'
  f.need(row['path']==path and c['inputs'][path]=={'bytes':row['bytes'],'sha256':row['sha256']},'source row differs')
  header=a.header_parser.header((work/'source-input'/path).read_bytes());imports=[r['module'] for r in header['imports']]
  f.need(header['modern'] and not header['prelude'] and imports==row['ordered_imports'],'source imports differ')
  for dep in [*imports,'Init']:
   f.need(dep in seen or dep in c['runtime_roots'],'unresolved dependency')
   if dep not in owned:external.add(dep)
  seen.add(m)
 f.need(external==set(c['runtime_roots']),'external boundary differs')
 def closure(m,original=False):
  seen=set()
  def visit(n):
   if n not in owned or n in seen:return
   seen.add(n)
   deps=owned[n]['ordered_imports']
   if n==PART32 and original:deps=['SpectreFinite.RadiusFiveRoot7Part31' if x=='SpectreFinite.RadiusFiveRoot7Part1' else x for x in deps]
   for x in deps:visit(x)
  visit(m);return seen
 f.need(closure(COVER)==set(owned),'cover closure differs')
 for mode in ['original','candidate']:f.need(closure(PART32,mode=='original')-{PART32}==set(c['prerequisite_views'][mode]),'Part32 exact view differs')
 return owned


def command_order(c):
 out=['bwrap-preflight','read-only-committed-root-preflight','check-interface-api']
 out+=['compile-fixture-'+v for v in FIXTURES];out+=['check-interface-fixture-'+v for v in FIXTURE_CASES]
 for m in c['module_order']:
  if m==PART32:out+=['compile-original-'+m,'check-original-'+m]
  out+=['compile-'+m,'check-'+m]
  if m==PART32:out+=['check-interface-part32']
 out+=['check-cover-axioms'];return out


def command_spec(c,work,name,cache_modules=()):
 runtime=work/'runtime';env=a.safe_env(runtime,work/'home',work/'tmp');env['LEAN_PATH']=str(work/'objects')+':'+str(runtime/'lib/lean')
 def sand(argv,sources,writable,cwd,seconds):
  return {'name':name,'argv':list(map(str,a.sandbox(argv,runtime=runtime,sources=sources,writable=writable,cwd=cwd,env=env))), 'cwd':str(work),'env':dict(env),'requested_timeout_seconds':seconds,'allowed_sessions':True}
 if name=='bwrap-preflight':return sand(['/bin/true'],[],[work/'home',work/'tmp'],work/'tmp',30)
 if name=='read-only-committed-root-preflight':
  src=work/'preflight-read-only';out=work/'preflight-quarantine';script='test -r "$1/predecessor"; if printf bad > "$1/predecessor"; then exit 11; fi; if chmod 0600 "$1/predecessor"; then exit 12; fi; if mkdir "$1/SpectreGeometry"; then exit 13; fi; printf allowed > "$2/output"'
  return sand(['/bin/sh','-eu','-c',script,'readonly-boundary-control',src,out],[src],[out,work/'home',work/'tmp'],out,30)
 if name.startswith('compile-fixture-'):
  v=name[len('compile-fixture-'):];f.need(v in FIXTURES,'unknown fixture')
  src=work/'fixtures'/v;out=work/'fixture-objects'/v;env['LEAN_PATH']=str(runtime/'lib/lean')
  return sand(d.compile_argv(runtime,src,out,'Fixture'),[src],[out,work/'home',work/'tmp'],src,180)
 if name.startswith('check-interface-') or name=='check-cover-axioms':
  env['LEAN_PATH']=str(runtime/'lib/lean');tool=work/'tools/ImportCut.lean';sources=[work/'tools']
  if name=='check-interface-api':args=['self-test'];seconds=180
  elif name.startswith('check-interface-fixture-'):
   v=name[len('check-interface-fixture-'):];f.need(v in FIXTURE_CASES,'unknown fixture case');args=['fixture',v,work/'fixture-objects',runtime];sources+=[work/'fixture-objects'];seconds=180
  elif name=='check-interface-part32':args=['compare',work/'view-original',work/'view-candidate',runtime];sources+=[work/'view-original',work/'view-candidate'];seconds=180
  elif name=='check-cover-axioms':args=['cover',work/'objects',runtime];sources+=[work/'objects'];seconds=120
  else:raise f.Rejected('unknown interface mode')
  return sand([runtime/'bin/lean','-j1','-M4096','-DElab.async=false','--run',tool,*args],sources,[work/'home',work/'tmp'],work/'tools',seconds)
 original=name.startswith(('compile-original-','check-original-'));phase='compile' if name.startswith('compile-') else 'check' if name.startswith('check-') else None
 f.need(phase is not None,'unknown command');m=name[len(phase)+len('-original-'):] if original else name[len(phase)+1:]
 f.need(m in c['module_order'] and (not original or m==PART32),'unknown module')
 src=work/'original-input' if original else work/'src';stage=work/'original-output' if original else work/'quarantine'/m
 view=work/('view-original' if original else 'view-candidate') if m==PART32 else work/'objects'
 env['LEAN_PATH']=str(view)+':'+str(runtime/'lib/lean')
 return sand(d.compile_argv(runtime,src,stage,m) if phase=='compile' else [runtime/'bin/leanchecker',m], [src,view],[stage,work/'home',work/'tmp'] if phase=='compile' else [work/'home',work/'tmp'],src,180 if phase=='compile' else 120)


def validate_command_spec(c,work,r,cache_modules=()):
 expected=command_spec(c,work,r['name'])
 for k in ['name','argv','cwd','env','requested_timeout_seconds']:f.need(r[k]==expected[k],'native command provenance differs: '+k)
 f.need(r['new_sessions_explicitly_allowed']==expected['allowed_sessions'],'session policy differs')
 f.need(r['limits']=={k:LIMITS[k] for k in ['address_space_bytes','rss_tree_bytes','max_created_file_bytes']} and r['max_log_bytes']==LIMITS['per_command_log_max_bytes'],'resource profile differs')
 f.need(type(r['effective_timeout_seconds']) is int and 0<r['effective_timeout_seconds']<=expected['requested_timeout_seconds'],'effective timeout differs')


def fixture_expected_output(case):
 f.need(type(case) is str and case in FIXTURE_CASES,'unknown fixture case')
 load=['FIXTURE_PHASE\t'+p for p in ['LOAD_BEGIN','PARTS_READY','BEFORE_IMPORT_BEGIN','BEFORE_IMPORT_DONE','AFTER_IMPORT_BEGIN','AFTER_IMPORT_DONE','LOAD_CHECKED']]
 lines=['FIXTURE_START\t'+case]
 if case=='native':
  lines+=load+['FIXTURE_PHASE\tNATIVE_CLASSIFICATION_BEGIN','FIXTURE_REJECTED\tnative\tENVIRONMENT_SUBTRACTION_SIZE','FIXTURE_PHASE\tNATIVE_CLASSIFICATION_PASSED']
 elif case=='axiom':
  lines+=load+['FIXTURE_PHASE\tAXIOM_TRAVERSAL_BEGIN','FIXTURE_PHASE\tAXIOM_TRAVERSAL_DONE','FIXTURE_REJECTED\taxiom\tUNPERMITTED_AXIOM']
 else:
  lines+=['FIXTURE_PHASE\tCOMPARE_BEGIN']+load+load+['FIXTURE_PHASE\tCOMPARE_LOADED']
  if case=='identical':lines+=['FIXTURE_PHASE\tCOMPARE_PASSED']
  else:lines+=['FIXTURE_REJECTED\t'+case+'\t'+FIXTURE_REJECTIONS[case]]
 return '\n'.join(lines+['FIXTURE_PASSED\t'+case])+'\n'


def parse_fixture_output(case,text):
 expected=fixture_expected_output(case)
 f.need(type(text) is str and text==expected,'fixture exact markers/result differ: '+case)
 return {'case':case,'status':'REAL_SOURCE_CASE_PASSED','result':'identical' if case=='identical' else FIXTURE_REJECTIONS[case],
  'stdout_sha256':f.sha(text.encode()),'marker_count':len(expected.splitlines()),'loaded_contexts':1 if case in ['axiom','native'] else 2}


def parse_interface(c,text):
 lines=text.splitlines();decl=[];loaded={'original':[],'candidate':[]};generated=[];generated_counts=[];counts=[]
 for line in lines:
  p=line.split('\t')
  if p[0]=='DECL':
   f.need(len(p)==4 and p[2] in ['axiom','def','theorem','opaque','quot','inductive','constructor','recursor'],'declaration report malformed')
   f.need(set(filter(None,p[3].split(',')))<={'propext','Quot.sound','Classical.choice'},'unpermitted reported axiom');decl.append({'name':p[1],'kind':p[2],'axioms':list(filter(None,p[3].split(',')))})
  elif p[0] in ['LOADED_ORIGINAL','LOADED_CANDIDATE']:f.need(len(p)==2,'loaded report malformed');loaded[p[0].split('_')[1].lower()].append(p[1])
  elif p[0]=='GENERATED':
   f.need(len(p)==4 and p[1] and p[2] in ['kernel','native_only'] and p[3]==PART32,'generated report malformed')
   generated.append({'name':p[1],'classification':p[2],'module':p[3]})
  elif p[0]=='GENERATED_COUNTS':
   f.need(len(p)==3 and all(x.isdigit() for x in p[1:]),'generated counts malformed');generated_counts.append([int(x) for x in p[1:]])
  elif p[0]=='PART32_EXACT_COMPARISON_PASSED':f.need(len(p)==2 and p[1].isdigit(),'interface count malformed');counts.append(int(p[1]))
  else:raise f.Rejected('unrecognized interface report')
 f.need(counts==[len(decl)] and len(decl)>=239 and len({r['name'] for r in decl})==len(decl),'introduced count differs')
 index={r['name']:r for r in decl}
 f.need(len({r['name'] for r in generated})==len(generated),'duplicate generated name')
 for row in generated:
  f.need((row['name'] in index)==(row['classification']=='kernel'),'generated kernel classification differs')
 expected_counts=[sum(r['classification']==kind for r in generated) for kind in ['kernel','native_only']]
 f.need(generated_counts==[expected_counts],'generated counts differ')
 for r in c['explicit_part32_declarations']:f.need(r['name'] in index and index[r['name']]['kind']==r['kind'],'explicit declaration missing/kind changed')
 for mode,names in loaded.items():
  f.need(len(names)==len(set(names)),'duplicate loaded module')
  owned=[n for n in names if n.startswith('Spectre')];f.need(set(owned)==set(c['prerequisite_views'][mode]),'loaded exact owned environment differs')
  f.need(all(n.startswith('Init') or n in owned for n in names),'unexpected loaded external module')
 return {'status':'EXACT_PART32_FIELDS_AND_AXIOMS_EQUAL','canonical_module':PART32,'declarations':decl,'loaded_modules':loaded,'accounted_generated_names':[r['name'] for r in generated],'generated_entries':generated,'generated_counts':dict(zip(['kernel','native_only'],expected_counts)),'generated_scope':'Exact metadata names, classifications and owning module only for native_only; no native body/type/value equivalence claim','normalization':'none; structural Names, ConstantInfo equality plus Expr.equal at every Expr field'}


def parse_cover(c,text):
 rows=[];counts=[]
 for line in text.splitlines():
  p=line.split('\t')
  if p[0]=='COVER_DECL':
   f.need(len(p)==4 and set(filter(None,p[3].split(',')))<={'propext','Quot.sound','Classical.choice'},'cover axiom report malformed');rows.append({'name':p[1],'kind':p[2],'axioms':list(filter(None,p[3].split(',')))})
  elif p[0]=='COVER_AXIOMS_PASSED':f.need(len(p)==2 and p[1].isdigit(),'cover count malformed');counts.append(int(p[1]))
  else:raise f.Rejected('unknown cover report')
 f.need(counts==[len(rows)] and rows and len({r['name'] for r in rows})==len(rows),'cover inventory differs')
 index={r['name']:r for r in rows}
 for r in c['explicit_cover_declarations']:f.need(r['name'] in index and index[r['name']]['kind']==r['kind'],'explicit Cover declaration missing/kind changed')
 return {'status':'ALL_INTRODUCED_COVER_DECLARATIONS_AXIOM_CHECKED','declarations':rows}


def run(c,contract_sha,work,watchdog):
 validate_contract(c,reviewed=True);validate_inputs(c)
 f.need(os.environ.get('GITHUB_REF')=='refs/heads/'+c['publication_branch'],'unexpected branch')
 f.need(a.git_capture(ROOT,'rev-parse','HEAD').decode().strip()==os.environ.get('GITHUB_SHA'),'workflow commit mismatch')
 f.need(not a.git_capture(ROOT,'status','--porcelain=v1','--untracked-files=all','--ignored'),'checkout not clean')
 f.no_symlink_path(work);f.need(not work.exists(),'work must be new');work.mkdir()
 for folder in ['logs','evidence','home','tmp','objects','quarantine','original-input','original-output','native-captures','fixture-objects']:(work/folder).mkdir()
 commands=[];receipts=[];checked=set();prior={};runtime=None;env={};views={};terminal=False
 result={'schema':SCHEMA,'status':'INCOMPLETE','contract_sha256':contract_sha,'command_count':0,'complete_log_bytes':0,'checked_owned_module_count':0,
  'workflow_commit':os.environ.get('GITHUB_SHA'),'run_id':os.environ.get('GITHUB_RUN_ID'),'run_attempt':os.environ.get('GITHUB_RUN_ATTEMPT'),
  'full_official_verification_claimed':False,'owned_objects_from_prior_runs':False,'mathlib_acquisition':False}
 a.write_json(work/'evidence/result.json',result)
 def command(name,argv=None,*,cwd=None,env=None,seconds=None,allowed_sessions=True,**ignored):
  watchdog.check();spec=command_spec(c,work,name);requested=spec['requested_timeout_seconds']
  f.need(name==command_order(c)[len(commands)],'nonfinite command order')
  if argv is not None:f.need(list(map(str,argv))==spec['argv'] and env==spec['env'] and seconds==requested and allowed_sessions==spec['allowed_sessions'],'native command differs before execution')
  a.validate_session_policy(name,spec['argv'],True,work,c)
  timeout=min(requested,max(1,int(watchdog.deadline-time.monotonic())))
  out=work/'native-captures'/(name+'.stdout');err=work/'native-captures'/(name+'.stderr')
  limits={k:LIMITS[k] for k in ['address_space_bytes','rss_tree_bytes','max_created_file_bytes']}
  watchdog.in_command=True
  try:r=f.run_process(spec['argv'],cwd=work,env=spec['env'],timeout=timeout,stdout=out,stderr=err,max_log_bytes=LIMITS['per_command_log_max_bytes'],limits=limits,allow_new_sessions=True)
  finally:
   watchdog.in_command=False
   if watchdog.expired:watchdog.failure_receipt_grace()
  r.update({k:v for k,v in spec.items() if k!='allowed_sessions'});r.update(effective_timeout_seconds=timeout,limits=limits,max_log_bytes=LIMITS['per_command_log_max_bytes'],capture_status='excluded_pending_safety_and_bounds')
  commands.append(r);result['command_count']=len(commands)
  def persist():
   (work/'evidence/commands.jsonl').write_text(''.join(json.dumps(x,sort_keys=True,separators=(',',':'))+'\n' for x in commands));a.write_json(work/'evidence/last_command.json',r);a.write_json(work/'evidence/result.json',result)
  persist()
  # Typed cleanup gate is persisted before every capture read or hash.
  if not d.clean_command(r):
   r['capture_status']='excluded_unsafe_native_result';persist();raise f.Rejected('unsafe native result; excluded captures: '+name)
  stdout=d.read_capture(out,LIMITS['per_command_log_max_bytes'],watchdog);stderr=d.read_capture(err,LIMITS['per_command_log_max_bytes'],watchdog)
  f.need(len(stdout)+len(stderr)<=LIMITS['per_command_log_max_bytes'],'combined native capture bound')
  for stream,data in [('stdout',stdout),('stderr',stderr)]:r[stream+'_sha256']=f.sha(data);(work/'logs'/(name+'.'+stream)).write_bytes(data)
  r['capture_status']='accepted_bounded_complete';r['captures']={s:{'bytes':len(v),'sha256':f.sha(v)} for s,v in [('stdout',stdout),('stderr',stderr)]}
  result['complete_log_bytes']+=len(stdout)+len(stderr);persist()
  f.need(result['complete_log_bytes']<=LIMITS['aggregate_log_max_bytes'],'aggregate log bound')
  f.need(r['exit_code']==0,'native command failed: '+name)
  if name.startswith('compile-'):
   f.need(not re.search(r'(?im)(^.*\berror:|\bsorry\b|declaration uses .sorry.)',(stdout+stderr).decode('utf-8')),'compiler error/sorry diagnostic')
  return work/'logs'/(name+'.stdout'),True
 def disk(required=0):f.need(shutil.disk_usage(work).free>=required+LIMITS['minimum_free_disk_bytes'],'insufficient disk reserve')
 def inventory(path):return a.checked_inventory(path,maximum=LIMITS['owned_output_max_bytes'])['files']
 def make_view(mode):
  modules=c['prerequisite_views'][mode];f.need(set(modules)<=checked,'view lacks fresh successful checks')
  mapping={p:prior[p] for m in modules for p in a.module_outputs(m)};disk(sum(r['bytes'] for r in mapping.values()))
  dest=work/('view-'+mode);dest.mkdir()
  for p in sorted(mapping):
   q=dest/p;q.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(work/'objects'/p,q);q.chmod(0o444)
  f.need(inventory(dest)==mapping,'exact view copy differs')
  views[mode]={'prerequisite_modules':modules,'prerequisite_objects':mapping,'complete_objects':None,'source_sha256':c['original_part32']['sha256'] if mode=='original' else owned[PART32]['sha256'],'canonical_module':PART32,'common_prefix_inventory_sha256':f.sha(f.json_bytes(a.verify_owned_final(work/'objects',prior,LIMITS['owned_output_max_bytes'])))}
 def append_view(mode,source,output_map):
  dest=work/('view-'+mode);disk(sum(r['bytes'] for r in output_map.values()))
  for p in sorted(output_map):
   q=dest/p;f.need(not q.exists(),'view target exists');q.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(source/p,q);q.chmod(0o444)
  complete={**views[mode]['prerequisite_objects'],**output_map};f.need(inventory(dest)==complete,'completed view differs');views[mode]['complete_objects']=complete
 def compile_one(module):
  nonlocal prior
  row=owned[module];rel=module.replace('.','/');disk()
  staging=work/'quarantine'/module;staging.mkdir();(staging/rel).parent.mkdir(parents=True,exist_ok=True)
  imports=a.direct_import_receipt(row,owned,checked,prior,{},runtime)
  if module==PART32:f.need(inventory(work/'view-candidate')==views['candidate']['prerequisite_objects'],'candidate prerequisite drift')
  compiler_index=len(commands);command('compile-'+module)
  prior=a.admit_quarantine(staging,work/'objects',module,prior,LIMITS['owned_output_max_bytes']);shutil.rmtree(staging)
  output_map={p:prior[p] for p in sorted(a.module_outputs(module))}
  if module==PART32:append_view('candidate',work/'objects',output_map)
  command('check-'+module)
  for p in output_map:f.need(f.file_sha(work/'objects'/p)==prior[p]['sha256'],'output changed during checker')
  checked.add(module);receipt={'module':module,'source_sha256':row['sha256'],'ordered_imports':imports,'outputs':output_map,'compiler_command':compiler_index,'checker_command':compiler_index+1,'checker_passed':True};receipts.append(receipt)
  with (work/'evidence/owned-modules.jsonl').open('a') as h:h.write(json.dumps(receipt,sort_keys=True,separators=(',',':'))+'\n')
  result['checked_owned_module_count']=len(checked);a.write_json(work/'evidence/result.json',result)
  print(json.dumps({'phase':'candidate_compile_and_kernel_check','module':module,'completed':len(checked),'total':388}),flush=True)
 def original_control():
  make_view('original');make_view('candidate');disk()
  stage=work/'original-output';(stage/PART32.replace('.','/')).parent.mkdir(parents=True,exist_ok=True)
  before=a.verify_owned_final(work/'objects',prior,LIMITS['owned_output_max_bytes']);i=len(commands)
  command('compile-original-'+PART32)
  outputs=a.checked_inventory(stage,maximum=512*1024**2)['files'];f.need(set(outputs)==a.module_outputs(PART32),'original output family differs')
  append_view('original',stage,outputs);command('check-original-'+PART32)
  f.need(inventory(work/'view-original')==views['original']['complete_objects'],'original loaded objects drift')
  f.need(a.verify_owned_final(work/'objects',prior,LIMITS['owned_output_max_bytes'])==before,'original control changed common objects')
  views['original'].update(compiler_command=i,checker_command=i+1,outputs=outputs,never_admitted_to_candidate=True)
  shutil.rmtree(stage)
 try:
  extraction=a.extract_owned_sources(ROOT/'owned-sources.tar.gz',work/'source-input',c);a.write_json(work/'evidence/source-extraction.json',extraction)
  owned=validate_graph(c,work);disk(c['source_archive']['source_bytes']);shutil.copytree(work/'source-input/src',work/'src')
  src_before=a.checked_inventory(work/'src',maximum=LIMITS['owned_source_max_bytes'])
  p=work/'original-input'/(PART32.replace('.','/')+'.lean');p.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(ROOT/c['original_part32']['path'],p);p.chmod(0o444)
  orig_before=a.checked_inventory(work/'original-input',maximum=LIMITS['owned_source_max_bytes'])
  shutil.copytree(ROOT/'tools',work/'tools');shutil.copytree(ROOT/'fixtures',work/'fixtures')
  tools_before=a.checked_inventory(work/'tools',maximum=1024**2);fixtures_before=a.checked_inventory(work/'fixtures',maximum=1024**2)
  runtime=d.acquire_runtime(work,env,command)
  api,_=command('check-interface-api');f.need(api.read_text()=='INTERFACE_API_SELF_TEST_PASSED\n','API self-test output differs')
  fixture_maps={}
  for v in FIXTURES:
   disk();dest=work/'fixture-objects'/v;dest.mkdir();command('compile-fixture-'+v);fixture_maps[v]=inventory(dest);f.need(set(fixture_maps[v])==a.module_outputs('Fixture'),'fixture output family differs')
  fixture_cases={}
  for v in FIXTURE_CASES:
   name='check-interface-fixture-'+v;i=len(commands);output,_=command(name)
   report=parse_fixture_output(v,output.read_bytes().decode('utf-8'))
   f.need(report['stdout_sha256']==commands[i]['captures']['stdout']['sha256'],'fixture capture digest differs')
   fixture_cases[v]={'command':name,'command_index':i,'result':report}
  for v in FIXTURES:f.need(inventory(work/'fixture-objects'/v)==fixture_maps[v],'fixture output drift')
  a.write_json(work/'evidence/early-fixtures.json',{'status':'REAL_SOURCE_CONTROLS_AND_NATIVE_METADATA_BOUNDARY_PASSED','objects':fixture_maps,'modes':FIXTURES,'cases':fixture_cases})
  shutil.rmtree(work/'fixture-objects')
  for module in c['module_order']:
   if module==PART32:original_control()
   compile_one(module)
   if module==PART32:
    for mode in views:f.need(inventory(work/('view-'+mode))==views[mode]['complete_objects'],'pre-comparison view drift')
    output,_=command('check-interface-part32');comparison=parse_interface(c,output.read_text());a.write_json(work/'evidence/interface-comparison.json',comparison)
    for mode in views:
     f.need(inventory(work/('view-'+mode))==views[mode]['complete_objects'],'post-comparison view drift');views[mode]['pre_post_hashes_unchanged']=True
    a.write_json(work/'evidence/part32-views.json',views)
    for mode in views:shutil.rmtree(work/('view-'+mode))
  output,_=command('check-cover-axioms');a.write_json(work/'evidence/cover-axioms.json',parse_cover(c,output.read_text()))
  f.need(checked==set(c['module_order']),'module coverage differs');a.write_json(work/'evidence/fresh-owned-objects.json',a.verify_owned_final(work/'objects',prior,LIMITS['owned_output_max_bytes']))
  for path,before,maxbytes in [('src',src_before,LIMITS['owned_source_max_bytes']),('original-input',orig_before,LIMITS['owned_source_max_bytes']),('tools',tools_before,1024**2),('fixtures',fixtures_before,1024**2)]:f.need(a.checked_inventory(work/path,maximum=maxbytes)==before,'protected working input changed: '+path)
  d.revalidate_runtime(runtime,f.load_json(work/'evidence/runtime-inventory.json'));validate_inputs(c)
  f.need(f.file_sha(ROOT/'smoke-contract.json')==contract_sha and f.file_sha(ROOT/'owned-sources.tar.gz')==c['source_archive']['sha256'],'protected archive/contract changed')
  result['protected_inputs_and_runtime_revalidated']=True;result['terminal_receipts']={n:f.file_sha(work/'evidence'/n) for n in sorted(TERMINAL)}
  watchdog.check();terminal=True
 except Exception as error:
  result['status']='FAILED_OR_INCOMPLETE';result['error']=str(error);raise
 finally:
  a.write_json(work/'evidence/result.json',result)
  try:
   d.copy_logs(work);a.checked_inventory(work/'evidence',maximum=LIMITS['evidence_max_bytes']-8192)
   if terminal:
    watchdog.check();result['status']=SUCCESS;result['complete_evidence']=True;a.write_json(work/'evidence/result.json',result);verify_success(c,contract_sha,work/'evidence',work);watchdog.check()
  except Exception as error:
   result['status']='FAILED_EVIDENCE_COLLECTION';result['complete_evidence']=False;result['collection_error']=str(error);a.write_json(work/'evidence/result.json',result);raise


def verify_success(c,contract_sha,evidence,work):
 result=f.load_json(evidence/'result.json');f.need(result['status']==SUCCESS and result['complete_evidence'] is True and result['contract_sha256']==contract_sha,'no complete focused success')
 f.need(result['full_official_verification_claimed'] is False and result['owned_objects_from_prior_runs'] is False and result['mathlib_acquisition'] is False,'scope differs')
 f.need(result['protected_inputs_and_runtime_revalidated'] is True,'missing protected revalidation')
 f.need(set(result['terminal_receipts'])==TERMINAL,'terminal membership differs')
 for name,digest in result['terminal_receipts'].items():f.need(f.file_sha(evidence/name)==digest,'terminal evidence changed')
 f.need(f.sha((evidence/'runtime-inventory.json').read_bytes())==a.RUNTIME_INVENTORY_SHA,'runtime inventory differs')
 expected_extraction={'schema':'authenticated-source-extraction-v1','archive':c['source_archive'],'source_file_count':388,'source_bytes':c['source_archive']['source_bytes'],'exact_source_tree':True,'all_source_pins_verified':True}
 f.need(f.load_json(evidence/'source-extraction.json')==expected_extraction,'source extraction differs')
 preflight={'status':'READ_ONLY_PREDECESSOR_WRITES_CHMOD_AND_NAMESPACE_CREATION_REJECTED','quarantine_write_allowed':True,'fixture_sha256':f.sha(b'IMMUTABLE_BOUNDARY_FIXTURE_ONLY\n'),'not_a_research_proof':True}
 f.need(f.load_json(evidence/'read-only-boundary-preflight.json')==preflight,'read-only preflight differs')
 commands=[f.parse_json(s) for s in (evidence/'commands.jsonl').read_bytes().splitlines()];modules=[f.parse_json(s) for s in (evidence/'owned-modules.jsonl').read_bytes().splitlines()]
 f.need([r['name'] for r in commands]==command_order(c) and result['command_count']==len(commands)==796,'full command coverage differs')
 f.need(sum(r['requested_timeout_seconds'] for r in commands)==119580,'finite deadline sum differs')
 total=0
 for r in commands:
  validate_command_spec(c,work,r);f.need(d.clean_command(r) and r['capture_status']=='accepted_bounded_complete' and r['exit_code']==0,'unsafe or failed terminal command')
  combined=0
  for stream in ['stdout','stderr']:
   p=evidence/'logs'/(r['name']+'.'+stream);st=p.lstat();f.need(stat.S_ISREG(st.st_mode) and st.st_nlink==1,'unsafe terminal log')
   f.need(st.st_size==r['captures'][stream]['bytes'] and f.file_sha(p)==r['captures'][stream]['sha256']==r[stream+'_sha256'],'terminal log differs');combined+=st.st_size
  f.need(combined<=LIMITS['per_command_log_max_bytes'],'combined terminal capture bound');total+=combined
  if r['name'].startswith('compile-'):
   text=(evidence/'logs'/(r['name']+'.stdout')).read_text()+(evidence/'logs'/(r['name']+'.stderr')).read_text()
   f.need(not re.search(r'(?im)(^.*\berror:|\bsorry\b|declaration uses .sorry.)',text),'compiler error/sorry in evidence')
 f.need(total==result['complete_log_bytes'] and total<=LIMITS['aggregate_log_max_bytes'],'aggregate logs differ')
 objects=f.load_json(evidence/'fresh-owned-objects.json');expected=set().union(*(a.module_outputs(m) for m in c['module_order']))
 f.need(set(objects['files'])==expected and objects['bytes']==sum(r['bytes'] for r in objects['files'].values())<=LIMITS['owned_output_max_bytes'],'fresh output family differs');objects=objects['files']
 f.need([r['module'] for r in modules]==c['module_order'] and result['checked_owned_module_count']==388,'candidate coverage differs')
 runtime=f.load_json(evidence/'runtime-inventory.json');owned={r['module']:r for r in c['modules']}
 def imports(m):
  rows=[]
  for dep in dict.fromkeys([*owned[m]['ordered_imports'],'Init']):
   if dep in owned:rows.append({'module':dep,'provider':'fresh_owned','companions':{p:objects[p] for p in sorted(a.module_outputs(dep))}})
   else:rows.append({'module':dep,'provider':'official_runtime','object_sha256':runtime['files']['lib/lean/'+dep.replace('.','/')+'.olean']['sha256']})
  return rows
 for row in modules:
  m=row['module'];i=row['compiler_command'];j=row['checker_command']
  f.need(j==i+1 and row['checker_passed'] is True and commands[i]['name']=='compile-'+m and commands[j]['name']=='check-'+m,'compile/check receipts differ')
  f.need(row['source_sha256']==owned[m]['sha256'] and row['ordered_imports']==imports(m) and row['outputs']=={p:objects[p] for p in sorted(a.module_outputs(m))},'module source/import/output differs')
 views=f.load_json(evidence/'part32-views.json');f.need(set(views)=={'original','candidate'},'view coverage differs')
 prefix={p:objects[p] for m in c['prerequisite_views']['original'] for p in a.module_outputs(m)}
 prefix_digest=f.sha(f.json_bytes({'files':prefix,'bytes':sum(r['bytes'] for r in prefix.values())}))
 for mode,row in views.items():
  expected={p:objects[p] for m in c['prerequisite_views'][mode] for p in a.module_outputs(m)}
  f.need(row['canonical_module']==PART32 and row['prerequisite_modules']==c['prerequisite_views'][mode] and row['prerequisite_objects']==expected and row['pre_post_hashes_unchanged'] is True,'exact view source/artifacts differ')
  f.need(row['common_prefix_inventory_sha256']==prefix_digest,'view common same-run prefix differs')
  own=row['outputs'] if mode=='original' else {p:objects[p] for p in a.module_outputs(PART32)}
  f.need(set(own)==a.module_outputs(PART32) and row['complete_objects']=={**expected,**own},'view target family differs')
  if mode=='original':
   f.need(row['source_sha256']==c['original_part32']['sha256'] and row['never_admitted_to_candidate'] is True,'original isolation differs')
   i=row['compiler_command'];j=row['checker_command'];f.need(j==i+1 and commands[i]['name']=='compile-original-'+PART32 and commands[j]['name']=='check-original-'+PART32,'original control receipts differ')
  else:f.need(row['source_sha256']==owned[PART32]['sha256'],'candidate Part32 source differs')
 comparison=parse_interface(c,(evidence/'logs/check-interface-part32.stdout').read_text());f.need(f.json_bytes(comparison)==f.json_bytes(f.load_json(evidence/'interface-comparison.json')),'interface receipt differs')
 cover=parse_cover(c,(evidence/'logs/check-cover-axioms.stdout').read_text());f.need(cover==f.load_json(evidence/'cover-axioms.json'),'cover receipt differs')
 f.need((evidence/'logs/check-interface-api.stdout').read_text()=='INTERFACE_API_SELF_TEST_PASSED\n','early API control log differs')
 expected_cases={}
 for v in FIXTURE_CASES:
  name='check-interface-fixture-'+v
  i=command_order(c).index(name);report=parse_fixture_output(v,(evidence/'logs'/(name+'.stdout')).read_bytes().decode('utf-8'))
  f.need(report['stdout_sha256']==commands[i]['captures']['stdout']['sha256'],'fixture capture digest differs')
  expected_cases[v]={'command':name,'command_index':i,'result':report}
 fixture=f.load_json(evidence/'early-fixtures.json');f.need(fixture['status']=='REAL_SOURCE_CONTROLS_AND_NATIVE_METADATA_BOUNDARY_PASSED' and fixture['modes']==FIXTURES and set(fixture['objects'])==set(FIXTURES) and set(fixture)=={'status','modes','objects','cases'} and f.json_bytes(fixture['cases'])==f.json_bytes(expected_cases),'fixture receipt differs')
 for v,mapping in fixture['objects'].items():f.need(set(mapping)==a.module_outputs('Fixture'),'fixture artifact family differs')
 return result


# Reuse source-reviewed bounded collector and capture controls with this finite
# test's vocabulary. No acquisition/cache execution function is reachable here.
for key,value in {'LIMITS':LIMITS,'SUCCESS':SUCCESS,'SCHEMA':SCHEMA,'EVIDENCE_NAMES':EVIDENCE_NAMES,
 'command_order':command_order,'command_spec':command_spec,'validate_command_spec':validate_command_spec,
 'validate_contract':validate_contract,'verify_success':verify_success}.items():setattr(d,key,value)


def main():
 parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--contract-sha256',required=True);parser.add_argument('--work',type=Path,required=True);parser.add_argument('--collect',action='store_true');args=parser.parse_args()
 f.need(sys.flags.isolated and sys.dont_write_bytecode,'use Python -I -B');f.need(args.work.is_absolute(),'work path must be absolute')
 watchdog=a.HostDeadline(ENTRY_TIME+(120 if args.collect else 7200));watchdog.arm()
 try:
  c=f.pinned_load(ROOT/'smoke-contract.json',args.contract_sha256)
  if args.collect:d.collect(c,args.contract_sha256,args.work.absolute(),watchdog)
  else:run(c,args.contract_sha256,args.work.absolute(),watchdog)
 finally:watchdog.close()

if __name__=='__main__':main()
