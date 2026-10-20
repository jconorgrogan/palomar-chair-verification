#!/usr/bin/env python3
"""Finite inactive two-pair semantic and rooted-cost pilot; inherited native boundaries."""
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
spec=importlib.util.spec_from_file_location('domains_inherited',p);d=importlib.util.module_from_spec(spec);sys.modules[spec.name]=d;spec.loader.exec_module(d)
a=d.a;f=d.f;GIB=1024**3
SCHEMA='palomar-domains-fast-pilot-v1';SUCCESS='DOMAINS_FAST_SEMANTIC_AND_ROOTED_COST_PILOT_PASSED'
WORKFLOW='.github/workflows/palomar-domains-fast-pilot.yml'
KINDS={'axiom','def','theorem','opaque','quot','inductive','constructor','recursor'}
LIMITS={'aggregate_command_deadline_seconds':7200,'outer_timeout_minutes':130,'diagnostic_timeout_seconds':180,'check_timeout_seconds':120,'lean_heap_mib':4096,'address_space_bytes':12*GIB,'rss_tree_bytes':8*GIB,'max_created_file_bytes':512*1024**2,'per_command_log_max_bytes':1024**2,'aggregate_log_max_bytes':64*1024**2,'evidence_max_bytes':124*1024**2,'upload_max_bytes':128*1024**2,'collection_reserve_bytes':4*1024**2,'owned_source_max_bytes':32*1024**2,'owned_output_max_bytes':6*GIB,'minimum_free_disk_bytes':1536*1024**2,'failure_evidence_grace_seconds':5}
EVIDENCE_NAMES={'result.json','commands.jsonl','last_command.json','source-extraction.json','runtime-inventory.json','read-only-boundary-preflight.json','owned-modules.jsonl','fresh-owned-objects.json','capture-collection-scope.json','isolated-views.json','public-interfaces.json','bridge-axioms.json','early-fixtures.json','cost-measurements.json','source-controls.json'}
TERMINAL=EVIDENCE_NAMES-{'result.json','last_command.json','capture-collection-scope.json'}

def case_for(c,key):return next(x for x in c['cases'] if x['id']==key)
def variant_rows(c):
 out=[{'id':'fixture','module':'Fixture','prerequisites':[],'declarations':[{'name':'DomainAliasFixture.'+n,'kind':k} for n,k in [('Domains','def'),('Fast','def'),('fast_eq','theorem')]],'bridge_name':'DomainAliasFixture.original_fast_equals_actual','fast_name':'DomainAliasFixture.Fast'}]
 return out+c['cases']
def command_plan(c):
 out=[{'name':'bwrap-preflight','kind':'preflight','seconds':30},{'name':'read-only-committed-root-preflight','kind':'readonly','seconds':30},{'name':'check-interface-api','kind':'api','seconds':180}]
 def add_variants(row):
  key=row['id']
  for mode in (['original','candidate','wrong'] if key=='fixture' else ['original','candidate']):
   for phase in ['compile-target','check-target','compile-bridge']+([] if mode=='wrong' else ['check-bridge','audit-bridge']):
    out.append({'name':('compile-' if phase.startswith('compile') else 'check-')+key+'-'+mode+'-'+phase,'kind':phase,'case':key,'mode':mode,'seconds':180 if phase.startswith('compile') or phase=='audit-bridge' else 120})
   if key!='fixture':
    out.extend([{'name':'compile-export-'+key+'-'+mode,'kind':'export','case':key,'mode':mode,'seconds':180},{'name':'check-export-'+key+'-'+mode,'kind':'replay','case':key,'mode':mode,'seconds':120}])
  out.append({'name':'check-public-'+key,'kind':'compare','case':key,'seconds':180})
 add_variants(variant_rows(c)[0])
 for m in c['common_module_order']:
  out.extend([{'name':'compile-'+m,'kind':'common-compile','module':m,'seconds':180},{'name':'check-'+m,'kind':'common-check','module':m,'seconds':120}])
 for row in c['cases']:add_variants(row)
 return out

def command_order(c):return [r['name'] for r in command_plan(c)]
def validate_contract(c,reviewed=False):
 f.need(c['schema']==SCHEMA and c['limits']==LIMITS,'profile differs')
 f.need(c['publication_branch']=='verify/palomar-domains-fast-diagnostics-20261020','branch differs')
 f.need(c['owned_module_count']==368 and len(c['module_order'])==len(set(c['module_order']))==368 and len(c['common_module_order'])==366,'source scope differs')
 f.need(c['runtime_roots']==['Init','Init.Data.List.OfFn'] and c['cache_roots']==[] and c['restore_project_objects'] is False and c['full_official_verification_claimed'] is False,'runtime boundary differs')
 f.need([(x['id'],x['module'],x['name'],x['fin'],x['closure_count'],x['source_saving_bytes']) for x in c['cases']]==[('small','SpectreFinite.RadiusThreeRoot2Part1','root2Node0Domains4',37,81,933),('stress','SpectreFinite.RadiusFiveRoot7Part43','root7Node110Domains1',91,304,4073)],'selected pair scope differs')
 f.need(c['owned_source_max_bytes']==LIMITS['owned_source_max_bytes'],'source bound differs')
 f.need(c['recorded_command_count']==len(command_plan(c)) and c['sum_command_timeout_seconds']==sum(r['seconds'] for r in command_plan(c)),'finite command envelope differs')
 for row in c['cases']:
  f.need(len(row['prerequisites'])==row['closure_count']-1 and len(set(row['prerequisites']))==len(row['prerequisites']) and set(row['prerequisites'])<=set(c['common_module_order']),'case view differs')
  consumer=row['namespace']+'.'+('root2Node0Step4_checked' if row['id']=='small' else 'root7Node110Step1_checked')
  f.need(row['export_roots']==[row['namespace']+'.'+row['name'],row['fast_name'],row['fast_eq_name'],consumer],'export roots differ')
 if reviewed:f.need(c['review_status']=='reviewed_for_execution' and type(c.get('independent_driver_review_sha256')) is str and f.SHA256.fullmatch(c['independent_driver_review_sha256']),'inactive or missing independent review')

def validate_inputs(c):
 expected=set(c['distribution_files']);files={}
 f.need(expected==(set(c['inputs'])-{p for p in c['inputs'] if p.startswith('src/')})|{'smoke-contract.json','owned-sources.tar.gz',WORKFLOW},'distribution lock differs')
 for parent,dirs,names in os.walk(ROOT,followlinks=False):
  if Path(parent)==ROOT and '.git' in dirs:dirs.remove('.git')
  for n in dirs:f.need(not (Path(parent)/n).is_symlink(),'distribution symlink')
  for n in names:
   p=Path(parent)/n;s=p.lstat();f.need(stat.S_ISREG(s.st_mode) and s.st_nlink==1,'nonregular input');files[p.relative_to(ROOT).as_posix()]=p
 f.need(set(files)==expected,'unexpected/missing distribution file')
 for rel,row in c['inputs'].items():
  f.safe_rel(rel)
  if not rel.startswith('src/'):f.need(files[rel].stat().st_size==row['bytes'] and f.file_sha(files[rel])==row['sha256'],'protected input differs: '+rel)
 data=files[WORKFLOW].read_bytes();active=c['review_status']=='reviewed_for_execution';token=f.sha(f.json_bytes(c)).encode() if active else b'0'*64
 guard=b'    if: ${{ true }}\n' if active else b'    if: ${{ false }}\n'
 f.need(data.count(b'--contract-sha256 '+token)==2 and data.count(guard)==1,'workflow slots differ')
 normalized=data.replace(b'--contract-sha256 '+token,b'--contract-sha256 '+b'0'*64).replace(guard,b'    if: ${{ false }}\n')
 f.need(f.sha(normalized)==c['workflow_template_sha256'],'normalized workflow differs')

def validate_graph(c,work):
 owned={r['module']:r for r in c['modules']};seen=set();external=set()
 f.need([r['module'] for r in c['modules']]==c['module_order']==c['common_module_order']+[r['module'] for r in c['cases']],'source order differs')
 for row in c['modules']:
  m=row['module'];f.need(row['path']=='src/'+m.replace('.','/')+'.lean' and c['inputs'][row['path']]=={'bytes':row['bytes'],'sha256':row['sha256']},'source row differs')
  header=a.header_parser.header((work/'source-input'/row['path']).read_bytes());imports=[r['module'] for r in header['imports']]
  f.need(header['modern'] and not header['prelude'] and imports==row['ordered_imports'],'source header differs')
  for dep in [*imports,'Init']:
   f.need(dep in seen or dep in c['runtime_roots'],'unresolved dependency')
   if dep not in owned:external.add(dep)
  seen.add(m)
 f.need(external==set(c['runtime_roots']),'external boundary differs')
 def closure(m,s):
  if m not in owned or m in s:return
  s.add(m)
  for dep in owned[m]['ordered_imports']:closure(dep,s)
 for row in c['cases']:
  s=set();closure(row['module'],s);f.need(s-{row['module']}==set(row['prerequisites']),'exact case closure differs')
 return owned

def command_spec(c,work,name,cache_modules=()):
 r=next(x for x in command_plan(c) if x['name']==name);kind=r['kind'];runtime=work/'runtime';env=a.safe_env(runtime,work/'home',work/'tmp');env['LEAN_PATH']=str(work/'objects')+':'+str(runtime/'lib/lean')
 def sand(argv,sources,writable,cwd):return {'name':name,'argv':list(map(str,a.sandbox(argv,runtime=runtime,sources=sources,writable=writable,cwd=cwd,env=env))),'cwd':str(work),'env':dict(env),'requested_timeout_seconds':r['seconds'],'allowed_sessions':True}
 if kind=='preflight':return sand(['/bin/true'],[],[work/'home',work/'tmp'],work/'tmp')
 if kind=='readonly':
  src=work/'preflight-read-only';out=work/'preflight-quarantine';script='test -r "$1/predecessor"; if printf bad > "$1/predecessor"; then exit 11; fi; if chmod 0600 "$1/predecessor"; then exit 12; fi; if mkdir "$1/SpectreGeometry"; then exit 13; fi; printf allowed > "$2/output"'
  return sand(['/bin/sh','-eu','-c',script,'readonly-boundary-control',src,out],[src],[out,work/'home',work/'tmp'],out)
 if kind in ['api','compare','audit-bridge']:
  env['LEAN_PATH']=str(runtime/'lib/lean');sources=[work/'tools'];args=['self-test']
  if kind=='compare':
   left=work/'views'/(r['case']+'-original');right=work/'views'/(r['case']+'-candidate');args=['compare',r['case'],left,right,runtime];sources += [left,right]
  if kind=='audit-bridge':
   view=work/'views'/(r['case']+'-'+r['mode']);args=['bridge',r['case'],view,runtime];sources += [view]
  return sand([runtime/'bin/lean','-j1','-M4096','-DElab.async=false','--run',work/'tools/DomainAlias.lean',*args],sources,[work/'home',work/'tmp'],work/'tools')
 if kind.startswith('common-'):
  m=r['module'];src=work/'src';view=work/'objects';stage=work/'quarantine'/m
 else:
  row=next(x for x in variant_rows(c) if x['id']==r['case']);key=r['case']+'-'+r['mode'];src=work/'variant-source'/key;view=work/'views'/key;stage=work/'quarantine'/key/('bridge' if 'bridge' in kind else 'target');m='PilotBridge' if 'bridge' in kind else row['module']
 env['LEAN_PATH']=str(view)+':'+str(runtime/'lib/lean')
 if kind=='export':
  dest=work/'exports'/(r['case']+'-'+r['mode']);script='output=$1; shift; exec "$@" > "$output"'
  return sand(['/bin/sh','-eu','-c',script,'fixed-export-redirection',dest/'rooted.export',runtime/'bin/leanexport',row['module'],'--',*row['export_roots']],[src,view],[dest,work/'home',work/'tmp'],src)
 if kind=='replay':return sand([runtime/'bin/leanchecker','--silent','--from-export',work/'exports'/(r['case']+'-'+r['mode'])/'rooted.export'],[src,view,work/'exports'/(r['case']+'-'+r['mode'])],[work/'home',work/'tmp'],src)
 compile=kind in ['common-compile','compile-target','compile-bridge']
 return sand(d.compile_argv(runtime,src,stage,m) if compile else [runtime/'bin/leanchecker',m],[src,view],[stage,work/'home',work/'tmp'] if compile else [work/'home',work/'tmp'],src)

def validate_command_spec(c,work,r,cache_modules=()):
 expected=command_spec(c,work,r['name'])
 for k in ['name','argv','cwd','env','requested_timeout_seconds']:f.need(r[k]==expected[k],'native command provenance differs: '+k)
 f.need(r['new_sessions_explicitly_allowed']==expected['allowed_sessions'],'session policy differs')
 f.need(r['limits']=={k:LIMITS[k] for k in ['address_space_bytes','rss_tree_bytes','max_created_file_bytes']} and r['max_log_bytes']==LIMITS['per_command_log_max_bytes'],'resource profile differs')
 f.need(type(r['effective_timeout_seconds']) is int and 0<r['effective_timeout_seconds']<=expected['requested_timeout_seconds'],'effective timeout differs')

def validate_wrong_table_failure(work,r,stdout,stderr):
 # This is the exact admitted pinned-toolchain diagnostic, at its fixed source
 # location. Only the verified work-root prefix varies across isolated runs.
 expected=(str(work/'variant-source/fixture-wrong/PilotBridge.lean')+
  ':11:59: error: Tactic `decide` proved that the proposition\n'
  '  ∀ (v : Fin 2), originalFast v = Fast v\nis false\n').encode('utf-8')
 f.need(work.is_absolute() and type(stdout) is bytes and type(stderr) is bytes,'negative control capture/path types differ')
 f.need(r.get('name')=='compile-fixture-wrong-compile-bridge' and
  d.clean_command(r) and r['exit_code']==1 and r.get('capture_status')=='accepted_bounded_complete','negative control requires exact command and clean exit1 receipt')
 f.need(stdout==expected and stderr==b'','wrong-table diagnostic location/case/proposition/stream bytes differ')

def parse_axioms(text):
 if text=='':return []
 xs=text.split(',');f.need(all(xs) and len(xs)==len(set(xs)) and set(xs)<={'propext','Quot.sound','Classical.choice'},'axiom list malformed or unpermitted');return xs

def parse_public(row,text):
 f.need(text.endswith('\n') and text.splitlines()[-1].startswith('PUBLIC_INTERFACE_AXIOMS_PASSED\t'),'public terminal not last')
 public=[];kernel={'original':[],'candidate':[]};generated={'original':[],'candidate':[]};loaded={'original':[],'candidate':[]};terminal=[];heights=[]
 for line in text.splitlines():
  p=line.split('\t')
  if p[0]=='PUBLIC':
   f.need(len(p)==4 and p[1] and p[2] in KINDS,'public row malformed');public.append({'name':p[1],'kind':p[2],'axioms':parse_axioms(p[3])})
  elif p[0]=='FAST_HEIGHT':
   f.need(len(p)==4 and p[1]==row['fast_name'] and all(x.isdigit() and 0<=int(x)<=4294967295 for x in p[2:]),'Fast regular-height row malformed');heights.append({'name':p[1],'original':int(p[2]),'candidate':int(p[3])})
  elif p[0]=='KERNEL':
   f.need(len(p)==5 and p[1] in kernel and p[2] and p[3] in KINDS,'kernel row malformed');kernel[p[1]].append({'name':p[2],'kind':p[3],'axioms':parse_axioms(p[4])})
  elif p[0]=='GENERATED':
   f.need(len(p)==5 and p[1] in generated and p[2] and p[3] in ['kernel','native_only'] and p[4]==row['module'],'generated row malformed');generated[p[1]].append({'name':p[2],'classification':p[3],'module':p[4]})
  elif p[0]=='LOADED':f.need(len(p)==3 and p[1] in loaded and p[2],'loaded row malformed');loaded[p[1]].append(p[2])
  elif p[0]=='PUBLIC_INTERFACE_AXIOMS_PASSED':f.need(len(p)==2 and p[1].isdigit(),'terminal malformed');terminal.append(int(p[1]))
  else:raise f.Rejected('unknown public interface output')
 f.need([{k:r[k] for k in ['name','kind']} for r in public]==row['declarations'] and terminal==[len(public)] and len(heights)==1,'source-declared inventory differs')
 for side in kernel:
  kn={r['name'] for r in kernel[side]};gn={r['name'] for r in generated[side]}
  f.need(len(kn)==len(kernel[side]) and len(gn)==len(generated[side]) and {r['name'] for r in public}<=kn,'duplicate/missing kernel declarations')
  index={r['name']:r for r in kernel[side]}
  for r in public:f.need(index[r['name']]==r,'public/kernel kind or axioms differ')
  for r in generated[side]:f.need((r['name'] in kn)==(r['classification']=='kernel'),'generated class differs')
  f.need(len(loaded[side])==len(set(loaded[side])) and {n for n in loaded[side] if n.startswith('Spectre')}==set(row['prerequisites']) and all(n.startswith('Init') or n in row['prerequisites'] for n in loaded[side]),'loaded prerequisite boundary differs')
 for r in public+kernel['original']+kernel['candidate']:f.need(set(r['axioms'])<={'propext','Quot.sound','Classical.choice'},'unpermitted axiom')
 return {'public':public,'kernel':kernel,'generated':generated,'loaded':loaded,'generated_differences_are_reported_not_equivalence_claimed':True,'selected_fast_regular_heights':heights[0]}

def parse_bridge(row,text):
 f.need(text.endswith('\n') and text.splitlines()[-1].startswith('BRIDGE_AXIOMS_PASSED\t'),'bridge terminal not last')
 decl=[];terminal=[]
 for line in text.splitlines():
  p=line.split('\t')
  if p[0]=='BRIDGE_DECL':f.need(len(p)==4 and p[1] and p[2] in KINDS and set(filter(None,p[3].split(',')))<={'propext','Quot.sound','Classical.choice'},'bridge row differs');decl.append({'name':p[1],'kind':p[2],'axioms':parse_axioms(p[3])})
  elif p[0]=='BRIDGE_AXIOMS_PASSED':f.need(len(p)==2,'bridge terminal differs');terminal.append(p[1])
  else:raise f.Rejected('unknown bridge output')
 f.need(terminal==[row['bridge_name']] and any(r['name']==row['bridge_name'] and r['kind']=='theorem' for r in decl) and len({r['name'] for r in decl})==len(decl),'bridge coverage differs')
 return decl

def source_controls(c,work):
 rows=[]
 for row in c['cases']:
  old=(ROOT/row['original_path']).read_text();new=(work/'src'/(row['module'].replace('.','/')+'.lean')).read_text();n=row['name'];fin=row['fin']
  pattern=rf'def {n} \(v : Fin {fin}\) : List State :=\n  match v.val with\n((?:  \|[^\n]*\n)+)def {n}Fast \(v : Fin {fin}\) : Option \(List State\) :=\n  match v.val with\n((?:  \|[^\n]*\n)+)theorem {n}_fast_eq : ([^\n]+) := by\n  funext v\n  exact \(show ∀ v : Fin {fin}, [^\n]+ from by decide\) v'
  matches=list(re.finditer(pattern,old));f.need(len(matches)==1,'selected exact pair missing');m=matches[0]
  ordinary=[x.strip().split(' => ',1) for x in m.group(1).splitlines()];fast=[x.strip().split(' => ',1) for x in m.group(2).splitlines()]
  f.need(len(ordinary)==len(fast)==fin and all(a[0]==b[0] and b[1]=='some '+a[1] for a,b in zip(ordinary,fast)),'paired literal branches differ')
  replacement=f'def {n} (v : Fin {fin}) : List State :=\n  match v.val with\n{m.group(1)}def {n}Fast (v : Fin {fin}) : Option (List State) :=\n  some ({n} v)\ntheorem {n}_fast_eq : {m.group(3)} := by\n  funext v\n  rfl'
  f.need(new==old[:m.start()]+replacement+old[m.end():] and len(old.encode())-len(new.encode())==row['source_saving_bytes'],'nonfinite source change')
  literal=f'def originalFast (v : Fin {fin}) : Option (List State) :=\n  match v.val with\n{m.group(2)}'
  for mode in ['original','candidate']:f.need((ROOT/'probes'/row['id']/mode/'PilotBridge.lean').read_text().count(literal)==1,'original literal bridge source differs')
  declarations=[{'name':row['namespace']+'.'+v.group(2),'kind':v.group(1)} for v in re.finditer(r'^(def|theorem) (\w+)\b',old,re.M)]
  f.need(declarations==row['declarations'],'explicit source declaration inventory differs')
  for root in row['export_roots']:f.need(root in {d['name'] for d in declarations},'export root missing')
  rows.append({'case':row['id'],'original_sha256':f.sha(old.encode()),'candidate_sha256':f.sha(new.encode()),'exact_source_saving_bytes':row['source_saving_bytes'],'only_selected_fast_and_proof_changed':True,'old_literal_preserved_in_both_bridges':True})
 return rows

def run(c,contract_sha,work,watchdog):
 validate_contract(c,reviewed=True);validate_inputs(c)
 f.need(os.environ.get('GITHUB_REF')=='refs/heads/'+c['publication_branch'],'unexpected branch')
 f.need(a.git_capture(ROOT,'rev-parse','HEAD').decode().strip()==os.environ.get('GITHUB_SHA'),'workflow commit mismatch')
 f.need(not a.git_capture(ROOT,'status','--porcelain=v1','--untracked-files=all','--ignored'),'checkout not clean')
 f.no_symlink_path(work);f.need(not work.exists(),'work must be new');work.mkdir()
 for folder in ['logs','evidence','home','tmp','objects','quarantine','native-captures','views','variant-source','exports']:(work/folder).mkdir()
 commands=[];receipts=[];checked=set();prior={};env={};views={};public={};bridges={};costs={};terminal=False
 result={'schema':SCHEMA,'status':'INCOMPLETE','contract_sha256':contract_sha,'command_count':0,'complete_log_bytes':0,'checked_owned_module_count':0,'workflow_commit':os.environ.get('GITHUB_SHA'),'run_id':os.environ.get('GITHUB_RUN_ID'),'run_attempt':os.environ.get('GITHUB_RUN_ATTEMPT'),'full_official_verification_claimed':False,'owned_objects_from_prior_runs':False,'mathlib_acquisition':False}
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
  negative=name=='compile-fixture-wrong-compile-bridge'
  if negative:validate_wrong_table_failure(work,r,stdout,stderr)
  else:f.need(r['exit_code']==0,'native command failed: '+name)
  if name.startswith('compile-') and not negative:
   f.need(not re.search(r'(?im)(^.*\berror:|\bsorry\b|declaration uses .sorry.)',(stdout+stderr).decode('utf-8')),'compiler error/sorry diagnostic')
  return work/'logs'/(name+'.stdout'),True
 def disk(required=0):f.need(shutil.disk_usage(work).free>=required+LIMITS['minimum_free_disk_bytes'],'insufficient disk reserve')
 def inv(path):return a.checked_inventory(path,maximum=LIMITS['owned_output_max_bytes'])['files']
 def make_view(row,mode):
  key=row['id']+'-'+mode;src=work/'variant-source'/key;view=work/'views'/key;src.mkdir();view.mkdir()
  f.need(set(row['prerequisites'])<=checked,'unchecked prerequisite view')
  mapping={p:prior[p] for m in row['prerequisites'] for p in a.module_outputs(m)};disk(sum(x['bytes'] for x in mapping.values()))
  for p in sorted(mapping):q=view/p;q.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(work/'objects'/p,q);q.chmod(0o444)
  f.need(inv(view)==mapping,'exact prerequisite copy differs')
  if row['id']=='fixture':shutil.copytree(ROOT/'fixtures'/mode,src,dirs_exist_ok=True)
  else:
   target=src/(row['module'].replace('.','/')+'.lean');target.parent.mkdir(parents=True,exist_ok=True)
   shutil.copyfile(ROOT/row['original_path'] if mode=='original' else work/'src'/(row['module'].replace('.','/')+'.lean'),target)
   shutil.copyfile(ROOT/'probes'/row['id']/mode/'PilotBridge.lean',src/'PilotBridge.lean')
  for p in src.rglob('*'):
   if p.is_file():p.chmod(0o444)
  views[key]={'module':row['module'],'mode':mode,'prerequisites':row['prerequisites'],'prerequisite_objects':mapping,'sources':inv(src),'objects':dict(mapping),'receipts':[]}
  return src,view
 def compile_variant(row,mode):
  key=row['id']+'-'+mode;src,view=make_view(row,mode);v=views[key]
  for kind,module in [('target',row['module']),('bridge','PilotBridge')]:
   stage=work/'quarantine'/key/kind;stage.mkdir(parents=True);(stage/module.replace('.','/')).parent.mkdir(parents=True,exist_ok=True);disk()
   i=len(commands);command('compile-'+key+'-compile-'+kind)
   if mode=='wrong' and kind=='bridge':
    v['negative_bridge_command']=i;shutil.rmtree(stage);break
   v['objects']=a.admit_quarantine(stage,view,module,v['objects'],LIMITS['owned_output_max_bytes']);shutil.rmtree(stage)
   command('check-'+key+'-check-'+kind);f.need(inv(view)==v['objects'],'variant output changed during checker')
   v['receipts'].append({'module':module,'compile_command':i,'check_command':i+1,'outputs':{p:v['objects'][p] for p in sorted(a.module_outputs(module))}})
  if mode!='wrong':
   output,_=command('check-'+key+'-audit-bridge');bridges[key]=parse_bridge(row,output.read_text())
  f.need(inv(src)==v['sources'] and inv(view)==v['objects'],'variant input/output drift')
  if row['id']!='fixture':
   dest=work/'exports'/key;dest.mkdir();disk(LIMITS['max_created_file_bytes']);eidx=len(commands);command('compile-export-'+key)
   export=dest/'rooted.export';f.need(inv(dest).keys()=={'rooted.export'},'unexpected export output');st=export.lstat();f.need(stat.S_ISREG(st.st_mode) and st.st_nlink==1 and 0<st.st_size<=LIMITS['max_created_file_bytes'],'export artifact bound');export.chmod(0o444)
   output={'bytes':st.st_size,'sha256':f.file_sha(export)};ridx=len(commands);command('check-export-'+key)
   f.need(inv(dest)=={'rooted.export':output},'rooted export changed during replay')
   target=v['receipts'][0];costs[key]={'module':row['module'],'roots':row['export_roots'],'export':output,'export_command':eidx,'replay_command':ridx,'target_compile_command':target['compile_command'],'target_check_command':target['check_command'],'export_elapsed_seconds':commands[eidx]['elapsed_seconds'],'export_replay_elapsed_seconds':commands[ridx]['elapsed_seconds'],'target_compile_elapsed_seconds':commands[target['compile_command']]['elapsed_seconds'],'target_check_elapsed_seconds':commands[target['check_command']]['elapsed_seconds'],'export_replay_peak_sampled_tree_rss_bytes':commands[ridx]['peak_sampled_tree_rss_bytes'],'single_ordered_measurement_not_benchmark':True}
 def compare(row):
  output,_=command('check-public-'+row['id']);public[row['id']]=parse_public(row,output.read_text())
  for mode in ['original','candidate']:
   key=row['id']+'-'+mode;f.need(inv(work/'views'/key)==views[key]['objects'],'post-comparison view drift')
 def compile_common(m):
  nonlocal prior
  row=owned[m];stage=work/'quarantine'/m;stage.mkdir();(stage/m.replace('.','/')).parent.mkdir(parents=True,exist_ok=True);disk()
  imports=a.direct_import_receipt(row,owned,checked,prior,{},runtime);i=len(commands);command('compile-'+m)
  prior=a.admit_quarantine(stage,work/'objects',m,prior,LIMITS['owned_output_max_bytes']);shutil.rmtree(stage);command('check-'+m)
  for p in a.module_outputs(m):f.need(f.file_sha(work/'objects'/p)==prior[p]['sha256'],'checked common output drift')
  checked.add(m);receipt={'module':m,'source_sha256':row['sha256'],'ordered_imports':imports,'outputs':{p:prior[p] for p in sorted(a.module_outputs(m))},'compiler_command':i,'checker_command':i+1,'checker_passed':True};receipts.append(receipt)
  with (work/'evidence/owned-modules.jsonl').open('a') as h:h.write(json.dumps(receipt,sort_keys=True,separators=(',',':'))+'\n')
  result['checked_owned_module_count']=len(checked);a.write_json(work/'evidence/result.json',result);print(json.dumps({'phase':'fresh_common_compile_and_check','module':m,'completed':len(checked),'total':366}),flush=True)
 try:
  extraction=a.extract_owned_sources(ROOT/'owned-sources.tar.gz',work/'source-input',c);a.write_json(work/'evidence/source-extraction.json',extraction)
  owned=validate_graph(c,work);disk(c['source_archive']['source_bytes']);shutil.copytree(work/'source-input/src',work/'src');src_before=inv(work/'src')
  a.write_json(work/'evidence/source-controls.json',source_controls(c,work));shutil.copytree(ROOT/'tools',work/'tools');tools_before=inv(work/'tools')
  runtime=d.acquire_runtime(work,env,command);output,_=command('check-interface-api');f.need(output.read_text()=='INTERFACE_API_SELF_TEST_PASSED\n','API control output differs')
  fixture=variant_rows(c)[0]
  for mode in ['original','candidate','wrong']:compile_variant(fixture,mode)
  compare(fixture);a.write_json(work/'evidence/early-fixtures.json',{'positive_semantic_bridge_compiled_and_kernel_checked':True,'valid_wrong_table_module_compiled_and_kernel_checked':True,'wrong_table_bridge_rejected_for_false_decide':True,'views':{k:v for k,v in views.items() if k.startswith('fixture-')}})
  for m in c['common_module_order']:compile_common(m)
  for row in c['cases']:
   for mode in ['original','candidate']:compile_variant(row,mode)
   compare(row)
  f.need(checked==set(c['common_module_order']),'common coverage differs')
  for key,v in views.items():f.need(inv(work/'views'/key)==v['objects'] and inv(work/'variant-source'/key)==v['sources'],'final variant drift')
  for key,cost in costs.items():f.need(inv(work/'exports'/key)=={'rooted.export':cost['export']},'final rooted export drift')
  f.need(inv(work/'src')==src_before and inv(work/'tools')==tools_before,'protected working inputs drift')
  a.write_json(work/'evidence/isolated-views.json',views);a.write_json(work/'evidence/public-interfaces.json',public);a.write_json(work/'evidence/bridge-axioms.json',bridges);a.write_json(work/'evidence/cost-measurements.json',costs);a.write_json(work/'evidence/fresh-owned-objects.json',a.verify_owned_final(work/'objects',prior,LIMITS['owned_output_max_bytes']))
  d.revalidate_runtime(runtime,f.load_json(work/'evidence/runtime-inventory.json'));validate_inputs(c);f.need(f.file_sha(ROOT/'smoke-contract.json')==contract_sha and f.file_sha(ROOT/'owned-sources.tar.gz')==c['source_archive']['sha256'],'protected archive/contract changed')
  result['protected_inputs_and_runtime_revalidated']=True;result['terminal_receipts']={n:f.file_sha(work/'evidence'/n) for n in sorted(TERMINAL)};watchdog.check();terminal=True
 except Exception as error:result['status']='FAILED_OR_INCOMPLETE';result['error']=str(error);raise
 finally:
  a.write_json(work/'evidence/result.json',result)
  try:
   d.copy_logs(work);a.checked_inventory(work/'evidence',maximum=LIMITS['evidence_max_bytes']-8192)
   if terminal:
    watchdog.check();result['status']=SUCCESS;result['complete_evidence']=True;a.write_json(work/'evidence/result.json',result);verify_success(c,contract_sha,work/'evidence',work);watchdog.check()
  except Exception as error:result['status']='FAILED_EVIDENCE_COLLECTION';result['complete_evidence']=False;result['collection_error']=str(error);a.write_json(work/'evidence/result.json',result);raise

def verify_success(c,contract_sha,evidence,work):
 result=f.load_json(evidence/'result.json');f.need(result['status']==SUCCESS and result['complete_evidence'] is True and result['contract_sha256']==contract_sha,'no complete pilot success')
 f.need(result['full_official_verification_claimed'] is False and result['owned_objects_from_prior_runs'] is False and result['mathlib_acquisition'] is False and result['protected_inputs_and_runtime_revalidated'] is True,'scope or protected-input receipt differs')
 f.need(set(result['terminal_receipts'])==TERMINAL,'terminal evidence membership differs')
 for name,digest in result['terminal_receipts'].items():f.need(f.file_sha(evidence/name)==digest,'terminal evidence changed')
 f.need(f.sha((evidence/'runtime-inventory.json').read_bytes())==a.RUNTIME_INVENTORY_SHA,'runtime inventory differs')
 f.need(f.load_json(evidence/'source-extraction.json')=={'schema':'authenticated-source-extraction-v1','archive':c['source_archive'],'source_file_count':368,'source_bytes':c['source_archive']['source_bytes'],'exact_source_tree':True,'all_source_pins_verified':True},'source extraction differs')
 f.need(f.load_json(evidence/'read-only-boundary-preflight.json')=={'status':'READ_ONLY_PREDECESSOR_WRITES_CHMOD_AND_NAMESPACE_CREATION_REJECTED','quarantine_write_allowed':True,'fixture_sha256':f.sha(b'IMMUTABLE_BOUNDARY_FIXTURE_ONLY\n'),'not_a_research_proof':True},'read-only preflight differs')
 commands=[f.parse_json(s) for s in (evidence/'commands.jsonl').read_bytes().splitlines()];plan=command_plan(c)
 f.need([r['name'] for r in commands]==command_order(c) and result['command_count']==len(commands)==c['recorded_command_count'] and sum(r['requested_timeout_seconds'] for r in commands)==c['sum_command_timeout_seconds'],'finite complete command coverage differs')
 total=0
 for r in commands:
  validate_command_spec(c,work,r);f.need(d.clean_command(r) and r['capture_status']=='accepted_bounded_complete','unsafe terminal command')
  streams=[]
  for stream in ['stdout','stderr']:
   p=evidence/'logs'/(r['name']+'.'+stream);st=p.lstat();f.need(stat.S_ISREG(st.st_mode) and st.st_nlink==1 and st.st_size==r['captures'][stream]['bytes'] and f.file_sha(p)==r['captures'][stream]['sha256']==r[stream+'_sha256'],'terminal log differs');streams.append(p.read_bytes())
  size=sum(map(len,streams));f.need(size<=LIMITS['per_command_log_max_bytes'],'terminal log bound');total+=size;text=b''.join(streams).decode('utf-8')
  negative=r['name']=='compile-fixture-wrong-compile-bridge'
  if negative:validate_wrong_table_failure(work,r,streams[0],streams[1])
  else:f.need(r['exit_code']==0,'failed positive command')
  if r['name'].startswith('compile-') and not negative:f.need(not re.search(r'(?im)(^.*\berror:|\bsorry\b|declaration uses .sorry.)',text),'compiler error/sorry')
 f.need(total==result['complete_log_bytes'] and total<=LIMITS['aggregate_log_max_bytes'],'aggregate logs differ')
 objects=f.load_json(evidence/'fresh-owned-objects.json');expected=set().union(*(a.module_outputs(m) for m in c['common_module_order']))
 f.need(set(objects['files'])==expected and objects['bytes']==sum(x['bytes'] for x in objects['files'].values())<=LIMITS['owned_output_max_bytes'],'common output inventory differs');objects=objects['files']
 modules=[f.parse_json(s) for s in (evidence/'owned-modules.jsonl').read_bytes().splitlines()];owned={r['module']:r for r in c['modules']};runtime=f.load_json(evidence/'runtime-inventory.json')
 f.need([r['module'] for r in modules]==c['common_module_order'] and result['checked_owned_module_count']==366,'common module coverage differs')
 for row in modules:
  m=row['module'];i=row['compiler_command'];j=row['checker_command'];imports=[]
  for dep in dict.fromkeys([*owned[m]['ordered_imports'],'Init']):
   if dep in owned:imports.append({'module':dep,'provider':'fresh_owned','companions':{p:objects[p] for p in sorted(a.module_outputs(dep))}})
   else:imports.append({'module':dep,'provider':'official_runtime','object_sha256':runtime['files']['lib/lean/'+dep.replace('.','/')+'.olean']['sha256']})
  f.need(j==i+1 and row['checker_passed'] is True and commands[i]['name']=='compile-'+m and commands[j]['name']=='check-'+m and row['source_sha256']==owned[m]['sha256'] and row['ordered_imports']==imports and row['outputs']=={p:objects[p] for p in sorted(a.module_outputs(m))},'common compile/import/check receipt differs')
 views=f.load_json(evidence/'isolated-views.json');expected_keys={r['id']+'-'+mode for r in variant_rows(c) for mode in (['original','candidate','wrong'] if r['id']=='fixture' else ['original','candidate'])};f.need(set(views)==expected_keys,'view membership differs')
 public=f.load_json(evidence/'public-interfaces.json');bridges=f.load_json(evidence/'bridge-axioms.json');f.need(set(public)=={'fixture','small','stress'} and set(bridges)==expected_keys-{'fixture-wrong'},'interface/bridge coverage differs')
 for row in variant_rows(c):
  key=row['id'];f.need(public[key]==parse_public(row,(evidence/'logs'/('check-public-'+key+'.stdout')).read_text()),'public interface receipt differs')
  for mode in (['original','candidate','wrong'] if key=='fixture' else ['original','candidate']):
   k=key+'-'+mode;v=views[k];prefix={p:objects[p] for m in row['prerequisites'] for p in a.module_outputs(m)}
   f.need(v['module']==row['module'] and v['mode']==mode and v['prerequisites']==row['prerequisites'] and v['prerequisite_objects']==prefix,'canonical isolated view differs')
   need_modules=[row['module']]+([] if mode=='wrong' else ['PilotBridge']);f.need([x['module'] for x in v['receipts']]==need_modules,'variant receipt membership differs')
   expected=dict(prefix)
   for index,x in enumerate(v['receipts']):
    kind='target' if index==0 else 'bridge';i=x['compile_command'];j=x['check_command'];f.need(j==i+1 and commands[i]['name']=='compile-'+k+'-compile-'+kind and commands[j]['name']=='check-'+k+'-check-'+kind and set(x['outputs'])==a.module_outputs(x['module']),'variant compile/check differs');expected.update(x['outputs'])
   f.need(v['objects']==expected,'complete view inventory differs')
   if mode=='wrong':f.need(commands[v['negative_bridge_command']]['name']=='compile-fixture-wrong-compile-bridge','negative command binding differs')
   else:f.need(bridges[k]==parse_bridge(row,(evidence/'logs'/('check-'+k+'-audit-bridge.stdout')).read_text()),'bridge axiom receipt differs')
   if key=='fixture':source_files={p.name:{'bytes':p.stat().st_size,'sha256':f.file_sha(p)} for p in (ROOT/'fixtures'/mode).iterdir()}
   else:
    target=ROOT/row['original_path'] if mode=='original' else ROOT/row['candidate_path'];probe=ROOT/'probes'/key.split('-')[0]/mode/'PilotBridge.lean';source_files={row['module'].replace('.','/')+'.lean':{'bytes':target.stat().st_size,'sha256':f.file_sha(target)},'PilotBridge.lean':{'bytes':probe.stat().st_size,'sha256':f.file_sha(probe)}}
   f.need(v['sources']==source_files,'variant source identity differs')
 fixture=f.load_json(evidence/'early-fixtures.json');f.need(fixture=={'positive_semantic_bridge_compiled_and_kernel_checked':True,'valid_wrong_table_module_compiled_and_kernel_checked':True,'wrong_table_bridge_rejected_for_false_decide':True,'views':{k:v for k,v in views.items() if k.startswith('fixture-')}},'early fixture gate differs')
 f.need((evidence/'logs/check-interface-api.stdout').read_text()=='INTERFACE_API_SELF_TEST_PASSED\n','API self-test differs')
 costs=f.load_json(evidence/'cost-measurements.json');f.need(set(costs)=={'small-original','small-candidate','stress-original','stress-candidate'},'cost coverage differs')
 for key,x in costs.items():
  case,mode=key.split('-');row=case_for(c,case);target=views[key]['receipts'][0];ei=x['export_command'];ri=x['replay_command'];f.need(ri==ei+1 and commands[ei]['name']=='compile-export-'+key and commands[ri]['name']=='check-export-'+key,'export/replay receipt differs')
  f.need(x['module']==row['module'] and x['roots']==row['export_roots'] and x['single_ordered_measurement_not_benchmark'] is True and 0<x['export']['bytes']<=LIMITS['max_created_file_bytes'] and f.SHA256.fullmatch(x['export']['sha256']),'rooted export identity differs')
  for field,command in [('export_elapsed_seconds',ei),('export_replay_elapsed_seconds',ri),('target_compile_elapsed_seconds',target['compile_command']),('target_check_elapsed_seconds',target['check_command'])]:f.need(x[field]==commands[command]['elapsed_seconds'],'measured time differs')
  f.need(x['export_replay_peak_sampled_tree_rss_bytes']==commands[ri]['peak_sampled_tree_rss_bytes'] and x['target_compile_command']==target['compile_command'] and x['target_check_command']==target['check_command'],'cost command/RSS differs')
 f.need(f.load_json(evidence/'source-controls.json')==source_controls(c,work),'source replacement control differs')
 return result

# The exact inherited bounded collector uses this finite pilot vocabulary.
for key,value in {'LIMITS':LIMITS,'SUCCESS':SUCCESS,'SCHEMA':SCHEMA,'EVIDENCE_NAMES':EVIDENCE_NAMES,'command_order':command_order,'command_spec':command_spec,'validate_command_spec':validate_command_spec,'validate_contract':validate_contract,'verify_success':verify_success}.items():setattr(d,key,value)

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
