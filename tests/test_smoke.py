"""Inert controls only: all subprocess, socket, and network calls are forbidden."""
import copy, importlib.util, json, os, socket, subprocess, sys, tempfile, unittest, urllib.request
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
def forbidden(*args,**kwargs):raise AssertionError('external/native operation forbidden in inert test')
subprocess.Popen=forbidden;subprocess.run=forbidden;os.system=forbidden
socket.socket=forbidden;socket.create_connection=forbidden;urllib.request.urlopen=forbidden
spec=importlib.util.spec_from_file_location('smoke_test_api',ROOT/'visibility_smoke.py');d=importlib.util.module_from_spec(spec);sys.modules[spec.name]=d;spec.loader.exec_module(d)
class Clock:
 def check(self):pass
class Tests(unittest.TestCase):
 @classmethod
 def setUpClass(cls):cls.c=d.f.load_json(ROOT/'smoke-contract.json')
 def reject(self,func,*args,**kwargs):
  with self.assertRaises((ValueError,RuntimeError,KeyError)):func(*args,**kwargs)
 def safe(self):
  return {'exit_code':0,'timed_out':False,'log_overflow':False,'memory_exceeded':False,'surviving_children':False,'process_group_empty':True,'descendants_empty':True,'escaped_descendants':False,'new_sessions_explicitly_allowed':True}
 def test_inactive_contract_and_all_pins(self):
  d.validate_contract(self.c);d.validate_inputs(self.c);self.reject(d.validate_contract,self.c,reviewed=True)
 def test_profile_mutations(self):
  for field in d.LIMITS:
   c=copy.deepcopy(self.c);c['limits'][field]+=1;self.reject(d.validate_contract,c)
  for field in ['restore_project_objects','full_official_verification_claimed']:
   c=copy.deepcopy(self.c);c[field]=True;self.reject(d.validate_contract,c)
 def test_fresh_source_extraction_and_graph(self):
  with tempfile.TemporaryDirectory() as td:
   work=Path(td);receipt=d.a.extract_owned_sources(ROOT/'owned-sources.tar.gz',work/'source-input',self.c)
   self.assertEqual(receipt['source_file_count'],174);owned=d.validate_graph(self.c,work);self.assertEqual(len(owned),174)
   c=copy.deepcopy(self.c);c['target_closures'][d.TARGETS[3]].pop(0);self.reject(d.validate_graph,c,work)
   c=copy.deepcopy(self.c);c['modules'][0]['ordered_imports']=['Wrong.Module'];self.reject(d.validate_graph,c,work)
 def test_all_native_specs_are_finite_and_fixed(self):
  names=d.command_order(self.c);self.assertEqual(len(names),394);self.assertEqual(len(names),len(set(names)))
  work=Path('/tmp/inert-visibility-fixture')
  for name in names:
   spec=d.command_spec(self.c,work,name,['Mathlib.Tactic.Linarith']);row={**spec,**self.safe(),'limits':{k:d.LIMITS[k] for k in ['address_space_bytes','rss_tree_bytes','max_created_file_bytes']},'max_log_bytes':1024**2,'effective_timeout_seconds':spec['requested_timeout_seconds']}
   row['new_sessions_explicitly_allowed']=spec['allowed_sessions'];d.validate_command_spec(self.c,work,row,['Mathlib.Tactic.Linarith'])
   mutated=copy.deepcopy(row);mutated['argv'].append('--unsafe');self.reject(d.validate_command_spec,self.c,work,mutated,['Mathlib.Tactic.Linarith'])
   if name.startswith(('compile-','check-')):self.assertNotIn('--share-net',spec['argv'])
  for m in d.TARGETS:
   spec=d.command_spec(self.c,work,'compile-original-'+m)
   self.assertTrue(spec['env']['LEAN_PATH'].split(':')[0].endswith('/original-prerequisites/'+m));self.assertNotIn(str(work/'objects'),spec['argv'])
 def test_safety_types_and_flags(self):
  self.assertTrue(d.clean_command(self.safe()))
  for key in self.safe():
   row=self.safe();row[key]='false';self.reject(d.clean_command,row)
  for key in ['timed_out','log_overflow','memory_exceeded','surviving_children']:
   row=self.safe();row[key]=True;self.assertFalse(d.clean_command(row))
  for key in ['process_group_empty','descendants_empty']:
   row=self.safe();row[key]=False;self.assertFalse(d.clean_command(row))
 def test_capture_regular_bounded_no_alias(self):
  with tempfile.TemporaryDirectory() as td:
   p=Path(td)/'capture';p.write_bytes(b'ok');self.assertEqual(d.read_capture(p,2,Clock()),b'ok');self.reject(d.read_capture,p,1,Clock())
   q=Path(td)/'alias';q.symlink_to(p);self.reject(d.read_capture,q,2,Clock());q.unlink();os.link(p,q);self.reject(d.read_capture,p,2,Clock())
 def test_original_exact_diagnostics(self):
  for module,expected in d.EXPECTED_UNKNOWN.items():
   text=''.join('/tmp/'+module.replace('.','/')+f'.lean:{line}:{col or 3}: error: Unknown identifier `{name}`\n' for line,col,name in expected)
   d.failure_diagnostics(module,text)
   for bad in ['',text+text,text.replace('Unknown identifier','type mismatch'),text.replace('.lean:', '.lean:1')]:self.reject(d.failure_diagnostics,module,bad)
  module=d.TARGETS[1];text='/tmp/'+module.replace('.','/')+'.lean:34:15: error: Unknown identifier `translated_contracting`\n'
  for (line,col),message in d.CASCADE.items():text+='/tmp/'+module.replace('.','/')+f'.lean:{line}:{col}: error: {message}\n'
  self.assertEqual(len(d.failure_diagnostics(module,text)['authenticated_cascade_headers']),3)
 def test_unexpected_evidence_rejected(self):
  with tempfile.TemporaryDirectory() as td:
   work=Path(td);(work/'evidence').mkdir();(work/'logs').mkdir();(work/'native-captures').mkdir()
   (work/'evidence/secret.txt').write_text('unexpected');self.reject(d.validate_capture_collection,self.c,work,Clock())
 def test_unreceipted_native_is_never_read(self):
  with tempfile.TemporaryDirectory() as td:
   work=Path(td);(work/'evidence').mkdir();(work/'logs').mkdir();(work/'native-captures').mkdir()
   (work/'native-captures/bwrap-preflight.stdout').symlink_to('/definitely/not/read')
   # Dangling unadmitted capture still must be described, never opened.
   omissions=d.validate_capture_collection(self.c,work,Clock())
   self.assertEqual(len(omissions),1)
 def test_prepopulated_evidence_log_rejected(self):
  with tempfile.TemporaryDirectory() as td:
   work=Path(td)
   for n in ['evidence/logs','logs','native-captures']:(work/n).mkdir(parents=True)
   (work/'evidence/logs/bwrap-preflight.stdout').write_text('unadmitted')
   self.reject(d.validate_capture_collection,self.c,work,Clock())
 def test_unsafe_capture_not_read(self):
  with tempfile.TemporaryDirectory() as td:
   work=Path(td)
   for n in ['evidence','logs','native-captures']:(work/n).mkdir()
   spec=d.command_spec(self.c,work,'bwrap-preflight');r={**spec,**self.safe(),'limits':{k:d.LIMITS[k] for k in ['address_space_bytes','rss_tree_bytes','max_created_file_bytes']},'max_log_bytes':1024**2,'effective_timeout_seconds':30,'capture_status':'excluded_unsafe_native_result'}
   r['timed_out']=True;(work/'evidence/commands.jsonl').write_text(json.dumps(r)+'\n')
   (work/'native-captures/bwrap-preflight.stdout').symlink_to('/definitely/not/read')
   self.assertEqual(len(d.validate_capture_collection(self.c,work,Clock())),1)
 def test_synthetic_success_and_terminal_mutations(self):
  spec=importlib.util.spec_from_file_location('synthetic_success',ROOT/'tests/inert_success_fixture.py');fixture=importlib.util.module_from_spec(spec);spec.loader.exec_module(fixture)
  with tempfile.TemporaryDirectory() as td:
   data=fixture.make(d,self.c,Path(td));old=d.a.RUNTIME_INVENTORY_SHA;d.a.RUNTIME_INVENTORY_SHA=data['synthetic_runtime_sha']
   try:
    d.verify_success(self.c,data['contract_sha'],Path(td)/'evidence',Path(td))
    d.validate_capture_collection(self.c,Path(td),Clock())
    result=Path(td)/'evidence/result.json';before=result.read_bytes();row=d.f.parse_json(before);row['checked_owned_module_count']=173;result.write_bytes(d.f.json_bytes(row))
    self.reject(d.verify_success,self.c,data['contract_sha'],Path(td)/'evidence',Path(td));result.write_bytes(before)
    log=Path(td)/'evidence/logs'/('check-'+self.c['module_order'][-1]+'.stdout');log.write_text('changed')
    self.reject(d.verify_success,self.c,data['contract_sha'],Path(td)/'evidence',Path(td))
   finally:d.a.RUNTIME_INVENTORY_SHA=old
 def test_actual_loop_with_inert_seams(self):
  spec=importlib.util.spec_from_file_location('inert_loop',ROOT/'tests/inert_loop_fixture.py');fixture=importlib.util.module_from_spec(spec);spec.loader.exec_module(fixture)
  with tempfile.TemporaryDirectory() as td:
   result=fixture.run(d,self.c,Path(td));self.assertEqual(result['native_calls'],394)
 def test_missing_result_cannot_pass(self):
  with tempfile.TemporaryDirectory() as td:
   work=Path(td);(work/'result.json').write_text(json.dumps({'status':'INCOMPLETE'}));self.reject(d.verify_success,self.c,'0'*64,work,work)
 def actual_cocycle_output(self):
  data=(ROOT/'tests/fixtures/cocycle-original-run39243482103.stdout').read_bytes()
  self.assertEqual(len(data),638)
  self.assertEqual(d.f.sha(data),'50e00f731b1b925266a0dc78d3d27253439c28e81eb3b6d91e9472ccaf3345cb')
  return data.decode('utf-8')
 def test_actual_coded_unknown_identifier_regression(self):
  self.assertEqual(d.failure_diagnostics(d.TARGETS[0],self.actual_cocycle_output()),
   {'unknown_identifiers':[(60,33,'position_cancel'),(61,25,'position_triangle')],'authenticated_cascade_headers':[]})
 def test_plain_coded_and_mixed_unknown_identifier_formats(self):
  for module,expected in d.EXPECTED_UNKNOWN.items():
   for style in ['plain','coded','mixed']:
    lines=[]
    for i,(line,col,name) in enumerate(expected):
     category='error' if style=='plain' or (style=='mixed' and i%2) else 'error(lean.unknownIdentifier)'
     lines.append(module.replace('.','/')+f'.lean:{line}:{col or 3}: {category}: Unknown identifier `{name}`')
    with self.subTest(module=module,style=style):
     result=d.failure_diagnostics(module,'\n'.join(lines)+'\n')
     self.assertEqual(result['unknown_identifiers'],[(line,col or 3,name) for line,col,name in expected])
     self.assertEqual(result['authenticated_cascade_headers'],[])
 def test_actual_coded_output_rejects_mutations_and_extra_errors(self):
  text=self.actual_cocycle_output();headers=[line for line in text.splitlines() if ': error(' in line]
  mutations={
   'wrong source':text.replace('SpectreClusters/ReverseClusterCocycleIntegration.lean','Wrong/Source.lean',1),
   'suffix source alias':text.replace('SpectreClusters/ReverseClusterCocycleIntegration.lean','OtherSpectreClusters/ReverseClusterCocycleIntegration.lean',1),
   'wrong line':text.replace(':60:33:',':59:33:',1),
   'wrong column':text.replace(':60:33:',':60:34:',1),
   'wrong identifier':text.replace('Unknown identifier `position_cancel`','Unknown identifier `position_cancelled`',1),
   'wrong message case':text.replace('Unknown identifier','unknown identifier',1),
   'wrong message':text.replace('Unknown identifier `position_cancel`','type mismatch',1),
   'missing first':text.replace(headers[0]+'\n','',1),
   'missing second':text.replace(headers[1]+'\n','',1),
   'duplicate first':text+headers[0]+'\n',
   'duplicate second':text+headers[1]+'\n',
   'plain duplicate':text+headers[0].replace('error(lean.unknownIdentifier)','error')+'\n',
  }
  for label in ['error(lean.typeMismatch)','error(lean.unsupported)','error(other.unknownIdentifier)',
                'error(lean.UnknownIdentifier)','error(lean.unknownIdentifier.extra)','error()',
                'error(lean.unknownIdentifier','error(lean.unknownIdentifier))','error[lean.unknownIdentifier]',
                'error (lean.unknownIdentifier)','error(lean.unknownIdentifier) extra']:
   mutations['replaced category '+label]=text.replace('error(lean.unknownIdentifier)',label,1)
   mutations['extra category '+label]=text+headers[0].replace('error(lean.unknownIdentifier)',label)+'\n'
  mutations['extra unlocated coded error']=text+'error(lean.unsupported): unexpected\n'
  mutations['extra spaced malformed code']=text+'error (lean.unsupported): unexpected\n'
  mutations['extra no-space coded duplicate']=text+headers[0].replace(': error(',':error(')+'\n'
  mutations['extra no-space unknown code']=text+headers[0].replace(': error(lean.unknownIdentifier)',':error(lean.other)')+'\n'
  mutations['extra no-space plain duplicate']=text+headers[0].replace(': error(lean.unknownIdentifier)',':error')+'\n'
  mutations['extra wrong-column malformed duplicate']=text+headers[0].replace(':60:33: error(',':60:34:error(')+'\n'
  for category in ['error)','error]','error}','error{lean.other}','error<lean.other>','error (lean.other)']:
   mutations['extra malformed token '+category]=text+headers[0].replace('error(lean.unknownIdentifier)',category)+'\n'
  mutations['extra bare error']=text+'error\n'
  mutations['extra plain error']=text+'error: unexpected\n'
  for label,bad in mutations.items():
   with self.subTest(mutation=label):self.reject(d.failure_diagnostics,d.TARGETS[0],bad)
 def test_coded_unknown_does_not_authorize_coded_cascades(self):
  module=d.TARGETS[1];path=module.replace('.','/')+'.lean'
  unknown=path+':34:15: error(lean.unknownIdentifier): Unknown identifier `translated_contracting`\n'
  cascades=''.join(path+f':{line}:{col}: error: {message}\n' for (line,col),message in d.CASCADE.items())
  result=d.failure_diagnostics(module,unknown+cascades)
  self.assertEqual(result['unknown_identifiers'],[(34,15,'translated_contracting')])
  self.assertEqual(result['authenticated_cascade_headers'],[(line,col,message) for (line,col),message in d.CASCADE.items()])
  for (line,col),message in d.CASCADE.items():
   plain=path+f':{line}:{col}: error: {message}\n'
   for category in ['error(lean.unknownIdentifier)','error(lean.unsolvedGoals)','error(lean.kernel)']:
    with self.subTest(location=(line,col),category=category):
     self.reject(d.failure_diagnostics,module,unknown+cascades.replace(plain,plain.replace(': error:',': '+category+':')))
   self.reject(d.failure_diagnostics,module,unknown+cascades.replace(plain,plain.replace(f':{line}:{col}:',f':{line+1}:{col}:')))
   self.reject(d.failure_diagnostics,module,unknown+cascades.replace(plain,plain.replace(message,message+' altered')))
 def test_actual_coded_output_preserves_terminal_exit_and_resource_gates(self):
  spec=importlib.util.spec_from_file_location('coded_terminal_fixture',ROOT/'tests/inert_success_fixture.py');fixture=importlib.util.module_from_spec(spec);spec.loader.exec_module(fixture)
  with tempfile.TemporaryDirectory() as td:
   work=Path(td);data=fixture.make(d,self.c,work);evidence=work/'evidence';commands=data['commands']
   command=next(row for row in commands if row['name']=='compile-original-'+d.TARGETS[0]);name=command['name']
   actual=self.actual_cocycle_output().encode();previous=command['captures']['stdout']['bytes']
   command['stdout_sha256']=d.f.sha(actual);command['captures']['stdout']={'bytes':len(actual),'sha256':d.f.sha(actual)}
   for parent in [work/'logs',evidence/'logs']:(parent/(name+'.stdout')).write_bytes(actual)
   result=d.f.load_json(evidence/'result.json');result['complete_log_bytes']+=len(actual)-previous
   def write_commands():
    (evidence/'commands.jsonl').write_text(''.join(json.dumps(row,sort_keys=True,separators=(',',':'))+'\n' for row in commands))
    result['terminal_receipts']['commands.jsonl']=d.f.file_sha(evidence/'commands.jsonl');d.a.write_json(evidence/'result.json',result)
   write_commands();old=d.a.RUNTIME_INVENTORY_SHA;d.a.RUNTIME_INVENTORY_SHA=data['synthetic_runtime_sha']
   try:
    d.verify_success(self.c,data['contract_sha'],evidence,work)
    d.validate_capture_collection(self.c,work,Clock())
    mutations=[('exit_code',0,'original unexpected pass'),('exit_code',2,'unexpected original exit/status'),
     ('timed_out',True,'unsafe command receipt'),('memory_exceeded',True,'unsafe command receipt'),
     ('log_overflow',True,'unsafe command receipt'),('surviving_children',True,'unsafe command receipt'),
     ('process_group_empty',False,'unsafe command receipt'),('descendants_empty',False,'unsafe command receipt'),
     ('requested_timeout_seconds',181,'full command provenance differs'),
     ('max_log_bytes',2*1024**2,'command limits differ'),
     ('limits',{**command['limits'],'rss_tree_bytes':9*d.GIB},'command limits differ')]
    for key,value,message in mutations:
     with self.subTest(gate=key,value=value):
      before=copy.deepcopy(command[key]);command[key]=value;write_commands()
      with self.assertRaisesRegex(ValueError,message):d.verify_success(self.c,data['contract_sha'],evidence,work)
      command[key]=before;write_commands()
    d.verify_success(self.c,data['contract_sha'],evidence,work)
   finally:d.a.RUNTIME_INVENTORY_SHA=old
if __name__=='__main__':unittest.main()
