"""Only guarded source tests. Never invoke Lean or a runtime CLI."""
import ast,copy,hashlib,json,sys,tempfile,unittest
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1];sys.path.insert(0,str(ROOT/'ci'))
import cache_diagnostic as a
import test_h5_as24 as previous_tests
h=a.higher;RAW='audit-AuditHigherPhysicalEndpoints';FIELD='higher_h5_raw_auditor_heap_mib'
class Heap5120Tests(unittest.TestCase):
 def c(self):return a.f.load_json(ROOT/'origin/higher-h5-heap5120-contract.json')
 def old(self):return a.f.load_json(ROOT/'origin/higher-h5-as24-contract.json')
 def expected(self,work,c):
  e=previous_tests.H5AS24Tests().expected(work,c);e['stage_rows']=[{'module':m} for m in c['stages']['H5_higher_assembly']['modules']];return e
 def specs(self,c,work):return a.transport.command_specs(self.expected(work,c),a)
 def fixture(self,work,c):
  helper=previous_tests.H5AS24Tests();helper.expected=self.expected;return helper.fixture(work,c)
 def test_exact_profile(self):
  c=self.c();a.validate_diagnostic_profile(c);self.assertEqual(c[FIELD],5120);self.assertEqual(c['lean_heap_mib'],4096);self.assertEqual(c['diagnostic_rss_gib'],8)
 def test_only_one_of_103_specs_changes(self):
  with tempfile.TemporaryDirectory() as d:
   current=self.specs(self.c(),Path(d));old=self.specs(self.old(),Path(d));self.assertEqual(len(current),103);self.assertEqual(len(old),103);changed=[]
   for n,o in zip(current,old):
    self.assertEqual(n['name'],o['name'])
    if n!=o:
     changed.append(n['name']);expected=copy.deepcopy(o);self.assertEqual(expected['argv'].count('-M4096'),1);expected['argv']=[('-M5120' if x=='-M4096' else x) for x in expected['argv']];self.assertEqual(n,expected)
   self.assertEqual(changed,[RAW]);self.assertEqual(sum(n==o for n,o in zip(current,old)),102)
 def test_previous_as24_contract_is_exact_and_valid(self):
  self.assertEqual(a.f.file_sha(ROOT/'origin/higher-h5-as24-contract.json'),'3e38bbd56e30868f63be4f8ff68485c0b4a643117bf78b763472c245b07f6630');a.validate_diagnostic_profile(self.old())
  raw=self.specs(self.old(),Path('/synthetic/work'))[-1];self.assertEqual(raw['name'],RAW);self.assertIn('-M4096',raw['argv']);self.assertEqual(raw['address_space_bytes'],24*a.GIB)
 def test_all_historical_raw_specs_keep_4096(self):
  for p in ['higher-producer-contract.json','higher-h0-h3-producer-contract.json','higher-h5-as12-contract.json','higher-h5-as24-contract.json']:
   c=a.f.load_json(ROOT/'origin'/p);specs=h.auditor_specs(c,Path('/synthetic/work'),Path('/synthetic/runtime'),[],a);self.assertIn('-M4096',specs[-1]['argv']);self.assertNotIn('-M5120',str(specs))
 def test_all_other_current_lean_arguments_keep_4096(self):
  for s in self.specs(self.c(),Path('/synthetic/work')):
   if s['name']!=RAW:self.assertNotIn('-M5120',s['argv']);self.assertNotIn('-M6144',s['argv'])
 def test_all_other_caps_and_scopes_unchanged(self):
  c=self.c();old=self.old()
  for key in old:
   if any(t in key for t in ['timeout','deadline','max_bytes','_heap_','_rss_','minimum_','failure_evidence_grace']):self.assertEqual(c[key],old[key],key)
  for key in ['stages','source_archive','origin_lock','producer_contracts','native_h0_h3_origin_lock','module_checker_timeout_exceptions','execution_stages','locked_origin_stages','higher_h5_as24','higher_h5_retry','higher_h5_raw_auditor_address_space_gib']:self.assertEqual(c[key],old[key],key)
  for path,pin in old['inputs'].items():
   if path.startswith(('src/','auditors/','locks/')):self.assertEqual(c['inputs'][path],pin,path)
 def test_current_and_previous_serialized_rows_pass(self):
  for c in [self.c(),self.old()]:
   with tempfile.TemporaryDirectory() as d:self.assertEqual(a.transport.validate_commands(*self.fixture(Path(d),c),a),0)
 def test_raw_old_heap_receipt_rejected_by_current_expected_argv(self):
  with tempfile.TemporaryDirectory() as d:
   rows,e,expected=self.fixture(Path(d),self.c());rows[-1]['argv']=[('-M4096' if x=='-M5120' else x) for x in rows[-1]['argv']]
   with self.assertRaises(Exception):a.transport.validate_commands(rows,e,expected,a)
 def test_old_receipt_cannot_claim_new_heap(self):
  with tempfile.TemporaryDirectory() as d:
   rows,e,expected=self.fixture(Path(d),self.old());rows[-1]['argv']=[('-M5120' if x=='-M4096' else x) for x in rows[-1]['argv']]
   with self.assertRaises(Exception):a.transport.validate_commands(rows,e,expected,a)
 def test_other_command_heap_increase_rejected(self):
  with tempfile.TemporaryDirectory() as d:
   rows,e,expected=self.fixture(Path(d),self.c());row=next(r for r in rows if r['name']!=RAW and '-M4096' in r['argv']);row['argv']=[('-M5120' if x=='-M4096' else x) for x in row['argv']]
   with self.assertRaises(Exception):a.transport.validate_commands(rows,e,expected,a)
 def test_unselected_6144_rejected(self):
  with tempfile.TemporaryDirectory() as d:
   rows,e,expected=self.fixture(Path(d),self.c());rows[-1]['argv']=[('-M6144' if x=='-M5120' else x) for x in rows[-1]['argv']]
   with self.assertRaises(Exception):a.transport.validate_commands(rows,e,expected,a)
 def test_duplicate_heap_argument_rejected(self):
  with tempfile.TemporaryDirectory() as d:
   rows,e,expected=self.fixture(Path(d),self.c());rows[-1]['argv'].insert(2,'-M6144')
   with self.assertRaises(Exception):a.transport.validate_commands(rows,e,expected,a)
 def test_scope_without_selector_rejected(self):
  c=self.c();del c[FIELD]
  with self.assertRaises(Exception):a.validate_diagnostic_profile(c)
 def test_selector_without_scope_rejected(self):
  c=self.c();del c['higher_h5_heap5120']
  with self.assertRaises(Exception):a.validate_diagnostic_profile(c)
 def test_as24_required(self):
  c=self.c();del c['higher_h5_raw_auditor_address_space_gib']
  with self.assertRaises(Exception):a.validate_diagnostic_profile(c)
 def test_historical_stage_profile_cannot_select_new_heap(self):
  c=a.f.load_json(ROOT/'origin/higher-producer-contract.json');c[FIELD]=5120
  with self.assertRaises(Exception):a.validate_diagnostic_profile(c)
 def test_provenance_and_scope_mutations_rejected(self):
  for key,value in [('raw_auditor_command','compile-auditor-AuditHigherPhysicalEndpoints'),('lean_heap_mib',6144),('rss_tree_bytes',16*a.GIB),('address_space_bytes',32*a.GIB),('failed_h5_objects_reused',True),('previous_contract_sha256','0'*64),('official_memory_source_binding_sha256','0'*64),('failed_h5_terminal_review_sha256','0'*64)]:
   c=self.c();c['higher_h5_heap5120'][key]=value
   with self.assertRaises(Exception):a.validate_diagnostic_profile(c)
 def test_actual_failure_and_diagnostics_retained(self):
  c=self.c();last=a.f.load_json(ROOT/'origin/failed-h5-as24-last-command.json');result=a.f.load_json(ROOT/'origin/failed-h5-as24-result.json');obs=a.f.load_json(ROOT/'origin/failed-h5-as24-ir-observation.json')
  self.assertEqual(result['run_id'],'39156079183');self.assertEqual(result['workflow_commit'],'f20a3135ad6f49dd3a8050053d1affd885891016');self.assertEqual(last['exit_code'],1);self.assertEqual(last['elapsed_seconds'],6.626029);self.assertEqual(last['address_space_bytes'],24*a.GIB);self.assertEqual(last['peak_sampled_tree_rss_bytes'],6770839552);self.assertEqual(last['max_sampled_process_virtual_size_bytes'],14166933504);self.assertIn('-M4096',last['argv']);self.assertTrue(obs['matches_expected_h0']);self.assertEqual(obs['observed']['sha256'],'c23815bcc4aa90a6789c65b76c996848cab3178cde51504fe42b3d352f1c858d');self.assertFalse(c['higher_h5_heap5120']['failed_h5_objects_reused']);self.assertEqual(c['fresh_execution_module_count'],27)
 def test_official_source_bytes_and_semantics(self):
  p=ROOT/'origin/lean-memory';b=a.f.load_json(p/'SOURCE_BINDING.json');self.assertEqual(b['commit'],'11acb17ec6b07a8f9e9173e6845197929540936b')
  for row in b['sources']:
   data=(p/row['local_name']).read_bytes();self.assertEqual(len(data),row['bytes']);self.assertEqual(hashlib.sha256(data).hexdigest(),row['sha256']);self.assertEqual(hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest(),row['git_blob_sha'])
  self.assertEqual(a.f.file_sha(p/'Shell.lean'),b['runtime_source_row']['sha256']);self.assertIn('maxMemory.toUSize * 1024 * 1024',(p/'Shell.lean').read_text());self.assertIn('r == 0 || r < g_max_memory',(p/'memory.cpp').read_text());self.assertEqual(b['semantics']['measured_sampled_margin_bytes'],1819095040)
 def test_archive_not_redundantly_in_inputs(self):
  c=self.c();self.assertNotIn('owned-sources.tar.gz',c['inputs']);self.assertEqual(c['source_archive'],self.old()['source_archive'])
 def test_command_closure_bytes_unchanged(self):
  old=(ROOT/'origin/higher-h5-as24-contract.json');c=a.f.load_json(old)
  # Cache helper changes only its approved higher_policy digest literal.
  s=(ROOT/'ci/cache_diagnostic.py').read_text();new=a.f.load_json(ROOT/'contract.json')['inputs']['ci/higher_policy.py']['sha256'];oldsha=c['inputs']['ci/higher_policy.py']['sha256'];self.assertEqual(s.count(new),1);self.assertEqual(hashlib.sha256(s.replace(new,oldsha).encode()).hexdigest(),c['inputs']['ci/cache_diagnostic.py']['sha256'])

def bad_value(value):
 def test(self):
  c=self.c();c[FIELD]=value
  with self.assertRaises(Exception):a.validate_diagnostic_profile(c)
 return test
for name,value in [('old',4096),('unselected',6144),('string','5120'),('float',5120.0),('bool',True),('null',None),('zero',0)]:setattr(Heap5120Tests,'test_invalid_fixed_heap_'+name,bad_value(value))
