"""Finite source-only controls. The joined runner installs permanent guards before import."""
import ast,copy,hashlib,json,sys,tempfile,unittest
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1];sys.path.insert(0,str(ROOT/'ci'))
import cache_diagnostic as a
import test_h5_heap5120 as oldtests
import test_higher_composition as receipt_tests
h=a.higher;RAW='audit-AuditHigherPhysicalEndpoints';FIELD='higher_h5_raw_auditor_heap_mib'
STATEMENTS=['  IO.println "HIGHER_AUDIT_PHASE '+p+'"\n' for p in ['entry','reference_import_returned','project_import_returned','model_checked']]+['      IO.println "HIGHER_AUDIT_PHASE endpoint_checked"\n']
class Heap7168Tests(unittest.TestCase):
 def c(self):return a.f.load_json(ROOT/'contract.json')
 def old(self):return a.f.load_json(ROOT/'origin/higher-h5-heap5120-contract.json')
 def specs(self,c,work):return oldtests.Heap5120Tests().specs(c,work)
 def fixture(self,work,c):return oldtests.Heap5120Tests().fixture(work,c)
 def rows(self):return receipt_tests.RawReceiptTests().rows()
 def lines(self):
  rows=self.rows();return h.PHASE_MARKERS[:4]+[json.dumps(rows[0]),h.PHASE_MARKERS[4],json.dumps(rows[1]),h.PHASE_MARKERS[5],'HIGHER_PHYSICAL_ENDPOINT_AUDIT_PASSED']
 def text(self):return '\n'.join(self.lines())+'\n'
 def test_exact_new_and_old_profiles(self):
  a.validate_diagnostic_profile(self.c());a.validate_diagnostic_profile(self.old());self.assertEqual(self.c()[FIELD],7168);self.assertEqual(self.old()[FIELD],5120);self.assertEqual(self.c()['lean_heap_mib'],4096)
 def test_103_specs_only_raw_heap_changes(self):
  new=self.specs(self.c(),Path('/synthetic'));old=self.specs(self.old(),Path('/synthetic'));self.assertEqual(len(new),103);self.assertEqual(len(old),103);changed=[]
  for n,o in zip(new,old):
   if n!=o:
    changed.append(n['name']);expected=copy.deepcopy(o);self.assertEqual(expected['argv'].count('-M5120'),1);expected['argv']=[('-M7168' if x=='-M5120' else x) for x in expected['argv']];self.assertEqual(n,expected)
  self.assertEqual(changed,[RAW]);self.assertEqual(sum(n==o for n,o in zip(new,old)),102)
 def test_all_other_caps_scopes_and_producers_exact(self):
  c=self.c();old=self.old()
  for k in old:
   if k!=FIELD and any(t in k for t in ['timeout','deadline','max_bytes','_heap_','_rss_','minimum_','failure_evidence_grace']):self.assertEqual(c[k],old[k],k)
  for k in ['stages','source_archive','origin_lock','producer_contracts','native_h0_h3_origin_lock','module_checker_timeout_exceptions','execution_stages','locked_origin_stages','higher_h5_as24','higher_h5_retry','higher_h5_heap5120','higher_h5_raw_auditor_address_space_gib']:self.assertEqual(c[k],old[k],k)
  for path,pin in old['inputs'].items():
   if path.startswith(('src/','auditors/','locks/')) and path!='auditors/AuditHigherPhysicalEndpoints.lean':self.assertEqual(c['inputs'][path],pin,path)
 def test_reverse_five_statements_recovers_exact_auditor(self):
  old=(ROOT/'origin/AuditHigherPhysicalEndpoints.pre-phase.lean').read_bytes();new=(ROOT/'auditors/AuditHigherPhysicalEndpoints.lean').read_bytes()
  for s in STATEMENTS:self.assertEqual(new.count(s.encode()),1);new=new.replace(s.encode(),b'',1)
  self.assertEqual(new,old);self.assertEqual(hashlib.sha256(old).hexdigest(),'ba9a502d5f121719b7fff10c73d3bf9cfa6857a0f2a42e99b36d39051b64af13')
 def test_audit_definitions_and_imports_exact(self):
  old=(ROOT/'origin/AuditHigherPhysicalEndpoints.pre-phase.lean').read_text();new=(ROOT/'auditors/AuditHigherPhysicalEndpoints.lean').read_text();self.assertEqual(old.split('def main ')[0],new.split('def main ')[0]);self.assertEqual(new.count('IO.println "HIGHER_AUDIT_PHASE'),5);self.assertEqual(new.count('  for pair in HigherPhysicalAudit.targets do'),1)
  self.assertIn('("extensions_loaded", .bool false)]).compress\n'+STATEMENTS[-1],new)
 def test_exact_new_success_and_legacy_success(self):
  self.assertEqual(h.audit_output(self.text(),a,self.c()),self.rows());old=receipt_tests.RawReceiptTests();self.assertEqual(h.audit_output(old.text(old.rows()),a,self.old()),old.rows())
 def test_new_grammar_cannot_satisfy_old(self):
  with self.assertRaises(Exception):h.audit_output(self.text(),a,self.old())
 def test_old_grammar_cannot_satisfy_new(self):
  old=receipt_tests.RawReceiptTests()
  with self.assertRaises(Exception):h.audit_output(old.text(old.rows()),a,self.c())
 def test_partial_prefix_never_success(self):
  for n in range(9):
   with self.assertRaises(Exception):h.audit_output('\n'.join(self.lines()[:n])+'\n',a,self.c())
 def test_duplicate_extra_reordered_and_changed_markers_refused(self):
  lines=self.lines();variants=[lines[:1]+lines,lines+['extra'],lines[:4]+[lines[5],lines[4]]+lines[6:],lines[:5]+lines[6:],['HIGHER_AUDIT_PHASE unknown']+lines[1:],list(reversed(lines)),lines[:3]+['']+lines[3:]]
  for variant in variants:
   with self.assertRaises(Exception):h.audit_output('\n'.join(variant)+'\n',a,self.c())
 def test_each_fixed_marker_slot_required(self):
  for i in [0,1,2,3,5,7]:
   lines=self.lines();lines[i]='HIGHER_AUDIT_PHASE altered'
   with self.assertRaises(Exception):h.audit_output('\n'.join(lines)+'\n',a,self.c())
 def test_original_json_predicates_still_checked(self):
  for key,value in [('axioms',['sorryAx']),('raw_type_equal',False),('raw_model_equal',False),('closed_type_and_proof',False),('trust_level',1),('plugins_enabled',True),('target','Wrong')]:
   lines=self.lines();row=json.loads(lines[4]);row[key]=value;lines[4]=json.dumps(row)
   with self.assertRaises(Exception):h.audit_output('\n'.join(lines)+'\n',a,self.c())
 def test_exact_serialized_profiles_pass(self):
  for c in [self.c(),self.old()]:
   with tempfile.TemporaryDirectory() as d:self.assertEqual(a.transport.validate_commands(*self.fixture(Path(d),c),a),0)
 def test_old_heap_rejected_for_current(self):
  with tempfile.TemporaryDirectory() as d:
   rows,e,expected=self.fixture(Path(d),self.c());rows[-1]['argv']=[('-M5120' if x=='-M7168' else x) for x in rows[-1]['argv']]
   with self.assertRaises(Exception):a.transport.validate_commands(rows,e,expected,a)
 def test_new_heap_rejected_for_original(self):
  with tempfile.TemporaryDirectory() as d:
   rows,e,expected=self.fixture(Path(d),self.old());rows[-1]['argv']=[('-M7168' if x=='-M5120' else x) for x in rows[-1]['argv']]
   with self.assertRaises(Exception):a.transport.validate_commands(rows,e,expected,a)
 def test_other_command_heap_increase_refused(self):
  with tempfile.TemporaryDirectory() as d:
   rows,e,expected=self.fixture(Path(d),self.c());row=next(x for x in rows if x['name']!=RAW and '-M4096' in x['argv']);row['argv']=[('-M7168' if x=='-M4096' else x) for x in row['argv']]
   with self.assertRaises(Exception):a.transport.validate_commands(rows,e,expected,a)
 def test_provenance_and_marker_scope_mutations_refused(self):
  for key,value in [('lean_heap_mib',8192),('phase_markers',[]),('failure_location_exact',True),('phase_peaks_observed',True),('failed_h5_objects_reused',True),('passing_standalone_probe_terminal_review_sha256','0'*64),('failed_h5_terminal_review_sha256','0'*64),('rss_tree_bytes',9*a.GIB),('address_space_bytes',32*a.GIB)]:
   c=self.c();c['higher_h5_heap7168'][key]=value
   with self.assertRaises(Exception):a.validate_diagnostic_profile(c)
 def test_old_auditor_pin_cannot_satisfy_new_profile(self):
  c=self.c();c['inputs']['auditors/AuditHigherPhysicalEndpoints.lean']=self.old()['inputs']['auditors/AuditHigherPhysicalEndpoints.lean']
  with self.assertRaises(Exception):a.validate_diagnostic_profile(c)
 def test_new_auditor_pin_cannot_satisfy_old_profile(self):
  c=self.old();c['inputs']['auditors/AuditHigherPhysicalEndpoints.lean']=self.c()['inputs']['auditors/AuditHigherPhysicalEndpoints.lean']
  with self.assertRaises(Exception):a.validate_diagnostic_profile(c)
 def test_actual_failure_probe_and_no_reused_payload(self):
  c=self.c();last=a.f.load_json(ROOT/'origin/failed-h5-heap5120-last-command.json');obs=a.f.load_json(ROOT/'origin/passing-heap-probe-observation.json')
  self.assertEqual(last['exit_code'],1);self.assertEqual(last['peak_sampled_tree_rss_bytes'],6776922112);self.assertIn('-M5120',last['argv']);self.assertEqual(obs['compiled_default_mib'],0);self.assertFalse(obs['override_present']);self.assertFalse(obs['runtime_threshold_directly_observed']);self.assertFalse(obs['failed_auditor_process_observed']);self.assertEqual(c['fresh_execution_module_count'],27);self.assertFalse(c['higher_h5_heap7168']['failed_h5_objects_reused'])
 def test_failure_markers_logs_and_whole_command_peaks_survive_collector(self):
  c=self.c();col=a.load_helper('collect_evidence')
  with tempfile.TemporaryDirectory() as d:
   root=Path(d);e=root/'evidence';e.mkdir();logs=root/'logs';logs.mkdir();partial='\n'.join(h.PHASE_MARKERS[:2])+'\n';err='(interpreter) excessive memory consumption\n'
   (logs/(RAW+'.stdout')).write_text(partial);(logs/(RAW+'.stderr')).write_text(err);values={'result.json':{'status':'FAILED_OR_INCOMPLETE','contract_sha256':h.digest(c)},'last_command.json':{'exit_code':1,'peak_sampled_tree_rss_bytes':6776922112,'max_sampled_process_virtual_size_bytes':14166933504,'max_sampled_tree_virtual_size_bytes':14174404608}}
   for p,v in values.items():(e/p).write_bytes(a.f.json_bytes(v))
   r=col.collect(root,c,h.digest(c));self.assertTrue(r['all_available_files_copied']);self.assertFalse(r['replay_acceptance_evidence_complete']);self.assertEqual((root/'upload/logs'/(RAW+'.stdout')).read_text(),partial);self.assertEqual((root/'upload/logs'/(RAW+'.stderr')).read_text(),err)
   for p in values:self.assertEqual((root/'upload'/p).read_bytes(),(e/p).read_bytes())
 def test_no_new_observers_or_transport_or_collector_changes(self):
  c=self.c();old=self.old()
  for path in ['ci/fresh_stage.py','ci/conditional_transport.py','ci/collect_evidence.py']:self.assertEqual(c['inputs'][path],old['inputs'][path])
  source=(ROOT/'ci/cache_diagnostic.py').read_text();new=c['inputs']['ci/higher_policy.py']['sha256'];oldsha=old['inputs']['ci/higher_policy.py']['sha256'];self.assertEqual(source.count(new),1);self.assertEqual(hashlib.sha256(source.replace(new,oldsha).encode()).hexdigest(),old['inputs']['ci/cache_diagnostic.py']['sha256'])
 def test_envelope_exact_inactive_metadata(self):
  c=self.c();w=(ROOT/'.github/workflows/conditional-geometry.yml').read_text();self.assertEqual(c['publication_parent_commit'],'ecf44513ecddd29507fec9f6046d47771fd6e0cd');self.assertEqual(c['publication_branch'],'verify/higher-h5-heap7168-20261018');self.assertIn(c['publication_branch'],w);self.assertIn(h.digest(c),w);self.assertEqual(w.count('    if: ${{ false }}'),1);self.assertEqual(c['execution_stages'],['H5_higher_assembly'])
def invalid(value):
 def test(self):
  c=self.c();c[FIELD]=value
  with self.assertRaises(Exception):a.validate_diagnostic_profile(c)
 return test
for name,value in [('old',5120),('unselected',6144),('larger',8192),('string','7168'),('float',7168.0),('bool',True),('zero',0),('null',None)]:setattr(Heap7168Tests,'test_invalid_fixed_heap_'+name,invalid(value))
