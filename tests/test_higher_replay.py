"""Data-only higher replay controls; never execute Lean, artifacts or network code."""
import copy,hashlib,importlib.util,json,sys,unittest
from pathlib import Path
from unittest.mock import patch
ROOT=Path(__file__).resolve().parents[1];sys.path.insert(0,str(ROOT/'ci'))
import cache_diagnostic as a
h=a.higher
class HigherTests(unittest.TestCase):
 def contract(self):return a.f.load_json(ROOT/'contract.json')
 def test_current_profile(self):a.validate_diagnostic_profile(self.contract())
 def test_current_partition(self):a.validate_stage_plan(self.contract())
 def test_exact_native_origins(self):
  c=self.contract();lock=a.f.load_json(ROOT/c['origin_lock']['path'])
  if lock['stages'].get(h.H4_STAGE,{}).get('selection_pending') is True:
   with self.assertRaises(Exception):a.validate_continuation_origins(c)
  else:a.validate_continuation_origins(c)
 def test_distribution_exact(self):a.validate_distribution_layout(self.contract())
 def test_no_fresh_async_options(self):
  c=self.contract()
  for m in [a.ASYNC_TARGET,*h.CHECKS,'ClarkSeed.PhysicalDimensions']:self.assertEqual(a.module_compile_arguments(c,m),[])
 def test_only_two_checker_exceptions(self):
  c=self.contract()
  for r in c['modules']:self.assertEqual(h.checker_seconds(c,r['module']),h.CHECKS.get(r['module'],(120,))[0])
 def test_original_checker_profile_unchanged(self):
  c=a.f.load_json(ROOT/'origin/producer-contract.json')
  for m in h.CHECKS:self.assertEqual(h.checker_seconds(c,m),120)
 def test_native_async_receipt_profile_preserved(self):
  c=a.f.load_json(ROOT/'origin/continuation-producer-contract.json');self.assertEqual(a.module_compile_arguments(c,a.ASYNC_TARGET),['-DElab.async=false']);self.assertEqual(a.module_compile_arguments(c,'ClarkSeed.PhysicalDimensions'),[])
 def test_no_uniform_claim(self):
  c=self.contract();self.assertFalse(c['all_dimension_uniform_proof_certified']);self.assertTrue(c['higher_endpoints_have_no_C_premise']);self.assertEqual(len(c['higher_endpoints']),2)
 def test_higher_width_four(self):
  c=self.contract();self.assertEqual(c['maximum_parallel_jobs'],4);self.assertEqual(c['workflow_aggregate_seconds'],19200);self.assertEqual(c['workflow_outer_runner_minutes'],330)
 def test_fresh_partition_exactly_once(self):
  c=self.contract();names=[m for sid in h.HSTAGES for m in c['stages'][sid]['modules']];self.assertEqual(len(names),len(set(names)));self.assertEqual(len(names),1138);self.assertFalse(set(names)&{m for sid in h.OLD for m in c['stages'][sid]['modules']})
 def test_h5_has_every_ancestor(self):self.assertEqual(self.contract()['stages'][h.HSTAGES[-1]]['admitted_stages'],h.OLD+h.HSTAGES[:-1])
 def test_partial_raw_audit_fails(self):
  r={'proof_scope':'higher-dimension-sources-and-c-free-endpoints','higher_endpoints_have_no_C_premise':True,'all_dimension_uniform_proof_certified':False,'final_C_proof_certified':False,'unconditional_monotile_proof_certified':False}
  with self.assertRaises(Exception):h.terminal_receipt(r,[],[],[],{},True,a)
 def test_nonfinal_raw_claim_fails(self):
  r={'proof_scope':'higher-dimension-sources-and-c-free-endpoints','higher_endpoints_have_no_C_premise':True,'all_dimension_uniform_proof_certified':False,'final_C_proof_certified':False,'unconditional_monotile_proof_certified':False}
  with self.assertRaises(Exception):h.terminal_receipt(r,[],[],[],{'higher_physical_endpoints':True},False,a)
 def test_source_archive_owned_context_count(self):
  c=self.contract();self.assertEqual(c['source_archive']['source_file_count'],1433);self.assertLess(c['source_archive']['source_bytes'],c['owned_source_max_bytes'])
 def test_no_final_C_source(self):self.assertNotIn('SpectreFinite.RadiusFivePruningHierarchy',{r['module'] for r in self.contract()['modules']})
 def test_freshness_certificate_rejects_wrong_origin(self):
  c=a.f.load_json(ROOT/'origin/higher-producer-contract.json');collector=a.load_helper('collect_evidence');locked=collector.locked_origin_rows(c);self.assertEqual(set(locked),set(h.OLD))
  with self.assertRaises(Exception):collector.make_cross_origin_certificate(c,'a'*64,{},h.HSTAGES[0],{},[],{},locked)

def mutation_test(key,value):
 def test(self):
  c=self.contract();c[key]=value
  with self.assertRaises(Exception):a.validate_diagnostic_profile(c)
 return test
for key,value in {'owned_module_count':1432,'fresh_higher_module_count':1139,'retained_historical_module_count':294,'higher_mathematical_closure_count':1433,'retained_context_outside_higher_closure_count':0,'diagnostic_timeout_seconds':181,'check_timeout_seconds':721,'outer_timeout_minutes':331,'aggregate_command_deadline_seconds':19201,'maximum_parallel_jobs':5,'workflow_aggregate_seconds':19201,'workflow_outer_runner_minutes':331,'owned_output_max_bytes':7*1024**3,'owned_source_max_bytes':33*1024**2,'cache_module_count':2804,'transport_timeout_seconds':1801,'final_C_proof_certified':True,'unconditional_monotile_proof_certified':True,'all_dimension_uniform_proof_certified':True,'higher_endpoints_have_no_C_premise':False,'fresh_research_modules_exactly_once':False,'module_compile_arguments':{},'module_checker_timeout_exceptions':{}}.items():setattr(HigherTests,'test_reject_'+key,mutation_test(key,value))
def stage_mutant(kind):
 def test(self):
  c=self.contract()
  if kind=='duplicate':c['stages']['H0_common']['modules'][1]=c['stages']['H0_common']['modules'][0]
  elif kind=='missing_ancestor':c['stages']['H1_coarse_contacts']['admitted_stages'].pop()
  elif kind=='missing_need':c['stages']['H5_higher_assembly']['needs'].pop()
  elif kind=='order':c['stages']['H3_contact_binding']['modules'].reverse()
  elif kind=='extra_stage':c['stages']['H6_unapproved']={}
  elif kind=='wrong_final':c['final_stage']='H0_common'
  with self.assertRaises(Exception):a.validate_stage_plan(c)
 return test
for key in ['duplicate','missing_ancestor','missing_need','order','extra_stage','wrong_final']:setattr(HigherTests,'test_stage_reject_'+key,stage_mutant(key))
class ExtensionTests(unittest.TestCase):
 @classmethod
 def setUpClass(cls):
  cls.c=a.f.load_json(ROOT/'contract.json');cls.inv={}
  cls.rows={};base=a.f.load_json(ROOT/'origin/base-required-modules.json')['modules']
  for r in base:
   p='lib/lean/'+r['module'].replace('.','/');ss=['.olean','.ilean']+(['.olean.server','.olean.private','.ir.sig','.ir'] if r['modern_module'] else [])
   companions={p+s:{'bytes':1,'sha256':hashlib.sha256((r['module']+s).encode()).hexdigest()} for s in ss}
   cls.inv.setdefault(r['package'],{'files':{},'bytes':0})['files'].update(companions)
   cls.rows[r['module']]={**r,'companions':companions}
  cls.base_interface=a.cache_interface_identity(cls.rows,cls.inv,a.RUNTIME_INVENTORY_SHA)
  lock=a.f.load_json(ROOT/'locks/cache-extension.json')
  for m,r in lock['approved_bootstrap_modules'].items():
   prefix='lib/lean/'+m.replace('.','/');cls.inv['mathlib']['files'].update({prefix+s:{'bytes':1,'sha256':hashlib.sha256((m+s).encode()).hexdigest()} for s in r['companion_suffixes']})
  for m,r in lock['extension_modules'].items():
   p='lib/lean/'+m.replace('.','/');rr={k:r[k] for k in ['module','package','path','sha256','modern_module']};rr['companions']={p+s:{'bytes':1,'sha256':'f'*64} for s in lock['cached_modern_companion_suffixes']};cls.rows[m]=rr;cls.inv['mathlib']['files'].update(rr['companions'])
 def check(self,rows=None,inv=None):
  original=a.f.load_json
  def read(path):return self.base_interface if Path(path)==ROOT/'origin/base-interface-identity.json' else original(path)
  with patch.object(a.f,'load_json',side_effect=read):return h.cache_extension(self.c,rows or self.rows,inv or self.inv,a.RUNTIME_INVENTORY_SHA,a)
 def test_exact_extension_accepts(self):
  base,old,full,cert=self.check();self.assertEqual(len(base),2786);self.assertEqual(len(cert['extension_companion_rows']),19);self.assertEqual(sum(len(r['companions']) for r in cert['extension_companion_rows'].values()),114);self.assertNotEqual(old,full)
 def test_changed_old_companion_rejected(self):
  rows=copy.deepcopy(self.rows);r=rows['Aesop'];next(iter(r['companions'].values()))['sha256']='0'*64
  with self.assertRaises(Exception):self.check(rows=rows)
 def test_missing_module_rejected(self):
  rows=dict(self.rows);rows.pop('Aesop')
  with self.assertRaises(Exception):self.check(rows=rows)
 def test_extra_module_rejected(self):
  rows=dict(self.rows);rows['Unknown.Module']={}
  with self.assertRaises(Exception):self.check(rows=rows)
 def test_new_native_library_rejected(self):
  inv=copy.deepcopy(self.inv);inv['mathlib']['files']['lib/new.so']={'bytes':1,'sha256':'a'*64}
  with self.assertRaises(Exception):self.check(inv=inv)
 def test_native_symlink_rejected(self):
  inv=copy.deepcopy(self.inv);inv['mathlib']['files']['lib/new.so']={'symlink':'other.data'}
  with self.assertRaises(Exception):self.check(inv=inv)
 def test_extension_source_changed_rejected(self):
  rows=copy.deepcopy(self.rows);rows['Mathlib.LinearAlgebra.Matrix.Orthogonal']['sha256']='0'*64
  with self.assertRaises(Exception):self.check(rows=rows)
 def test_cache_C_companion_rejected(self):
  rows=copy.deepcopy(self.rows);r=rows['Mathlib.LinearAlgebra.Matrix.Orthogonal'];r['companions']['lib/lean/Mathlib/LinearAlgebra/Matrix/Orthogonal.c']={'bytes':1,'sha256':'f'*64}
  with self.assertRaises(Exception):self.check(rows=rows)
 def test_missing_extension_companion_rejected(self):
  rows=copy.deepcopy(self.rows);r=rows['Mathlib.LinearAlgebra.Matrix.Orthogonal'];r['companions'].pop(next(iter(r['companions'])))
  with self.assertRaises(Exception):self.check(rows=rows)

class CurrentImportTests(unittest.TestCase):
 def fixture(self,root):
  runtime=Path(root)/'runtime';(runtime/'lib/lean').mkdir(parents=True);(runtime/'lib/lean/Init.olean').write_bytes(b'inert runtime fixture')
  rows={'Fixture.A':{'module':'Fixture.A','ordered_imports':[]},'Fixture.B':{'module':'Fixture.B','ordered_imports':['Fixture.A']}}
  output={m:{p:{'bytes':1,'sha256':'1'*64} for p in a.module_outputs(m)} for m in rows};final={**output['Fixture.A'],**output['Fixture.B']}
  c={'stages':{'OLD':{'modules':['Fixture.A']},'H5_higher_assembly':{'modules':['Fixture.B'],'admitted_stages':['OLD']}}}
  r={'module':'Fixture.B','source_sha256':'2'*64,'ordered_imports':a.direct_import_receipt(rows['Fixture.B'],rows,{'Fixture.A'},output['Fixture.A'],{},runtime),'outputs':output['Fixture.B'],'compiler_command':0,'checker_command':1,'checker_passed':True,'proof_scope':'higher-dimension-sources-and-c-free-endpoints'}
  return c,[r],final,rows,runtime
 def run_case(self,mutate=None):
  import tempfile
  with tempfile.TemporaryDirectory() as d:
   c,rs,final,rows,runtime=self.fixture(d)
   if mutate:mutate(rs[0])
   h.validate_current_imports(c,'H5_higher_assembly',rs,final,rows,{},runtime,a)
 def test_final_imports_exact(self):self.run_case()
 def test_final_import_missing(self):
  with self.assertRaises(Exception):self.run_case(lambda r:r['ordered_imports'].pop())
 def test_final_import_wrong_provider(self):
  with self.assertRaises(Exception):self.run_case(lambda r:r['ordered_imports'][0].update(provider='official_runtime'))
 def test_final_import_changed_companion(self):
  def mutate(r):next(iter(r['ordered_imports'][0]['companions'].values()))['sha256']='0'*64
  # Change only a serialized receipt copy, not the accepted predecessor inventory.
  import tempfile
  with tempfile.TemporaryDirectory() as d:
   c,rs,final,rows,runtime=self.fixture(d);rs=copy.deepcopy(rs);mutate(rs[0])
   with self.assertRaises(Exception):h.validate_current_imports(c,'H5_higher_assembly',rs,final,rows,{},runtime,a)
 def test_higher_receipt_rejects_inherited_C_field(self):
  with self.assertRaises(Exception):self.run_case(lambda r:r.update(conditional_C_remains_explicit=True))

class ExtraCacheTests(ExtensionTests):
 def test_unlisted_zero_provider_package_rejected(self):
  inv=copy.deepcopy(self.inv);inv.setdefault('Cli',{'files':{},'bytes':0})['files']['lib/lean/Cli/Unlisted.olean']={'bytes':1,'sha256':'0'*64}
  with self.assertRaisesRegex(Exception,'unlisted or missing cache/bootstrap'):self.check(inv=inv)
 def test_unlisted_same_root_provider_rejected(self):
  inv=copy.deepcopy(self.inv);inv['mathlib']['files']['lib/lean/Mathlib/Unlisted.olean']={'bytes':1,'sha256':'0'*64}
  with self.assertRaises(Exception):self.check(inv=inv)
 def test_new_companion_symlink_rejected(self):
  rows=copy.deepcopy(self.rows);r=rows['Mathlib.LinearAlgebra.Matrix.Orthogonal'];r['companions'][next(iter(r['companions']))]={'symlink':'different-object.data'}
  with self.assertRaises(Exception):self.check(rows=rows)
 def test_nested_search_directory_alias_rejected(self):
  inv=copy.deepcopy(self.inv);inv['mathlib']['files']['lib/lean/Mathlib/Alias']={'symlink':'../Analysis'}
  with self.assertRaises(Exception):self.check(inv=inv)
 def test_missing_bootstrap_provider_rejected(self):
  inv=copy.deepcopy(self.inv);del inv['mathlib']['files']['lib/lean/Cache/Main.olean']
  with self.assertRaises(Exception):self.check(inv=inv)
 def test_bootstrap_companion_symlink_rejected(self):
  inv=copy.deepcopy(self.inv);inv['mathlib']['files']['lib/lean/Cache/Main.ilean']={'symlink':'other.data'}
  with self.assertRaises(Exception):self.check(inv=inv)

if __name__=='__main__':unittest.main()
