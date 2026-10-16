import importlib.util,json,os,sys,tempfile,unittest
from pathlib import Path
from unittest.mock import patch
ROOT=Path(__file__).resolve().parents[1];sys.path.insert(0,str(ROOT/'ci'))
import cache_diagnostic as c
class Tests(unittest.TestCase):
 def test_env_no_ambient(self):
  with patch.dict(os.environ,{'GITHUB_TOKEN':'secret','MATHLIB_CACHE_GET_URL':'evil','LEAN_PATH':'old'}):
   e=c.safe_env(Path('/runtime'),Path('/home-new'),Path('/temp-new'))
  self.assertNotIn('GITHUB_TOKEN',e);self.assertNotIn('MATHLIB_CACHE_GET_URL',e);self.assertNotIn('LEAN_PATH',e);self.assertEqual(e['LAKE_NO_CACHE'],'true')
 def test_network_default_off(self):
  a=c.sandbox(['/bin/true'],runtime=Path('/runtime'),sources=[Path('/official')],writable=[Path('/cache')],cwd=Path('/official'),env={})
  self.assertIn('--unshare-all',a);self.assertNotIn('--share-net',a);self.assertNotIn('/',a);self.assertNotIn('/home',a)
 def test_explicit_official_network(self):
  a=c.sandbox(['/bin/true'],runtime=Path('/runtime'),sources=[Path('/official')],writable=[Path('/cache')],cwd=Path('/official'),env={},network=True)
  self.assertIn('--share-net',a);self.assertIn('--clearenv',a);self.assertIn('--new-session',a)
 def test_inventory_regular(self):
  with tempfile.TemporaryDirectory() as d:
   p=Path(d);(p/'a').write_text('abc');x=c.checked_inventory(p);self.assertEqual(x['bytes'],3);self.assertEqual(set(x['files']),{'a'})
 def test_inventory_byte_limit(self):
  with tempfile.TemporaryDirectory() as d:
   p=Path(d);(p/'a').write_text('abc')
   with self.assertRaises(Exception):c.checked_inventory(p,maximum=2)
 def test_reject_external_symlink(self):
  with tempfile.TemporaryDirectory() as d:
   p=Path(d);(p/'a').symlink_to('/etc/passwd')
   with self.assertRaises(Exception):c.checked_inventory(p,allow_links=True)
 def test_reject_hardlink(self):
  with tempfile.TemporaryDirectory() as d:
   p=Path(d);(p/'a').write_text('x');os.link(p/'a',p/'b')
   with self.assertRaises(Exception):c.checked_inventory(p)
 def test_allow_internal_relative_link(self):
  with tempfile.TemporaryDirectory() as d:
   p=Path(d);(p/'a').write_text('x');(p/'b').symlink_to('a');self.assertEqual(c.checked_inventory(p,allow_links=True)['files']['b'],{'symlink':'a'})
 def test_exact_dependency_allowlist(self):
  x=json.loads((ROOT/'locks/dependencies.json').read_text())['packages'];c.validate_dependencies(x);x[0]['url']='https://github.com/evil/mathlib4'
  with self.assertRaises(Exception):c.validate_dependencies(x)
 def test_mutable_pin_rejected(self):
  x=json.loads((ROOT/'locks/dependencies.json').read_text())['packages'];x[0]['rev']='main'
  with self.assertRaises(Exception):c.validate_dependencies(x)
 def test_required_closure_contains_all_roots(self):
  x=json.loads((ROOT/'locks/required-modules.json').read_text());self.assertLessEqual(set(x['roots']),{r['module'] for r in x['modules']});self.assertEqual(len(x['modules']),len({r['module'] for r in x['modules']}))
 def test_diagnostics_explicit_modern(self):
  x=json.loads((ROOT/'contract.json').read_text())
  for r in x['diagnostics']:
   s=(ROOT/'src'/(r['module'].replace('.','/')+'.lean')).read_text();self.assertIn('\nmodule\n', '\n'+s)
 def test_explicit_review_state(self):
  self.assertIn(json.loads((ROOT/'contract.json').read_text())['review_status'],('pending_independent_review','reviewed_for_execution'))

class NamespaceTests(unittest.TestCase):
 def test_empty_prefix_shadows(self):
  with tempfile.TemporaryDirectory() as d:
   a=Path(d)/'a';b=Path(d)/'b';(a/'Mathlib').mkdir(parents=True);(b/'Mathlib').mkdir(parents=True)
   with self.assertRaises(Exception):c.namespace_providers([a,b])
 def test_distinct_prefixes(self):
  with tempfile.TemporaryDirectory() as d:
   a=Path(d)/'a';b=Path(d)/'b';(a/'Mathlib').mkdir(parents=True);(b/'Batteries').mkdir(parents=True)
   self.assertEqual(len(c.namespace_providers([a,b])),2)
 def test_prior_mutation_rejected(self):
  with tempfile.TemporaryDirectory() as d:
   p=Path(d);(p/'a.olean').write_bytes(b'a');prior=c.checked_inventory(p)['files'];(p/'a.olean').write_bytes(b'b')
   with self.assertRaises(Exception):c.verify_prior_outputs(p,prior)
 def test_prior_preserved_new_output_allowed(self):
  with tempfile.TemporaryDirectory() as d:
   p=Path(d);(p/'a.olean').write_bytes(b'a');prior=c.checked_inventory(p)['files'];(p/'b.olean').write_bytes(b'b');self.assertEqual(len(c.verify_prior_outputs(p,prior)),2)



class ExactOfficialLinkTests(unittest.TestCase):
 def setup_link(self,root,package,rel):
  repo=root/package;repo.mkdir();target,resolved,oid=c.OFFICIAL_SOURCE_LINKS[package][rel]
  endpoint=repo/resolved;endpoint.parent.mkdir(parents=True,exist_ok=True);endpoint.write_text('pinned regular source')
  link=repo/rel;link.parent.mkdir(parents=True,exist_ok=True);link.symlink_to(target)
  return repo,link,endpoint,oid
 def test_all_three_exact_links(self):
  for package,links in c.OFFICIAL_SOURCE_LINKS.items():
   for rel in links:
    with tempfile.TemporaryDirectory() as d:
     repo,link,end,oid=self.setup_link(Path(d),package,rel)
     row=c.source_blob(repo,rel,'120000',oid)
     self.assertEqual(row['git_mode'],'120000');self.assertEqual(row['target'],os.readlink(link))
     c.validate_source_links({rel:row,row['resolved_source_path']:{'kind':'regular'}})
 def test_unknown_link_rejected(self):
  with tempfile.TemporaryDirectory() as d:
   repo=Path(d)/'mathlib';repo.mkdir();(repo/'file').write_text('x');(repo/'unknown').symlink_to('file')
   with self.assertRaises(Exception):c.source_blob(repo,'unknown','120000','a'*40)
 def test_changed_link_object_rejected(self):
  with tempfile.TemporaryDirectory() as d:
   repo,link,end,oid=self.setup_link(Path(d),'batteries','docs/README.md')
   with self.assertRaises(Exception):c.source_blob(repo,'docs/README.md','120000','a'*40)
 def test_absolute_target_rejected(self):
  self.changed_target('/etc/passwd')
 def test_escape_target_rejected(self):
  self.changed_target('../../outside')
 def test_cycle_target_rejected(self):
  self.changed_target('README.md')
 def test_jump_dotdot_target_rejected(self):
  self.changed_target('jump/../README.md')
 def changed_target(self,target):
  with tempfile.TemporaryDirectory() as d:
   repo,link,end,oid=self.setup_link(Path(d),'batteries','docs/README.md');link.unlink();link.symlink_to(target)
   with self.assertRaises(Exception):c.source_blob(repo,'docs/README.md','120000',oid)
 def test_endpoint_symlink_rejected(self):
  with tempfile.TemporaryDirectory() as d:
   repo,link,end,oid=self.setup_link(Path(d),'batteries','docs/README.md');end.unlink();end.symlink_to('/etc/passwd')
   with self.assertRaises(Exception):c.source_blob(repo,'docs/README.md','120000',oid)
 def test_missing_endpoint_rejected(self):
  with tempfile.TemporaryDirectory() as d:
   repo,link,end,oid=self.setup_link(Path(d),'batteries','docs/README.md');end.unlink()
   with self.assertRaises(Exception):c.source_blob(repo,'docs/README.md','120000',oid)
 def test_ignored_git_endpoint_rejected(self):
  with self.assertRaises(Exception):c.validate_source_links({'link':{'kind':'symlink','resolved_source_path':'.git/HEAD'}})
 def test_ignored_lake_endpoint_rejected(self):
  with self.assertRaises(Exception):c.validate_source_links({'link':{'kind':'symlink','resolved_source_path':'.lake/ignored'}})
 def test_regular_replacing_link_rejected(self):
  with tempfile.TemporaryDirectory() as d:
   repo,link,end,oid=self.setup_link(Path(d),'batteries','docs/README.md');link.unlink();link.write_text('../README.md')
   with self.assertRaises(Exception):c.source_blob(repo,'docs/README.md','120000',oid)


class DiagnosticProfileTests(unittest.TestCase):
 def test_contract_matches_bounded_profile(self):
  x=json.loads((ROOT/'contract.json').read_text());self.assertEqual(x['lean_heap_mib'],c.DIAGNOSTIC_HEAP_MIB);self.assertEqual(x['diagnostic_rss_gib']*1024**3,c.DIAGNOSTIC_RSS_BYTES);self.assertEqual(c.DIAGNOSTIC_HEAP_MIB,4096);self.assertEqual(c.DIAGNOSTIC_RSS_BYTES,8*1024**3);self.assertEqual(len(x['diagnostics']),69);self.assertEqual(x['diagnostic_timeout_seconds'],120);self.assertEqual(x['outer_timeout_minutes'],90)


class BodyGraphTests(unittest.TestCase):
 def setUp(self):
  self.contract=json.loads((ROOT/'contract.json').read_text());self.owned=json.loads((ROOT/'locks/owned-sources.json').read_text());self.required=json.loads((ROOT/'locks/required-modules.json').read_text())
 def check(self):c.validate_owned_graph(self.contract,self.owned,self.required)
 def test_exact_graph(self):self.check();self.assertEqual(len(self.owned['sources']),69)
 def test_first_four_retained(self):self.assertEqual(self.owned['module_order'][:4],['SparseMonotiles.Model','PalomarCurvedChallenge','PalomarKeyedProductChallenge','ContractModelBridgeSmoke']);self.assertEqual(self.owned['module_order'][-1],'ContractBodyBridgeSmoke')
 def test_every_source_hash(self):
  for r in self.owned['sources']:
   p=ROOT/r['path'];self.assertEqual(p.stat().st_size,r['bytes']);self.assertEqual(c.f.file_sha(p),r['sha256'])
 def test_body_sources_exact_count(self):self.assertEqual(sum(x['role']=='modern_body_dependency' for x in self.owned['sources']),65)
 def test_duplicate_owned(self):
  self.owned['sources'][1]=self.owned['sources'][0]
  with self.assertRaises(Exception):self.check()
 def test_wrong_module_order(self):
  self.owned['module_order'][0],self.owned['module_order'][1]=self.owned['module_order'][1],self.owned['module_order'][0]
  with self.assertRaises(Exception):self.check()
 def test_early_body_smoke(self):
  for key in ['sources','module_order']:
   x=self.owned[key];x.insert(0,x.pop())
  x=self.contract['diagnostics'];x.insert(0,x.pop())
  with self.assertRaises(Exception):self.check()
 def test_path_alias(self):
  self.owned['sources'][0]['path']='src/Other.lean'
  with self.assertRaises(Exception):self.check()
 def test_wrong_source_pin(self):
  self.owned['sources'][0]['sha256']='0'*64
  with self.assertRaises(Exception):self.check()
 def test_unresolved_import(self):
  self.owned['sources'][0]['ordered_imports'].append('Unknown.Module')
  with self.assertRaises(Exception):self.check()
 def test_C_import(self):
  self.owned['sources'][0]['ordered_imports'].append('SpectreFinite.NativeCoarsening')
  with self.assertRaises(Exception):self.check()
 def test_duplicate_cache(self):
  self.required['modules'][1]=self.required['modules'][0]
  with self.assertRaises(Exception):self.check()
 def test_extra_cache_root(self):
  self.contract['cache_roots'].append('Mathlib.Unknown')
  with self.assertRaises(Exception):self.check()
 def test_owned_cache_shadow(self):
  self.required['modules'][0]['module']='SparseMonotiles.Model'
  with self.assertRaises(Exception):self.check()
 def test_extra_source_input(self):
  self.contract['inputs']['src/Extra.lean']={'bytes':0,'sha256':'0'*64}
  with self.assertRaises(Exception):self.check()
 def test_scope_changed(self):
  self.owned['no_C_dependency']=False
  with self.assertRaises(Exception):self.check()

class AxiomAuditTests(unittest.TestCase):
 names=['PalomarCurved.body_bridge_smoke','PalomarKeyedProduct.body_bridge_smoke']
 def text(self,axs='propext, Classical.choice, Quot.sound'):
  return ''.join("'"+n+"' depends on axioms: ["+axs+"]\n" for n in self.names)
 def test_exact_body_names(self):self.assertEqual(set(c.audit_axiom_output(self.text(),self.names)),set(self.names))
 def test_model_actual_passed_format(self):
  names=['curved_model_eq','keyed_product_model_eq'];text=''.join("'"+n+"' depends on axioms: [propext, Classical.choice, Quot.sound]\n" for n in names);self.assertEqual(set(c.audit_axiom_output(text,names)),set(names))
 def test_empty_axioms(self):
  text=''.join("'"+n+"' does not depend on any axioms\n" for n in self.names);self.assertEqual(c.audit_axiom_output(text,self.names),{n:[] for n in self.names})
 def test_allowed_subset(self):c.audit_axiom_output(self.text('propext'),self.names)
 def test_multiline_axioms(self):c.audit_axiom_output(self.text('propext,\n Classical.choice, Quot.sound'),self.names)
 def test_sorry_rejected(self):
  with self.assertRaises(Exception):c.audit_axiom_output(self.text('sorryAx'),self.names)
 def test_custom_axiom_rejected(self):
  with self.assertRaises(Exception):c.audit_axiom_output(self.text('Custom.hiddenAssumption'),self.names)
 def test_missing_record_rejected(self):
  with self.assertRaises(Exception):c.audit_axiom_output(self.text().splitlines()[0]+'\n',self.names)
 def test_name_in_warning_not_record(self):
  with self.assertRaises(Exception):c.audit_axiom_output('warning: '+','.join(self.names),self.names)
 def test_duplicate_record_rejected(self):
  with self.assertRaises(Exception):c.audit_axiom_output(self.text()+self.text(),self.names)
 def test_extra_record_rejected(self):
  with self.assertRaises(Exception):c.audit_axiom_output(self.text()+"'Extra' depends on axioms: []\n",self.names)
 def test_duplicate_axiom_rejected(self):
  with self.assertRaises(Exception):c.audit_axiom_output(self.text('propext,propext'),self.names)
 def test_malformed_axiom_output_rejected(self):
  with self.assertRaises(Exception):c.audit_axiom_output(self.text().replace('axioms:', 'assumptions:'),self.names)

class BodyProfileTests(unittest.TestCase):
 def test_explicit_profile(self):c.validate_diagnostic_profile(json.loads((ROOT/'contract.json').read_text()))
 def test_resource_and_scope_mutants(self):
  base=json.loads((ROOT/'contract.json').read_text())
  for key in ['diagnostic_module_count','body_union_module_count','lean_heap_mib','diagnostic_rss_gib','diagnostic_timeout_seconds','outer_timeout_minutes','aggregate_command_deadline_seconds','maximum_parallel_jobs']:
   with self.subTest(key=key):
    x=dict(base);x[key]+=1
    with self.assertRaises(Exception):c.validate_diagnostic_profile(x)
 def test_axiom_contract_cannot_weaken(self):
  x=json.loads((ROOT/'contract.json').read_text());x['axiom_audits']=[]
  with self.assertRaises(Exception):c.validate_diagnostic_profile(x)
 def test_no_final_theorem_claim(self):
  x=json.loads((ROOT/'contract.json').read_text());x['no_theorem_certification']=False
  with self.assertRaises(Exception):c.validate_diagnostic_profile(x)



class ActualOutputLoopTests(unittest.TestCase):
 """Run the exact production loop AST with synthetic command outputs, never Lean."""
 def run_loop(self,hook=None,cache_prefix=None,loop_source=None):
  import ast,copy
  text=loop_source if loop_source is not None else (ROOT/'ci/cache_diagnostic.py').read_text()
  tree=ast.parse(text)
  loops=[x for x in ast.walk(tree) if isinstance(x,ast.For) and isinstance(x.target,ast.Name) and x.target.id=='entry' and isinstance(x.iter,ast.Subscript) and isinstance(x.iter.value,ast.Name) and x.iter.value.id=='contract' and isinstance(x.iter.slice,ast.Constant) and x.iter.slice.value=='diagnostics']
  self.assertEqual(len(loops),1,'Production diagnostic loop must be uniquely identified')
  setup=ast.parse('prior={}\nexpected_outputs=set()\n').body
  function=ast.FunctionDef(name='execute_actual_loop',args=ast.arguments(posonlyargs=[],args=[],kwonlyargs=[],kw_defaults=[],defaults=[]),body=setup+[copy.deepcopy(loops[0])],decorator_list=[])
  code=compile(ast.fix_missing_locations(ast.Module(body=[function],type_ignores=[])),'<actual-production-loop-synthetic-control>','exec')
  with tempfile.TemporaryDirectory() as directory:
   work=Path(directory);objects=work/'objects';objects.mkdir();(work/'src').mkdir();(work/'home').mkdir();(work/'tmp').mkdir();(work/'packages').mkdir()
   runtime=work/'runtime';(runtime/'lib/lean').mkdir(parents=True);(runtime/'bin').mkdir()
   cache=work/'packages/mathlib/lib/lean';(cache/'Mathlib').mkdir(parents=True);(cache/'Mathlib/Seed.olean').write_bytes(b'SYNTHETIC_CACHE_FIXTURE_ONLY')
   if cache_prefix:(cache/cache_prefix).mkdir()
   contract=json.loads((ROOT/'contract.json').read_text());calls=[]
   suffixes=['.olean','.olean.private','.olean.server','.ilean','.ir.sig','.ir','.c']
   def command(name,argv,**kwargs):
    self.assertNotIn('--share-net',argv);self.assertEqual(kwargs['seconds'],120);self.assertEqual(kwargs['rss'],8*1024**3)
    phase,module=name.split('-',1);calls.append((phase,module));stem=objects/module.replace('.','/')
    if phase=='compile':
     self.assertIn('-j1',argv);self.assertIn('-M4096',argv);self.assertIn('-Dcompiler.postponeCompile=false',argv)
     for suffix in suffixes:Path(str(stem)+suffix).write_bytes(('SYNTHETIC_NOT_PROOF:'+module+suffix).encode())
    else:self.assertEqual(phase,'check')
    if hook:hook(phase,module,objects,stem)
    return work/'unused.stdout',True
   namespace=dict(vars(c));namespace.update(work=work,runtime=runtime,contract=contract,search=[str(cache)],env={},command=command)
   exec(code,namespace);namespace['execute_actual_loop']()
   return {'calls':calls,'output_count':len(c.checked_inventory(objects)['files'])}
 def at_last(self,action):
  def hook(phase,module,objects,stem):
   if module=='ContractBodyBridgeSmoke':action(phase,objects,stem)
  return hook
 def test_exact_69_module_sequence(self):
  r=self.run_loop();self.assertEqual(len(r['calls']),138);self.assertEqual(r['output_count'],69*7)
  names=[r['module'] for r in json.loads((ROOT/'contract.json').read_text())['diagnostics']]
  self.assertEqual(r['calls'],[(p,n) for n in names for p in ['compile','check']])
 def test_each_missing_modern_companion(self):
  for suffix in ['.olean','.olean.private','.olean.server','.ilean','.ir.sig','.ir','.c']:
   with self.subTest(suffix=suffix):
    def action(phase,objects,stem):
     if phase=='compile':Path(str(stem)+suffix).unlink()
    with self.assertRaisesRegex(Exception,'missing fresh companion'):self.run_loop(self.at_last(action))
 def test_extra_path_after_last_compiler(self):
  def action(phase,objects,stem):
   if phase=='compile':(objects/'unexpected.bin').write_bytes(b'extra')
  with self.assertRaisesRegex(Exception,'unexpected fresh output path'):self.run_loop(self.at_last(action))
 def test_extra_path_after_last_checker(self):
  def action(phase,objects,stem):
   if phase=='check':(objects/'unexpected.bin').write_bytes(b'extra')
  with self.assertRaisesRegex(Exception,'unexpected fresh output path after checker'):self.run_loop(self.at_last(action))
 def test_empty_shadow_prefix_after_last_compile(self):
  def action(phase,objects,stem):
   if phase=='compile':(objects/'Mathlib').mkdir()
  with self.assertRaisesRegex(Exception,'namespace prefix has multiple search roots'):self.run_loop(self.at_last(action))
 def test_empty_shadow_prefix_after_last_checker(self):
  def action(phase,objects,stem):
   if phase=='check':(objects/'Mathlib').mkdir()
  with self.assertRaisesRegex(Exception,'namespace prefix has multiple search roots'):self.run_loop(self.at_last(action))
 def test_later_owned_prefix_already_in_cache(self):
  with self.assertRaisesRegex(Exception,'namespace prefix has multiple search roots'):self.run_loop(cache_prefix='SpectreGeometry')
 def test_earlier_output_mutated_during_last_check(self):
  def action(phase,objects,stem):
   if phase=='check':(objects/'SparseMonotiles/Model.olean').write_bytes(b'MUTATED_SYNTHETIC_BYTES')
  with self.assertRaisesRegex(Exception,'previous fresh diagnostic output changed'):self.run_loop(self.at_last(action))
 def test_earlier_output_removed_during_last_check(self):
  def action(phase,objects,stem):
   if phase=='check':(objects/'SparseMonotiles/Model.olean.private').unlink()
  with self.assertRaisesRegex(Exception,'previous fresh diagnostic output changed'):self.run_loop(self.at_last(action))
 def test_current_output_mutated_during_check(self):
  def action(phase,objects,stem):
   if phase=='check':Path(str(stem)+'.ir').write_bytes(b'MUTATED_SYNTHETIC_IR')
  with self.assertRaisesRegex(Exception,'previous fresh diagnostic output changed'):self.run_loop(self.at_last(action))
 def test_symlink_created_during_last_check(self):
  def action(phase,objects,stem):
   if phase=='check':(objects/'escape.olean').symlink_to('/etc/passwd')
  with self.assertRaisesRegex(Exception,'escaping or disallowed artifact link'):self.run_loop(self.at_last(action))

if __name__=='__main__':unittest.main()
