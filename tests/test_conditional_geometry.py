import importlib.util,json,os,sys,tempfile,unittest
from pathlib import Path
from unittest.mock import patch
ROOT=Path(__file__).resolve().parents[1];sys.path.insert(0,str(ROOT/'ci'))
import cache_diagnostic as c
_SOURCE_TEMP=tempfile.TemporaryDirectory(prefix='conditional-test-source-')
SOURCE_ROOT=Path(_SOURCE_TEMP.name)/'admitted'
c.extract_owned_sources(ROOT/'owned-sources.tar.gz',SOURCE_ROOT,json.loads((ROOT/'contract.json').read_text()))


class Tests(unittest.TestCase):

    def test_env_no_ambient(self):
        with patch.dict(os.environ, {'GITHUB_TOKEN': 'secret', 'MATHLIB_CACHE_GET_URL': 'evil', 'LEAN_PATH': 'old'}):
            e = c.safe_env(Path('/runtime'), Path('/home-new'), Path('/temp-new'))
        self.assertNotIn('GITHUB_TOKEN', e)
        self.assertNotIn('MATHLIB_CACHE_GET_URL', e)
        self.assertNotIn('LEAN_PATH', e)
        self.assertEqual(e['LAKE_NO_CACHE'], 'true')

    def test_network_default_off(self):
        a = c.sandbox(['/bin/true'], runtime=Path('/runtime'), sources=[Path('/official')], writable=[Path('/cache')], cwd=Path('/official'), env={})
        self.assertIn('--unshare-all', a)
        self.assertNotIn('--share-net', a)
        self.assertNotIn('/', a)
        self.assertNotIn('/home', a)

    def test_explicit_official_network(self):
        a = c.sandbox(['/bin/true'], runtime=Path('/runtime'), sources=[Path('/official')], writable=[Path('/cache')], cwd=Path('/official'), env={}, network=True)
        self.assertIn('--share-net', a)
        self.assertIn('--clearenv', a)
        self.assertIn('--new-session', a)

    def test_inventory_regular(self):
        with tempfile.TemporaryDirectory() as d:
            p = Path(d)
            (p / 'a').write_text('abc')
            x = c.checked_inventory(p)
            self.assertEqual(x['bytes'], 3)
            self.assertEqual(set(x['files']), {'a'})

    def test_inventory_byte_limit(self):
        with tempfile.TemporaryDirectory() as d:
            p = Path(d)
            (p / 'a').write_text('abc')
            with self.assertRaises(Exception):
                c.checked_inventory(p, maximum=2)

    def test_reject_external_symlink(self):
        with tempfile.TemporaryDirectory() as d:
            p = Path(d)
            (p / 'a').symlink_to('/etc/passwd')
            with self.assertRaises(Exception):
                c.checked_inventory(p, allow_links=True)

    def test_reject_hardlink(self):
        with tempfile.TemporaryDirectory() as d:
            p = Path(d)
            (p / 'a').write_text('x')
            os.link(p / 'a', p / 'b')
            with self.assertRaises(Exception):
                c.checked_inventory(p)

    def test_allow_internal_relative_link(self):
        with tempfile.TemporaryDirectory() as d:
            p = Path(d)
            (p / 'a').write_text('x')
            (p / 'b').symlink_to('a')
            self.assertEqual(c.checked_inventory(p, allow_links=True)['files']['b'], {'symlink': 'a'})

    def test_exact_dependency_allowlist(self):
        x = json.loads((ROOT / 'locks/dependencies.json').read_text())['packages']
        c.validate_dependencies(x)
        x[0]['url'] = 'https://github.com/evil/mathlib4'
        with self.assertRaises(Exception):
            c.validate_dependencies(x)

    def test_mutable_pin_rejected(self):
        x = json.loads((ROOT / 'locks/dependencies.json').read_text())['packages']
        x[0]['rev'] = 'main'
        with self.assertRaises(Exception):
            c.validate_dependencies(x)

    def test_required_closure_contains_all_roots(self):
        x = json.loads((ROOT / 'locks/required-modules.json').read_text())
        self.assertLessEqual(set(x['roots']), {r['module'] for r in x['modules']})
        self.assertEqual(len(x['modules']), len({r['module'] for r in x['modules']}))

    def test_explicit_review_state(self):
        self.assertIn(json.loads((ROOT / 'contract.json').read_text())['review_status'], ('pending_independent_review', 'reviewed_for_execution'))

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

class ScopedVisibilitySourceTests(unittest.TestCase):
 def test_exact_two_source_insertions(self):
  lock=json.loads((ROOT/'locks/visibility-exception.json').read_text());source=(SOURCE_ROOT/lock['source']).read_text()
  option=lock['added_command']+'\n';self.assertEqual(source.count(option),2)
  original=source
  for anchor in lock['insert_before_anchors']:
   self.assertEqual(original.count(option+anchor),1);original=original.replace(option+anchor,anchor,1)
  self.assertEqual(c.f.sha(original.encode()),lock['baseline_source_sha256']);self.assertEqual(c.f.sha(source.encode()),lock['candidate_source_sha256'])
 def test_compatibility_option_only_in_target_module(self):
  lock=json.loads((ROOT/'locks/visibility-exception.json').read_text());matches=[]
  for path in sorted((SOURCE_ROOT/'src').rglob('*.lean')):
   if 'backward.privateInPublic' in path.read_text():matches.append(path.relative_to(SOURCE_ROOT).as_posix())
  predictions=json.loads((ROOT/'locks/visibility-predictions.json').read_text());self.assertEqual(matches,sorted([lock['source']]+[r['path'] for r in predictions['files']]));self.assertNotIn('backward.privateInPublic.warn', (SOURCE_ROOT/lock['source']).read_text())
 def test_private_helper_and_exact_proof_source_retained(self):
  source=(SOURCE_ROOT/'src/SpectreGeometry/PolygonProductKeyBody.lean').read_text()
  self.assertEqual(source.count('private theorem product_key_collar_interior_disjoint'),1)
  self.assertIn('isOpen_interior hx (product_key_collar_interior_disjoint s)',source)
  self.assertNotIn('sorry',source);self.assertNotIn('axiom ',source)

class ConditionalGraphTests(unittest.TestCase):
 def setUp(self):
  self.contract=json.loads((ROOT/'contract.json').read_text());self.owned=json.loads((ROOT/'locks/owned-sources.json').read_text());self.required=json.loads((ROOT/'locks/required-modules.json').read_text())
 def check(self):c.validate_owned_graph(self.contract,self.owned,self.required,SOURCE_ROOT)
 def test_exact_graph(self):self.check()
 def test_profile(self):c.validate_diagnostic_profile(self.contract)
 def test_all_sources_and_exact_modern_headers(self):
  for r in self.owned['sources']:
   p=SOURCE_ROOT/r['path'];self.assertEqual(p.stat().st_size,r['bytes']);self.assertEqual(c.f.file_sha(p),r['sha256']);self.assertTrue(c.header_parser.header(p.read_bytes())['modern'])
 def test_exact_endpoints_last(self):self.assertEqual(self.owned['module_order'][-2:],c.ENDPOINTS)
 def test_no_unconditional_source(self):
  names=self.owned['module_order'];self.assertNotIn('SpectreFinite.RadiusFivePruningHierarchy',names);self.assertNotIn('ClosedCurvedFinal',names);self.assertNotIn('ClosedKeyedProductFinal',names)
 def test_no_challenge_holes_admitted(self):self.assertFalse(any('Challenge' in r['module'] for r in self.owned['sources']))
 def test_all_profile_mutants(self):
  for k in ['owned_module_count','finite_prerequisite_count','owned_geometry_count','ordinary_bridge_count','conditional_endpoint_count','lean_heap_mib','diagnostic_rss_gib','diagnostic_timeout_seconds','check_timeout_seconds','outer_timeout_minutes','aggregate_command_deadline_seconds','maximum_parallel_jobs','owned_output_max_bytes','owned_source_max_bytes','evidence_max_bytes','aggregate_log_max_bytes','per_command_log_max_bytes','minimum_free_disk_bytes','auditor_timeout_seconds','cache_module_count']:
   with self.subTest(k=k):
    x=dict(self.contract);x[k]+=1
    with self.assertRaises(Exception):c.validate_diagnostic_profile(x)
 def test_scope_mutants(self):
  for k in ['conditional_C_remains_explicit','final_C_proof_certified','unconditional_monotile_proof_certified','fresh_external_source_rebuild','owned_objects_from_prior_runs_allowed']:
   x=dict(self.contract);x[k]=not x[k]
   with self.assertRaises(Exception):c.validate_diagnostic_profile(x)
 def test_owned_duplicate(self):
  self.owned['sources'][1]=self.owned['sources'][0]
  with self.assertRaises(Exception):self.check()
 def test_unresolved_import(self):
  self.owned['sources'][0]['ordered_imports'].append('Unknown.Module')
  with self.assertRaises(Exception):self.check()
 def test_wrong_runtime_boundary(self):
  self.contract['runtime_roots'].append('Init.Unexpected')
  with self.assertRaises(Exception):self.check()
 def test_extra_source_pin(self):
  self.contract['inputs']['src/Unexpected.lean']={'bytes':0,'sha256':'0'*64}
  with self.assertRaises(Exception):self.check()
 def test_endpoint_early(self):
  for k in ['module_order','sources']:
   a=self.owned[k];a.insert(0,a.pop())
  a=self.contract['modules'];a.insert(0,a.pop())
  with self.assertRaises(Exception):self.check()
 def test_bad_source_pin(self):
  self.owned['sources'][0]['sha256']='0'*64
  with self.assertRaises(Exception):self.check()
 def test_cache_shadow(self):
  self.required['modules'][0]['module']=self.owned['module_order'][0]
  with self.assertRaises(Exception):self.check()

class QuarantineTests(unittest.TestCase):
 def fixture(self,root,mod='Shared.A'):
  stage=root/'stage';stage.mkdir();objects=root/'objects';objects.mkdir()
  for name in c.module_outputs(mod):p=stage/name;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(('SYNTHETIC:'+name).encode())
  return stage,objects,mod
 def test_exact_admission_and_terminal_hash(self):
  with tempfile.TemporaryDirectory() as t:
   stage,objects,mod=self.fixture(Path(t));prior=c.admit_quarantine(stage,objects,mod,{},100000);self.assertEqual(set(prior),c.module_outputs(mod));c.verify_owned_final(objects,prior,100000)
 def test_each_missing_companion(self):
  for suffix in c.SUFFIXES:
   with tempfile.TemporaryDirectory() as t:
    stage,objects,mod=self.fixture(Path(t));(stage/('Shared/A'+suffix)).unlink()
    with self.assertRaises(Exception):c.admit_quarantine(stage,objects,mod,{},100000)
 def test_extra_file_and_empty_directory(self):
  for isdir in [False,True]:
   with tempfile.TemporaryDirectory() as t:
    stage,objects,mod=self.fixture(Path(t));p=stage/'extra';p.mkdir() if isdir else p.write_bytes(b'bad')
    with self.assertRaises(Exception):c.admit_quarantine(stage,objects,mod,{},100000)
 def test_hardlink_and_symlink(self):
  for link in ['hard','symbolic']:
   with tempfile.TemporaryDirectory() as t:
    stage,objects,mod=self.fixture(Path(t));p=stage/'Shared/A.olean';p.unlink();q=stage/'Shared/A.ir'
    os.link(q,p) if link=='hard' else p.symlink_to(q)
    with self.assertRaises(Exception):c.admit_quarantine(stage,objects,mod,{},100000)
 def test_existing_destination_is_not_overwritten(self):
  with tempfile.TemporaryDirectory() as t:
   stage,objects,mod=self.fixture(Path(t));p=objects/'Shared/A.olean';p.parent.mkdir();p.write_bytes(b'old')
   with self.assertRaises(Exception):c.admit_quarantine(stage,objects,mod,{},100000)
   self.assertEqual(p.read_bytes(),b'old')
 def test_aggregate_size_rejection(self):
  with tempfile.TemporaryDirectory() as t:
   stage,objects,mod=self.fixture(Path(t))
   with self.assertRaises(Exception):c.admit_quarantine(stage,objects,mod,{},1)
 def test_final_mutation_and_extra_rejected(self):
  for mutation in ['changed','extra','missing']:
   with tempfile.TemporaryDirectory() as t:
    stage,objects,mod=self.fixture(Path(t));prior=c.admit_quarantine(stage,objects,mod,{},100000);p=objects/'Shared/A.olean'
    if mutation=='changed':p.chmod(0o644);p.write_bytes(b'bad')
    elif mutation=='extra':(objects/'unexpected').write_bytes(b'bad')
    else:p.unlink()
    with self.assertRaises(Exception):c.verify_owned_final(objects,prior,100000)

class ActualConditionalLoopTests(unittest.TestCase):
 def run_loop(self,hook=None,observed=None):
  import ast,copy
  tree=ast.parse((ROOT/'ci/cache_diagnostic.py').read_text())
  main=next(n for n in tree.body if isinstance(n,ast.FunctionDef) and n.name=='main')
  loops=[n for n in ast.walk(main) if isinstance(n,ast.For) and isinstance(n.target,ast.Name) and n.target.id=='module' and isinstance(n.iter,ast.Subscript) and isinstance(n.iter.slice,ast.Constant) and n.iter.slice.value=='modules']
  self.assertEqual(len(loops),1)
  fn=ast.FunctionDef(name='loop',args=ast.arguments(posonlyargs=[],args=[],kwonlyargs=[],kw_defaults=[],defaults=[]),body=ast.parse('prior={}\nchecked=set()\nreceipts=[]').body+[copy.deepcopy(loops[0])]+ast.parse('return prior,receipts').body,decorator_list=[])
  code=compile(ast.fix_missing_locations(ast.Module(body=[fn],type_ignores=[])),'<production-loop-synthetic-test>','exec')
  with tempfile.TemporaryDirectory() as t:
   work=Path(t)
   for n in ['objects','quarantine','src','packages','home','tmp','evidence','runtime/lib/lean','runtime/bin']:(work/n).mkdir(parents=True)
   (work/'runtime/lib/lean/Init.olean').write_bytes(b'OFFICIAL_RUNTIME_FIXTURE_NOT_PROOF')
   rows=[{'module':'Shared.A','ordered_imports':['Init'],'sha256':'a'*64},{'module':'Shared.B','ordered_imports':['Shared.A'],'sha256':'b'*64}]
   contract=json.loads((ROOT/'contract.json').read_text());contract['modules']=rows;calls=observed if observed is not None else []
   env={'LEAN_PATH':str(work/'objects')+':'+str(work/'runtime/lib/lean')}
   def command(name,argv,**kwargs):
    phase,mod=name.split('-',1);calls.append((phase,mod));self.assertNotIn('--share-net',argv)
    binds=[argv[i+1] for i,x in enumerate(argv) if x=='--bind'];readonly=[argv[i+1] for i,x in enumerate(argv) if x=='--ro-bind']
    self.assertIn(str(work/'objects'),readonly);self.assertNotIn(str(work/'objects'),binds)
    self.assertEqual(kwargs['env']['LEAN_PATH'],env['LEAN_PATH']);self.assertNotIn('quarantine',kwargs['env']['LEAN_PATH'])
    if phase=='compile':
     self.assertEqual(kwargs['seconds'],180);out=Path(argv[argv.index('-o')+1]);stage=work/'quarantine'/mod
     self.assertTrue(out.is_relative_to(stage));self.assertIn(str(stage),binds)
     if mod=='Shared.B':self.assertTrue((work/'objects/Shared/A.olean').is_file())
     for rel in c.module_outputs(mod):p=stage/rel;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(('SYNTHETIC:'+rel).encode())
    else:
     self.assertEqual(kwargs['seconds'],120);self.assertTrue((work/'objects'/(mod.replace('.','/')+'.olean')).is_file());self.assertFalse((work/'quarantine'/mod).exists())
    if hook:hook(phase,mod,work)
    return work/'unused',True
   ns=dict(vars(c));ns.update(work=work,runtime=work/'runtime',contract=contract,stage={'modules':[r['module'] for r in rows]},a=type('Args',(),{'stage':'synthetic'})(),env=env,search=[],prior={},checked=set(),receipts=[],owned_rows={r['module']:r for r in rows},cache_rows={},result={},commands=[],command=command)
   exec(code,ns)
   with patch('builtins.print'),patch.object(c.shutil,'disk_usage',return_value=type('Disk',(),{'free':20*c.GIB})()):prior,receipts=ns['loop']()
   c.verify_owned_final(work/'objects',prior,contract['owned_output_max_bytes'])
   return calls,receipts
 def test_same_prefix_single_root_compile_and_checker(self):
  calls,receipts=self.run_loop();self.assertEqual(calls,[('compile','Shared.A'),('check','Shared.A'),('compile','Shared.B'),('check','Shared.B')]);self.assertEqual(receipts[1]['ordered_imports'][0]['module'],'Shared.A');self.assertEqual(len(receipts[1]['ordered_imports'][0]['companions']),7)
 def test_missing_companion_stops_before_checker(self):
  def hook(phase,mod,work):
   if phase=='compile' and mod=='Shared.B':(work/'quarantine/Shared.B/Shared/B.ir').unlink()
  with self.assertRaises(Exception):self.run_loop(hook)
 def test_checker_failure_stops_loop(self):
  def hook(phase,mod,work):
   if phase=='check':raise c.f.Rejected('synthetic failed checker')
  with self.assertRaisesRegex(Exception,'failed checker'):self.run_loop(hook)
 def test_current_checker_mutation_rejected(self):
  def hook(phase,mod,work):
   if phase=='check':p=work/'objects'/(mod.replace('.','/')+'.olean');p.chmod(0o644);p.write_bytes(b'bad')
  with self.assertRaisesRegex(Exception,'changed during checker'):self.run_loop(hook)
 def test_unexpected_prior_host_mutation_rejected_final(self):
  def hook(phase,mod,work):
   if phase=='check' and mod=='Shared.B':p=work/'objects/Shared/A.ir';p.chmod(0o644);p.write_bytes(b'bad')
  with self.assertRaisesRegex(Exception,'committed owned output changed'):self.run_loop(hook)

class InterruptedAdmissionTests(unittest.TestCase):
 def test_partial_host_admission_stops_before_checker_and_has_no_resume(self):
  observed=[];original=Path.rename;count=0
  def rename(path,dest):
   nonlocal count
   if '/objects/' in str(dest):
    count+=1
    if count==2:raise OSError('synthetic interruption after one admitted companion')
   return original(path,dest)
  with patch.object(Path,'rename',rename):
   with self.assertRaisesRegex(OSError,'synthetic interruption'):
    ActualConditionalLoopTests().run_loop(observed=observed)
  self.assertEqual(observed,[('compile','Shared.A')])
  self.assertIn("f.need(not work.exists(),'diagnostic workspace must be new')",(ROOT/'ci/cache_diagnostic.py').read_text())
 def test_final_empty_directory_rejected(self):
  with tempfile.TemporaryDirectory() as d:
   p=Path(d);(p/'empty-shadow').mkdir()
   with self.assertRaises(Exception):c.verify_owned_final(p,{},1024)

class TerminalReceiptTests(unittest.TestCase):
 def fixture(self):
  result={'conditional_C_remains_explicit':True,'final_C_proof_certified':False,'unconditional_monotile_proof_certified':False}
  rows=[{'module':'Shared.A'},{'module':'Shared.B'}]
  commands=[{'name':p+'-'+r['module'],'exit_code':0,'timed_out':False,'log_overflow':False,'memory_exceeded':False,'surviving_children':False,'process_group_empty':True,'descendants_empty':True,'escaped_descendants':False,'new_sessions_explicitly_allowed':False} for r in rows for p in ['compile','check']]
  receipts=[{'module':r['module'],'checker_passed':True} for r in rows]
  return result,commands,rows,receipts,{'ordinary_bridges':True,'conditional_endpoints':True}
 def test_complete(self):c.validate_terminal_receipt(*self.fixture())
 def test_each_failure_flag(self):
  for key in ['timed_out','log_overflow','memory_exceeded','surviving_children','process_group_empty','descendants_empty']:
   args=list(self.fixture());args[1][-1][key]=not args[1][-1][key]
   with self.assertRaises(Exception):c.validate_terminal_receipt(*args)
 def test_nonzero_exit(self):
  args=list(self.fixture());args[1][-1]['exit_code']=1
  with self.assertRaises(Exception):c.validate_terminal_receipt(*args)
 def test_missing_or_duplicate_pair(self):
  for duplicate in [True,False]:
   args=list(self.fixture());args[1].append(args[1][-1]) if duplicate else args[1].pop()
   with self.assertRaises(Exception):c.validate_terminal_receipt(*args)
 def test_unchecked_receipt(self):
  args=list(self.fixture());args[3][-1]['checker_passed']=False
  with self.assertRaises(Exception):c.validate_terminal_receipt(*args)
 def test_missing_endpoint_or_bridge_audit(self):
  for key in ['ordinary_bridges','conditional_endpoints']:
   args=list(self.fixture());args[4][key]=False
   with self.assertRaises(Exception):c.validate_terminal_receipt(*args)
 def test_unconditional_claim_rejected(self):
  args=list(self.fixture());args[0]['unconditional_monotile_proof_certified']=True
  with self.assertRaises(Exception):c.validate_terminal_receipt(*args)


class AuditReceiptTests(unittest.TestCase):
 def endpoint_records(self):
  return [{'status':'CONDITIONAL_ENDPOINT_PASSED','theorem':c.ENDPOINT_THEOREMS[i],'module':c.ENDPOINTS[i],'universe_parameters':[],'explicit_C_binders':1,'C_type':'SpectreFinite.HexSearch.NativeHierarchy.ParentOccurrenceTheorem','exact_raw_type':True,'closed_type_and_proof':True,'C_definition_expansion':True,'exact_module_owned_set':True,'small_semantic_anchors_only':True,'transitive_axioms':['propext','Classical.choice','Quot.sound']} for i in range(2)]
 def text(self,rows):return '\n'.join([*(json.dumps(r) for r in rows),'CONDITIONAL_ENDPOINT_AUDIT_PASSED'])
 def test_both_exact_endpoint_records(self):self.assertEqual(len(c.audit_endpoint_output(self.text(self.endpoint_records()))),2)
 def test_marker_only_rejected(self):
  with self.assertRaises(Exception):c.audit_endpoint_output('CONDITIONAL_ENDPOINT_AUDIT_PASSED')
 def test_missing_or_duplicate_endpoint(self):
  rows=self.endpoint_records()
  for bad in [rows[:1],[rows[0],rows[0]],rows+rows[:1]]:
   with self.assertRaises(Exception):c.audit_endpoint_output(self.text(bad))
 def test_each_contract_field_mutant(self):
  for field,bad in [('explicit_C_binders',0),('explicit_C_binders',True),('universe_parameters',['u']),('C_type','True'),('exact_raw_type',False),('closed_type_and_proof',False),('C_definition_expansion',False),('exact_module_owned_set',False),('small_semantic_anchors_only',False),('theorem','ClosedCurvedFinal.curved_monotile'),('module','ClosedCurvedFinal')]:
   rows=self.endpoint_records();rows[0][field]=bad
   with self.assertRaises(Exception):c.audit_endpoint_output(self.text(rows))
 def test_bad_and_duplicate_axioms(self):
  for axioms in [['sorryAx'],['Custom.C'],['propext','propext'],['native_decide_ax']]:
   rows=self.endpoint_records();rows[0]['transitive_axioms']=axioms
   with self.assertRaises(Exception):c.audit_endpoint_output(self.text(rows))
 def test_trailing_or_duplicate_success_marker(self):
  text=self.text(self.endpoint_records())
  for suffix in ['\nunexpected','\nCONDITIONAL_ENDPOINT_AUDIT_PASSED']:
   with self.assertRaises(Exception):c.audit_endpoint_output(text+suffix)
 def test_bridge_marker_only_rejected(self):
  with self.assertRaises(Exception):c.audit_bridge_output('ALL_FOUR_EXACT_RAW_BRIDGE_CONTRACTS_PASSED')
 def test_bridge_complete_and_missing_ownership(self):
  names=['KernelCurvedPilot.existing_curved_geometry_and_tiling','KernelCurvedParentPilot.curved_period_eq_zero_of_parent','KernelSeedPilot.existing_physical_product_tiling','KernelParentPilot.physical_polygon_product_period_eq_zero_of_parent']
  lines=['EXACT_RAW_TYPE_PROOF_UNIVERSES_AXIOMS: '+n for n in names]+['EXACT_MODULE_OWNED_SET: '+m+': '+n for m,n in zip(c.BRIDGES,names)]+['ALL_FOUR_EXACT_RAW_BRIDGE_CONTRACTS_PASSED']
  c.audit_bridge_output('\n'.join(lines));lines.pop(-2)
  with self.assertRaises(Exception):c.audit_bridge_output('\n'.join(lines))
 def test_auditors_only_import_official_core(self):
  for p in (ROOT/'auditors').glob('*.lean'):
   h=c.header_parser.header(p.read_bytes());self.assertTrue(h['modern']);self.assertTrue(all(x['module'].startswith('Lean.') for x in h['imports']))

class CollectionTests(unittest.TestCase):
 def collector(self):
  spec=importlib.util.spec_from_file_location('collector',ROOT/'ci/collect_evidence.py');m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m);return m
 def test_interrupted_available_files_not_success(self):
  m=self.collector()
  with tempfile.TemporaryDirectory() as d:
   p=Path(d);(p/'logs').mkdir();(p/'logs/interrupted.stdout').write_text('partial command output')
   r=m.collect(p,json.loads((ROOT/'contract.json').read_text()));self.assertTrue(r['all_available_files_copied']);self.assertFalse(r['replay_acceptance_evidence_complete']);self.assertTrue((p/'upload/logs/interrupted.stdout').is_file())
 def test_marker_only_success_result_rejected(self):
  m=self.collector()
  with tempfile.TemporaryDirectory() as d:
   p=Path(d);(p/'evidence').mkdir();(p/'evidence/result.json').write_text(json.dumps({'status':m.SUCCESS,'complete_evidence':True}))
   r=m.collect(p,json.loads((ROOT/'contract.json').read_text()));self.assertFalse(r['replay_acceptance_evidence_complete'])
 def test_fixed_upload_envelope_and_reserve(self):
  m=self.collector();self.assertEqual(m.MAXIMUM,128*1024**2);self.assertEqual(m.RESERVE,4*1024**2)



class ReadonlyPreflightTests(unittest.TestCase):
 def run_probe(self,mutate=False):
  with tempfile.TemporaryDirectory() as d:
   work=Path(d)
   for n in ['home','tmp','evidence','runtime']:(work/n).mkdir()
   def command(name,argv,**kwargs):
    self.assertEqual(name,'read-only-committed-root-preflight');self.assertNotIn('--share-net',argv)
    readonly=[argv[i+1] for i,x in enumerate(argv) if x=='--ro-bind'];writable=[argv[i+1] for i,x in enumerate(argv) if x=='--bind']
    self.assertIn(str(work/'preflight-read-only'),readonly);self.assertNotIn(str(work/'preflight-read-only'),writable);self.assertIn(str(work/'preflight-quarantine'),writable)
    self.assertIn('chmod 0600',argv[argv.index('-c')+1]);self.assertIn('mkdir',argv[argv.index('-c')+1]);(work/'preflight-quarantine/output').write_bytes(b'allowed')
    if mutate:(work/'preflight-read-only/predecessor').write_bytes(b'bad')
   c.readonly_boundary_preflight(work/'runtime',work,{},command)
 def test_exact_inert_probe_shape(self):self.run_probe()
 def test_mutated_predecessor_rejected(self):
  with self.assertRaises(Exception):self.run_probe(True)

class CollectorReadbackTests(unittest.TestCase):
 @classmethod
 def setUpClass(cls):
  import copy,hashlib
  cls.copy=copy;cls.hashlib=hashlib;cls.temp=tempfile.TemporaryDirectory();cls.root=Path(cls.temp.name);cls.m=CollectionTests().collector()
  (cls.root/'logs').mkdir();empty=hashlib.sha256(b'').hexdigest();suffixes=c.SUFFIXES
  cls.contract={'modules':[{'module':f'Synthetic.M{i:04d}'} for i in range(2481)],'inputs':{},'aggregate_log_max_bytes':64*1024**2}
  cls.commands=[];cls.modules=[];objects={}
  for i,r in enumerate(cls.contract['modules']):
   mod=r['module'];cls.contract['inputs']['src/'+mod.replace('.','/')+'.lean']={'sha256':'a'*64,'bytes':0};outputs={name:{'sha256':'b'*64,'bytes':0} for name in c.module_outputs(mod)};objects.update(outputs)
   cls.modules.append({'module':mod,'source_sha256':'a'*64,'outputs':outputs,'compiler_command':2*i,'checker_command':2*i+1,'checker_passed':True})
   for phase in ['compile','check']:
    name=phase+'-'+mod;cls.commands.append({'name':name,'exit_code':0,'timed_out':False,'log_overflow':False,'memory_exceeded':False,'surviving_children':False,'process_group_empty':True,'descendants_empty':True,'escaped_descendants':False,'new_sessions_explicitly_allowed':False,'stdout_sha256':empty,'stderr_sha256':empty})
    for stream in ['stdout','stderr']:(cls.root/'logs'/(name+'.'+stream)).write_bytes(b'')
  cls.contract['owned_module_count']=2481;cls.contract['source_archive']={'sha256':'d'*64,'source_bytes':0}
  (cls.root/'source-extraction.json').write_text(json.dumps({'schema':'authenticated-source-extraction-v1','archive':cls.contract['source_archive'],'source_file_count':2481,'source_bytes':0,'exact_source_tree':True,'all_source_pins_verified':True}))
  cls.contract_sha=hashlib.sha256((json.dumps(cls.contract,sort_keys=True,indent=2)+'\n').encode()).hexdigest()
  (cls.root/'fresh-owned-objects.json').write_text(json.dumps({'files':objects,'bytes':0}))
  for name in ['cached-build-inventory.json','runtime-inventory.json']:(cls.root/name).write_text('{}')
 @classmethod
 def tearDownClass(cls):cls.temp.cleanup()
 def write(self,mutation=None):
  commands=self.copy.deepcopy(self.commands);modules=self.copy.deepcopy(self.modules)
  if mutation:mutation(commands,modules)
  for name,data in [('commands.jsonl',commands),('owned-modules.jsonl',modules)]:
   (self.root/name).write_text(''.join(json.dumps(r,separators=(',',':'))+'\n' for r in data))
  result={'status':self.m.SUCCESS,'complete_evidence':True,'contract_sha256':self.contract_sha,'conditional_C_remains_explicit':True,'final_C_proof_certified':False,'unconditional_monotile_proof_certified':False,'command_count':len(commands),'checked_owned_module_count':2481,'complete_log_bytes':0,'raw_audits':{'conditional_endpoints':True,'ordinary_bridges':True}}
  for name,key in [('commands.jsonl','command_receipts_sha256'),('owned-modules.jsonl','owned_module_receipts_sha256'),('fresh-owned-objects.json','owned_output_inventory_sha256'),('cached-build-inventory.json','cached_build_inventory_sha256'),('runtime-inventory.json','runtime_inventory_sha256')]:result[key]=self.m.sha(self.root/name)
  result['source_extraction_receipt_sha256']=self.m.sha(self.root/'source-extraction.json');result['source_archive_sha256']=self.contract['source_archive']['sha256']
  (self.root/'result.json').write_text(json.dumps(result));return result
 def verify(self):self.m.verify_complete(self.root,self.contract,self.contract_sha)
 def test_complete_synthetic_receipts_only(self):self.write();self.verify()
 def test_source_extraction_receipt_guards(self):
  p=self.root/'source-extraction.json';original=p.read_bytes()
  for field,value in [('source_file_count',2480),('exact_source_tree',False),('all_source_pins_verified',False),('archive',{})]:
   self.write();receipt=json.loads(original);receipt[field]=value;p.write_text(json.dumps(receipt))
   result=json.loads((self.root/'result.json').read_text());result['source_extraction_receipt_sha256']=self.m.sha(p);(self.root/'result.json').write_text(json.dumps(result))
   try:
    with self.subTest(field=field),self.assertRaises(Exception):self.verify()
   finally:p.write_bytes(original)
 def test_missing_source_extraction_receipt(self):
  self.write();p=self.root/'source-extraction.json';original=p.read_bytes();p.unlink()
  try:
   with self.assertRaises(Exception):self.verify()
  finally:p.write_bytes(original)
 def test_source_archive_identity_receipt(self):
  result=self.write();result['source_archive_sha256']='0'*64;(self.root/'result.json').write_text(json.dumps(result))
  with self.assertRaises(Exception):self.verify()
 def test_invalid_command_indexes(self):
  for index in [-1,True,999999]:
   self.write(lambda commands,modules:modules[0].update(compiler_command=index))
   with self.assertRaises(Exception):self.verify()
 def test_nonadjacent_or_reordered_pairs(self):
  self.write(lambda commands,modules:commands.__setitem__(slice(0,2),list(reversed(commands[:2]))))
  with self.assertRaises(Exception):self.verify()
 def test_changed_source_and_output(self):
  self.write(lambda commands,modules:modules[0].update(source_sha256='c'*64))
  with self.assertRaises(Exception):self.verify()
  self.write(lambda commands,modules:modules[0].update(outputs={}))
  with self.assertRaises(Exception):self.verify()
 def test_unsafe_command_paths(self):
  for name in ['../escape','/absolute','a/b','a\\b']:
   self.write(lambda commands,modules:commands[0].update(name=name))
   with self.assertRaises(Exception):self.verify()
 def test_contract_identity_mismatch(self):
  result=self.write();result['contract_sha256']='0'*64;(self.root/'result.json').write_text(json.dumps(result))
  with self.assertRaises(Exception):self.verify()
 def test_missing_log(self):
  self.write();p=self.root/'logs/compile-Synthetic.M0000.stdout';p.unlink()
  try:
   with self.assertRaises(Exception):self.verify()
  finally:p.write_bytes(b'')
 def test_success_with_bad_evidence_fails_collector_step(self):
  source=(ROOT/'ci/collect_evidence.py').read_text();self.assertIn("receipt['runner_status'] in (SUCCESS,STAGE_SUCCESS) and not receipt['replay_acceptance_evidence_complete']",source)



class AdditionalVisibilityTests(unittest.TestCase):
 def test_exact_reviewed_four_file_insertions(self):
  lock=json.loads((ROOT/'locks/visibility-predictions.json').read_text());self.assertEqual(lock['added_commands'],14);self.assertEqual(lock['added_bytes'],616);self.assertEqual(len(lock['files']),4)
  self.assertFalse(lock['actual_research_variants_compiled']);self.assertFalse(lock['actual_research_raw_expression_identity_verified']);self.assertFalse(lock['global_option_enabled']);self.assertFalse(lock['warnings_disabled'])
  for row in lock['files']:
   data=(SOURCE_ROOT/row['path']).read_bytes();self.assertEqual(c.f.sha(data),row['variant_sha256']);self.assertEqual(len(data),row['variant_bytes'])
   insertions=sorted(row['insertions'],key=lambda x:x['original_byte_offset']);offsets=[];added=0
   for ins in insertions:
    value=ins['insert_utf8'].encode();self.assertEqual(value,b'set_option backward.privateInPublic true in\n');offsets.append((ins['original_byte_offset']+added,value));added+=len(value)
   original=data
   for at,value in reversed(offsets):self.assertEqual(original[at:at+len(value)],value);original=original[:at]+original[at+len(value):]
   self.assertEqual(c.f.sha(original),row['baseline_sha256']);self.assertEqual(len(original),row['baseline_bytes'])
   self.assertEqual([r['module'] for r in c.header_parser.header(original)['imports']],[r['module'] for r in c.header_parser.header(data)['imports']])
 def test_only_sixteen_total_command_local_scopes(self):
  total=0
  for p in (SOURCE_ROOT/'src').rglob('*.lean'):
   for line in p.read_text().splitlines():
    if 'set_option backward.privateInPublic' in line:
     self.assertEqual(line,'set_option backward.privateInPublic true in');total+=1
  self.assertEqual(total,16)
 def test_predicted_pattern_first_and_no_owned_dependencies(self):
  owned=json.loads((ROOT/'locks/owned-sources.json').read_text());first=owned['sources'][0];self.assertEqual(first['module'],'SpectreGeometry.DeformationHomeomorphism');names=set(owned['module_order']);self.assertFalse(names.intersection(first['ordered_imports']))




class SourceArchiveTests(unittest.TestCase):
 def fixture(self,root,mutate=None,compressed_mutate=None,pin_mutate=None):
  import io,gzip,tarfile
  entries=[('src/Shared/A.lean',b'module\n'),('src/Shared/B.lean',b'module\npublic import Shared.A\n')]
  infos=[]
  for name,data in entries:
   info=tarfile.TarInfo(name);info.size=len(data);info.mode=0o644;infos.append((info,data))
  if mutate:mutate(infos)
  buf=io.BytesIO()
  with tarfile.open(fileobj=buf,mode='w',format=tarfile.USTAR_FORMAT) as tf:
   for info,data in infos:tf.addfile(info,io.BytesIO(data))
  raw=buf.getvalue();compressed=gzip.compress(raw,mtime=0)
  if compressed_mutate:compressed=compressed_mutate(compressed,raw)
  path=root/'owned-sources.tar.gz';path.write_bytes(compressed)
  pins={name:{'bytes':len(data),'sha256':c.f.sha(data)} for name,data in entries}
  contract={'inputs':pins,'owned_module_count':2,'owned_source_max_bytes':32*1024**2,'source_archive':{'path':path.name,'bytes':len(compressed),'sha256':c.f.sha(compressed),'tar_bytes':10240,'source_file_count':2,'source_bytes':sum(len(data) for _,data in entries),'format':'single-gzip-canonical-ustar-regular-sources-v1'}}
  if pin_mutate:pin_mutate(contract)
  return path,root/'new-source-root',contract
 def reject(self,**kwargs):
  with tempfile.TemporaryDirectory() as d:
   path,target,contract=self.fixture(Path(d),**kwargs)
   with self.assertRaises(Exception):c.extract_owned_sources(path,target,contract)
   self.assertFalse((Path(d)/'escape').exists())
 def test_exact_archive(self):
  with tempfile.TemporaryDirectory() as d:
   path,target,contract=self.fixture(Path(d));receipt=c.extract_owned_sources(path,target,contract)
   self.assertEqual(receipt['source_file_count'],2);self.assertTrue(receipt['all_source_pins_verified'])
   c.f.exact_tree(target,set(contract['inputs']))
 def test_frozen_archive_roundtrip_and_source_pins(self):
  contract=json.loads((ROOT/'contract.json').read_text());self.assertEqual(len(contract['distribution_files']),38);self.assertFalse((ROOT/'src').exists());self.assertEqual(contract['source_archive']['source_file_count'],2481)
  c.validate_distribution_layout(contract)
  for rel,pin in contract['inputs'].items():
   if rel.startswith('src/'):self.assertEqual(c.f.file_sha(SOURCE_ROOT/rel),pin['sha256'])
 def test_compressed_hash_before_destination(self):
  with tempfile.TemporaryDirectory() as d:
   path,target,contract=self.fixture(Path(d));contract['source_archive']['sha256']='0'*64
   with self.assertRaises(Exception):c.extract_owned_sources(path,target,contract)
   self.assertFalse(target.exists())
 def test_wrong_compressed_size(self):self.reject(pin_mutate=lambda c:c['source_archive'].update(bytes=1))
 def test_compressed_upper_bound(self):self.reject(pin_mutate=lambda c:c['source_archive'].update(bytes=8*1024**2+1))
 def test_expanded_tar_upper_bound(self):self.reject(pin_mutate=lambda c:c['source_archive'].update(tar_bytes=65*1024**2))
 def test_expanded_source_bound(self):self.reject(pin_mutate=lambda c:c.update(owned_source_max_bytes=1))
 def test_archive_manifest_source_count(self):self.reject(pin_mutate=lambda c:c['source_archive'].update(source_file_count=3))
 def test_archive_manifest_source_bytes(self):self.reject(pin_mutate=lambda c:c['source_archive'].update(source_bytes=1))
 def test_changed_member_bytes(self):self.reject(mutate=lambda xs:xs.__setitem__(0,(xs[0][0],b'changed')))
 def test_oversized_member(self):
  def change(xs):xs[0][0].size=100;xs[0]=(xs[0][0],b'x'*100)
  self.reject(mutate=change)
 def test_duplicate_member(self):self.reject(mutate=lambda xs:setattr(xs[1][0],'name',xs[0][0].name))
 def test_member_order(self):self.reject(mutate=lambda xs:xs.reverse())
 def test_missing_member(self):self.reject(mutate=lambda xs:xs.pop())
 def test_extra_member(self):self.reject(mutate=lambda xs:xs.append(xs[0]))
 def test_unsafe_or_non_source_names(self):
  for name in ['../escape','/escape','src/../escape','src//Shared/A.lean','src/./Shared/A.lean','ci/evil.py','contract.json','src/Shared/A.olean','src\\Shared\\A.lean']:
   with self.subTest(name=name):self.reject(mutate=lambda xs:setattr(xs[0][0],'name',name))
 def test_symlink_hardlink_directory_and_special(self):
  import tarfile
  for kind in [tarfile.SYMTYPE,tarfile.LNKTYPE,tarfile.DIRTYPE,tarfile.FIFOTYPE,tarfile.CHRTYPE,tarfile.XHDTYPE,tarfile.GNUTYPE_LONGNAME]:
   def change(xs):xs[0][0].type=kind;xs[0][0].linkname='../../escape'
   with self.subTest(kind=kind):self.reject(mutate=change)
 def test_executable_mode(self):self.reject(mutate=lambda xs:setattr(xs[0][0],'mode',0o755))
 def test_noncanonical_owner(self):self.reject(mutate=lambda xs:setattr(xs[0][0],'uid',10))
 def test_gzip_truncated(self):self.reject(compressed_mutate=lambda compressed,raw:compressed[:-1])
 def test_gzip_extra_member(self):
  import gzip
  self.reject(compressed_mutate=lambda compressed,raw:compressed+gzip.compress(b'extra'))
 def test_gzip_trailing_garbage(self):self.reject(compressed_mutate=lambda compressed,raw:compressed+b'extra')
 def test_gzip_expansion_bomb(self):
  import gzip
  self.reject(compressed_mutate=lambda compressed,raw:gzip.compress(b'x'*20000))
 def test_nonzero_tar_trailer(self):
  import gzip
  self.reject(compressed_mutate=lambda compressed,raw:gzip.compress(raw[:-1]+b'x'))
 def test_nonzero_member_padding(self):
  import gzip
  self.reject(compressed_mutate=lambda compressed,raw:gzip.compress(raw[:519]+b'x'+raw[520:]))
 def test_existing_destination_or_archive_link(self):
  for kind in ['existing','destination-link','archive-link','archive-hardlink']:
   with tempfile.TemporaryDirectory() as d:
    root=Path(d);path,target,contract=self.fixture(root)
    if kind=='existing':target.mkdir()
    if kind=='destination-link':target.symlink_to(root/'absent')
    if kind=='archive-link':copy=root/'copy';path.rename(copy);path.symlink_to(copy)
    if kind=='archive-hardlink':os.link(path,root/'copy')
    with self.subTest(kind=kind):
     with self.assertRaises(Exception):c.extract_owned_sources(path,target,contract)
 def test_distribution_extra_empty_directory_and_link(self):
  contract=json.loads((ROOT/'contract.json').read_text())
  for kind in ['empty-directory','extra-file','directory-link','file-link']:
   with tempfile.TemporaryDirectory() as d:
    root=Path(d)
    for rel in contract['distribution_files']:
     p=root/rel;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(b'')
    if kind=='empty-directory':(root/'shadow').mkdir()
    if kind=='extra-file':(root/'extra').write_bytes(b'')
    if kind=='directory-link':(root/'shadow').symlink_to(root/'ci',target_is_directory=True)
    if kind=='file-link':(root/'README.md').unlink();(root/'README.md').symlink_to(root/'LICENSE')
    with self.subTest(kind=kind),patch.object(c,'ROOT',root):
     with self.assertRaises(Exception):c.validate_distribution_layout(contract)
 def test_source_admission_before_runtime_and_cache(self):
  source=(ROOT/'ci/cache_diagnostic.py').read_text();self.assertLess(source.index('source_receipt=extract_owned_sources'),source.index('if a.runtime:'));self.assertLess(source.index('validate_owned_graph(contract,owned,required_lock,source_root)'),source.index('if a.runtime:'))
  self.assertIn("git_capture(ROOT,'status','--porcelain=v1','--untracked-files=all','--ignored')",source)
 def test_failed_partial_extraction_cannot_resume(self):
  with tempfile.TemporaryDirectory() as d:
   root=Path(d);path,target,contract=self.fixture(root,mutate=lambda xs:setattr(xs[1][0],'name','src/Shared/A.lean'))
   with self.assertRaises(Exception):c.extract_owned_sources(path,target,contract)
   self.assertTrue((target/'src/Shared/A.lean').is_file())
   path,_,contract=self.fixture(root)
   with self.assertRaises(Exception):c.extract_owned_sources(path,target,contract)

if __name__=='__main__':unittest.main()
