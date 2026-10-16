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
  x=json.loads((ROOT/'contract.json').read_text());self.assertEqual(x['lean_heap_mib'],c.DIAGNOSTIC_HEAP_MIB);self.assertEqual(x['diagnostic_rss_gib']*1024**3,c.DIAGNOSTIC_RSS_BYTES);self.assertEqual(c.DIAGNOSTIC_HEAP_MIB,4096);self.assertEqual(c.DIAGNOSTIC_RSS_BYTES,8*1024**3);self.assertEqual(len(x['diagnostics']),4);self.assertEqual(x['diagnostic_timeout_seconds'],120);self.assertEqual(x['outer_timeout_minutes'],90)
if __name__=='__main__':unittest.main()
