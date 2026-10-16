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
 def test_pending_review(self):
  self.assertEqual(json.loads((ROOT/'contract.json').read_text())['review_status'],'pending_independent_review')

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

if __name__=='__main__':unittest.main()
