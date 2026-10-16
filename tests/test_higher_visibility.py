"""Data-only reconstruction controls for the independently reviewed four scopes."""
import copy,json,sys,tarfile,unittest
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1];sys.path.insert(0,str(ROOT/'ci'))
import cache_diagnostic as a
h=a.higher
class VisibilityTests(unittest.TestCase):
 @classmethod
 def setUpClass(cls):
  cls.lock=a.f.load_json(ROOT/'locks/higher-visibility-variants.json');cls.rows=cls.lock['files'];cls.data={}
  with tarfile.open(ROOT/'owned-sources.tar.gz') as tar:
   for row in cls.rows:cls.data[row['module']]=tar.extractfile(row['path']).read()
 def test_exact_four_scopes_preserve_every_original_byte(self):
  self.assertEqual(sum(len(r['insertions']) for r in self.rows),4)
  for row in self.rows:
   old=h.reconstruct_visibility_source(self.data[row['module']],row,a);self.assertEqual(len(self.data[row['module']])-len(old),88)
 def test_changed_proof_body_rejected(self):
  row=self.rows[0];data=self.data[row['module']].replace(b'exact congrArg',b'exact  congrArg')
  with self.assertRaises(Exception):h.reconstruct_visibility_source(data,row,a)
 def test_missing_local_scope_rejected(self):
  row=self.rows[0];data=self.data[row['module']].replace(b'set_option backward.privateInPublic true in\n',b'',1)
  with self.assertRaises(Exception):h.reconstruct_visibility_source(data,row,a)
 def test_global_option_rejected(self):
  row=self.rows[0];data=self.data[row['module']].replace(b' true in\n',b' true\n',1)
  with self.assertRaises(Exception):h.reconstruct_visibility_source(data,row,a)
 def test_wrong_insertion_anchor_rejected(self):
  row=copy.deepcopy(self.rows[0]);row['insertions'][0]['anchor']='private theorem unapproved'
  with self.assertRaises(Exception):h.reconstruct_visibility_source(self.data[row['module']],row,a)
 def test_wrong_original_hash_rejected(self):
  row=copy.deepcopy(self.rows[0]);row['baseline_sha256']='0'*64
  with self.assertRaises(Exception):h.reconstruct_visibility_source(self.data[row['module']],row,a)
 def test_profile_requires_review_pin(self):
  c=a.f.load_json(ROOT/'contract.json');c['higher_visibility_independent_review_sha256']='0'*64
  with self.assertRaises(Exception):a.validate_diagnostic_profile(c)
if __name__=='__main__':unittest.main()
