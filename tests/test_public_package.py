import hashlib,json,re,unittest
from pathlib import Path

ROOT=Path(__file__).resolve().parents[1]
def digest(path):return hashlib.sha256(path.read_bytes()).hexdigest()

class PublicPackageTests(unittest.TestCase):
    def test_exact_plan_input_and_distribution_pins(self):
        p=json.loads((ROOT/'payload-verification-plan.json').read_bytes())
        rows=p['input_files'];names=[r['path'] for r in rows]
        self.assertEqual(names,sorted(set(names)))
        for row in rows:self.assertEqual(digest(ROOT/row['path']),row['sha256'])
        expected=set(names)|{'payload-verification-plan.json','.github/workflows/conditional-payload-verification.yml'}
        actual={f.relative_to(ROOT).as_posix() for f in ROOT.rglob('*') if f.is_file() and '.git' not in f.relative_to(ROOT).parts}
        self.assertEqual(actual,expected)
        self.assertEqual(p['helper_sha256'],digest(ROOT/'ci/verify_official_payload.py'))
        self.assertEqual(p['core_sha256'],'7fffe6644346845193ee2e8d4213590816f00858fb1948862de2f50e5b198bdc')
        self.assertEqual([r['stage_id'] for r in p['stages']],['F2_period_hierarchy'])

    def test_exact_workflow_limits_and_success_binding(self):
        text=(ROOT/'.github/workflows/conditional-payload-verification.yml').read_text()
        self.assertEqual(re.findall(r'uses: (.+)',text),[
            'actions/checkout@11d5960a326750d5838078e36cf38b85af677262',
            'actions/upload-artifact@ea165f8d65b6e75b540449e92b4886f43607fa02'])
        for value in ['runs-on: ubuntu-22.04','timeout-minutes: 35','timeout-minutes: 31',
                      'persist-credentials: false','contents: read','actions: read',
                      '/usr/bin/timeout --signal=KILL 1800s','/usr/bin/python3 -I -S -B',
                      '--seconds 1740','test "$(git rev-parse HEAD)" = "$GITHUB_SHA"',
                      'git status --porcelain --untracked-files=all','if: ${{ success() }}',
                      'CONDITIONAL_PAYLOAD_VERIFIED_V1','steps.upload_receipt.outputs.artifact-digest']:
            self.assertIn(value,text)
        self.assertEqual(text.count(digest(ROOT/'payload-verification-plan.json')),2)
        self.assertNotIn('sudo ',text)
        self.assertNotIn('write',text)

    def test_scope_and_exact_f2_producer(self):
        p=json.loads((ROOT/'payload-verification-plan.json').read_bytes())
        e=json.loads((ROOT/p['stages'][0]['expectation_file']).read_bytes())
        c=json.loads((ROOT/p['stages'][0]['certificate_file']).read_bytes())
        self.assertEqual(e['origin']['artifact_id'],12063266670)
        self.assertEqual(e['origin']['artifact_zip_bytes'],971940387)
        self.assertEqual(e['origin']['artifact_zip_sha256'],'c4b451deb867d8bb0b5edbd40d33ab18815cec4e7edebea5866038cf4c12b788')
        self.assertEqual(e['origin']['identity'],p['producer']['identity'])
        self.assertEqual(c['fresh_compile_count'],1226)
        self.assertEqual(c['fresh_kernel_check_count'],1226)
        self.assertEqual(p['producer']['status_policy'],'completed_only')
        self.assertEqual(c['raw_audits'],{})
        self.assertTrue(c['conditional_C_remains_explicit'])
        self.assertFalse(c['final_C_proof_certified'])
        self.assertFalse(c['unconditional_monotile_proof_certified'])
        self.assertEqual(c['payload_byte_verification_status'],'pending')
        self.assertEqual(c['independent_review_sha256'],p['stages'][0]['independent_review_sha256'])

if __name__=='__main__':unittest.main()
