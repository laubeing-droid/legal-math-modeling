"""Actual child pytest runs, including fixtures and failure/skip/xfail handling."""
from pathlib import Path
import unittest,tempfile,subprocess,sys,json,os
R=Path(__file__).resolve().parents[1]

class PytestRunnerTests(unittest.TestCase):
 def check(self,content):
  with tempfile.TemporaryDirectory() as td:
   p=Path(td);(p/'test_sample.py').write_text(content,encoding='utf-8');out=p/'evidence.json'
   proc=subprocess.run([sys.executable,'-B',str(R/'scripts/run_all_registered_tests.py'),
      '--repo',str(p),'--worker',str(p),'--pytest-worker','--output',str(out)],
      capture_output=True,text=True,env={**os.environ,'PYTHONDONTWRITEBYTECODE':'1'})
   return proc.returncode,json.loads(out.read_text(encoding='utf-8'))
 def test_fixture_runs(self):
  code,r=self.check('import pytest\n@pytest.fixture\ndef x(): return 7\ndef test_ok(x): assert x==7\n')
  self.assertEqual(code,0);self.assertEqual(r['count'],1);self.assertEqual(r['tests'][0]['status'],'PASS')
 def test_failure_not_pass(self):
  code,r=self.check('def test_bad(): assert 1==2\n');self.assertNotEqual(code,0);self.assertEqual(r['tests'][0]['status'],'FAIL')
 def test_skip_not_pass(self):
  code,r=self.check('import pytest\n@pytest.mark.skip(reason="not implemented")\ndef test_skip(): pass\n')
  self.assertNotEqual(code,0);self.assertEqual(r['tests'][0]['status'],'SKIP')
 def test_xfail_not_pass(self):
  code,r=self.check('import pytest\n@pytest.mark.xfail(reason="missing")\ndef test_bad(): assert False\n')
  self.assertNotEqual(code,0);self.assertEqual(r['tests'][0]['status'],'XFAIL_NOT_COMPLETE')
 def test_empty_suite_not_pass(self):
  code,r=self.check('x=1\n');self.assertNotEqual(code,0);self.assertEqual(r['count'],0)
 def test_teardown_error_not_overwritten(self):
  code,r=self.check('import pytest\n@pytest.fixture\ndef f():\n yield 1\n raise ValueError("teardown")\ndef test_a(f): assert f==1\n')
  self.assertNotEqual(code,0);self.assertEqual(r['tests'][0]['phase'],'teardown');self.assertEqual(r['tests'][0]['status'],'FAIL')
if __name__=='__main__':unittest.main()
