import unittest,sys,copy
from pathlib import Path
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'scripts'))
from patch_ci import patch

class CIPatchTests(unittest.TestCase):
 def data(self):
  return {'name':'existing','on':{'push':{'branches':['main']}},'jobs':{
    'python-gates':{'steps':[{'name':'existing','run':'original-tests'}]},
    'lean-full-clean-build':{'steps':[{'name':'Build all project Lean modules from a clean project build','run':'existing-build'}]},
    'seven-axis-acceptance':{'needs':['python-gates','lean-full-clean-build']},
    'runtime-refinement':{'uses':'existing'},
    'release-certificate':{'needs':['python-gates','lean-full-clean-build','runtime-refinement','seven-axis-acceptance'],'steps':[]},
    'final-gate':{'needs':['python-gates','lean-full-clean-build','runtime-refinement','seven-axis-acceptance','release-certificate'],'steps':[{'run':"required={'lean-full-clean-build','python-gates','runtime-refinement','seven-axis-acceptance','release-certificate'}"}]}}}
 def test_preserve_old_jobs(self):
  d=self.data();q=patch(d);self.assertTrue(set(d['jobs'])<=set(q['jobs']));self.assertEqual(q['jobs']['runtime-refinement'],d['jobs']['runtime-refinement'])
 def test_gate_dependency(self):
  q=patch(self.data());self.assertIn('mathematics-completion',q['jobs']['final-gate']['needs'])
 def test_idempotent(self):q=patch(self.data());self.assertEqual(patch(q),q)
 def test_not_modify_input(self):d=self.data();old=copy.deepcopy(d);patch(d);self.assertEqual(d,old)
 def test_missing_authority_rejected(self):
  d=self.data();del d['jobs']['seven-axis-acceptance']
  with self.assertRaises(ValueError):patch(d)
 def test_changed_final_script_rejected(self):
  d=self.data();d['jobs']['final-gate']['steps']=[]
  with self.assertRaises(ValueError):patch(d)
 def test_generation_before_build(self):
  ss=patch(self.data())['jobs']['lean-full-clean-build']['steps'];ns=[s.get('name') for s in ss]
  self.assertLess(ns.index('Generate and verify all mathematics type assertions'),ns.index('Build all project Lean modules from a clean project build'))
 def test_partial_dispatch_not_completion(self):self.assertIn('full-release',patch(self.data())['jobs']['mathematics-completion']['if'])
if __name__=='__main__':unittest.main()
