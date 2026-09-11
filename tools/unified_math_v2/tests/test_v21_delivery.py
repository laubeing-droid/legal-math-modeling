import unittest,json,tempfile,importlib.util
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
def module(name):
    spec=importlib.util.spec_from_file_location('delivery_'+name,ROOT/'scripts'/f'{name}.py')
    m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m);return m
class DeliveryTests(unittest.TestCase):
    def test_full_task_and_source_coverage(self):self.assertEqual(module('validate_plan').validate()['tasks'],34)
    def test_environment_audit_requires_output(self):
        with self.assertRaises(ValueError):module('environment_audit').verify_log('')
    def test_environment_audit_rejects_bad_axiom(self):
        m=module('environment_audit');rows=[{'name':n,'axioms':['sorryAx'],'proof_dependencies':[]} for n in m.REQUIRED]
        with self.assertRaises(ValueError):m.verify_log(m.PREFIX+json.dumps(rows))
    def test_environment_audit_checks_actual_roots(self):
        m=module('environment_audit');rows=[{'name':'JurisLean.ULM.UnifiedV21.not_the_required_root','axioms':[],'proof_dependencies':[]}]
        with self.assertRaises(ValueError):m.verify_log(m.PREFIX+json.dumps(rows))
    def test_audit_parser_fixture_not_machine_acceptance(self):
        m=module('environment_audit');rows=[{'name':n,'axioms':[],'proof_dependencies':[]} for n in m.REQUIRED]
        r=m.verify_log(m.PREFIX+json.dumps(rows));self.assertEqual(r['theorem_count'],3)
        # This tests only parsing. These fabricated rows are never shipped as CI evidence.
    def test_source_capture_does_not_approve_law(self):
        m=module('source_intake')
        with tempfile.TemporaryDirectory() as tmp:
            f=Path(tmp)/'text.txt';f.write_text('SYNTHETIC_SOURCE_TEST')
            r=m.capture('L-CIVIL-CODE',f,'https://www.court.gov.cn/zixun/xiangqing/233181.html',Path(tmp)/'out')
            self.assertEqual(r['translation_approval'],'NOT_GRANTED')
    def test_source_host_mismatch(self):
        m=module('source_intake')
        with tempfile.TemporaryDirectory() as tmp:
            f=Path(tmp)/'text.txt';f.write_text('SYNTHETIC_SOURCE_TEST')
            with self.assertRaises(ValueError):m.capture('L-CIVIL-CODE',f,'https://example.invalid/fake',Path(tmp)/'out')
    def test_current_jc_pin_is_not_old_review(self):
        b=json.loads((ROOT/'manifests/baseline-v21.json').read_text());self.assertNotEqual(b['jc_commit'],b['old_review_jc_commit'])
    def test_all_original_targets_preserved(self):
        old=set([f'F{i:02}' for i in range(1,15)]+[f'P{i:02}' for i in range(1,14)]+['E01']+
          [f'N{i:02}' for i in range(1,11)]+[f'B{i:02}' for i in range(1,8)]+[f'G{i:02}' for i in range(1,6)]+[f'C{i:02}' for i in range(1,8)])
        self.assertEqual(old,{x['id'] for x in json.loads((ROOT/'manifests/proof_targets.json').read_text())})

class NumericAndImmutabilityTests(unittest.TestCase):
    def test_model_snapshots_mutable_state_lists(self):
        from fractions import Fraction as Q
        from reference.core import Node
        from v21.context import synthetic_context
        from v21.model_binding import bind_synthetic_model
        states=['yes','no'];n=Node('A',states,[],{():(Q(1,2),Q(1,2))})
        model=bind_synthetic_model(synthetic_context(),[n]);states[0]='forged'
        self.assertEqual(model.nodes[0].states,('yes','no'))
    def test_float_output_does_not_count_as_exact_witness(self):
        from fractions import Fraction as Q
        from v21.context import synthetic_context
        from v21.bridge import SettlementInput,solve_settlement,check_settlement
        c=synthetic_context();x=SettlementInput(c,100,40,Q(1,2),Q(1,2),5,5,0,0,(75,80,85),'test-only',70)
        r=solve_settlement(x);r['claimant_expectation']=80.0
        self.assertFalse(check_settlement(c,x,r))
