"""有限数学探针：只检验本报告反例/有限构造，不是JC实现或Lean证明。"""
from fractions import Fraction as Q
from itertools import product
import unittest, json
from pathlib import Path


def classify_family(family):
    if not family:
        return {'status':'incompatible','may_out':None,'robustly_allowed':None}
    if any(not outcomes for outcomes in family):
        return {'status':'model_infeasible','may_out':None,'robustly_allowed':None}
    return {'status':'defined','may_out':set.union(*family),'robustly_allowed':set.intersection(*family)}


def denote_rel(a,b):
    return {(x,y) for x in a for y in b if x+y==4}


def reduce_rel(a,b):
    full=denote_rel(a,b)
    return ({x for x,y in full},{y for x,y in full})


def impact_closure(direct, dependents):
    reached=set(direct)
    changed=True
    while changed:
        new=reached|{v for u in reached for v in dependents.get(u,set())}
        changed=new!=reached
        reached=new
    return reached


def settlement(allowed,lo,hi):
    return {x for x in allowed if lo<=x<=hi}


class BusinessSemanticsProbes(unittest.TestCase):
    def test_01_rubric_seven_is_not_business_eight(self):
        required=set(range(8));covered=set(range(7))
        self.assertTrue(len(covered)>=7)
        self.assertFalse(required<=covered)

    def test_02_one_legal_claim_is_not_all_claims(self):
        allowed={'principal','interest','eligible_costs'};found={'principal'}
        self.assertLess(found,allowed)
        self.assertTrue(found<=allowed)

    def test_03_vacuity_needs_consistency(self):
        states=range(-3,4)
        assumption=lambda x:x>0 and x<0
        self.assertTrue(all(not assumption(x) or x==42 for x in states))
        self.assertFalse(any(assumption(x) for x in states))

    def test_04_cannot_control_external_win(self):
        actions={'file','settle_offer'};courts={'win','lose'}
        self.assertFalse(any(all(outcome=='win' for outcome in courts) for _ in actions))

    def test_05_projection_inverse_image(self):
        a={1};b={100};w=set(product(a,b))
        correct={(x,y) for x,y in w if x in a and y in b}
        wrong={(x,0) for x in a}&{(0,y) for y in b}
        self.assertEqual(correct,{(1,100)});self.assertEqual(wrong,set())

    def test_06_real_reduction_preserves_joint_semantics(self):
        a={0,1,2,3,4};b={2,3}
        a2,b2=reduce_rel(a,b)
        self.assertEqual(denote_rel(a,b),denote_rel(a2,b2))
        self.assertEqual(a2,{1,2});self.assertLess(a2,a)

    def test_07_source_probability_shared_event(self):
        worlds=list(product([False,True],repeat=3))
        p=Q(sum(x and (y or z) for x,y,z in worlds),len(worlds))
        wrong=1-(1-Q(1,4))**2
        self.assertEqual(p,Q(3,8));self.assertNotEqual(p,wrong)

    def test_08_payment_conservation(self):
        payment=Q(30);allocation={'principal':Q(30),'interest':Q(30)}
        self.assertGreater(sum(allocation.values()),payment)
        allocation={'principal':Q(20),'interest':Q(10)}
        self.assertEqual(sum(allocation.values()),payment)

    def test_09_joint_liability_not_double_recovery(self):
        loss=Q(100);external_demands={'A':Q(100),'B':Q(100)}
        self.assertEqual(sum(external_demands.values()),2*loss)
        receipts={'A':Q(70),'B':Q(30)}
        self.assertEqual(sum(receipts.values()),loss)

    def test_10_typed_effect_exclusivity_is_not_termination(self):
        state={'license_active':True,'exclusive':True,'settlement_due':Q(10)}
        after=dict(state);after['exclusive']=False
        self.assertTrue(after['license_active']);self.assertEqual(after['settlement_due'],10)

    def test_11_no_document_is_not_no_event(self):
        payment_evidence=[]
        event_status='unknown' if not payment_evidence else 'observed'
        self.assertEqual(event_status,'unknown');self.assertNotEqual(event_status,'not_occurred')

    def test_12_definition_patch_impacts_unedited_clause(self):
        graph={'definition':{'obligation'},'obligation':{'amount'},'amount':set(),'unrelated':set()}
        affected=impact_closure({'definition'},graph)
        self.assertEqual(affected,{'definition','obligation','amount'})
        self.assertNotIn('unrelated',affected)

    def test_13_may_must_and_empty(self):
        r=classify_family([{'pay70','fee'},{'pay100','fee'}])
        self.assertEqual(r['robustly_allowed'],{'fee'});self.assertIn('pay70',r['may_out'])
        ambiguous=[{'win','lose'},{'win','lose'}]
        self.assertIn('win',classify_family(ambiguous)['robustly_allowed'])
        self.assertFalse(all(y=='win' for possible in ambiguous for y in possible))
        self.assertEqual(classify_family([set()])['status'],'model_infeasible')
        self.assertEqual(classify_family([])['status'],'incompatible')

    def test_14_legal_set_and_bargaining_interval(self):
        lawful={Q(0),Q(10)}
        self.assertEqual(settlement(lawful,Q(3),Q(7)),set())
        self.assertNotIn(Q(5),lawful)

    def test_15_selection_does_not_preserve_conditional_coverage(self):
        # 100等概率样本，5个错误恰好是系统展示的5个。
        worlds=set(range(100));bad=set(range(5));accept=set(range(5))
        self.assertEqual(Q(len(bad&accept),len(worlds)),Q(1,20))
        self.assertEqual(Q(len(bad&accept),len(accept)),1)

    def test_16_actual_and_adjudicated_probability_differ(self):
        p_fact=Q(3,4);sensitivity=Q(2,3);false_positive=Q(1,5)
        p_admitted=p_fact*sensitivity+(1-p_fact)*false_positive
        self.assertEqual(p_admitted,Q(11,20));self.assertNotEqual(p_fact,p_admitted)
        self.assertEqual(100-30*p_admitted,Q(167,2))


if __name__=='__main__':
    suite=unittest.defaultTestLoader.loadTestsFromTestCase(BusinessSemanticsProbes)
    result=unittest.TextTestRunner(verbosity=2).run(suite)
    target=Path(__file__).resolve().parents[1]/'evidence/probes_result.json'
    target.write_text(json.dumps({'kind':'本轮有限数学/语义反例探针，不是生产测试或全称证明','run':result.testsRun,'failures':len(result.failures),'errors':len(result.errors),'skipped':len(result.skipped),'success':result.wasSuccessful()},ensure_ascii=False,indent=2))
    raise SystemExit(0 if result.wasSuccessful() else 1)
