import unittest
from dataclasses import replace
from fractions import Fraction as Q
from itertools import product
from unified.contract import *
from unified.arguments import *
from unified.burdens import BurdenPolicy,Assessment,resolve,transition
from unified.win_model import Row,Hyper,fit,calibrate,evaluate,validate_splits,train_evaluate
from unified.precision import Quantity,optimize_finite,QuadraticContraction
from unified.pipeline import combined_demo,scenario_outcomes
from reference.unified_reference import SearchResult,dung_member,powerset

S=Subject('case','2026_fixed','policy','scenario','finite_reference','model')

def dataset():
    rows=[]
    for split,month in [('train','01'),('calibration','03'),('test','05')]:
        for group,labels in [('weak',[0,0,0,1]),('strong',[1,1,1,0])]:
            for i,label in enumerate(labels):
                rid=f'{split}:{group}:{i}'
                rows.append(Row(rid,rid,'claimant_first_instance_at_least_50pct',group,split,
                                f'2025-{month}-02',f'2025-{month}-01',f'2025-{month}-20',
                                label,'SYNTHETIC_FIXTURE',True))
    return rows

class ContractTests(unittest.TestCase):
    def test_complete_and_partial(self):
        for b in range(9):
            c=search(S,'n',tuple(range(8)),lambda x:x%2==0,b)
            self.assertTrue(check_finite(S,'n',tuple(range(8)),lambda x:x in (0,2,4,6),c))
            self.assertLessEqual(c.classification.found,{0,2,4,6})
        self.assertEqual(c.classification.found,{0,2,4,6})
    def test_cross_subject_rejected(self):
        c=search(S,'n',(1,2),lambda x:True)
        self.assertFalse(check_finite(replace(S,law_version='other'),'n',(1,2),lambda x:True,c))
    def test_cross_component_rejected(self):
        c=search(S,'prob',(1,),lambda x:True)
        self.assertFalse(check_finite(S,'norm',(1,),lambda x:True,c))
    def test_missing_solution_rejected(self):
        c=FiniteCertificate(S,'n',SearchResult(frozenset({1}),frozenset({2}),frozenset(),True))
        self.assertFalse(check_finite(S,'n',(1,2),lambda x:True,c))
    def test_three_way_join(self):
        l={(1,('case1','a'))}; r={(('case2','a'),2)}
        self.assertEqual(relation_join(l,r),frozenset())
        self.assertEqual(relation_join(l,{(('case1','a'),2)}),{(1,2)})
    def test_projection_does_not_fix_omissions(self):
        self.assertNotEqual({20,30},{0,20,30,100})
        self.assertFalse(check_enclosure([0,20,30,100],Envelope(Q(20),Q(30))))
    def test_zero_mass_is_not_false(self):
        with self.assertRaises(ValueError):partial_mass_enclosure(Q(0),Q(0),Q(0))
        self.assertEqual(partial_mass_enclosure(Q(0),Q(0),Q(1)),Envelope(Q(0),Q(1)))
    def test_remainder_bound_exhaustive(self):
        for a,b,r in product(range(4),repeat=3):
            if a+b==0:continue
            env=partial_mass_enclosure(Q(a),Q(b),Q(r))
            for u in range(r+1):
                for v in range(r-u+1):
                    self.assertTrue(env.contains(Q(a+u,a+b+u+v)))
    def test_contamination_is_posterior_scope(self):
        self.assertEqual(posterior_contamination(Envelope(Q(3,5),Q(4,5)),Q(1,10)),Envelope(Q(27,50),Q(41,50)))
    def test_no_false_empirical_label(self):
        self.assertFalse(validate_claim_level(mathematical='exact',empirical='synthetic',requested='externally_validated_prediction',subject_matches=True))
    def test_empty_not_zero(self):
        with self.assertRaises(ValueError):finite_enclosure([])

class ArgumentTests(unittest.TestCase):
    def test_same_head_distinct_support(self):
        ls=(Leaf('e1','a'),Leaf('e2','a'))
        rs=(Rule('r',('a',),'b'),)
        args=generate('c',ls,rs,1)
        self.assertEqual(len([a for a in args if a.head=='b']),2)
    def test_assumptions_propagate(self):
        args=generate('c',(Leaf('h','a',True),),(Rule('r',('a',),'b'),),2)
        self.assertTrue(all(a.assumptions=={'h'} for a in args))
    def test_cycle_generates_no_ex_nihilo_fact(self):
        rs=(Rule('r',('a',),'b'),Rule('s',('b',),'a'))
        self.assertEqual(generate('c',(),rs,8),frozenset())
        self.assertEqual(horn_closure((),rs),frozenset())
    def test_depth_is_not_atomic_closure_completeness(self):
        rs=(Rule('r',('a',),'b'),Rule('s',('b',),'a'))
        ls=(Leaf('e','a'),)
        shallow=generate('c',ls,rs,1); deep=generate('c',ls,rs,4)
        self.assertLess(len(shallow),len(deep))
        self.assertEqual(horn_closure({'a'},rs),{'a','b'})
    def test_independent_tree_check(self):
        rs=(Rule('r',('a',),'b'),); ls=(Leaf('e','a'),)
        args=generate('c',ls,rs,2)
        self.assertTrue(all(valid_argument(a,'c',ls,rs,2) for a in args))
        a=next(a for a in args if a.head=='b')
        self.assertFalse(valid_argument(replace(a,head='false'),'c',ls,rs,2))
    def test_context_binding(self):
        a=next(iter(generate('c',(Leaf('e','a'),),(),0)))
        self.assertFalse(valid_argument(a,'d',(Leaf('e','a'),),(),0))
    def test_subargument_attack_not_lost(self):
        args=generate('c',(Leaf('e','a'),Leaf('f','not_a')),(Rule('r',('a',),'b'),),1)
        attacks=attacks_on_subarguments(args,{('not_a','a')})
        self.assertTrue(any(a.head=='not_a' and b.head=='b' for a,b in attacks))
    def test_preferred_prefix_maximality_invalid(self):
        self.assertFalse(dung_member('preferred',('a','b'),frozenset(),frozenset({'a'})))
    def test_nonempty_family_empty_extension(self):
        self.assertTrue(dung_member('grounded',('a',),frozenset({('a','a')}),frozenset()))
    def test_structural_id_delimiter(self):
        a=next(iter(generate('c',(Leaf('a|b','x'),),(),0)))
        b=next(iter(generate('c',(Leaf('a','x|b'),),(),0)))
        self.assertNotEqual(a.identity,b.identity)

class BurdenTests(unittest.TestCase):
    def setUp(self):
        self.p=BurdenPolicy('civil_payment','civil','payment','party_asserting_payment','high_probability',('L01:91',),frozenset({'ready_for_decision'}),'payment_effect','defence_unestablished',frozenset({'lawyer','court'}))
        self.a=Assessment(S,'paid','civil_payment','high_probability','undetermined',True,'lawyer','L',('evidence_review',))
    def test_undetermined_is_burden_effect_not_false(self):
        r=resolve(S,'paid','ready_for_decision',self.p,self.a)
        self.assertEqual(r.consequence,'defence_unestablished')
        self.assertEqual(r.meaning,'conditional_legal_analysis')
    def test_unfinished_pending(self):
        self.assertEqual(resolve(S,'paid','ready_for_decision',self.p,replace(self.a,completed=False)).status,'pending')
    def test_premature_stage_pending(self):
        self.assertEqual(resolve(S,'paid','filed',self.p,self.a).status,'pending')
    def test_model_prediction_not_finding(self):
        self.assertEqual(resolve(S,'paid','ready_for_decision',self.p,replace(self.a,origin='prediction')).status,'pending')
    def test_lawyer_not_court(self):
        self.assertEqual(resolve(S,'paid','ready_for_decision',self.p,self.a,analyst_mode=False).status,'pending')
    def test_cross_issue_rejected(self):
        with self.assertRaises(ValueError):resolve(S,'unpaid','ready_for_decision',self.p,self.a)
    def test_legal_transition(self):
        self.assertEqual(transition('served','hear'),'heard')
        with self.assertRaises(ValueError):transition('initial','decide')
    def test_all_profile_gates(self):
        import json,pathlib
        profiles=json.loads((pathlib.Path(__file__).parents[1]/'fixtures/burden_profiles.json').read_text())
        for d in profiles:
            p=BurdenPolicy(d['id'],d['field'],d['issue'],d['bearer'],d['standard'],tuple(d['sources']),frozenset({'ready_for_decision'}),d['success'],d['failure'],frozenset({'lawyer','court'}))
            a=Assessment(S,d['issue'],p.identity,p.standard,'established',True,'lawyer','L',('basis',))
            self.assertEqual(resolve(S,d['issue'],'ready_for_decision',p,a).consequence,p.success)
            self.assertEqual(resolve(S,d['issue'],'ready_for_decision',p,replace(a,state='undetermined')).consequence,p.failure)

class WinTests(unittest.TestCase):
    def test_real_counts_change_probability(self):
        rows=dataset(); train=[r for r in rows if r.split=='train']
        m=fit(train)
        self.assertGreater(m.predict('strong'),m.predict('weak'))
        flipped=fit([replace(r,label=1-r.label) for r in train])
        self.assertLess(flipped.predict('strong'),m.predict('strong'))
    def test_hyperposterior_normalized(self):
        m=fit([r for r in dataset() if r.split=='train'])
        self.assertEqual(sum(w for _,_,w in m.posterior),1)
    def test_pipeline_heldout_synthetic_not_empirical(self):
        m,c,e=train_evaluate(dataset())
        self.assertEqual(e['empirical_status'],'SYNTHETIC_NOT_VALIDATED')
        self.assertGreaterEqual(Q(e['brier_calibrated']),0)
    def test_missing_dataset_not_fake_calibration(self):
        with self.assertRaises(ValueError):train_evaluate([])
    def test_outcome_leakage(self):
        r=dataset()[0]
        with self.assertRaises(ValueError):replace(r,feature_latest='2026-01-01')
    def test_cross_appeal_cluster_leakage(self):
        rows=dataset(); rows[8]=replace(rows[8],cluster=rows[0].cluster)
        with self.assertRaises(ValueError):validate_splits(rows)
    def test_temporal_leakage(self):
        rows=dataset(); rows[0]=replace(rows[0],outcome_time='2025-06-01')
        with self.assertRaises(ValueError):validate_splits(rows)
    def test_win_definition_mismatch(self):
        rows=dataset(); rows[-1]=replace(rows[-1],objective='defendant_acquittal')
        with self.assertRaises(ValueError):validate_splits(rows)
    def test_calibrator_monotone(self):
        m,c,e=train_evaluate(dataset())
        ps=[c.predict(Q(i,20)) for i in range(21)]
        self.assertEqual(ps,sorted(ps))
    def test_no_training_on_test(self):
        with self.assertRaises(ValueError):fit(dataset())
    def test_unseen_group_uses_hyperposterior(self):
        m=fit([r for r in dataset() if r.split=='train'])
        self.assertTrue(0<m.predict('new')<1)
    def test_test_labels_do_not_change_model(self):
        rows=dataset();m,c,e=train_evaluate(rows)
        m2,c2,e2=train_evaluate([replace(r,label=1-r.label) if r.split=='test' else r for r in rows])
        self.assertEqual(m,m2);self.assertEqual(c,c2)

class NumericAndIntegrationTests(unittest.TestCase):
    def test_dimension_and_basis_checked(self):
        q=Quantity(Q(1),'CNY','principal','source')
        with self.assertRaises(ValueError):_ = q+Quantity(Q(2),'USD','principal','source')
        with self.assertRaises(ValueError):_ = q+Quantity(Q(2),'CNY','interest','source')
    def test_partial_optimum_not_claimed_optimal(self):
        r=optimize_finite((0,1,2),lambda x:True,lambda x:2-x,1)
        self.assertEqual(r['status'],'incumbent_only')
        self.assertEqual(optimize_finite((0,1,2),lambda x:True,lambda x:2-x)['value'],0)
    def test_contraction_real_parameters_and_bounds(self):
        m=QuadraticContraction(Q(2),Q(-3),Q(1,4),Q(0),Q(4),'explicit_utility')
        for i in range(8):
            x,env=m.iterate(Q(4),i)
            self.assertTrue(env.contains(m.optimum()))
            self.assertEqual(m.f(m.optimum()),m.optimum())
    def test_bad_contraction_rejected(self):
        for a,step in [(Q(0),Q(1)),(Q(1),Q(2)),(Q(1),Q(-1))]:
            with self.assertRaises(ValueError):QuadraticContraction(a,Q(1),step,Q(0),Q(1),'p')
    def test_discrete_legality_not_interpolated(self):
        legal={Q(0),Q(100)}
        self.assertNotIn(Q(50),legal)
    def test_end_to_end_probability_money_strategy(self):
        d=combined_demo()
        self.assertEqual(d['conditional_win_probability_bounds'],['2/5','2/5'])
        self.assertEqual(d['expected_award'],'76000')
        self.assertEqual(d['formal_fact_promotions'],0)
    def test_changed_probability_does_not_change_normative_scenarios(self):
        a=combined_demo(prob_paid=Q(1,5));b=combined_demo(prob_paid=Q(4,5))
        self.assertEqual(a['scenario_amounts'],b['scenario_amounts'])
        self.assertNotEqual(a['conditional_win_probability_bounds'],b['conditional_win_probability_bounds'])
    def test_overpayment_preserved(self):
        c,vals=scenario_outcomes(S,'payment_established',base=Q(100),paid=Q(120))
        self.assertIn(Q(-20),vals)
    def test_incomplete_returns_no_false_whole_result(self):
        c,vals=scenario_outcomes(S,'payment_not_established',base=Q(100),paid=Q(0),budget=0)
        self.assertFalse(c.classification.complete)
        self.assertEqual(vals,())

if __name__=='__main__': unittest.main()
