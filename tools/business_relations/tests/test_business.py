import unittest
from dataclasses import replace
from fractions import Fraction as Q
from datetime import date
from pathlib import Path
import json
from business import *

class BusinessTests(unittest.TestCase):
    def setUp(self):self.s=demo_spec();self.r=solve(self.s)
    def bad_outcome(self, **kw):
        r=replace(self.r,outcomes=(replace(self.r.outcomes[0],**kw),)+self.r.outcomes[1:])
        self.assertFalse(check(self.s,r))
    def test_exact_700_1000(self):
        self.assertTrue(check(self.s,self.r));self.assertEqual({o.principal_balance for o in self.r.outcomes},{Q(700),Q(1000)})
    def test_subject_swap(self):self.bad_outcome(context=replace(self.s.context,request='other'))
    def test_creditor_swap(self):self.bad_outcome(creditor='丙公司')
    def test_debtor_swap(self):self.bad_outcome(debtor='丙公司')
    def test_debt_swap(self):self.bad_outcome(debt_id='DEBT-2')
    def test_relation_swap(self):self.bad_outcome(relation_id='different-remedy')
    def test_basis_swap(self):self.bad_outcome(basis_ids=('OTHER-SOURCE',))
    def test_asof_swap(self):self.bad_outcome(asof_day=date(2025,1,1))
    def test_premise_laundering(self):self.bad_outcome(conclusion_kind='COURT_CONFIRMED')
    def test_wrong_money(self):self.bad_outcome(principal_balance=Q(999))
    def test_nonnegative_complementarity(self):
        o=self.r.outcomes[0];self.bad_outcome(principal_balance=o.principal_balance+1,overpayment_residual=Q(1))
    def test_float_money_rejected(self):self.bad_outcome(principal_balance=1000.0)
    def test_bool_not_int_world(self):self.bad_outcome(world=(('payment_recognized',0),))
    def test_source_span_mismatch(self):
        with self.assertRaises(ValueError):solve(replace(self.s,sources=(replace(self.s.sources[0],quoted='different'),)))
    def test_quoted_text_does_not_authenticate_truth(self):
        # Explicitly verify only the limited structural source statement.
        body='这是一个未经真实认证的陈述。'
        a=SourceSpan('S','1',body,0,len(body),body)
        self.assertTrue(a.valid())  # text equality only; no authenticated-truth output exists
    def test_unknown_preserves_both_worlds(self):self.assertEqual(len(self.r.outcomes),2)
    def test_fixed_true_has_one(self):
        s=replace(self.s,facts=(('payment_recognized',True),));r=solve(s)
        self.assertTrue(check(s,r));self.assertEqual(r.outcomes[0].principal_balance,Q(700))
    def test_constraints_inconsistent_not_success(self):
        s=replace(self.s,constraint=And(Atom('payment_recognized'),Not(Atom('payment_recognized'))))
        r=solve(s);self.assertEqual(r.mode,'INCONSISTENT_ASSUMPTIONS');self.assertTrue(check(s,r))
        self.assertFalse(check(s,replace(r,mode='EXACT_FINITE_SCENARIOS')))
    def test_partial_zero_not_complete(self):
        r=solve(self.s,0);self.assertTrue(check(self.s,r));self.assertEqual(len(r.pending),2)
        self.assertFalse(check(self.s,replace(r,mode='EXACT_FINITE_SCENARIOS')))
    def test_partial_one_keeps_unseen(self):
        r=solve(self.s,1);self.assertTrue(check(self.s,r));self.assertEqual(len(r.pending),1)
    def test_missing_branch_not_complete(self):self.assertFalse(check(self.s,replace(self.r,outcomes=self.r.outcomes[:1])))
    def test_duplicate_branch_rejected(self):self.assertFalse(check(self.s,replace(self.r,outcomes=self.r.outcomes+(self.r.outcomes[0],))))
    def test_false_rejected_world_as_pending(self):
        r=solve(self.s,1);self.assertFalse(check(self.s,replace(r,pending=((('bogus',True),),))))
    def test_nonempty_no_unknown_world(self):
        s=replace(self.s,payments=(),facts=());r=solve(s);self.assertEqual(len(r.outcomes),1);self.assertTrue(check(s,r))
    def test_early_date_not_final_claim(self):
        with self.assertRaises(ValueError):solve(replace(self.s,asof_day=date(2026,7,1)))
    def test_future_payment(self):
        with self.assertRaises(ValueError):solve(replace(self.s,payments=(replace(self.s.payments[0],event_day=date(2027,1,1)),)))
    def test_wrong_payment_party(self):
        with self.assertRaises(ValueError):solve(replace(self.s,payments=(replace(self.s.payments[0],payer='丙'),)))
    def test_duplicate_payment(self):
        with self.assertRaises(ValueError):solve(replace(self.s,payments=self.s.payments*2))
    def test_overpaid_residual_not_erased(self):
        s=replace(self.s,principal=Q(100),facts=(('payment_recognized',True),));r=solve(s)
        self.assertTrue(check(s,r));self.assertEqual((r.outcomes[0].principal_balance,r.outcomes[0].overpayment_residual),(Q(0),Q(200)))
    def test_all_small_conservation_cases(self):
        for amount in range(12):
            for paid in range(12):
                s=replace(self.s,principal=Q(amount),payments=(replace(self.s.payments[0],amount=Q(paid)),))
                self.assertTrue(check(s,solve(s)))
    def test_compilation_semantics(self):
        a,b=Atom('a'),Atom('b');forms=[TRUE,Formula('false'),a,b,Not(a),And(a,b),Or(a,b),And(Or(a,b),Not(b))]
        for f in forms:
            for av,bv in product((False,True),repeat=2):
                w=(('a',av),('b',bv));self.assertEqual(execute(compile_formula(f),w),denote(f,w))
    def test_independent_world_algorithms(self):
        for x,y in product((None,False,True),repeat=2):
            for f in (TRUE,And(Atom('a'),Atom('b')),Or(Atom('a'),Not(Atom('b')))):
                s=replace(self.s,payments=(),facts=(('a',x),('b',y)),constraint=f)
                self.assertEqual(frozenset(solver_worlds(s)),checker_worlds(s))
    def test_no_callback_argument(self):
        with self.assertRaises(TypeError):check(self.s,self.r,lambda _:True)
    def test_actual_file_roundtrip(self):
        from tempfile import TemporaryDirectory
        with TemporaryDirectory() as d:
            f=Path(d)/'output.txt';f.write_text(render(self.s,self.r),encoding='utf-8')
            self.assertTrue(verify_document(self.s,self.r,f.read_text(encoding='utf-8')))
    def test_doc_wrong_party(self):self.assertFalse(verify_document(self.s,self.r,render(self.s,self.r).replace('义务人："乙公司"','义务人："丙公司"')))
    def test_doc_wrong_money(self):self.assertFalse(verify_document(self.s,self.r,render(self.s,self.r).replace('本金余额：700','本金余额：800')))
    def test_doc_deleted_guard(self):self.assertFalse(verify_document(self.s,self.r,render(self.s,self.r).replace('；性质：条件计算','；性质：无条件')))
    def test_doc_wrong_basis(self):self.assertFalse(verify_document(self.s,self.r,render(self.s,self.r).replace('依据：["SYNTHETIC-BASIS"]','依据：["OTHER"]')))
    def test_doc_extra_unchecked_claim(self):self.assertFalse(verify_document(self.s,self.r,render(self.s,self.r)+'因此本案必胜。\n'))
    def test_doc_removed_branch(self):
        text=render(self.s,self.r);lines=text.splitlines();text='\n'.join(l for l in lines if '本金余额：700' not in l)+'\n'
        self.assertFalse(verify_document(self.s,self.r,text))
    def test_doc_duplicate_branch(self):
        text=render(self.s,self.r);ln=next(l for l in text.splitlines() if l.startswith('情景：'))
        self.assertFalse(verify_document(self.s,self.r,text.replace(FOOTER,ln+'\n'+FOOTER)))
    def test_doc_false_exact_status(self):
        r=solve(self.s,1);text=render(self.s,r).replace('PARTIAL_SCENARIOS','EXACT_FINITE_SCENARIOS')
        self.assertFalse(verify_document(self.s,r,text))
    def test_doc_semantically_same_row_order(self):
        lines=render(self.s,self.r).splitlines();lines[13:15]=reversed(lines[13:15])
        self.assertTrue(verify_document(self.s,self.r,'\n'.join(lines)+'\n'))
    def test_context_encoding_colon_safe(self):
        a=replace(self.s.context,request='a:b',scenario='c');b=replace(self.s.context,request='a',scenario='b:c')
        self.assertNotEqual(a.canonical_json(),b.canonical_json())
        self.assertEqual(ContextKey.from_json(a.canonical_json()),a)

class DecisionTests(unittest.TestCase):
    def setUp(self):
        self.s=demo_spec();self.r=solve(self.s)
        weights=tuple((o.world,Q(2,5) if dict(o.world)['payment_recognized'] else Q(3,5)) for o in self.r.outcomes)
        self.m=DecisionInputs(self.s.context,weights,Q(800),(Q(100),Q(60),Q(10),Q(10)),(Q(600),Q(850),Q(1100)))
        self.a=derive_analytics(self.s,self.r,self.m)
    def test_same_inputs_feed_every_value(self):
        self.assertEqual((self.a.expected,self.a.event_probability,self.a.lower,self.a.upper,self.a.selected),(Q(880),Q(3,5),Q(790),Q(930),Q(850)))
        self.assertTrue(check_analytics(self.s,self.r,self.m,self.a))
    def test_float_candidate_rejected(self):self.assertFalse(check_analytics(self.s,self.r,self.m,replace(self.a,selected=850.0)))
    def test_arbitrary_bargaining_interval(self):self.assertFalse(check_analytics(self.s,self.r,self.m,replace(self.a,lower=Q(10**9),upper=Q(10**9+1))))
    def test_midpoint_not_legal(self):self.assertFalse(check_analytics(self.s,self.r,self.m,replace(self.a,selected=(self.a.lower+self.a.upper)/2)))
    def test_replace_entire_legal_set(self):self.assertFalse(check_analytics(self.s,self.r,self.m,replace(self.a,legal_options=(Q(860),),mutually_acceptable=(Q(860),),selected=Q(860))))
    def test_probabilities_not_silent_reweight(self):
        other=replace(self.m,weights=tuple((w,Q(1,2)) for w,_ in self.m.weights));a=derive_analytics(self.s,self.r,other)
        self.assertFalse(check_analytics(self.s,self.r,self.m,a))
    def test_incomplete_probability_mass(self):
        with self.assertRaises(ValueError):derive_analytics(self.s,self.r,replace(self.m,weights=self.m.weights[:1]))
    def test_bad_normalization(self):
        with self.assertRaises(ValueError):derive_analytics(self.s,self.r,replace(self.m,weights=tuple((w,Q(3,5)) for w,_ in self.m.weights)))
    def test_no_settlement_is_honest(self):
        m=replace(self.m,legal_options=(Q(0),Q(1000)));a=derive_analytics(self.s,self.r,m)
        self.assertIsNone(a.selected);self.assertTrue(check_analytics(self.s,self.r,m,a))
    def test_model_scope_mismatch(self):
        with self.assertRaises(ValueError):derive_analytics(self.s,self.r,replace(self.m,context=replace(self.s.context,model_version='other')))
    def test_no_metrics_on_partial(self):
        with self.assertRaises(ValueError):derive_analytics(self.s,solve(self.s,1),self.m)

if __name__=='__main__':unittest.main()
