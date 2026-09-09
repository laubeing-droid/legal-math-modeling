import json
import tempfile
import unittest
from dataclasses import replace
from fractions import Fraction as Q
from pathlib import Path
from business import (demo_spec,solve,DecisionInputs,derive_analytics,render,check_analytics)
from delivery_bundle import *

class DeliveryBundleTests(unittest.TestCase):
    def setUp(self):
        self.s=demo_spec(); self.r=solve(self.s)
        weights=tuple((o.world,Q(2,5) if dict(o.world)['payment_recognized'] else Q(3,5)) for o in self.r.outcomes)
        self.m=DecisionInputs(self.s.context,weights,Q(800),(Q(100),Q(60),Q(10),Q(10)),(Q(600),Q(850),Q(1100)))
        self.bound=snapshot_inputs(self.s,self.m)
        self.a=derive_analytics(self.s,self.r,self.m)
        self.docs=self.files(self.s,self.r,self.m,self.a)
    @staticmethod
    def files(s,r,m,a):
        return {FILES[0]:render(s,r).encode(),FILES[1]:render_calculation_json(s,r,m,a).encode()}
    def verdict(self,docs=None,**kwargs):
        values=dict(expected=self.bound,spec=self.s,result=self.r,model=self.m,analytics=self.a,
                    artifact_bytes=self.docs if docs is None else docs)
        values.update(kwargs)
        return check_business_bundle(**values)
    def changed(self,edit):
        docs=self.docs.copy(); obj=json.loads(docs[FILES[1]]);edit(obj)
        docs[FILES[1]]=json.dumps(obj,ensure_ascii=False).encode()
        return docs
    def test_whole_bundle_accepts(self):
        v=self.verdict();self.assertTrue(v.accepted);self.assertEqual(len(v.checked_artifacts),2)
    def test_actual_two_files_are_read(self):
        with tempfile.TemporaryDirectory() as tmp:
            root=Path(tmp)
            for name,content in self.docs.items():(root/name).write_bytes(content)
            self.assertTrue(self.verdict(read_artifacts(root)).accepted)
            obj=json.loads((root/FILES[1]).read_text());obj['analytics']['event_probability']='1'
            (root/FILES[1]).write_text(json.dumps(obj))
            self.assertFalse(self.verdict(read_artifacts(root)).accepted)
    def test_probability_tampering_rejected(self):
        self.assertFalse(self.verdict(self.changed(lambda o:o['analytics'].__setitem__('event_probability','1'))).accepted)
    def test_expectation_tampering_rejected(self):
        self.assertFalse(self.verdict(self.changed(lambda o:o['analytics'].__setitem__('expected','999'))).accepted)
    def test_bounds_tampering_rejected(self):
        for key in ('lower','upper'):
            with self.subTest(key=key):
                self.assertFalse(self.verdict(self.changed(lambda o:o['analytics'].__setitem__(key,'999999'))).accepted)
    def test_selected_outside_action_grid_rejected(self):
        self.assertFalse(self.verdict(self.changed(lambda o:o['analytics'].__setitem__('selected','860'))).accepted)
    def test_eligible_list_omission_rejected(self):
        self.assertFalse(self.verdict(self.changed(lambda o:o['analytics'].__setitem__('mutually_acceptable',[]))).accepted)
    def test_wrong_json_world_balance_rejected(self):
        self.assertFalse(self.verdict(self.changed(lambda o:o['result']['outcomes'][0].__setitem__('principal_balance','999'))).accepted)
    def test_json_world_branch_swap_without_money_swap_rejected(self):
        def change(o):
            a,b=o['result']['outcomes'];a['world'],b['world']=b['world'],a['world']
        self.assertFalse(self.verdict(self.changed(change)).accepted)
    def test_missing_json_world_rejected(self):
        self.assertFalse(self.verdict(self.changed(lambda o:o['result']['outcomes'].pop())).accepted)
    def test_duplicate_json_world_rejected(self):
        self.assertFalse(self.verdict(self.changed(lambda o:o['result']['outcomes'].append(o['result']['outcomes'][0]))).accepted)
    def test_reordered_json_worlds_preserve_semantics(self):
        self.assertTrue(self.verdict(self.changed(lambda o:o['result']['outcomes'].reverse())).accepted)
    def test_wrong_principal_document_party_rejected(self):
        docs=self.docs.copy();docs[FILES[0]]=docs[FILES[0]].replace('乙公司'.encode(),'丙公司'.encode())
        self.assertFalse(self.verdict(docs).accepted)
    def test_extra_unverified_text_rejected(self):
        docs=self.docs.copy();docs[FILES[0]]+='因此必胜。'.encode()
        self.assertFalse(self.verdict(docs).accepted)
    def test_missing_or_extra_deliverable_rejected(self):
        for files in ({FILES[0]:self.docs[FILES[0]]},{**self.docs,'unverified.txt':b'win'}):
            self.assertFalse(self.verdict(files).accepted)
    def test_bad_encoding_rejected(self):
        docs=self.docs.copy();docs[FILES[1]]=b'\xff';self.assertFalse(self.verdict(docs).accepted)
    def test_duplicate_json_key_rejected(self):
        docs=self.docs.copy(); raw=docs[FILES[1]].decode()
        docs[FILES[1]]=raw.replace('"schema":',f'"schema":"{SCHEMA}","schema":',1).encode()
        self.assertFalse(self.verdict(docs).accepted)
    def test_extra_claim_json_field_rejected(self):
        self.assertFalse(self.verdict(self.changed(lambda o:o.__setitem__('guaranteed_win',True))).accepted)
    def test_nan_or_float_or_zero_denominator_rejected(self):
        for value in (float('nan'),0.6,True,'1/0','0.6'):
            with self.subTest(value=value):
                self.assertFalse(self.verdict(self.changed(lambda o:o['analytics'].__setitem__('event_probability',value))).accepted)
    def test_model_version_mismatch_rejected(self):
        self.assertFalse(self.verdict(self.changed(lambda o:o['decision_inputs'].__setitem__('model_version','other'))).accepted)
    def test_model_basis_changed_rejected(self):
        self.assertFalse(self.verdict(self.changed(lambda o:o['decision_inputs'].__setitem__('basis','new-source'))).accepted)
    def test_same_model_id_but_all_parameters_replaced_rejected(self):
        m=replace(self.m,weights=tuple((w,Q(1,2)) for w,_ in self.m.weights),threshold=Q(750),
                  costs=(Q(10),)*4,legal_options=(Q(850),))
        a=derive_analytics(self.s,self.r,m)
        self.assertTrue(check_analytics(self.s,self.r,m,a))
        v=self.verdict(self.files(self.s,self.r,m,a),model=m,analytics=a)
        self.assertFalse(v.accepted);self.assertEqual(v.reason,'SELECTED_INPUTS_CHANGED')
    def test_new_explicit_request_can_legitimately_change_model(self):
        ctx=replace(self.s.context,request='explicit-new-scenario',model_version='synthetic-model-2')
        s=replace(self.s,context=ctx);m=replace(self.m,context=ctx,threshold=Q(750));b=snapshot_inputs(s,m)
        r=solve(s);a=derive_analytics(s,r,m)
        self.assertTrue(check_business_bundle(b,s,r,m,a,self.files(s,r,m,a)).accepted)
    def test_changed_principal_same_context_rejected_by_snapshot(self):
        s=replace(self.s,principal=Q(1200));r=solve(s);a=derive_analytics(s,r,self.m)
        self.assertFalse(self.verdict(self.files(s,r,self.m,a),spec=s,result=r,analytics=a).accepted)
    def test_text_and_json_from_different_models_rejected(self):
        other=replace(self.m,weights=tuple((w,Q(1,2)) for w,_ in self.m.weights))
        a=derive_analytics(self.s,self.r,other)
        docs=self.docs.copy();docs[FILES[1]]=render_calculation_json(self.s,self.r,other,a).encode()
        self.assertFalse(self.verdict(docs).accepted)
    def test_partial_root_cannot_claim_exact_task_done(self):
        self.assertFalse(self.verdict(result=solve(self.s,1)).accepted)
    def test_selected_null_when_no_legal_intersection(self):
        m=replace(self.m,legal_options=(Q(0),Q(1000)))
        b=snapshot_inputs(self.s,m);a=derive_analytics(self.s,self.r,m)
        self.assertIsNone(a.selected)
        docs=self.files(self.s,self.r,m,a)
        self.assertTrue(check_business_bundle(b,self.s,self.r,m,a,docs).accepted)
        self.assertIsNone(json.loads(docs[FILES[1]])['analytics']['selected'])
    def test_overpayment_uses_clipped_expectation_and_probability(self):
        s=replace(self.s,principal=Q(100));r=solve(s);m=replace(self.m,threshold=Q(0),legal_options=(Q(10),))
        b=snapshot_inputs(s,m);a=derive_analytics(s,r,m);docs=self.files(s,r,m,a)
        self.assertEqual(a.expected,Q(60));self.assertEqual(a.event_probability,Q(1))
        self.assertTrue(check_business_bundle(b,s,r,m,a,docs).accepted)
        obj=json.loads(docs[FILES[1]]);obj['analytics']['expected']='-20';docs[FILES[1]]=json.dumps(obj).encode()
        self.assertFalse(check_business_bundle(b,s,r,m,a,docs).accepted)
    def test_context_fields_not_duplicated(self):
        self.assertEqual(len([f for f in fields(ContextKey) if f.name=='model_version']),1)
        self.assertNotIn('approved_model_id',[f.name for f in fields(ContextKey)])
    def test_result_bytes_not_persistent_file_attestation(self):
        v=self.verdict();docs=self.docs.copy();docs[FILES[1]]=docs[FILES[1]].replace(b'"880"',b'"999"')
        self.assertTrue(v.accepted)
        self.assertFalse(self.verdict(docs).accepted)

if __name__=='__main__': unittest.main()
