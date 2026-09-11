import unittest,sys,importlib.util
from pathlib import Path
from unified.pipeline import all_fields_demo
from unified.taint import affected_closure,reusable
from unified.burdens import ScenarioAssessment
from test_v2_contract_and_models import S
class CrossDomainTests(unittest.TestCase):
    def test_each_domain_flows_to_conditional_projection(self):
        rows=all_fields_demo()
        self.assertEqual(len(rows),37)
        for r in rows:
            self.assertEqual(r['fact_promotions'],0)
            self.assertFalse(any(a['formal_admission'] for a in r['alternatives']))
            self.assertNotEqual(r['alternatives'][0]['assumptions'],r['alternatives'][1]['assumptions'])
    def test_exclusion_removes_indirect_dependents(self):
        deps={'extract':{'evidence'},'prob':{'extract'},'advice':{'prob'},'other':{'unrelated'}}
        self.assertEqual(affected_closure({'evidence'},deps),{'evidence','extract','prob','advice'})
    def test_dependency_cycle_terminates(self):
        self.assertEqual(affected_closure({'a'},{'a':{'b'},'b':{'a'}}),{'a','b'})
    def test_new_law_subject_invalidates_reuse(self):
        self.assertFalse(reusable('old','new','x',set(),{}))
    def test_hypothesis_requires_identity(self):
        with self.assertRaises(ValueError):ScenarioAssessment('','established')

class RosettaPatchTests(unittest.TestCase):
    def setUp(self):
        f=Path(__file__).parents[1]/'scripts/patch_rosetta.py'
        spec=importlib.util.spec_from_file_location('patch_rosetta',f);mod=importlib.util.module_from_spec(spec);spec.loader.exec_module(mod)
        self.patch=mod.transform
        self.original='''-- original header
import Mathlib.Data.Fintype.Basic
/-- Mapping status from claim_mapping.csv -/
inductive MappingStatus : Type
| CN_ONLY
/-- No total functor can exist: misleading claim -/
theorem no_total_functor :
    ¬ (∀ i : Fin 44, mappingStatus i.val ≠ .CN_ONLY) := by
  intro h
  have := h ⟨0, by decide⟩
  simp [mappingStatus] at this
'''
    def test_renames_without_changing_proposition(self):
        p=self.patch(self.original)
        self.assertIn('theorem sample_mapping_not_total :',p)
        self.assertIn('¬ (∀ i : Fin 44, mappingStatus i.val ≠ .CN_ONLY)',p)
        self.assertNotIn('theorem no_total_functor',p)
    def test_idempotent(self):
        p=self.patch(self.original);self.assertEqual(self.patch(p),p)
    def test_unrecognized_baseline_is_not_silently_rewritten(self):
        with self.assertRaises(ValueError):self.patch('other theorem')
