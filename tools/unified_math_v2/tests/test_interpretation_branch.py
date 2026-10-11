"""Downstream consumption of the T122/T123 interpretation layer by run_case.

The main chain (J.6.1) consumes the environment's declared interpretation
candidates through interpretation_ref.build_interp_layer and attaches the
resulting Γ-level branch layer to every selection branch; unadjudicated
same-rank conflicts surface as referral pending notes.  The independent
checker re-validates every attached layer from the raw candidates.
"""

from fractions import Fraction as Q
from unittest import TestCase

from theory.spec.canonical_v2.case import (
    CaseInput,
    Claim,
    ExactQuantity,
    FactRecord,
    FactStanding,
    LegalEnvironment,
    Polar,
    ProcessState,
    RunStatus,
    ScopedAtom,
)
from theory.spec.canonical_v2.kernel import (
    Judgment,
    Jurisdiction,
    JurisdictionRoute,
    NormState,
)
from unified.pipeline import run_case

from tools.full_math.implementation import interpretation_ref as R
from tools.full_math.implementation import interp_ref_check as K


def _atom(predicate, polar=Polar.POS, subject="D"):
    return ScopedAtom(case_id="case-1", subject=subject, issue="loan",
                      stage="trial", predicate=predicate, polar=polar)


def _state():
    return ProcessState(
        r=NormState(relations=()),
        environment_id="env-1",
        stages=(("loan-trial", "trial"),),
        events=(),
        target_day=10,
        as_of_day=10,
    )


def _case():
    return CaseInput(
        case_id="case-1",
        initial_state=_state(),
        parties=("C", "D"),
        issues=("loan",),
        claims=(Claim("c1", "C", "D", "loan", "money", "payment"),),
        defenses=(),
        fact_records=(
            FactRecord("f-contract", _atom("contract_signed"),
                       FactStanding.ADMITTED_POSITIVE, produced_at=1,
                       known_at=1),
        ),
        evidence_records=(),
        questions=(),
        quantities=(ExactQuantity(Q(100), "CNY", "principal", "contract"),),
    )


RULE_A = R.RuleAst(rule_id="R-1", premises=("contract_signed",),
                   conclusion="payment_due")
RULE_B = R.RuleAst(rule_id="R-2", premises=("usage_evidenced",),
                   conclusion="payment_due")
RULE_C = R.RuleAst(rule_id="R-3", premises=("unauth_premise",),
                   conclusion="payment_due")
INPUT_X = R.InterpInput(text_id="art7-text", context_ids=("mat-11",))
INPUT_Y = R.InterpInput(text_id="art7-text", context_ids=("mat-22",))


def _interp_cands():
    """Two sourced conflicting readings of the same provision (§3.1: 法律
    允许数个解释) plus one UNADOPTED candidate (no authority, its own rule
    R-3 so non-entry into the rule base is observable).  Adoptable
    candidates carry statutory authority via mk_candidate; the thin mk_*
    constructors build unadopted candidates only."""
    literal = R.mk_candidate(R.InterpMethod.LITERAL, "c1", INPUT_X, "art7",
                             "civil", R.InterpEffect.SELECT_READING, RULE_A,
                             "reason-1", "court-9")
    systematic = R.mk_candidate(R.InterpMethod.SYSTEMATIC, "c2", INPUT_Y,
                                "art7", "civil",
                                R.InterpEffect.SELECT_READING, RULE_B,
                                "reason-2", "court-9")
    unauth = R.mk_literal("c3", INPUT_Y, "art7", "civil",
                          R.InterpEffect.SELECT_READING, RULE_C, "reason-3")
    return literal, systematic, unauth


def _env(cands, priorities=()):
    return LegalEnvironment(
        environment_id="env-1",
        jurisdiction=Jurisdiction(route=JurisdictionRoute.MAINLAND),
        interpretation_candidates=tuple(cands),
        interpretation_priorities=tuple(priorities),
    )


class InterpretationBranchConsumptionTests(TestCase):
    def test_run_case_attaches_interp_layer(self):
        literal, systematic, _unauth = _interp_cands()
        env = _env([literal, systematic],
                   (R.PriorityPair("c1", "c2"),))
        run = run_case(_case(), env)
        self.assertIs(run.status, RunStatus.COMPLETE)
        self.assertTrue(run.branches)
        layer = run.branches[0].interp_layer
        self.assertEqual(layer.pool, ("c1", "c2"))
        # 具名优先收敛：采用集只留优位支（§3.1 profile）
        self.assertEqual(layer.resolved, ("c1",))
        # 规则库只收已采用解释的规则；未采用候选的规则不出现
        self.assertEqual(layer.rule_base, frozenset({RULE_A}))
        # Γ-level：同一层挂到每个 selection 分支
        self.assertTrue(
            all(b.interp_layer is layer for b in run.branches))

    def test_run_case_referral_note_on_unadjudicated_conflict(self):
        literal, systematic, _unauth = _interp_cands()
        env = _env([literal, systematic])  # 无具名优先边
        run = run_case(_case(), env)
        self.assertTrue(
            any("referral" in note for note in run.pending),
            run.pending)
        layer = run.branches[0].interp_layer
        self.assertEqual(layer.resolved, ("c1", "c2"))  # 不作选择，全保留
        self.assertIn(("c1", "c2"), layer.referral)

    def test_unadoptable_never_enters_layer(self):
        """T122 原反例经主链：无权限候选不进池、不进采用集、不进规则库。"""
        literal, systematic, unauth = _interp_cands()
        env = _env([literal, systematic, unauth])
        run = run_case(_case(), env)
        layer = run.branches[0].interp_layer
        self.assertNotIn("c3", layer.pool)
        self.assertNotIn("c3", layer.resolved)
        self.assertNotIn(unauth.rule, layer.rule_base)
        self.assertTrue(
            all(b.branch_id != "c3" for b in layer.branches))

    def test_attached_layer_passes_independent_checker(self):
        """下游消费差分：主链挂接的解释层被独立 checker 从原始候选重算认可。"""
        literal, systematic, unauth = _interp_cands()
        env = _env([literal, systematic, unauth],
                   (R.PriorityPair("c1", "c2"),))
        run = run_case(_case(), env)
        layer = run.branches[0].interp_layer
        report = K.check_interp_layer(
            [literal, systematic, unauth], (R.PriorityPair("c1", "c2"),),
            layer)
        self.assertTrue(report.ok, report.reasons)
        # T123 隔离门在消费记录上：跨支推导被拒
        bx = next(b for b in layer.branches if b.branch_id == "c1")
        by = next(b for b in layer.branches if b.branch_id == "c2")
        own = R.BranchDerivation("d-own", "payment_due",
                                 frozenset({"mat-11"}))
        cross = R.BranchDerivation("d-cross", "payment_due",
                                   frozenset({"mat-22"}))
        self.assertTrue(R.derivation_ok(bx, own))
        self.assertFalse(R.derivation_ok(bx, cross))
        gate = K.check_cross_branch_rejection(bx, by, cross)
        self.assertTrue(gate.ok, gate.reasons)

    def test_interp_failure_is_technical_failed_not_a_verdict(self):
        """坏候选（重复 id）使主链进入 FAILED——技术失败不是法律结论。"""
        literal, systematic, _unauth = _interp_cands()
        dup = R.mk_candidate(R.InterpMethod.HISTORICAL, "c1", INPUT_Y,
                             "art7", "civil", R.InterpEffect.SELECT_READING,
                             RULE_B, "reason-dup", "court-9")
        env = _env([literal, dup])
        run = run_case(_case(), env)
        self.assertIs(run.status, RunStatus.FAILED)
        self.assertTrue(run.failures)
