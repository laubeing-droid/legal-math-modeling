"""Campaign tests, batch 3: argumentation, negotiation, computation, and
delivery contracts (P-057..P-066, P-068/070, P-073..P-087, P-089,
P-096..P-103, P-105..P-107, P-114, P-117, P-121/122/124..P-132)."""

from __future__ import annotations

from decimal import Decimal

import pytest

from theory.spec.argument_contracts import (
    AmbiguityProbe,
    AnalogyProbe,
    DamageKind,
    GapSignalKind,
    InterpretationMethod,
    LiabilityForm,
    LiabilityFormKind,
    LawmakingSignals,
    NormKind,
    ReadingAttack,
    ToulminArgument,
    ValuePreorder,
    ambiguity_state,
    analogous_application,
    attack_admissible,
    classify_damage,
    evaluate_isolated,
    gap_signalled,
    lawmaking_flagged,
    norm_contribution,
    value_relation,
)
from theory.spec.negotiation_contracts import (
    AppealDecision,
    ContingencyTerms,
    DualTrackParams,
    EthicsConstraint,
    EvidenceItemEVPI,
    FeeMode,
    LegalityVerdict,
    MediationInputs,
    RetrievalDutyRecord,
    SameCaseObligation,
    SettlementDecision,
    SuitStrategy,
    acquisition_order,
    assess_legality,
    fee_quote,
    plea_stage_advance,
    tactic_permitted,
)
from theory.spec.computation_contracts import (
    ContractState,
    DebtItem,
    InterestSegment,
    SimilarityToolOutput,
    TaxBracket,
    allocate_payment,
    compute_damage_item,
    deduction_implies_probability_one,
    delay_interest,
    progressive_tax,
    reduce_penalty,
    segmented_interest,
    transition_contract_state,
)
from theory.spec.delivery_contracts import (
    AnonymizationBoundary,
    CitationCheck,
    ConceptUse,
    DisclosureRecord,
    DueProcessElement,
    HallucinationPattern,
    HumanGate,
    LifecycleState,
    LitigationSubject,
    ProceduralDisposition,
    Proposal,
    ScriptAsset,
    VersionDiscipline,
    action_requires_gate,
    admit_proposal,
    block_hallucination,
    disposition_sequence_valid,
    due_process_satisfied,
    effect_log_apply,
    lifecycle_transition_valid,
    smuggling_blocked,
)

D = Decimal

# --- P-057 类比 ---


def test_p057_analogy_and_distinguishing() -> None:
    assert analogous_application(AnalogyProbe(True, True, False)) is True
    assert analogous_application(AnalogyProbe(True, True, True)) is False
    assert analogous_application(AnalogyProbe(True, False, False)) is False


# --- P-058 图尔敏 ---


def test_p058_toulmin_six_slots() -> None:
    full = ToulminArgument(
        claim="contract formed",
        ground=frozenset({"offer", "acceptance"}),
        warrant="mirror-image rule",
        backing=frozenset({" statute 483"}),
        qualifier="presumably",
        rebuttals=frozenset(),
    )
    assert full.well_formed()
    thin = ToulminArgument(
        claim="", ground=frozenset({"g"}), warrant="w",
        backing=frozenset({"b"}), qualifier="q", rebuttals=frozenset(),
    )
    assert not thin.well_formed()


# --- P-060 解释构造子 ---


def test_p060_isolated_branches() -> None:
    readings = {
        InterpretationMethod.LITERAL: "narrow",
        InterpretationMethod.PURPOSIVE: "broad",
    }
    out = evaluate_isolated(readings)
    assert out == readings and len(out) == 2


# --- P-061 解释之争 ---


def test_p061_pinned_reading_immune_to_lower_precedence() -> None:
    attack = ReadingAttack(attacker="scholar", target="guiding_case_reading", attacker_precedence=1)
    assert attack_admissible(attack, target_pinned=True, target_precedence=3) is False
    assert attack_admissible(attack, target_pinned=False, target_precedence=3) is True
    stronger = ReadingAttack(attacker="spc", target="x", attacker_precedence=5)
    assert attack_admissible(stronger, target_pinned=True, target_precedence=3) is True


# --- P-062 歧义检测 ---


def test_p062_ambiguity_needs_context() -> None:
    assert ambiguity_state(
        AmbiguityProbe(term="deposit", candidate_senses=frozenset({"s1", "s2"}), context_provided=False)
    ) == "AMBIGUOUS"
    assert ambiguity_state(
        AmbiguityProbe(term="deposit", candidate_senses=frozenset({"s1", "s2"}), context_provided=True)
    ) == "RESOLVED"


# --- P-063 规则原则 ---


def test_p063_rule_all_or_nothing_principle_weighed() -> None:
    assert norm_contribution(NormKind.RULE, True, None) == "SATISFIED"
    assert norm_contribution(NormKind.RULE, False, None) == "VIOLATED"
    assert norm_contribution(NormKind.PRINCIPLE, True, 3) == "WEIGHED"
    assert norm_contribution(NormKind.PRINCIPLE, True, None) == "NO_WEIGHT"


# --- P-064 预序 ---


def test_p064_incomparability_is_legal() -> None:
    pre = ValuePreorder(ordered_pairs=frozenset({("a", "b")}))
    assert value_relation(pre, "a", "b") == "LE"
    assert value_relation(pre, "b", "a") == "GE"
    assert value_relation(pre, "c", "d") == "INCOMPARABLE"


# --- P-065/066 造法与漏洞 ---


def test_p065_lawmaking_detection() -> None:
    assert lawmaking_flagged(LawmakingSignals(True, True, True))
    assert not lawmaking_flagged(LawmakingSignals(True, False, True))


def test_p066_gap_signals() -> None:
    assert gap_signalled(frozenset({GapSignalKind.RULE_CONFLICT}))
    assert not gap_signalled(frozenset())


# --- P-068/070 责任形态与损害分型 ---


def test_p068_liability_forms() -> None:
    assert LiabilityForm(LiabilityFormKind.JOINT).well_formed()
    assert not LiabilityForm(LiabilityFormKind.SEVERAL).well_formed()
    assert LiabilityForm(LiabilityFormKind.SEVERAL, shares=(3, 7)).well_formed()


def test_p070_damage_classification() -> None:
    assert classify_damage("m", "REPAIR_COST") is DamageKind.ACTUAL
    assert classify_damage("m", "LOST_PROFIT") is DamageKind.EXPECTATION
    assert classify_damage("m", "MENTAL_DISTRESS") is DamageKind.SPIRITUAL
    assert classify_damage("m", "KARMA") is None


# --- P-073 双轨 ---


def test_p073_dual_tracks_merge_at_declaration() -> None:
    params = DualTrackParams(responsibility_band=(24, 36), prevention_band=(6, 12))
    lo, hi = params.merged_declaration()
    assert lo == 24 and hi == 36


# --- P-074 合法性 ---


def test_p074_legality_grades() -> None:
    assert assess_legality(prohibited=True, unlawful=None) is LegalityVerdict.ILLEGAL
    assert assess_legality(prohibited=False, unlawful=None) is LegalityVerdict.VIOLATION
    assert assess_legality(prohibited=False, unlawful=False) is LegalityVerdict.LEGAL
    assert assess_legality(prohibited=False, unlawful=True) is LegalityVerdict.VIOLATION


# --- P-078/079 调解与和解 ---


def test_p078_mediation_zone() -> None:
    inputs = MediationInputs(
        neutral_assessment_low=80.0,
        neutral_assessment_high=120.0,
        plaintiff_reservation=90.0,
        defendant_reservation=110.0,
    )
    assert inputs.zone() == (90.0, 110.0)
    broken = MediationInputs(80.0, 100.0, 120.0, 110.0)
    assert broken.zone() is None


def test_p079_settlement_ev() -> None:
    yes = SettlementDecision(ev_settle=70.0, ev_litigate=80.0, risk_premium=15.0)
    assert yes.accept_settlement()
    no = SettlementDecision(ev_settle=60.0, ev_litigate=80.0, risk_premium=15.0)
    assert not no.accept_settlement()


# --- P-080 认罪认罚 ---


def test_p080_plea_stages_in_order() -> None:
    assert plea_stage_advance(()) == "VOLUNTARINESS"
    assert plea_stage_advance(("VOLUNTARINESS", "FACT_ADMISSION")) == "SENTENCE_PROPOSAL"
    assert plea_stage_advance(("FACT_ADMISSION",)) is None  # 跳步不可能
    assert plea_stage_advance(tuple(_ for _ in () )) == "VOLUNTARINESS"


# --- P-081 伦理约束 ---


def test_p081_any_violation_voids() -> None:
    constraints = frozenset(EthicsConstraint)
    assert tactic_permitted(constraints, violated=frozenset())
    assert not tactic_permitted(constraints, violated=frozenset({EthicsConstraint.NO_FRAUD}))


# --- P-082/083 策略 ---


def test_p082_preservation_needs_ground() -> None:
    ok = SuitStrategy("now", "tort", "basic", preservation_needed=True, preservation_ground=True)
    bad = SuitStrategy("now", "tort", "basic", preservation_needed=True, preservation_ground=False)
    assert ok.feasible() and not bad.feasible()


def test_p083_evpi_ordering() -> None:
    items = (
        EvidenceItemEVPI("a", 5.0),
        EvidenceItemEVPI("b", 9.0),
        EvidenceItemEVPI("c", 7.0),
    )
    assert acquisition_order(items) == ("b", "c", "a")


# --- P-084/085/086 上诉/定价/风险代理 ---


def test_p084_appeal_ev() -> None:
    assert AppealDecision(0.5, 100.0, 40.0).appeal_worthwhile()
    assert not AppealDecision(0.3, 100.0, 40.0).appeal_worthwhile()
    with pytest.raises(ValueError):
        AppealDecision(1.5, 100.0, 40.0).appeal_worthwhile()


def test_p085_fee_needs_disclosure() -> None:
    assert fee_quote(FeeMode.HOURLY, disclosed=True) == "QUOTE::HOURLY"
    assert fee_quote(FeeMode.CONTINGENCY, disclosed=False) is None


def test_p086_contingency_capped() -> None:
    terms = ContingencyTerms(win_rate=0.6, fee_rate=D("0.2"), cap=D("10"))
    assert terms.expected_fee(D("100")) == D("10")  # 0.6*0.2*100=12 -> cap 10
    assert terms.expected_fee(D("50")) == D("6")


# --- P-087/089 同案同判与检索义务 ---


def test_p087_shall_follow_duty() -> None:
    assert SameCaseObligation("gc_24", distinguishing_reason_recorded=False).discharge() == "SHOULD_FOLLOW"
    assert SameCaseObligation("gc_24", distinguishing_reason_recorded=True).discharge() == "DISTINGUISHED_WITH_REASON"


def test_p089_retrieval_duty() -> None:
    assert RetrievalDutyRecord(True, True).compliant()
    assert not RetrievalDutyRecord(True, False).compliant()
    assert not RetrievalDutyRecord(False, False).compliant()


# --- P-096 利息分段 ---


def test_p096_segmented_refinement() -> None:
    principal = D("10000")
    segments = (InterestSegment(0, 180, D("0.0001")), InterestSegment(180, 365, D("0.0002")))
    whole = segmented_interest(principal, segments)
    per_segment = segmented_interest(principal, segments[:1]) + segmented_interest(principal, segments[1:])
    assert whole == per_segment == D("550")


# --- P-097 抵充 ---


def test_p097_allocation_conservation() -> None:
    debts = (DebtItem("interest", D("30"), order=1), DebtItem("principal", D("100"), order=2))
    allocation, remainder = allocate_payment(D("50"), debts)
    assert allocation == {"interest": D("30"), "principal": D("20")}
    assert remainder == D("0")
    _, short = allocate_payment(D("10"), debts)
    assert short == D("0")


# --- P-098 酌减 ---


def test_p098_penalty_reduction_band() -> None:
    assert reduce_penalty(D("100"), (D("10"), D("30")), excessive=True) == D("30")
    assert reduce_penalty(D("5"), (D("10"), D("30")), excessive=True) == D("10")
    assert reduce_penalty(D("20"), (D("10"), D("30")), excessive=False) == D("20")


# --- P-099 税档 ---


def test_p099_progressive_brackets() -> None:
    brackets = (TaxBracket(up_to=36, rate=D("0.03")), TaxBracket(up_to=144, rate=D("0.1")), TaxBracket(up_to=None, rate=D("0.25")))
    assert progressive_tax(30, brackets) == D("0.9")
    assert progressive_tax(60, brackets) == D("3.48")  # 36*0.03 + 24*0.1


# --- P-100/102 损害与执行 ---


def test_p100_formula_registry() -> None:
    registry = {"medical": D("1.0")}
    assert compute_damage_item("medical", registry, {"base": D("123")}) == D("123")
    assert compute_damage_item("karma", registry, {"base": D("1")}) is None


def test_p102_delay_interest() -> None:
    assert delay_interest(D("1000"), D("0.001"), 10) == D("10")
    with pytest.raises(ValueError):
        delay_interest(D("1"), D("0.1"), -1)


# --- P-103 智能合约 ---


def test_p103_consent_locked_transitions() -> None:
    assert transition_contract_state(ContractState.DRAFT, ContractState.LOCKED, consent_recorded=True) is ContractState.LOCKED
    assert transition_contract_state(ContractState.DRAFT, ContractState.LOCKED, consent_recorded=False) is ContractState.DRAFT
    assert transition_contract_state(ContractState.DRAFT, ContractState.TERMINATED, consent_recorded=True) is ContractState.DRAFT


# --- P-114 逻辑概率桥 ---


def test_p114_one_way_bridge() -> None:
    assert deduction_implies_probability_one() == "DEDUCTION=>P1;P1=~>DEDUCTION"


# --- P-117 文本相似 ---


def test_p117_similarity_never_structural() -> None:
    assert SimilarityToolOutput(0.99).grade() == "CANDIDATE_ONLY"
    assert SimilarityToolOutput(0.99, asserted_structural_equivalence=True).grade() == "INVALID_OVERREACH"


# --- P-105/106 程序与标的 ---


def test_p105_disposition_sequences() -> None:
    ok = (ProceduralDisposition.FILE, ProceduralDisposition.ANSWER, ProceduralDisposition.CROSS_EXAMINE)
    assert disposition_sequence_valid(ok)
    bad = (ProceduralDisposition.FILE, ProceduralDisposition.TERMINATE)
    assert not disposition_sequence_valid(bad)


def test_p106_subject_identity() -> None:
    a = LitigationSubject("c1", "contract_breach", ("plaintiff", "defendant"))
    b = LitigationSubject("c2", "contract_breach", ("defendant", "plaintiff"))
    c = LitigationSubject("c3", "tort", ("plaintiff", "defendant"))
    assert a.same_subject_as(b)
    assert not a.same_subject_as(c)


# --- P-107/121/122/124 交付族 ---


def test_p107_script_masquerade_rejected() -> None:
    assert ScriptAsset("s1", contains_legal_fact_assertions=False).receipt_verdict() == "DELIVERY_ASSET_OK"
    assert ScriptAsset("s2", contains_legal_fact_assertions=True).receipt_verdict() == "REJECTED_MASQUERADE"


def test_p121_proposal_gated() -> None:
    p = Proposal("p1", source="LLM")
    assert p.grade() == "CANDIDATE_ONLY"
    assert admit_proposal(True, p).grade() == "ADMITTED_CANDIDATE"
    assert admit_proposal(False, p).grade() == "CANDIDATE_ONLY"


def test_p122_version_binding() -> None:
    v = VersionDiscipline("src@1", "model@2", "data@3")
    assert v.bound() == "src@1|model@2|data@3"


def test_p124_disclosure() -> None:
    assert DisclosureRecord("corpus@9", deletions_disclosed=True).compliant()
    assert not DisclosureRecord("corpus@9", deletions_disclosed=False).compliant()


# --- P-125..P-128 压制件 ---


def test_p125_hallucination_blocked() -> None:
    assert block_hallucination(frozenset({HallucinationPattern.FABRICATED_DOCKET}))
    assert not block_hallucination(frozenset())


def test_p126_smuggling_blocked() -> None:
    use = ConceptUse("felony_murder", home_jurisdiction="US", adapted=False)
    assert smuggling_blocked(use, "CN") is True
    assert smuggling_blocked(ConceptUse("felony_murder", "US", adapted=True), "CN") is False
    assert smuggling_blocked(ConceptUse("诉讼时效", "CN", adapted=False), "CN") is False


def test_p127_citation_verbatim() -> None:
    assert CitationCheck("第X条", "前文 第X条 后文").verbatim_hit()
    assert not CitationCheck("第Y条", "第X条").verbatim_hit()


def test_p128_due_process_mapping() -> None:
    full = frozenset(DueProcessElement)
    assert due_process_satisfied(full)
    assert not due_process_satisfied(frozenset({DueProcessElement.NOTICE}))


# --- P-129..P-132 工作台件 ---


def test_p129_anonymization_boundary() -> None:
    assert AnonymizationBoundary(anonymized=True, reidentification_tested=True).within_boundary()
    assert not AnonymizationBoundary(anonymized=True, reidentification_tested=False).within_boundary()
    assert not AnonymizationBoundary(anonymized=False, reidentification_tested=True).within_boundary()


def test_p130_lifecycle_edges() -> None:
    assert lifecycle_transition_valid(LifecycleState.INTAKE, LifecycleState.ACTIVE)
    assert lifecycle_transition_valid(LifecycleState.SUSPENDED, LifecycleState.ACTIVE)
    assert not lifecycle_transition_valid(LifecycleState.INTAKE, LifecycleState.ARCHIVED)


def test_p131_idempotent_effect_log() -> None:
    log = effect_log_apply({}, "cmd1", "effect_a")
    twice = effect_log_apply(log, "cmd1", "effect_a")
    assert twice == {"cmd1": "effect_a"}
    grown = effect_log_apply(twice, "cmd2", "effect_b")
    assert grown == {"cmd1": "effect_a", "cmd2": "effect_b"}


def test_p132_human_gates() -> None:
    assert action_requires_gate("FILE_DOCUMENT", HumanGate.SIGNATURE)
    assert action_requires_gate("ISSUE_OPINION", HumanGate.LAWYER_APPROVAL)
    assert not action_requires_gate("FILE_DOCUMENT", HumanGate.FINAL_REVIEW)
