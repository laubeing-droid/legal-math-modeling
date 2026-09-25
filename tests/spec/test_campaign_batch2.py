"""Campaign tests, batch 2: time, proof, and claim-structure contracts
(P-012, P-029, P-034/035/038, P-042, P-047..P-052, P-094/095)."""

from __future__ import annotations

import pytest

from theory.spec.time_contracts import (
    AnchorRule,
    CommencementCell,
    LimitationCause,
    LimitationClock,
    apply_limitation_cause,
    days_elapsed,
    lookup_commencement,
    select_anchor,
)
from theory.spec.proof_contracts import (
    AgencyKind,
    AnspruchBasis,
    BindingKind,
    ButForCase,
    CompetitionRelation,
    ElementTrace,
    ExemptionGround,
    EvidenceWeight,
    ExclusionKind,
    FilingWindow,
    FreeEvaluationBoundary,
    NormBinding,
    but_for_test,
    claim_available,
    effect_attribution,
    evidence_admissible_on_time,
    excluded,
    exempts,
    mapping_complete,
    secondary_attaches,
)

# --- P-012 时效动因 ---


def test_p012_limitation_causes() -> None:
    started = apply_limitation_cause(
        LimitationClock(running=False, elapsed_days=0), LimitationCause.COMMENCE, day=10
    )
    assert (started.running, started.commenced_day, started.elapsed_days) == (True, 10, 0)
    suspended = apply_limitation_cause(started, LimitationCause.SUSPEND, day=40)
    assert suspended.running is False
    interrupted = apply_limitation_cause(suspended, LimitationCause.INTERRUPT, day=60)
    assert (interrupted.running, interrupted.commenced_day, interrupted.elapsed_days) == (True, 60, 0)


def test_p012_commence_is_idempotent_guard() -> None:
    once = apply_limitation_cause(
        LimitationClock(running=False, elapsed_days=0), LimitationCause.COMMENCE, day=1
    )
    again = apply_limitation_cause(once, LimitationCause.COMMENCE, day=5)
    assert again.commenced_day == 1


# --- P-094 期限锚点 ---


def test_p094_anchor_selection_fail_closed() -> None:
    rules = (AnchorRule(event_key="delivery"), AnchorRule(event_key="invoice"))
    assert select_anchor(rules, {"invoice": 30, "delivery": 10}) == 10
    assert select_anchor(rules, {}) is None
    assert days_elapsed(None, 100) is None
    assert days_elapsed(10, 100) == 90


# --- P-095 起算矩阵 ---


def test_p095_matrix_empty_cell_unknown() -> None:
    matrix = (CommencementCell(period_kind="limitation", event_kind="knowledge", rule_id="R1"),)
    assert lookup_commencement(matrix, "limitation", "knowledge") == "R1"
    assert lookup_commencement(matrix, "limitation", "hurricane") is None


# --- P-029 Binding 二分 ---


def test_p029_secondary_attaches_to_violated_primary() -> None:
    sec = NormBinding(kind=BindingKind.SECONDARY, norm_id="n2", attaches_to="n1")
    pri = NormBinding(kind=BindingKind.PRIMARY, norm_id="n1")
    assert secondary_attaches("n1", sec)
    assert not secondary_attaches(None, sec)
    assert not secondary_attaches("n1", pri)


# --- P-034 请求权 ---


def test_p034_claim_requires_complete_basis() -> None:
    bases = (
        AnspruchBasis(
            basis_id="contract_577",
            required_elements=frozenset({"contract", "breach", "damage"}),
        ),
    )
    assert (
        claim_available(bases, "contract_577", frozenset({"contract", "breach", "damage"}))
        is True
    )
    assert claim_available(bases, "contract_577", frozenset({"contract"})) is False
    assert claim_available(bases, "tort_1165", frozenset()) is None  # 未登记基础=UNKNOWN


# --- P-035 代理三分 ---


def test_p035_agency_trichotomy() -> None:
    assert effect_attribution(AgencyKind.AGENCY, within_scope=False, ratified=False) == "PRINCIPAL"
    assert (
        effect_attribution(AgencyKind.REPRESENTATION, within_scope=True, ratified=False)
        == "PRINCIPAL_IF_IN_SCOPE"
    )
    assert effect_attribution(AgencyKind.REPRESENTATION, within_scope=False, ratified=False) == "NONE"
    assert effect_attribution(AgencyKind.IMPERSONATION, within_scope=False, ratified=False) == "NONE"
    assert effect_attribution(AgencyKind.IMPERSONATION, within_scope=False, ratified=True) == "PRINCIPAL"


# --- P-038 竞争关系 ---


def test_p038_competition_requires_all_three() -> None:
    assert CompetitionRelation(True, True, True).established
    assert not CompetitionRelation(True, True, False).established


# --- P-042 证明力分级 ---


def test_p042_weakest_factor_caps_grade() -> None:
    assert EvidenceWeight(reliability=5, integrity=3, authenticity=4).grade == 3


# --- P-047 but-for ---


def test_p047_butfor_needs_both_directions() -> None:
    assert but_for_test(ButForCase(occurred_outcome=True, non_occurred_outcome=False)) is True
    assert but_for_test(ButForCase(occurred_outcome=True, non_occurred_outcome=True)) is False
    assert but_for_test(ButForCase(occurred_outcome=None, non_occurred_outcome=False)) is None


# --- P-048 免责 ---


def test_p048_exemption_needs_own_elements() -> None:
    ground = ExemptionGround(
        ground_id="force_majeure",
        required_elements=frozenset({"unforeseeable", "unavoidable"}),
    )
    assert exempts(ground, frozenset({"unforeseeable", "unavoidable"}))
    assert not exempts(ground, frozenset({"unforeseeable"}))


# --- P-049 举证时限 ---


def test_p049_late_evidence_needs_good_cause() -> None:
    assert evidence_admissible_on_time(10, FilingWindow(deadline_day=10))
    assert not evidence_admissible_on_time(11, FilingWindow(deadline_day=10))
    assert evidence_admissible_on_time(11, FilingWindow(deadline_day=10, extended_for_good_cause=True))


# --- P-050 非法证据排除 ---


def test_p050_any_listed_illegality_excludes() -> None:
    assert excluded(frozenset({ExclusionKind.ILLEGALLY_OBTAINED}))
    assert not excluded(frozenset())


# --- P-051 心证边界 ---


def test_p051_boundary_is_positively_recorded() -> None:
    b = FreeEvaluationBoundary(supplied_inputs=frozenset({"admissible_evidence", "provenance"}))
    assert b.boundary_statement() == "KERNEL_SUPPLIES_INPUTS_ONLY;EVALUATION_ACT_OUTSIDE_KERNEL=UNKNOWN"


# --- P-052 三元映射 ---


def test_p052_mapping_incomplete_when_trace_missing() -> None:
    traces = (
        ElementTrace(element="breach", facts=frozenset({"f1"}), evidence=frozenset({"e1"})),
        ElementTrace(element="damage", facts=frozenset(), evidence=frozenset({"e2"})),
    )
    assert not mapping_complete(frozenset({"breach", "damage"}), traces)


def test_p052_mapping_complete_all_traced() -> None:
    traces = (
        ElementTrace(element="breach", facts=frozenset({"f1"}), evidence=frozenset({"e1"})),
        ElementTrace(element="damage", facts=frozenset({"f2"}), evidence=frozenset({"e2"})),
    )
    assert mapping_complete(frozenset({"breach", "damage"}), traces)
