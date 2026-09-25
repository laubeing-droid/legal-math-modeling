"""ON-01..ON-10 gate tests: Hohfeld involutions, contract-level subsumption
completeness, chain reuse, presumption transfer, explicit rewrites, context
parameters, characterization, subject-identity effect, fact typing, and
attribution principles."""

from __future__ import annotations

import pytest

from theory.spec.ontology_v3 import (
    CORRELATIVE,
    OPPOSITE,
    AttributionParameters,
    AttributionPrinciple,
    Characterization,
    ClaimBasisChain,
    ClaimBasisNode,
    ContextInterval,
    ContextParameter,
    FaultGrade,
    HohfeldConcept,
    JudgmentEffect,
    LegalFactType,
    RewriteKind,
    RewriteRule,
    RebuttablePresumption,
    SubjectMatter,
    SubsumptionSpec,
    TypedLegalFact,
    apply_rebuttable_presumption,
    characterize,
    evaluate_claim_basis_chain,
    judgment_effect,
    rewrite_fact,
    subsume,
)


# --- ON-01 ---


def test_hohfeld_opposite_is_involutive() -> None:
    for concept in HohfeldConcept:
        assert OPPOSITE[OPPOSITE[concept]] is concept


def test_hohfeld_correlative_is_involutive() -> None:
    for concept in HohfeldConcept:
        assert CORRELATIVE[CORRELATIVE[concept]] is concept


def test_hohfeld_maps_never_fix_a_concept() -> None:
    for concept in HohfeldConcept:
        assert OPPOSITE[concept] is not concept
        assert CORRELATIVE[concept] is not concept
    assert len(HohfeldConcept) == 8


# --- ON-02 ---


def test_subsumption_complete_iff_no_missing_elements() -> None:
    spec = SubsumptionSpec(required_elements=frozenset({"a", "b", "c"}))
    complete = subsume(facts=frozenset({"a", "b", "c", "extra"}), spec=spec)
    partial = subsume(facts=frozenset({"a"}), spec=spec)
    assert complete.complete is True and complete.missing == frozenset()
    assert partial.complete is False and partial.missing == frozenset({"b", "c"})


# --- ON-03 ---


def test_claim_basis_reuses_subsumption() -> None:
    chain = ClaimBasisChain(
        nodes=(
            ClaimBasisNode("basis_contract", frozenset({"contract", "breach"})),
            ClaimBasisNode("basis_tort", frozenset({"tort", "damage"})),
        )
    )
    results = evaluate_claim_basis_chain(
        facts=frozenset({"contract", "breach"}), chain=chain
    )
    assert len(results) == 2
    assert results[0].complete is True
    assert results[1].complete is False
    assert results[0].missing == frozenset()  # same SubsumptionResult type


# --- ON-04 ---


def test_rebuttable_presumption_can_be_rebutted() -> None:
    rule = RebuttablePresumption(
        trigger="long_possession",
        presumed_fact="good_faith_ownership",
        rebuttal_fact="stolen_goods_proven",
    )
    started = apply_rebuttable_presumption(
        facts=frozenset({"long_possession"}), rule=rule
    )
    rebutted = apply_rebuttable_presumption(
        facts=frozenset({"long_possession", "stolen_goods_proven"}), rule=rule
    )
    idle = apply_rebuttable_presumption(facts=frozenset({"other"}), rule=rule)
    assert started.presumed and started.shifted_fact == "good_faith_ownership"
    assert rebutted.rebutted and not rebutted.presumed
    assert not idle.presumed and not idle.rebutted  # trigger absent: no start


# --- ON-05 ---


def test_service_fiction_rewrites_explicitly() -> None:
    rule = RewriteRule(
        kind=RewriteKind.SERVICE_FICTION,
        source_fact="document_dispatched",
        rewritten_fact="deemed_served",
    )
    out = rewrite_fact(facts=frozenset({"document_dispatched", "case_open"}), rule=rule)
    assert out == frozenset({"deemed_served", "case_open"})
    untouched = rewrite_fact(facts=frozenset({"case_open"}), rule=rule)
    assert untouched == frozenset({"case_open"})


def test_death_fiction_rewrites_explicitly() -> None:
    rule = RewriteRule(
        kind=RewriteKind.DEATH_FICTION,
        source_fact="missing_person_4_years",
        rewritten_fact="presumed_dead",
    )
    out = rewrite_fact(facts=frozenset({"missing_person_4_years"}), rule=rule)
    assert out == frozenset({"presumed_dead"})


# --- ON-06 ---


def test_context_interval_rejects_reverse_bounds() -> None:
    ContextInterval(lower=0.2, upper=0.8)
    with pytest.raises(ValueError):
        ContextInterval(lower=0.8, upper=0.2)
    with pytest.raises(ValueError):
        ContextParameter(context_key=" ", penumbra=ContextInterval(0.0, 1.0))


# --- ON-07 ---


def test_characterization_requires_context() -> None:
    ctx = ContextParameter(
        context_key="consumer_vs_merchant", penumbra=ContextInterval(0.3, 0.6)
    )
    c = characterize(source_id="conduct_17", type_key="unfair_conduct", context=ctx)
    assert c.context is ctx
    with pytest.raises(ValueError):  # empty context key cannot sneak a default
        characterize(
            source_id="x",
            type_key="t",
            context=ContextParameter(context_key="", penumbra=ContextInterval(0, 1)),
        )


# --- ON-08 ---


def test_judgment_effect_checks_subject_identity() -> None:
    same = judgment_effect(
        former=SubjectMatter("claim::2024_118"),
        latter=SubjectMatter("claim::2024_118"),
        enforceable=True,
    )
    diff = judgment_effect(
        former=SubjectMatter("claim::2024_118"),
        latter=SubjectMatter("claim::2025_002"),
        enforceable=True,
    )
    assert same.res_judicata and same.same_subject_matter and same.enforceable
    assert not diff.res_judicata and not diff.same_subject_matter


# --- ON-09 ---


def test_legal_fact_event_and_action_are_distinct() -> None:
    event = TypedLegalFact(fact_id="storm_hit", fact_type=LegalFactType.EVENT)
    action = TypedLegalFact(fact_id="signed_contract", fact_type=LegalFactType.ACTION)
    assert event.fact_type is not action.fact_type
    assert len(LegalFactType) == 2


# --- ON-10 ---


def test_attribution_principles_are_explicit() -> None:
    assert {p.value for p in AttributionPrinciple} == {"FAULT", "NO_FAULT", "EQUITY"}
    fault = AttributionParameters(
        principle=AttributionPrinciple.FAULT, fault_grade=FaultGrade(level=2)
    )
    no_fault = AttributionParameters(principle=AttributionPrinciple.NO_FAULT, fault_grade=None)
    assert fault.fault_grade.level == 2
    assert no_fault.fault_grade is None
    with pytest.raises(ValueError):  # EQUITY never masquerades as fault
        AttributionParameters(
            principle=AttributionPrinciple.EQUITY, fault_grade=FaultGrade(1)
        )
