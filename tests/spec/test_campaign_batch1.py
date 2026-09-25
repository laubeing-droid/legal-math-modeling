"""Campaign tests, batch 1: source-layer and meta-concept contracts
(P-002/003/009/010, P-014/015/018..024)."""

from __future__ import annotations

import pytest

from theory.spec.source_contracts import (
    CauseOfActionRoute,
    HierarchyRank,
    JurisdictionRule,
    JurisdictionRuleKind,
    NormProvision,
    PrecedentBinding,
    PublicPolicyOverride,
    SourceKind,
    TransitionClause,
    apply_override,
    apply_transition,
    binding_effect,
    classify_source,
    renvoi_resolves,
    resolve_conflict,
    route_cause_of_action,
    route_jurisdiction,
    select_applicable_law,
)
from theory.spec.concept_meta import (
    ConceptAsDataset,
    ConceptRecord,
    ConceptVersionEntry,
    InfoPath,
    LegalTermBinding,
    PersonalInfo,
    TermTranslation,
    anonymize,
    canonical_term,
    concepts_identical,
    processing_requires_triple_consent,
    register_concept_version,
    translation_preserves_meaning,
)


# --- P-014 法源类型 ---


def test_p014_source_typology_grades_admission() -> None:
    assert classify_source("STATUTE").admission_grade == "BINDING"
    assert classify_source("GUIDING_CASE").admission_grade == "SHALL_REFER"
    assert classify_source("DOCTRINE").admission_grade == "REFERENCE_ONLY"
    with pytest.raises(ValueError):
        classify_source("DIVINE_REVELATION")


# --- P-015 效力位阶 ---


def _p(pid: str, rank: HierarchyRank, day: int, special: bool = False) -> NormProvision:
    return NormProvision(provision_id=pid, rank=rank, enacted_day=day, special=special)


def test_p015_lex_superior_and_posterior() -> None:
    assert resolve_conflict(_p("a", HierarchyRank.STATUTE, 100), _p("b", HierarchyRank.LOCAL_REGULATION, 200)) == "a"
    assert resolve_conflict(_p("new", HierarchyRank.DEPARTMENTAL_RULE, 200), _p("old", HierarchyRank.DEPARTMENTAL_RULE, 100)) == "new"


def test_p015_special_vs_new_general_is_unknown() -> None:
    old_special = _p("os", HierarchyRank.STATUTE, 100, special=True)
    new_general = _p("ng", HierarchyRank.STATUTE, 200)
    assert resolve_conflict(new_general, old_special) is None


# --- P-018 版本衔接 ---


def test_p018_transition_fires_only_on_trigger() -> None:
    clause = TransitionClause(from_version="v2010", to_version="v2021", trigger_fact="conduct_after_2021")
    assert apply_transition("v2010", clause, frozenset({"conduct_after_2021"})) == "v2021"
    assert apply_transition("v2010", clause, frozenset()) == "v2010"
    assert apply_transition("v2005", clause, frozenset({"conduct_after_2021"})) == "v2005"


# --- P-019 判例拘束力 ---


def test_p019_binding_grades() -> None:
    assert binding_effect(PrecedentBinding.SHALL_REFER, distinguishing_reason=False) == "SHOULD_FOLLOW"
    assert binding_effect(PrecedentBinding.SHALL_REFER, distinguishing_reason=True) == "DISTINGUISHED"
    assert binding_effect(PrecedentBinding.MAY_REFERENCE, distinguishing_reason=False) == "NON_BINDING"


# --- P-020 管辖 ---


def test_p020_jurisdiction_routing_fail_closed() -> None:
    rules = (
        JurisdictionRule(JurisdictionRuleKind.LEVEL, "basic_court"),
        JurisdictionRule(JurisdictionRuleKind.SPECIALIZED, "ip_court"),
    )
    assert route_jurisdiction(rules, frozenset({JurisdictionRuleKind.LEVEL})) == "basic_court"
    assert (
        route_jurisdiction(rules, frozenset({JurisdictionRuleKind.SPECIALIZED, JurisdictionRuleKind.LEVEL}))
        == "ip_court"
    )
    assert route_jurisdiction(rules, frozenset({JurisdictionRuleKind.FOREIGN_RELATED})) is None


# --- P-021 反致 ---


def test_p021_renvoi_one_hop_terminates() -> None:
    assert renvoi_resolves("CN_LAW", "US_LAW", foreign_points_back=False) == "US_LAW"
    assert renvoi_resolves("CN_LAW", "US_LAW", foreign_points_back=True) == "CN_LAW"


# --- P-022 公序保留 ---


def test_p022_scoped_override() -> None:
    rules = frozenset({"r1", "r2", "r3"})
    out = apply_override(rules, PublicPolicyOverride(overridden_rule="r2", ground="public_policy"))
    assert out == frozenset({"r1", "r3"})


# --- P-023 准据法联合 ---


def test_p023_joint_selection_requires_both() -> None:
    assert select_applicable_law("CN", "v2021") == "CN::v2021"
    assert select_applicable_law(None, "v2021") == "UNKNOWN"
    assert select_applicable_law("CN", "") == "UNKNOWN"


# --- P-024 案由路由 ---


def test_p024_cause_routing_table() -> None:
    routes = (CauseOfActionRoute(cause="contract_breach", procedure="first_instance", applicable_law="CN::civil"),)
    assert route_cause_of_action(routes, "contract_breach") == ("first_instance", "CN::civil")
    assert route_cause_of_action(routes, "unknown_cause") is None


# --- P-002 概念=数据集+演算 ---


def test_p002_concept_identity_is_pair() -> None:
    d1 = ConceptRecord(concept_id="c", intension="int", extension=("a",))
    a = ConceptAsDataset(definition=d1, computation_rule_id="r1")
    b = ConceptAsDataset(definition=d1, computation_rule_id="r2")
    c = ConceptAsDataset(definition=d1, computation_rule_id="r1")
    assert concepts_identical(a, c)
    assert not concepts_identical(a, b)


# --- P-003 法律语言 ---


def test_p003_translation_preserves_meaning() -> None:
    bindings = (
        LegalTermBinding(term="诉讼时效", definition_id="d1", jurisdiction="CN"),
        LegalTermBinding(term="limitation period", definition_id="d1", jurisdiction="EN"),
    )
    assert canonical_term(bindings, "d1", "CN") == "诉讼时效"
    t = TermTranslation(term_from="诉讼时效", term_to="limitation period", definition_id="d1")
    assert translation_preserves_meaning(t, bindings[0], bindings[1])
    bad = TermTranslation(term_from="诉讼时效", term_to="limitation period", definition_id="d2")
    assert not translation_preserves_meaning(bad, bindings[0], bindings[1])


# --- P-009 概念版本化 ---


def test_p009_registration_strictly_increases() -> None:
    e1 = ConceptVersionEntry(concept_id="virtual_asset", version=1, registered_object="bitcoin")
    e2 = ConceptVersionEntry(concept_id="virtual_asset", version=2, registered_object="nft")
    reg = register_concept_version(register_concept_version((), e1), e2)
    assert len(reg) == 2
    with pytest.raises(ValueError):
        register_concept_version(reg, e1)


# --- P-010 个人信息族 ---


def test_p010_anonymization_and_triple_consent() -> None:
    info = PersonalInfo(
        item_id="x",
        paths=frozenset({InfoPath.IDENTIFICATION}),
        sensitive=True,
        consents=frozenset({"inform", "express_intent"}),
    )
    assert info.is_personal
    assert not processing_requires_triple_consent(info)  # 缺一项同意
    full = PersonalInfo(
        item_id="x",
        paths=frozenset({InfoPath.IDENTIFICATION}),
        sensitive=True,
        consents=frozenset({"inform", "express_intent", "lawful_purpose"}),
    )
    assert processing_requires_triple_consent(full)
    assert not anonymize(full).is_personal


# --- P-036 关系类型谱 ---


def test_p036_relation_spectrum_signature() -> None:
    from theory.spec.concept_meta import RelationKind, classify_relation

    assert classify_relation(RelationKind.OBLIGATIONAL, against_person=True, against_world=False) == "OK"
    assert classify_relation(RelationKind.REAL, against_person=False, against_world=True) == "OK"
    assert classify_relation(RelationKind.REAL, against_person=True, against_world=False) == "MISMATCH"
    assert len(RelationKind) == 5
