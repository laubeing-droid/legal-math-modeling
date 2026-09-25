"""Contract tests for the TY-01..TY-04 registry additions (object definition v3).

Two jobs: (1) the registry itself grew to 52 names with the four new types in
the agreed layers, Python and Lean in lockstep (a textual drift gate reads the
Lean name lists and the size theorem straight from source); (2) the minimal
kernel carriers honour the frozen clauses — shared constraints ride on the
relation whole, the three LegalPower modalities never imply one another at the
schema level, H is a mandatory argument of the ApplicableNorm signature, and
the jurisdiction axis routes with an explicit OTHER code.
"""

from __future__ import annotations

import re
from itertools import combinations, product
from pathlib import Path

import pytest

from theory.spec.canonical_v2 import (
    ENUM_REGISTRY,
    TYPE_LAYERS,
    ApplicableNormQuery,
    Event,
    EventHistory,
    Jurisdiction,
    JurisdictionRoute,
    LegalPower,
    Relation,
    SharedConstraint,
    SharedConstraintKind,
    build_manifest,
    canonical_v2_type_names,
)

ROOT = Path(__file__).resolve().parents[2]
LEAN = ROOT / "proofs" / "lean" / "juris_lean" / "JurisLean" / "LegalModelV2.lean"

NEW_REASONING_TYPES = ["Relation", "LegalPower", "Event"]
NEW_SOURCE_TYPES = ["Jurisdiction"]
EXPECTED_COUNT = 52


def _lean_list(def_name: str) -> list[str]:
    text = LEAN.read_text(encoding="utf-8")
    match = re.search(
        rf"def {def_name} : List String :=\s*(.*?)(?=\n/--|\nstructure|\ntheorem|\ninductive|\ndef )",
        text,
        re.DOTALL,
    )
    assert match is not None, f"Lean def {def_name} not found in {LEAN}"
    body = match.group(1)
    names = re.findall(r'"([^"]+)"', body)
    assert names, f"Lean def {def_name} carries no string literals"
    if "v1CanonicalTypeNames" in body:
        names = _lean_list("v1CanonicalTypeNames") + names
    return names


def test_registry_grows_to_52_in_agreed_layers() -> None:
    manifest = build_manifest()
    names = canonical_v2_type_names()

    assert manifest["type_count"] == EXPECTED_COUNT
    assert len(names) == EXPECTED_COUNT == len(set(names))
    assert manifest["invariants"]["no_duplicate_type_names"] is True
    assert manifest["invariants"]["v1_types_preserved_in_reasoning"] is True
    for name in NEW_REASONING_TYPES:
        assert name in TYPE_LAYERS["reasoning"]
    for name in NEW_SOURCE_TYPES:
        assert name in TYPE_LAYERS["source"]


def test_python_manifest_matches_lean_registry_source() -> None:
    """Drift gate: the four layer lists and the size theorem come out of the
    Lean source itself, so a one-sided edit fails closed."""

    pairs = [
        ("identity", "identityV2TypeNames"),
        ("source", "sourceV2TypeNames"),
        ("reasoning", "reasoningV2TypeNames"),
        ("compilation", "compilationV2TypeNames"),
    ]
    for layer, def_name in pairs:
        assert TYPE_LAYERS[layer] == _lean_list(def_name), (
            f"Drift between manifest layer {layer} and Lean def {def_name}"
        )

    text = LEAN.read_text(encoding="utf-8")
    size = re.search(r"canonicalV2TypeNames\.length = (\d+)", text)
    assert size is not None, "v2_registry_size theorem not found in Lean source"
    assert int(size.group(1)) == len(canonical_v2_type_names())


def test_new_enums_are_registered_shared_vocabularies() -> None:
    assert ENUM_REGISTRY["SharedConstraintKind"] == [
        kind.value for kind in SharedConstraintKind
    ]
    assert ENUM_REGISTRY["JurisdictionRoute"] == [
        route.value for route in JurisdictionRoute
    ]


def test_relation_carries_the_three_shared_constraint_kinds() -> None:
    same_loss = SharedConstraint(
        kind=SharedConstraintKind.SAME_LOSS,
        memberRelations=("tort_claim", "contract_claim"),
        subjectRef="loss::medical_2024",
    )
    exclusive = SharedConstraint(
        kind=SharedConstraintKind.COMPETING_EXCLUSIVE,
        memberRelations=("tort_claim", "contract_claim"),
    )
    reduction = SharedConstraint(
        kind=SharedConstraintKind.JOINT_REDUCTION,
        memberRelations=("tort_claim", "contract_claim"),
    )

    tort = Relation(
        relationId="tort_claim",
        parties=("plaintiff", "defendant"),
        kind="tort_liability",
        sharedConstraints=(same_loss, exclusive, reduction),
    )
    contract = Relation(
        relationId="contract_claim",
        parties=("plaintiff", "defendant"),
        kind="breach_of_contract",
        sharedConstraints=(same_loss, exclusive, reduction),
    )

    kinds = {c.kind for r in (tort, contract) for c in r.sharedConstraints}
    assert kinds == set(SharedConstraintKind)
    for constraint in (same_loss, exclusive, reduction):
        assert {tort.relationId, contract.relationId} <= set(constraint.memberRelations)

    # Constraints participate in identity: same id/parties/kind, different
    # constraint set -> different relation record.
    stripped = Relation(tort.relationId, tort.parties, tort.kind, ())
    assert stripped != tort


def test_same_loss_constraint_requires_named_subject() -> None:
    with pytest.raises(ValueError):
        SharedConstraint(
            kind=SharedConstraintKind.SAME_LOSS,
            memberRelations=("a", "b"),
            subjectRef="",
        )
    with pytest.raises(ValueError):
        SharedConstraint(kind=SharedConstraintKind.JOINT_REDUCTION, memberRelations=())


def test_legal_power_three_modalities_never_imply_each_other() -> None:
    """Clause 5: no unconditional implication. Schema-level witness: every one
    of the 8 modality combinations constructs, and all are distinct records —
    the type itself forces no co-variation. The three named Lean theorems
    (Power ⇏ Occurred, Obligation ⇏ Occurred, Power ⇏ Obligation) must exist
    in the Lean mirror."""

    combos = [
        LegalPower(f"synthetic_{i}", power, obligation, occurred)
        for i, (power, obligation, occurred) in enumerate(product((True, False), repeat=3))
    ]
    assert len(combos) == 8
    assert len(set(combos)) == 8
    for left, right in combinations(combos, 2):
        assert left != right

    text = LEAN.read_text(encoding="utf-8")
    for theorem in (
        "legalPower_power_not_implies_occurred",
        "legalPower_obligation_not_implies_occurred",
        "legalPower_power_not_implies_obligation",
    ):
        assert f"theorem {theorem}" in text, f"missing Lean theorem {theorem}"


def test_history_h_is_mandatory_and_identity_forming() -> None:
    filing = Event(eventId="case_filed", atDay=20240, eventType="filing")
    hearing = Event(eventId="hearing", atDay=20280, eventType="hearing")
    history = EventHistory(events=(filing, hearing))
    assert history.events == (filing, hearing)  # insertion order preserved

    jurisdiction = Jurisdiction(route=JurisdictionRoute.MAINLAND)
    base = dict(
        jurisdiction=jurisdiction,
        normEnv="civil_law_2020",
        question="q_breach",
        atDay=20281,
    )
    with_history = ApplicableNormQuery(history=history, **base)
    other_history = ApplicableNormQuery(history=EventHistory(events=(filing,)), **base)
    assert with_history != other_history  # H participates in identity

    # The signature has no default for H: a query without history cannot be built.
    with pytest.raises(TypeError):
        ApplicableNormQuery(**base)  # type: ignore[call-arg]


def test_jurisdiction_axis_routes_and_accepts_explicit_other() -> None:
    assert len(JurisdictionRoute) == 4
    assert Jurisdiction(route=JurisdictionRoute.MAINLAND) != Jurisdiction(
        route=JurisdictionRoute.HONG_KONG
    )
    with pytest.raises(ValueError):
        Jurisdiction(route=JurisdictionRoute.OTHER)  # OTHER without a code fails closed
    assert Jurisdiction(route=JurisdictionRoute.OTHER, code="MO").code == "MO"

    # TY-04 acceptance: empirical assets t85..t94 can each hang off the axis.
    routes = [
        JurisdictionRoute.MAINLAND,
        JurisdictionRoute.HONG_KONG,
        JurisdictionRoute.UNITED_STATES,
        JurisdictionRoute.OTHER,
    ]
    tagged = {
        f"t{n}": Jurisdiction(route=routes[n % 4], code="MO" if n % 4 == 3 else "")
        for n in range(85, 95)
    }
    assert len(tagged) == 10
    assert len({j.route for j in tagged.values()}) == 4
