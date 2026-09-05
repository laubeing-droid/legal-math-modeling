from __future__ import annotations

import pytest

from theory.spec.canonical_v2 import (
    ENUM_REGISTRY,
    TYPE_LAYERS,
    V1_CANONICAL_TYPES,
    FailureStatus,
    IdKind,
    TypedId,
    build_manifest,
    canonical_collection,
    canonical_digest,
    canonical_json,
    canonical_v2_type_names,
    migrate_v1_payload,
)
from theory.spec.canonical_v2.migration import migrate_v1_fact, migrate_v1_rule


def test_typed_id_kinds_cannot_cross_substitute() -> None:
    fact = TypedId(IdKind.FACT, "contract")

    assert fact.canonical == "fact::contract"
    assert TypedId.parse("fact::contract", IdKind.FACT) == fact
    with pytest.raises(ValueError):
        TypedId.parse(fact.canonical, IdKind.RULE)
    with pytest.raises(ValueError):
        TypedId.parse("unknown::x", IdKind.FACT)
    with pytest.raises(ValueError):
        TypedId.parse("malformed", IdKind.FACT)
    with pytest.raises(ValueError):
        TypedId(IdKind.FACT, "")


def test_canonical_collection_is_sorted_and_duplicate_free() -> None:
    ids = [
        TypedId(IdKind.FACT, "beta"),
        TypedId(IdKind.FACT, "alpha"),
        TypedId(IdKind.FACT, "beta"),
        TypedId(IdKind.RULE, "alpha"),
    ]

    collection = canonical_collection(ids)

    assert collection == ["fact::alpha", "fact::beta", "rule::alpha"]
    assert canonical_collection(reversed(ids)) == collection


def test_canonical_json_is_deterministic_and_unicode_stable() -> None:
    value = {"义务": "交付", "amount": 1, "nested": {"z": [1, 2], "a": None}}

    assert canonical_json(value) == canonical_json(
        {"nested": {"a": None, "z": [1, 2]}, "amount": 1, "义务": "交付"}
    )
    assert canonical_digest(value) == canonical_digest(dict(value))
    assert "义务" in canonical_json(value)
    assert canonical_json({}) == "{}"


def test_canonical_digest_detects_tamper() -> None:
    original = {"facts": ["fact::contract"], "status": "PROVED"}
    tampered = {"facts": ["fact::contract"], "status": "REFUTED"}

    assert canonical_digest(original) != canonical_digest(tampered)


def test_every_failure_status_except_success_is_fail_closed() -> None:
    assert FailureStatus.SUCCESS.fail_closed is False
    for member in FailureStatus:
        if member is not FailureStatus.SUCCESS:
            assert member.fail_closed is True


def test_manifest_covers_four_layers_without_duplicates() -> None:
    manifest = build_manifest()
    names = canonical_v2_type_names()

    assert manifest["schema_version"] == "spec-canonical-manifest-v2"
    assert manifest["type_count"] == 48
    assert len(names) == len(set(names))
    assert manifest["invariants"]["no_duplicate_type_names"] is True
    assert manifest["invariants"]["v1_types_preserved_in_reasoning"] is True
    for name in V1_CANONICAL_TYPES:
        assert name in TYPE_LAYERS["reasoning"]
        assert name in names


def test_manifest_enums_match_shared_vocabularies() -> None:
    assert ENUM_REGISTRY["DecisionStatus"] == ["PROVED", "REFUTED", "UNDECIDED", "TAINTED"]
    assert ENUM_REGISTRY["IdKind"] == [kind.value for kind in IdKind]
    assert "CI_NOT_RUN" in ENUM_REGISTRY["FailureStatus"]
    assert ENUM_REGISTRY["AuthorityLevel"][0] == "UNTRUSTED_PROPOSAL"


def test_v1_fact_migration_records_source_loss() -> None:
    migrated = migrate_v1_fact(
        {"fact_id": "contract", "predicate": "contract_exists", "extra": 1}
    )

    assert migrated["admitted"] is False
    assert migrated["authority_level"] == "UNTRUSTED_PROPOSAL"
    assert "NO_SOURCE_BINDING_DOWNGRADED_TO_CANDIDATE" in migrated["loss_report"]
    assert "UNKNOWN_V1_FIELD:extra" in migrated["loss_report"]

    bound = migrate_v1_fact(
        {"fact_id": "contract", "predicate": "contract_exists", "source_ref": "snapshot::a"}
    )
    assert bound["authority_level"] == "SOURCE_BOUND_CANDIDATE"
    assert bound["admitted"] is False


def test_v1_rule_migration_records_missing_conclusions() -> None:
    migrated = migrate_v1_rule({"rule_id": "breach", "kind": "HORN", "premises": []})

    assert "EMPTY_CONCLUSIONS" in migrated["loss_report"]
    assert migrated["version"] == "unknown"


def test_v1_payload_migration_is_never_decisive() -> None:
    report = migrate_v1_payload({"schema_version": "spec-cert-v1", "status": "PROVED"})

    assert report["decisive"] is False
    assert "V1_PAYLOAD_NEVER_DECISIVE_IN_V2" in report["loss_report"]

    unknown = migrate_v1_payload({"schema_version": "spec-cert-v1", "status": "EXPLODED"})
    assert unknown["migrated_status"] == "UNDECIDED"
    assert "UNKNOWN_V1_STATUS:EXPLODED" in unknown["loss_report"]
