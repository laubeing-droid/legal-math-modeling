from __future__ import annotations

from copy import deepcopy

import pytest

from theory.spec.certificate_schema import (
    build_certificate_envelope_v2,
    check_certificate_envelope,
    envelope_to_dict,
)


def _valid_envelope() -> dict:
    envelope = build_certificate_envelope_v2(
        certificate_id="certificate::contract-breach",
        status="PROVED",
        evidence_kind="FORMAL_BACKEND",
        evidence_verified=True,
        expected_fact_ids=("fact::contract", "fact::non-delivery"),
        used_fact_ids=("fact::contract", "fact::non-delivery"),
        expected_obligation_ids=("obligation::delivery",),
        discharged_obligation_ids=("obligation::delivery",),
        rule_ids=("rule::delivery-breach",),
        arguments=(
            {
                "argument_id": "argument::breach",
                "rule_id": "rule::delivery-breach",
                "support_fact_ids": ["fact::contract", "fact::non-delivery"],
                "conclusion": "delivery_breach",
            },
        ),
        attacks=(),
        accepted_argument_ids=("argument::breach",),
        source_snapshots=(
            {
                "snapshot_id": "snapshot::contract",
                "content": {"text": "bound test source"},
            },
        ),
        rule_pack_content={"rules": [{"id": "rule::delivery-breach"}]},
        semantics_id="grounded",
        semantics_version="1",
        trace_steps=(
            {"step_index": 0, "phase": "input", "event": "facts_loaded"},
            {"step_index": 1, "phase": "output", "event": "decision_status"},
        ),
        producer_commit="1" * 40,
    )
    return envelope_to_dict(envelope)


def _assert_rejected(payload: dict, code: str) -> None:
    verdict = check_certificate_envelope(payload)
    assert verdict.decisive is False
    assert verdict.status in {"UNDECIDED", "TAINTED"}
    assert code in verdict.error_codes


def test_v2_checker_accepts_content_bound_envelope() -> None:
    verdict = check_certificate_envelope(_valid_envelope())

    assert verdict.decisive is True
    assert verdict.status == "PROVED"
    assert not verdict.error_codes


def test_v1_payload_is_parseable_but_never_v2_decisive() -> None:
    payload = {
        "schema_version": "spec-cert-v1",
        "trace_id": "legacy",
        "status": "PROVED",
        "facts": [],
        "horn_rules_fired": [],
        "arguments_constructed": [],
        "attacks_constructed": [],
        "accepted_argument_ids": [],
        "attack_kinds": [],
        "fail_closed_reason": None,
        "wellFormed": True,
        "requiredFactsPresent": True,
        "proofObligationsPresent": True,
    }

    _assert_rejected(payload, "V1_NOT_DECISIVE")


@pytest.mark.parametrize(
    ("mutator", "code"),
    (
        (lambda p: p["trace"].clear(), "EMPTY_TRACE"),
        (lambda p: p["used_fact_ids"].remove("fact::contract"), "MISSING_REQUIRED_FACT"),
        (
            lambda p: p["discharged_obligation_ids"].clear(),
            "MISSING_PROOF_OBLIGATION",
        ),
        (
            lambda p: p["accepted_argument_ids"].append("argument::invented"),
            "UNKNOWN_ACCEPTED_ARGUMENT",
        ),
        (lambda p: p["source_snapshots"][0].update(content_digest="0" * 64), "SOURCE_DIGEST_MISMATCH"),
        (lambda p: p["rule_pack"].update(content_digest="0" * 64), "RULE_PACK_DIGEST_MISMATCH"),
        (lambda p: p["semantics"].update(version="unknown"), "UNKNOWN_SEMANTICS"),
        (lambda p: p["checker"].update(version="unknown"), "UNKNOWN_CHECKER_VERSION"),
        (lambda p: p["evidence"].update(kind="CANDIDATE", verified=True), "CANDIDATE_EVIDENCE"),
        (lambda p: p["used_fact_ids"].append("fact::contract"), "DUPLICATE_ID"),
        (lambda p: p["used_fact_ids"].reverse(), "UNSTABLE_SEQUENCE"),
    ),
)
def test_v2_checker_rejects_required_mutations(mutator, code: str) -> None:
    payload = deepcopy(_valid_envelope())
    mutator(payload)

    _assert_rejected(payload, code)


def test_v2_checker_rejects_stale_snapshot_replay() -> None:
    payload = _valid_envelope()
    verdict = check_certificate_envelope(
        payload,
        expected_source_digests={"snapshot::contract": "f" * 64},
    )

    assert verdict.decisive is False
    assert "STALE_SOURCE_SNAPSHOT" in verdict.error_codes

