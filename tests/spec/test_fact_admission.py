from __future__ import annotations

from copy import deepcopy

import pytest

from theory.spec.fact_admission import (
    check_fact_admission,
    compute_taint,
    revoke_attestation,
)
from theory.spec.receipt_authority import (
    can_issue,
    consensus_level,
    verify_authority_receipt,
)

PASS_GATES = {"source": "PASS", "interpretation": "PASS", "fact": "PASS"}


def _candidate(**overrides) -> dict:
    candidate = {
        "fact_id": "fact::contract",
        "inputs": ({"subject": "source::contract", "taint": "CLEAN"},),
    }
    candidate.update(overrides)
    return candidate


def _attestation(**overrides) -> dict:
    attestation = {
        "fact_id": "fact::contract",
        "status": "ADMITTED",
        "case_scope": "case::1",
        "run_scope": "run::1",
    }
    attestation.update(overrides)
    return attestation


def test_admission_passes_with_three_gates_and_bound_attestation() -> None:
    report = check_fact_admission(
        _candidate(),
        gates=PASS_GATES,
        attestations=(_attestation(),),
        case_scope="case::1",
        run_scope="run::1",
    )

    assert report.admitted is True
    assert report.taint == "CLEAN"


@pytest.mark.parametrize(
    ("gates", "code"),
    (
        ({**PASS_GATES, "source": "FAIL"}, "SOURCE_GATE_FAIL"),
        ({**PASS_GATES, "interpretation": "FAIL"}, "INTERPRETATION_GATE_FAIL"),
        ({**PASS_GATES, "fact": "BLOCKED"}, "FACT_GATE_BLOCKED"),
        ({**PASS_GATES, "source": "DISPUTED"}, "SOURCE_GATE_DISPUTED"),
        ({**PASS_GATES, "source": "MAYBE"}, "UNKNOWN_SOURCE_GATE_STATE"),
    ),
)
def test_gate_independence_blocks_admission(gates, code: str) -> None:
    report = check_fact_admission(
        _candidate(), gates=gates, attestations=(_attestation(),)
    )

    assert report.admitted is False
    assert code in report.error_codes


@pytest.mark.parametrize(
    ("mutator", "code"),
    (
        (lambda a: a.update(status="CANDIDATE"), "CANDIDATE_ATTESTATION_NOT_DECISIVE"),
        (
            lambda a: a.update(status="USER_ASSUMED"),
            "USER_ASSUMED_ATTESTATION_NOT_DECISIVE",
        ),
        (lambda a: a.update(status="DISPUTED"), "DISPUTED_ATTESTATION_NOT_DECISIVE"),
        (lambda a: a.update(expired=True), "EXPIRED_ATTESTATION_NOT_DECISIVE"),
        (
            lambda a: a.update(fact_id="fact::other"),
            "ATTESTATION_BINDING_MISMATCH",
        ),
    ),
)
def test_non_admitted_attestations_are_rejected(mutator, code: str) -> None:
    attestation = _attestation()
    mutator(attestation)

    report = check_fact_admission(
        _candidate(), gates=PASS_GATES, attestations=(attestation,)
    )

    assert report.admitted is False
    assert code in report.error_codes


def test_cross_scope_replay_is_rejected() -> None:
    report = check_fact_admission(
        _candidate(),
        gates=PASS_GATES,
        attestations=(_attestation(case_scope="case::other"),),
        case_scope="case::1",
    )

    assert report.admitted is False
    assert "CROSS_SCOPE_REPLAY" in report.error_codes


def test_tainted_input_never_becomes_admitted_even_with_majority() -> None:
    candidate = _candidate(
        inputs=(
            {"subject": "agent::1", "taint": "CLEAN"},
            {"subject": "agent::2", "taint": "CLEAN"},
            {"subject": "agent::3", "taint": "TAINTED"},
        )
    )

    report = check_fact_admission(
        candidate, gates=PASS_GATES, attestations=(_attestation(),)
    )

    assert report.admitted is False
    assert report.taint == "TAINTED"
    assert "TAINTED_INPUT_NONINTERFERENCE" in report.error_codes
    assert compute_taint(candidate["inputs"]) == "TAINTED"


def test_revocation_is_monotone_and_framed() -> None:
    attestations = (
        _attestation(),
        _attestation(fact_id="fact::delivery", case_scope="case::2"),
    )

    revoked = revoke_attestation(attestations, "fact::contract")

    assert revoked[0]["status"] == "REVOKED"
    assert revoked[1]["status"] == "ADMITTED"

    report = check_fact_admission(
        _candidate(), gates=PASS_GATES, attestations=(revoked[0],)
    )
    assert report.admitted is False
    assert "REVOKED_ATTESTATION_NOT_DECISIVE" in report.error_codes


def _valid_receipt(**overrides) -> dict:
    receipt = {
        "issuer_level": "SOURCE_BOUND_CANDIDATE",
        "target_level": "HUMAN_REVIEWED_CANDIDATE",
        "case_scope": "case::1",
        "issuer_identity": "reviewer::alice",
        "subject": "fact::contract",
        "issued_day": 10,
        "expiry_day": 20,
    }
    receipt.update(overrides)
    return receipt


def test_valid_receipt_escalates_one_level() -> None:
    report = verify_authority_receipt(_valid_receipt(), expected_scope="case::1", now_day=15)

    assert report.valid is True
    assert report.escalated_level == "HUMAN_REVIEWED_CANDIDATE"


@pytest.mark.parametrize(
    ("mutator", "code"),
    (
        (
            lambda r: r.update(target_level="ADMITTED_FORMAL_INPUT"),
            "LEVEL_SKIP_NOT_ALLOWED",
        ),
        (
            lambda r: r.update(target_level="SOURCE_BOUND_CANDIDATE"),
            "NO_ESCALATION",
        ),
        (lambda r: r.update(case_scope="case::other"), "RECEIPT_SCOPE_MISMATCH"),
        (lambda r: r.update(self_issued=True), "SELF_ISSUED_RECEIPT"),
        (lambda r: r.update(revoked=True), "RECEIPT_REVOKED"),
    ),
)
def test_receipt_mutations_are_fail_closed(mutator, code: str) -> None:
    receipt = _valid_receipt()
    mutator(receipt)

    report = verify_authority_receipt(receipt, expected_scope="case::1", now_day=15)

    assert report.valid is False
    assert code in report.error_codes


def test_expired_receipt_is_fail_closed() -> None:
    report = verify_authority_receipt(_valid_receipt(), now_day=99)

    assert report.valid is False
    assert "RECEIPT_EXPIRED" in report.error_codes


def test_proposals_cannot_issue_formal_artifacts() -> None:
    assert can_issue("UNTRUSTED_PROPOSAL", "PROPOSAL") is True
    assert can_issue("UNTRUSTED_PROPOSAL", "FACT_ATTESTATION") is False
    assert can_issue("UNTRUSTED_PROPOSAL", "CERTIFICATE") is False
    assert can_issue("UNTRUSTED_PROPOSAL", "DECISION_STATUS") is False
    assert can_issue("HUMAN_REVIEWED_CANDIDATE", "CERTIFICATE") is False
    assert can_issue("ADMITTED_FORMAL_INPUT", "CERTIFICATE") is True


def test_consensus_never_escalates() -> None:
    assert consensus_level(("UNTRUSTED_PROPOSAL",) * 10) == "UNTRUSTED_PROPOSAL"
    assert (
        consensus_level(("SOURCE_BOUND_CANDIDATE", "SOURCE_BOUND_CANDIDATE"))
        == "SOURCE_BOUND_CANDIDATE"
    )
