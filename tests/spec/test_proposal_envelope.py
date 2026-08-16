from __future__ import annotations

import pytest

from theory.spec.proposal_envelope import (
    check_proposal_envelope,
    consensus_authority,
    record_behavior_counterexample,
)


def test_llm_proposal_only_issues_proposals() -> None:
    report = check_proposal_envelope({"origin": "LLM"})

    assert report.accepted_as_formal_input is False
    assert report.allowed_artifacts == ("PROPOSAL",)


def test_agent_proposal_cannot_issue_formal_artifacts() -> None:
    report = check_proposal_envelope({"origin": "AGENT"})

    assert "FACT_ATTESTATION" not in report.allowed_artifacts
    assert "CERTIFICATE" not in report.allowed_artifacts
    assert "DECISION_STATUS" not in report.allowed_artifacts


@pytest.mark.parametrize(
    ("mutator", "code"),
    (
        (lambda p: p.update(self_approved=True), "SELF_APPROVAL_NOT_ESCALATION"),
        (lambda p: p.update(prompt_injected=True), "PROMPT_INJECTION_QUARANTINED"),
        (
            lambda p: p.update(claimed_level="ADMITTED_FORMAL_INPUT"),
            "PROPOSAL_LEVEL_INFLATION",
        ),
        (lambda p: p.update(origin="ORACLE"), "UNKNOWN_PROPOSAL_ORIGIN"),
    ),
)
def test_proposal_mutations_are_fail_closed(mutator, code: str) -> None:
    proposal = {"origin": "LLM"}
    mutator(proposal)

    report = check_proposal_envelope(proposal)

    assert code in report.error_codes


def test_consensus_of_proposals_never_escalates() -> None:
    proposals = [{"origin": "LLM"} for _ in range(50)]

    assert consensus_authority(proposals) == "UNTRUSTED_PROPOSAL"
    assert consensus_authority(()) == "UNTRUSTED_PROPOSAL"


def test_false_accept_reject_records_stay_counterexamples() -> None:
    registry: list = []
    record_behavior_counterexample(
        registry, case_id="case::1", kind="FALSE_ACCEPT", detail="model accepted stale source"
    )
    record_behavior_counterexample(
        registry, case_id="case::2", kind="FALSE_REJECT", detail="model rejected valid receipt"
    )

    assert len(registry) == 2
    with pytest.raises(ValueError):
        record_behavior_counterexample(registry, case_id="c", kind="PREMISE", detail="x")
