"""RT-01/RT-02 gate tests: candidates only, structure decides, direction and
flip witnesses are explicit, reverse-without-witness carries null attack."""

from __future__ import annotations

import pytest

from theory.spec.retrieval_v4 import (
    CandidateStatus,
    ComparisonDirection,
    RetrievalCandidate,
    StructuralComparison,
    StructuralSignature,
    accept_vector_candidates,
    exact_structural_compare,
    signature_bucket,
)


def _signature(prefix: str) -> StructuralSignature:
    return StructuralSignature(
        issues=frozenset({prefix + ":breach"}),
        facts=frozenset({prefix + ":delivery", prefix + ":payment"}),
        roles=frozenset({"buyer", "seller"}),
        rule_keys=frozenset({prefix + ":rule"}),
    )


def test_vector_layer_returns_candidate_only() -> None:
    recalled = accept_vector_candidates(
        [
            RetrievalCandidate("case_a", 0.9),
            RetrievalCandidate("case_b", 0.4),
        ]
    )
    assert all(c.status is CandidateStatus.CANDIDATE for c in recalled)
    # The contract type has no stronger status to offer.
    assert len(CandidateStatus) == 1


def test_similarity_score_bounds() -> None:
    RetrievalCandidate("case_a", 0.0)
    RetrievalCandidate("case_a", 1.0)
    with pytest.raises(ValueError):
        RetrievalCandidate("case_a", 1.2)
    with pytest.raises(ValueError):
        RetrievalCandidate("case_a", -0.1)


def test_vector_score_never_means_isomorphism() -> None:
    """Same similarity score, different structures: exact_match comes from
    signature fields, so identical scores cannot force isomorphism."""

    twin_score = 0.8
    a = RetrievalCandidate("case_a", twin_score)
    b = RetrievalCandidate("case_b", twin_score)

    same = exact_structural_compare(
        candidate_id="case_b",
        left=_signature("a"),
        right=_signature("a"),
        direction=ComparisonDirection.FORWARD,
    )
    diff = exact_structural_compare(
        candidate_id="case_b",
        left=_signature("a"),
        right=_signature("b"),
        direction=ComparisonDirection.FORWARD,
    )
    assert same.exact_match is True
    assert diff.exact_match is False
    assert a.similarity_score == b.similarity_score  # score stayed equal throughout


def test_signature_bucket_binds_candidate_to_key() -> None:
    a = RetrievalCandidate("case_a", 0.7)
    sig = _signature("a")
    bound = signature_bucket(a, sig)
    assert bound[0] is a
    assert bound[1].bucket_key() == sig.bucket_key()


def test_direction_is_explicit_and_reverse_needs_flip_for_witness() -> None:
    forward = exact_structural_compare(
        candidate_id="case_b",
        left=_signature("a"),
        right=_signature("a"),
        direction=ComparisonDirection.FORWARD,
    )
    reverse_bare = exact_structural_compare(
        candidate_id="case_b",
        left=_signature("a"),
        right=_signature("a"),
        direction=ComparisonDirection.REVERSE,
        flip_factors=(),
        attack_witness=None,
    )
    reverse_flip = exact_structural_compare(
        candidate_id="case_b",
        left=_signature("a"),
        right=_signature("a"),
        direction=ComparisonDirection.REVERSE,
        flip_factors=("burden_shift",),
        attack_witness="witness::expert_report",
    )
    assert forward.direction is ComparisonDirection.FORWARD
    assert reverse_bare.direction is ComparisonDirection.REVERSE
    assert reverse_bare.attack_witness is None
    assert reverse_flip.flip_factors == ("burden_shift",)
    assert reverse_flip.attack_witness == "witness::expert_report"

    with pytest.raises(ValueError):
        exact_structural_compare(
            candidate_id="case_b",
            left=_signature("a"),
            right=_signature("a"),
            direction=ComparisonDirection.REVERSE,
            flip_factors=(),
            attack_witness="witness::smuggled",
        )


def test_flip_factors_are_enumerated_and_exact_requires_bucket() -> None:
    comp = exact_structural_compare(
        candidate_id="case_b",
        left=_signature("a"),
        right=_signature("a"),
        direction=ComparisonDirection.REVERSE,
        flip_factors=("burden_shift", "evidence_admitted"),
        attack_witness="witness::expert_report",
    )
    assert comp.flip_factors == ("burden_shift", "evidence_admitted")
    with pytest.raises(ValueError):
        StructuralComparison(
            candidate_id="x",
            direction=ComparisonDirection.FORWARD,
            same_bucket=False,
            exact_match=True,
            flip_factors=(),
            attack_witness=None,
        )
