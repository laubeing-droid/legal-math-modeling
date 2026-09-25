#!/usr/bin/env python3
"""RT-01/RT-02: two-layer retrieval contracts (V4).

Layer one is vector recall as a *contract*: the repo carries no embedding
engine, and this module deliberately does not build one. Recall emits
candidates and nothing more — a similarity score never asserts isomorphism,
same-structure, or same-case. Layer two is Horn-style structural comparison:
buckets come from structural signatures, exact matches come from field-level
comparison of those signatures (never from the similarity score), direction
is explicit, flip factors are enumerated, and a reverse comparison without a
flip witness carries a null attack witness (fail-closed).
"""

from __future__ import annotations

from dataclasses import dataclass
from enum import Enum
from typing import FrozenSet, Optional, Sequence, Tuple


class CandidateStatus(str, Enum):
    """Layer-one outputs are candidates; no stronger status exists here."""

    CANDIDATE = "CANDIDATE"


class ComparisonDirection(str, Enum):
    FORWARD = "FORWARD"
    REVERSE = "REVERSE"


@dataclass(frozen=True)
class RetrievalCandidate:
    """One recalled case. similarity_score is a ranking hint only."""

    case_id: str
    similarity_score: float
    status: CandidateStatus = CandidateStatus.CANDIDATE

    def __post_init__(self) -> None:
        if not 0.0 <= self.similarity_score <= 1.0:
            raise ValueError("similarity_score must be in [0, 1]")


@dataclass(frozen=True)
class StructuralSignature:
    """Horn-structure signature: the bucket key for layer two."""

    issues: FrozenSet[str]
    facts: FrozenSet[str]
    roles: FrozenSet[str]
    rule_keys: FrozenSet[str]

    def bucket_key(self) -> Tuple[FrozenSet[str], ...]:
        return (self.issues, self.facts, self.roles, self.rule_keys)


@dataclass(frozen=True)
class StructuralComparison:
    """Layer-two result: exact structure comparison plus direction/flip data.

    Reverse comparisons with no flip factors admit no attack witness.
    """

    candidate_id: str
    direction: ComparisonDirection
    same_bucket: bool
    exact_match: bool
    flip_factors: Tuple[str, ...]
    attack_witness: Optional[str]

    def __post_init__(self) -> None:
        if self.direction is ComparisonDirection.REVERSE and not self.flip_factors:
            if self.attack_witness is not None:
                raise ValueError(
                    "reverse comparison without flip factors cannot carry "
                    "an attack witness"
                )
        if self.exact_match and not self.same_bucket:
            raise ValueError("exact match requires same bucket")


def accept_vector_candidates(
    candidates: Sequence[RetrievalCandidate],
) -> Tuple[RetrievalCandidate, ...]:
    """Layer one: recall returns candidates only; nothing is promoted here."""

    return tuple(candidates)


def signature_bucket(
    candidate: RetrievalCandidate, signature: StructuralSignature
) -> Tuple[RetrievalCandidate, StructuralSignature]:
    """Bind a candidate to its structural signature (the bucket key)."""

    return (candidate, signature)


def exact_structural_compare(
    *,
    candidate_id: str,
    left: StructuralSignature,
    right: StructuralSignature,
    direction: ComparisonDirection,
    flip_factors: Sequence[str] = (),
    attack_witness: Optional[str] = None,
) -> StructuralComparison:
    """Exact structural comparison from signature fields, never from score."""

    same_bucket = left.bucket_key() == right.bucket_key()
    return StructuralComparison(
        candidate_id=candidate_id,
        direction=direction,
        same_bucket=same_bucket,
        exact_match=left == right,
        flip_factors=tuple(flip_factors),
        attack_witness=attack_witness,
    )
