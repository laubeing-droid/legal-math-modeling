"""One subject-bound contract for finite exact/partial results and enclosures.

This reference does not assert that Python has been proved in Lean. Finite
generic checkers accept caller predicates for pedagogical tests only.
The accepted V2.1 reference surface is v21.checker, which has no predicate port.
"""
from __future__ import annotations
from dataclasses import dataclass
from fractions import Fraction as Q
from typing import Callable, Hashable, Sequence
from reference.unified_reference import SearchResult, scan, verify_partition


@dataclass(frozen=True)
class Subject:
    request: str
    law_version: str
    interpretation: str
    scenario: str
    scope: str
    model: str

    def __post_init__(self):
        if any(type(v) is not str or not v for v in self.__dict__.values()):
            raise ValueError('Complete subject identity required')


@dataclass(frozen=True)
class FiniteCertificate:
    subject: Subject
    component: str
    classification: SearchResult


def search(subject: Subject, component: str, universe: Sequence[Hashable],
           predicate: Callable[[Hashable], bool | None], budget: int | None = None):
    if not component:
        raise ValueError('Component identity required')
    return FiniteCertificate(subject, component, scan(universe, predicate, budget))


def check_finite(expected: Subject, component: str, universe: Sequence[Hashable],
                 semantic_predicate: Callable[[Hashable], bool], cert: FiniteCertificate):
    if cert.subject != expected or cert.component != component:
        return False
    return verify_partition(universe, cert.classification, semantic_predicate)


def relation_join(left, right):
    """Composition R: A×B, S:B×C; shared B must be preserved, not cartesian mixed."""
    return frozenset((a, c) for a, b in left for b2, c in right if b == b2)


@dataclass(frozen=True)
class Envelope:
    lower: Q
    upper: Q
    meaning: str = 'outer_enclosure'

    def __post_init__(self):
        if any(type(x) not in (int, Q) for x in (self.lower, self.upper)):
            raise TypeError('Exact rational endpoints required')
        if self.lower > self.upper or self.meaning != 'outer_enclosure':
            raise ValueError('Invalid enclosure')

    def contains(self, x):
        return self.lower <= x <= self.upper


def finite_enclosure(values):
    vals = tuple(values)
    if not vals:
        raise ValueError('EMPTY is not [0,0]')
    return Envelope(min(vals), max(vals))


def check_enclosure(values, envelope: Envelope):
    """Finite mathematical oracle. Production requires interval/dual proofs."""
    vals = tuple(values)
    return bool(vals) and all(envelope.contains(x) for x in vals)


def posterior_contamination(envelope: Envelope, epsilon: Q):
    """epsilon bounds contamination AFTER conditioning, not a prior bound."""
    if not 0 <= epsilon <= 1 or not 0 <= envelope.lower <= envelope.upper <= 1:
        raise ValueError('Invalid probability/contamination bounds')
    return Envelope((1-epsilon)*envelope.lower, (1-epsilon)*envelope.upper + epsilon)


def partial_mass_enclosure(a: Q, b: Q, remaining: Q):
    if min(a,b,remaining) < 0:
        raise ValueError('Negative mass')
    if a+b == 0:
        if remaining == 0:
            raise ValueError('No positive evidence probability: undefined posterior')
        return Envelope(Q(0),Q(1))
    return Envelope(a/(a+b+remaining),(a+remaining)/(a+b+remaining))


def validate_claim_level(*, mathematical: str, empirical: str,
                         requested: str, subject_matches: bool):
    """Do not reinterpret a model calculation as empirically calibrated truth."""
    if not subject_matches:
        return False
    if requested == 'exact_model_output':
        return mathematical == 'exact'
    if requested == 'sound_partial_output':
        return mathematical in ('exact','sound_partial')
    if requested == 'model_enclosure':
        return mathematical in ('exact','outer_enclosure')
    if requested == 'externally_validated_prediction':
        return mathematical in ('exact','outer_enclosure','numeric_estimate') and empirical == 'heldout_validated'
    return False
