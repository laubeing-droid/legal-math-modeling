#!/usr/bin/env python3
"""NN-01/NN-02: certificate-forced approximator contracts (military-grade).

An approximation enters the system only through ``admit_approximation`` with
a certificate that carries a non-negative error bound within tolerance and a
non-empty applicable domain; there is no certificate-less entry. Admitted
candidates are REFERENCE grade (per the receipt ledger, empirical-line
outputs cap at REFERENCE). NN-02 wraps probability-pipeline estimates into
interval outputs that must keep interval, identity, and certificate.
"""

from __future__ import annotations

from dataclasses import dataclass
from decimal import Decimal
from enum import Enum
from typing import FrozenSet, Optional

from theory.spec.probability_pipeline import (
    IdentificationStatus,
    ProbabilityEstimate,
)


class ApproximationIdentity(str, Enum):
    """Admitted approximations are reference-grade, never decisive."""

    REFERENCE = "REFERENCE"


@dataclass(frozen=True)
class ApproximationDomain:
    keys: FrozenSet[str]

    def __post_init__(self) -> None:
        if not self.keys:
            raise ValueError("applicable domain must be non-empty")


@dataclass(frozen=True)
class ApproximationCertificate:
    error_bound: Decimal
    tolerance: Decimal
    applicable_domain: ApproximationDomain

    def __post_init__(self) -> None:
        if self.error_bound < 0:
            raise ValueError("error_bound must be non-negative")
        if self.tolerance < 0:
            raise ValueError("tolerance must be non-negative")
        if self.error_bound > self.tolerance:
            raise ValueError("error_bound exceeds tolerance")


@dataclass(frozen=True)
class ApproximationCandidate:
    value: object
    certificate: ApproximationCertificate
    identity: ApproximationIdentity = ApproximationIdentity.REFERENCE


def admit_approximation(
    *,
    value: object,
    certificate: Optional[ApproximationCertificate],
) -> ApproximationCandidate:
    """The only entry: no certificate, no approximation in the system."""

    if certificate is None:
        raise ValueError("certificate required")
    return ApproximationCandidate(value=value, certificate=certificate)


@dataclass(frozen=True)
class ApproximationIntervalOutput:
    low: Decimal
    high: Decimal
    identity: ApproximationIdentity
    certificate: ApproximationCertificate
    source_pipeline: str

    def __post_init__(self) -> None:
        if self.low > self.high:
            raise ValueError("interval low must not exceed high")


def approximate_probability_output(
    *,
    estimate: ProbabilityEstimate,
    certificate: ApproximationCertificate,
    low: Decimal,
    high: Decimal,
    source_pipeline: str = "win_rate_retrieved_cohort",
) -> ApproximationIntervalOutput:
    """NN-02: wrap a PR estimate as a certified interval output.

    An UNKNOWN estimate cannot be upgraded into a determinate output; the
    function fails closed instead.
    """

    if estimate.status is not IdentificationStatus.IDENTIFIED:
        raise ValueError("cannot approximate an unidentified estimate")
    if not source_pipeline.strip():
        raise ValueError("source pipeline must be declared")
    return ApproximationIntervalOutput(
        low=low,
        high=high,
        identity=ApproximationIdentity.REFERENCE,
        certificate=certificate,
        source_pipeline=source_pipeline,
    )
