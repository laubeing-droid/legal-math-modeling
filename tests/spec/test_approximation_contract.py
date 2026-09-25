"""NN-01/NN-02 gate tests: no certificate means no entry, certificates carry
error bound + domain + identity, and outputs keep interval/identity/certificate."""

from __future__ import annotations

from decimal import Decimal

import pytest

from theory.spec.approximation_contract import (
    ApproximationCertificate,
    ApproximationDomain,
    ApproximationIdentity,
    admit_approximation,
    approximate_probability_output,
)
from theory.spec.probability_pipeline import (
    IdentificationStatus,
    ProbabilityEstimate,
)
from fractions import Fraction

D = Decimal


def _certificate(**overrides) -> ApproximationCertificate:
    base = dict(
        error_bound=D("0.05"),
        tolerance=D("0.10"),
        applicable_domain=ApproximationDomain(keys=frozenset({"labor_first_instance"})),
    )
    base.update(overrides)
    return ApproximationCertificate(**base)


def _estimate(status: IdentificationStatus) -> ProbabilityEstimate:
    return ProbabilityEstimate(
        status=status,
        successes=5,
        observed_total=8,
        frequency=Fraction(5, 8) if status is IdentificationStatus.IDENTIFIED else None,
        interval_low=Fraction(1, 4),
        interval_high=Fraction(3, 4),
        identity="RETRIEVED_COHORT",
    )


def test_no_certificate_no_entry() -> None:
    with pytest.raises(ValueError):
        admit_approximation(value="estimate", certificate=None)


def test_error_bound_required_and_bounded() -> None:
    with pytest.raises(ValueError):
        _certificate(error_bound=D("-0.01"))
    with pytest.raises(ValueError):
        _certificate(tolerance=D("-1"))
    with pytest.raises(ValueError):
        _certificate(error_bound=D("0.2"), tolerance=D("0.1"))


def test_applicable_domain_required() -> None:
    with pytest.raises(ValueError):
        ApproximationDomain(keys=frozenset())
    with pytest.raises(ValueError):
        _certificate(applicable_domain=ApproximationDomain(keys=frozenset()))


def test_admitted_candidate_is_reference_grade() -> None:
    candidate = admit_approximation(value="estimate", certificate=_certificate())
    assert candidate.identity is ApproximationIdentity.REFERENCE
    assert len(ApproximationIdentity) == 1  # no decisive identity exists


def test_output_keeps_interval_identity_certificate() -> None:
    out = approximate_probability_output(
        estimate=_estimate(IdentificationStatus.IDENTIFIED),
        certificate=_certificate(),
        low=D("0.3"),
        high=D("0.7"),
    )
    assert out.low <= out.high
    assert out.identity is ApproximationIdentity.REFERENCE
    assert out.certificate.error_bound <= out.certificate.tolerance
    assert out.source_pipeline == "win_rate_retrieved_cohort"


def test_unknown_estimate_cannot_be_upgraded() -> None:
    with pytest.raises(ValueError):
        approximate_probability_output(
            estimate=_estimate(IdentificationStatus.UNKNOWN),
            certificate=_certificate(),
            low=D("0.3"),
            high=D("0.7"),
        )


def test_reversed_interval_rejected_and_source_declared() -> None:
    with pytest.raises(ValueError):
        approximate_probability_output(
            estimate=_estimate(IdentificationStatus.IDENTIFIED),
            certificate=_certificate(),
            low=D("0.7"),
            high=D("0.3"),
        )
    with pytest.raises(ValueError):
        approximate_probability_output(
            estimate=_estimate(IdentificationStatus.IDENTIFIED),
            certificate=_certificate(),
            low=D("0.3"),
            high=D("0.7"),
            source_pipeline=" ",
        )
