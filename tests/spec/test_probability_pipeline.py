"""PR-01/PR-02/PR-03 gate tests: five-element event contract, retrieved-cohort
population, delegation to the existing win_model interval, and flip-witness
recomputation."""

from __future__ import annotations

from pathlib import Path

import pytest

from theory.spec.probability_pipeline import (
    RETRIEVED_IDENTITY,
    SYNTHETIC_IDENTITY,
    CohortFrequency,
    FlipWitness,
    IdentificationStatus,
    RetrievedOutcome,
    TemporalProtocol,
    WinEventDefinition,
    build_comparison_report,
    estimate_retrieved_cohort,
    identify_event,
    load_win_model_module,
    observed_frequency,
)
from theory.spec.retrieval_v4 import ComparisonDirection, StructuralSignature

ROOT = Path(__file__).resolve().parents[2]

T_TEMPORAL = TemporalProtocol(
    split="train",
    cutoff="2024-06-01T00:00:00",
    feature_latest="2024-01-01T00:00:00",
    outcome_time="2024-12-01T00:00:00",
)


def _event(**overrides) -> WinEventDefinition:
    base = dict(
        identity="win::severance_2024",
        cluster="labor::severance",
        objective="severance_claim_upheld",
        group="labor_first_instance",
        temporal=T_TEMPORAL,
        target_population="all first-instance severance claims in the retrieved cohort",
        outcome_variable="claim upheld (1/0)",
        observation_mechanism="retrieved judgments, observed rows only",
    )
    base.update(overrides)
    return WinEventDefinition(**base)


def _cohort(n_success: int, n_fail: int, synthetic: bool = False):
    rows = []
    for i in range(n_success):
        rows.append(
            RetrievedOutcome(f"win_{i}", observed=True, success=True, synthetic=synthetic)
        )
    for i in range(n_fail):
        rows.append(
            RetrievedOutcome(f"loss_{i}", observed=True, success=False, synthetic=synthetic)
        )
    return rows


# --- PR-01 ---


def test_missing_target_population_is_unknown() -> None:
    result = identify_event(_event(target_population=" "))
    assert result.status is IdentificationStatus.UNKNOWN
    assert "target_population" in result.reasons


def test_missing_observation_mechanism_is_unknown() -> None:
    result = identify_event(_event(observation_mechanism=""))
    assert result.status is IdentificationStatus.UNKNOWN
    assert "observation_mechanism" in result.reasons


def test_missing_temporal_protocol_is_unknown() -> None:
    broken = _event(
        temporal=TemporalProtocol(split="", cutoff="", feature_latest="", outcome_time="")
    )
    result = identify_event(broken)
    assert result.status is IdentificationStatus.UNKNOWN
    assert set(result.reasons) >= {"split", "cutoff", "feature_latest", "outcome_time"}


def test_complete_event_is_identified() -> None:
    assert identify_event(_event()).status is IdentificationStatus.IDENTIFIED


# --- PR-02 ---


def test_population_is_exactly_retrieved_observed_rows() -> None:
    rows = _cohort(3, 2) + [
        RetrievedOutcome("pending_1", observed=False, success=False)
    ]
    freq = observed_frequency(rows)
    assert freq == CohortFrequency(successes=3, observed_total=5)
    assert freq.frequency == __import__("fractions").Fraction(3, 5)


def test_zero_observation_returns_unknown() -> None:
    estimate = estimate_retrieved_cohort(
        event=_event(), rows=[RetrievedOutcome("pending", False, False)], repo_root=ROOT
    )
    assert estimate.status is IdentificationStatus.UNKNOWN
    assert estimate.interval_low is None and estimate.interval_high is None


def test_synthetic_cohort_is_hard_marked() -> None:
    estimate = estimate_retrieved_cohort(
        event=_event(), rows=_cohort(5, 3, synthetic=True), repo_root=ROOT
    )
    assert estimate.identity == SYNTHETIC_IDENTITY
    assert estimate.status is IdentificationStatus.IDENTIFIED
    assert estimate.interval_low is not None
    assert estimate.interval_low <= estimate.interval_high


def test_beta_interval_delegates_to_existing_win_model(monkeypatch) -> None:
    win = load_win_model_module(ROOT)
    calls = {}

    def fake_interval(model, group, tail=win.Q(1, 20), steps=24):
        calls["group"] = group
        calls["counts"] = model.counts
        return {"lo": win.Q(1, 4), "hi": win.Q(3, 4)}

    monkeypatch.setattr(win, "latent_rate_interval", fake_interval)
    estimate = estimate_retrieved_cohort(
        event=_event(), rows=_cohort(6, 2), repo_root=ROOT
    )
    # The adapter really called the existing module function.
    assert calls["group"] == "labor_first_instance"
    assert calls["counts"][0][0] == "labor_first_instance"
    assert (calls["counts"][0][1], calls["counts"][0][2]) == (6, 2)
    assert estimate.interval_low == win.Q(1, 4)
    assert estimate.interval_high == win.Q(3, 4)
    assert estimate.successes == 6 and estimate.observed_total == 8


def test_real_interval_math_runs_on_retrieved_cohort() -> None:
    estimate = estimate_retrieved_cohort(
        event=_event(), rows=_cohort(5, 3), repo_root=ROOT
    )
    assert estimate.identity == RETRIEVED_IDENTITY
    assert estimate.status is IdentificationStatus.IDENTIFIED
    assert 0 <= estimate.interval_low <= estimate.interval_high <= 1


def test_row_time_order_is_enforced_fail_closed() -> None:
    broken = _event(
        temporal=TemporalProtocol(
            split="train",
            cutoff="2024-01-01T00:00:00",
            feature_latest="2024-06-01T00:00:00",  # feature after cutoff
            outcome_time="2024-12-01T00:00:00",
        )
    )
    with pytest.raises(ValueError):
        estimate_retrieved_cohort(event=broken, rows=_cohort(2, 2), repo_root=ROOT)


# --- PR-03 ---


def _comparison(direction: ComparisonDirection) -> object:
    from theory.spec.retrieval_v4 import exact_structural_compare

    sig = StructuralSignature(
        issues=frozenset({"i"}),
        facts=frozenset({"f"}),
        roles=frozenset({"r"}),
        rule_keys=frozenset({"k"}),
    )
    return exact_structural_compare(
        candidate_id="case_b",
        left=sig,
        right=sig,
        direction=direction,
        flip_factors=("evidence_admitted",),
        attack_witness="witness::expert_report",
    )


def _score(features: dict) -> float:
    return 0.5 + (0.3 if features.get("evidence_admitted") == "yes" else 0.0)


def test_forward_direction_is_preserved() -> None:
    report = build_comparison_report(
        direction=ComparisonDirection.FORWARD,
        structural_comparison=_comparison(ComparisonDirection.FORWARD),
        base_features={"evidence_admitted": "no"},
        flip_witnesses=[FlipWitness("evidence_admitted", "no", "yes")],
        score_fn=_score,
    )
    assert report.direction is ComparisonDirection.FORWARD
    assert report.base_score == 0.5


def test_reverse_direction_is_preserved() -> None:
    report = build_comparison_report(
        direction=ComparisonDirection.REVERSE,
        structural_comparison=_comparison(ComparisonDirection.REVERSE),
        base_features={"evidence_admitted": "yes"},
        flip_witnesses=[FlipWitness("evidence_admitted", "yes", "no")],
        score_fn=_score,
    )
    assert report.direction is ComparisonDirection.REVERSE


def test_flip_witness_recomputes_score() -> None:
    report = build_comparison_report(
        direction=ComparisonDirection.FORWARD,
        structural_comparison=_comparison(ComparisonDirection.FORWARD),
        base_features={"evidence_admitted": "no"},
        flip_witnesses=[FlipWitness("evidence_admitted", "no", "yes")],
        score_fn=_score,
    )
    assert report.base_score == 0.5
    assert report.flipped_score == 0.8  # recomputed by score_fn, not asserted


def test_flip_without_real_feature_change_is_rejected() -> None:
    with pytest.raises(ValueError):  # before-value mismatch = no real change
        build_comparison_report(
            direction=ComparisonDirection.FORWARD,
            structural_comparison=_comparison(ComparisonDirection.FORWARD),
            base_features={"evidence_admitted": "yes"},
            flip_witnesses=[FlipWitness("evidence_admitted", "no", "yes")],
            score_fn=_score,
        )
    with pytest.raises(ValueError):  # factor not present at all
        build_comparison_report(
            direction=ComparisonDirection.FORWARD,
            structural_comparison=_comparison(ComparisonDirection.FORWARD),
            base_features={},
            flip_witnesses=[FlipWitness("missing_factor", 0, 1)],
            score_fn=_score,
        )
