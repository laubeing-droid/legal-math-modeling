"""AC-01..AC-04 gate tests: dual-track separation with a synthetic 23x23
table, ZOPA existence and monotone concessions, honest equilibrium
semantics labels, and never-overwriting tendency priors."""

from __future__ import annotations

from decimal import Decimal

import pytest

from theory.spec.action_decision import (
    SYNTHETIC_TABLE_MARKER,
    AttackEdge,
    EquilibriumSemantics,
    ReferenceFrame,
    StrategyProfile,
    SyntheticRuleTable,
    TendencyKey,
    TendencyPrior,
    apply_tendency_prior,
    build_empirical_line,
    determine_zopa,
    run_normative_line,
    solve_equilibrium_contract,
    synthetic_guizhou_23x23,
    validate_concession_ladder,
)
from theory.spec.approximation_contract import ApproximationCertificate, ApproximationDomain

D = Decimal


def _certificate() -> ApproximationCertificate:
    return ApproximationCertificate(
        error_bound=D("0.5"),
        tolerance=D("2.0"),
        applicable_domain=ApproximationDomain(keys=frozenset({"sentencing_empirical"})),
    )


# --- AC-01 ---


def test_dual_track_results_stay_separate() -> None:
    table = synthetic_guizhou_23x23()
    assert table.rows == 23
    assert table.columns == 23
    assert table.marker == SYNTHETIC_TABLE_MARKER

    normative = run_normative_line(table, 4, 9)
    empirical = build_empirical_line(
        low=10.0, high=16.0, certificate=_certificate()
    )
    assert normative.track.value == "NORMATIVE"
    assert empirical.track.value == "EMPIRICAL"
    assert type(normative) is not type(empirical)
    # The empirical line never collapses into a single normative point.
    assert empirical.low < empirical.high


def test_normative_line_is_deterministic_table_execution() -> None:
    table = synthetic_guizhou_23x23()
    assert run_normative_line(table, 0, 0).months == table.values[0][0]
    assert run_normative_line(table, 0, 0).months == run_normative_line(table, 0, 0).months
    with pytest.raises(IndexError):
        run_normative_line(table, 23, 0)
    with pytest.raises(IndexError):
        run_normative_line(table, 0, 23)


def test_synthetic_marker_is_mandatory() -> None:
    with pytest.raises(ValueError):
        SyntheticRuleTable(
            rows=2,
            columns=2,
            marker="REAL",
            values=((1, 2), (3, 4)),
        )


# --- AC-02 ---


def test_zopa_exists_iff_intervals_overlap() -> None:
    yes = determine_zopa(seller_min=100.0, buyer_max=120.0)
    no = determine_zopa(seller_min=130.0, buyer_max=120.0)
    edge = determine_zopa(seller_min=120.0, buyer_max=120.0)
    assert yes.exists and yes.lower == 100.0 and yes.upper == 120.0
    assert not no.exists
    assert edge.exists  # touching reservations still overlap


def test_concession_sizes_are_monotone_nonincreasing() -> None:
    assert validate_concession_ladder((10.0, 6.0, 3.0, 1.0))
    assert validate_concession_ladder((5.0, 5.0))  # equal allowed
    assert not validate_concession_ladder((3.0, 7.0))  # later concession larger
    assert not validate_concession_ladder(())
    assert not validate_concession_ladder((1.0, -2.0))


# --- AC-03 ---


def test_equilibrium_result_identifies_semantic_source() -> None:
    result = solve_equilibrium_contract(
        profiles=(StrategyProfile(("arg_settle",)), StrategyProfile(("arg_sue",))),
        attacks=frozenset(),
    )
    assert result.semantics is EquilibriumSemantics.CONFLICT_FREE_FILTER
    # The label vocabulary has no Nash entry to abuse.
    assert {s.value for s in EquilibriumSemantics} == {"CONFLICT_FREE_FILTER"}


def test_attack_edges_reach_argumentation_layer() -> None:
    result = solve_equilibrium_contract(
        profiles=(
            StrategyProfile(("arg_settle", "arg_mediate")),
            StrategyProfile(("arg_sue",)),
        ),
        attacks=frozenset({AttackEdge(attacker="arg_sue", target="arg_settle")}),
    )
    assert result.accepted_arguments == frozenset({"arg_sue", "arg_mediate"})
    assert result.profiles == (StrategyProfile(("arg_sue",)),)  # attacked profile filtered


# --- AC-04 ---


def test_three_reference_frames_are_distinct() -> None:
    assert len(ReferenceFrame) == 3
    assert {f.value for f in ReferenceFrame} == {"SELF", "PEERS", "SUPERIOR"}


def test_tendency_key_contains_period() -> None:
    key = TendencyKey(court="G01", judge=None, region="SW", period="2024H1")
    assert key.period == "2024H1"
    with pytest.raises(ValueError):
        TendencyKey(court=None, judge=None, region=None, period=" ")


def test_designated_prior_is_explicit_input_and_never_overwrites() -> None:
    prior = TendencyPrior(
        key=TendencyKey(court=None, judge=None, region=None, period="2024H1"),
        value=8.0,
        weight=0.25,
    )
    blended = apply_tendency_prior(structural_value=4.0, prior=prior)
    assert blended == 5.0  # structural fact still visible
    with pytest.raises(ValueError):
        TendencyPrior(
            key=TendencyKey(court=None, judge=None, region=None, period="2024H1"),
            value=8.0,
            weight=1.0,  # full overwrite forbidden
        )
    with pytest.raises(ValueError):
        TendencyPrior(
            key=TendencyKey(court=None, judge=None, region=None, period="2024H1"),
            value=8.0,
            weight=-0.1,
        )
