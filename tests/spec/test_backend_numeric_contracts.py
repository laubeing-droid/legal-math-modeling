from __future__ import annotations

import pytest

from theory.spec.backend_contract import (
    check_solver_receipt,
    classify_outcome,
    outcome_to_failure_status,
    route_backend,
)
from theory.spec.exact_numeric_contract import (
    check_amount,
    check_range,
    divide_exact,
    rate_well_formed,
    reject_floats,
    round_minor_units,
)


def test_amount_requires_currency_and_int_sort() -> None:
    assert check_amount(1000, "CNY").ok is True
    assert "MISSING_CURRENCY" in check_amount(1000, "").error_codes
    assert "WRONG_SORT" in check_amount(10.5, "CNY").error_codes
    assert "WRONG_SORT" in check_amount(True, "CNY").error_codes


def test_division_by_zero_fails_closed() -> None:
    report = divide_exact(100, 0)

    assert report.ok is False
    assert "DIVISION_BY_ZERO" in report.error_codes
    assert divide_exact(100, 3).value == (100, 3)


def test_range_check_fails_closed_on_boundaries() -> None:
    assert check_range(0, 0, 10).ok is True
    assert check_range(10, 0, 10).ok is True
    assert "OUT_OF_RANGE" in check_range(11, 0, 10).error_codes
    assert "OUT_OF_RANGE" in check_range(-1, 0, 10).error_codes


def test_missing_rounding_policy_is_not_decisive() -> None:
    report = round_minor_units(105, None)

    assert report.ok is False
    assert "MISSING_ROUNDING_POLICY" in report.error_codes
    assert "UNKNOWN_ROUNDING_MODE" in round_minor_units(105, "BANKERS").error_codes
    assert round_minor_units(105, "HALF_UP").value == 105


def test_rate_zero_denominator_fails_closed() -> None:
    assert "ZERO_DENOMINATOR" in rate_well_formed(5, 0).error_codes
    assert rate_well_formed(5, 10000).ok is True


def test_binary_floats_forbidden_on_formal_path() -> None:
    assert reject_floats([1, 2, (3, 4)]).ok is True
    assert "BINARY_FLOAT_FORBIDDEN" in reject_floats([1, 2.0]).error_codes


def test_routing_is_deterministic_and_feature_complete() -> None:
    assert route_backend(
        {"needs_nonmonotonic": True, "needs_arithmetic": False, "needs_disjunction": False, "plain_horn": False}
    ).backend == "ASP"
    assert route_backend(
        {"needs_nonmonotonic": False, "needs_arithmetic": True, "needs_disjunction": False, "plain_horn": False}
    ).backend == "SMT"
    assert route_backend(
        {"needs_nonmonotonic": False, "needs_arithmetic": False, "needs_disjunction": False, "plain_horn": True}
    ).backend == "HORN"
    assert route_backend(
        {"needs_nonmonotonic": False, "needs_arithmetic": False, "needs_disjunction": False, "plain_horn": False}
    ).backend == "DIRECT_REFERENCE"

    missing = route_backend({"needs_nonmonotonic": True})
    assert missing.backend is None
    assert any(code.startswith("MISSING_FEATURE") for code in missing.error_codes)

    wrong_sort = route_backend(
        {"needs_nonmonotonic": "yes", "needs_arithmetic": False, "needs_disjunction": False, "plain_horn": False}
    )
    assert wrong_sort.backend is None
    assert "WRONG_FEATURE_SORT:needs_nonmonotonic" in wrong_sort.error_codes


@pytest.mark.parametrize(
    "outcome", ("UNKNOWN", "TIMEOUT", "BACKEND_UNAVAILABLE", "ERROR")
)
def test_fail_closed_outcomes_never_become_decisive(outcome: str) -> None:
    assert classify_outcome(outcome) == "FAIL_CLOSED"
    assert outcome_to_failure_status(outcome) == outcome


def test_sat_unsat_are_decisive() -> None:
    assert classify_outcome("SAT") == "DECISIVE"
    assert classify_outcome("UNSAT") == "DECISIVE"
    assert outcome_to_failure_status("SAT") == "SUCCESS"


def test_solver_receipt_identity_fields_are_required() -> None:
    receipt = {
        "solver_id": "z3",
        "options_digest": "d" * 64,
        "seed": 7,
        "limits": "time=60",
        "problem_digest": "e" * 64,
        "outcome": "SAT",
    }
    ok, errors = check_solver_receipt(receipt)
    assert ok is True

    incomplete = dict(receipt)
    incomplete.pop("problem_digest")
    ok, errors = check_solver_receipt(incomplete)
    assert ok is False
    assert "MISSING_RECEIPT_FIELD:problem_digest" in errors

    unknown = dict(receipt, outcome="MAYBE")
    ok, errors = check_solver_receipt(unknown)
    assert ok is False
    assert "UNKNOWN_OUTCOME" in errors
