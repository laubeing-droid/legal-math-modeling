#!/usr/bin/env python3
"""P04 exact numeric reference semantics.

Integer minor currency units, rational rates, currency/unit/scale,
rounding node/mode/precision, intervals and bounds. Division by zero,
out-of-range, and overflow fail closed. Binary floats never enter the
formal path; a missing rounding policy blocks decisive results.
"""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
from typing import List, Optional, Tuple

from .canonical_v2.case import round_fraction

ROUNDING_MODES = frozenset({"HALF_UP", "HALF_DOWN", "DOWN", "UP"})


@dataclass(frozen=True)
class NumericReport:
    ok: bool
    value: Optional[object]
    error_codes: Tuple[str, ...]


def check_amount(minor_units: int, currency: str) -> NumericReport:
    if not isinstance(minor_units, int) or isinstance(minor_units, bool):
        return NumericReport(False, None, ("WRONG_SORT",))
    if not currency:
        return NumericReport(False, None, ("MISSING_CURRENCY",))
    return NumericReport(True, {"minor_units": minor_units, "currency": currency}, ())


def divide_exact(numerator: int, denominator: int) -> NumericReport:
    """Exact rational division; zero denominator fails closed."""

    if not (isinstance(numerator, int) and isinstance(denominator, int)):
        return NumericReport(False, None, ("WRONG_SORT",))
    if denominator == 0:
        return NumericReport(False, None, ("DIVISION_BY_ZERO",))
    return NumericReport(True, (numerator, denominator), ())


def check_range(value: int, lower: int, upper: int) -> NumericReport:
    if not isinstance(value, int) or isinstance(value, bool):
        return NumericReport(False, None, ("WRONG_SORT",))
    if value < lower or value > upper:
        return NumericReport(False, None, ("OUT_OF_RANGE",))
    return NumericReport(True, value, ())


def round_minor_units(amount, mode: Optional[str]) -> NumericReport:
    """Rounding at minor-unit boundaries; missing policy is fail-closed.

    Accepts integers and Fractions; binary floats and bools are rejected.
    Midpoints are resolved by exact integer arithmetic — the previous
    ``amount + 0.5`` float expression is gone (J.4.3).
    """

    if mode is None:
        return NumericReport(False, None, ("MISSING_ROUNDING_POLICY",))
    if mode not in ROUNDING_MODES:
        return NumericReport(False, None, ("UNKNOWN_ROUNDING_MODE",))
    if isinstance(amount, bool) or not isinstance(amount, (int, Fraction)):
        return NumericReport(False, None, ("WRONG_SORT", "BINARY_FLOAT_FORBIDDEN"))
    return NumericReport(True, round_fraction(Fraction(amount), mode), ())


def rate_well_formed(numerator: int, denominator: int) -> NumericReport:
    if denominator == 0:
        return NumericReport(False, None, ("ZERO_DENOMINATOR",))
    return NumericReport(True, {"numerator": numerator, "denominator": denominator}, ())


def reject_floats(values: List[object]) -> NumericReport:
    """Binary floats are forbidden on the formal numeric path."""

    for value in values:
        if isinstance(value, float):
            return NumericReport(False, None, ("BINARY_FLOAT_FORBIDDEN",))
    return NumericReport(True, None, ())
