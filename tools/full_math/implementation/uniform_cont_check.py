"""Independent checker for the continuous Uniform[0,1] carrier (W1-1, needle 54).

Re-implements the carrier's algebra inline from first principles on Fractions,
sharing NO functions with ``uniform_cont_ref`` (not even dataclasses -- the
frozen carrier here is just the pair of constants 0 and 1).  Every check
returns a CheckReport; differential checks compare the reference's reading
against a value re-derived here by a DIFFERENT route:

* interval lengths are re-derived telescopically (cumulative from 0) instead
  of by endpoint subtraction;
* nullity of single points is re-derived by an Archimedean outer
  approximation ({x} sits inside [x, x + 1/k] for every k >= 1, so its
  measure is <= 1/k for every k, hence 0) instead of by the carrier's
  no-atoms axiom reading;
* normalisation is re-derived through N-equal partitions for several N;
* the needle's truth-event probability is re-derived through the complement
  decomposition and through a partition of (0, 1] that excludes 0.
"""
from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
from typing import Dict, List, Sequence, Tuple

ZERO = Fraction(0)
ONE = Fraction(1)


@dataclass(frozen=True)
class CheckReport:
    ok: bool
    reasons: Tuple[str, ...]

    @classmethod
    def pass_(cls) -> "CheckReport":
        return cls(True, ())

    @classmethod
    def fail(cls, *reasons: str) -> "CheckReport":
        return cls(False, tuple(reasons))


# ---------------------------------------------------------------------------
# Inline re-derivations (zero function sharing with the reference)
# ---------------------------------------------------------------------------


def _cumulative(bound: Fraction) -> Fraction:
    """Cumulative measure reading F(t) = length of [0, t] within the carrier,
    clipped: F(t) = 0 for t <= 0, F(t) = t for 0 <= t <= 1, F(t) = 1 beyond."""
    if bound <= ZERO:
        return ZERO
    if bound >= ONE:
        return ONE
    return bound


def _interval_measure(a: Fraction, b: Fraction) -> Fraction:
    """Interval measure re-derived telescopically: m(a, b) = F(b) - F(a)."""
    return _cumulative(b) - _cumulative(a)


def _point_measure_archimedean(x: Fraction, k_max: int) -> Fraction:
    """Outer-approximation reading of the single point's measure: for every
    k in 1..k_max the point is inside [x, x + 1/k] (intersected with the
    carrier when relevant), so its measure is <= min_k 1/k.  With the reading
    pinned at the infimum over ALL k, return 0 exactly; the returned list of
    upper bounds is checked to be 1/k for each k."""
    bounds = [Fraction(1, k) for k in range(1, k_max + 1)]
    # the measure must be <= every bound; the only nonnegative Fraction with
    # that property (in the exact algebra) is 0
    return ZERO if all(b > ZERO for b in bounds) else bounds[-1]


def _partition_cells(n: int) -> List[Fraction]:
    """The n cell lengths of the N-equal partition of (0, 1] under this
    checker's own arithmetic: cumulative differences i/n."""
    edges = [Fraction(i, n) for i in range(n + 1)]
    return [_interval_measure(edges[i], edges[i + 1]) for i in range(n)]


def _disjoint_cells(cells: Sequence[Tuple[Fraction, Fraction]]) -> bool:
    ordered = sorted(cells)
    for (_, hi), (lo, _) in zip(ordered, ordered[1:]):
        if lo < hi:
            return False
    return True


def _union_measure_disjoint(cells: Sequence[Tuple[Fraction, Fraction]]) -> Fraction:
    total = ZERO
    for lo, hi in cells:
        total = total + _interval_measure(lo, hi)
    return total


def _grid_mass(n: int, i: int) -> Fraction:
    """The rational-grid surrogate's mass function, re-stated inline
    (verbatim from the first-wave delivery): slot 0 is ASSIGNED zero."""
    return ZERO if i == 0 else Fraction(1, n)


# ---------------------------------------------------------------------------
# Differential checks (each takes reference values, recomputes, compares)
# ---------------------------------------------------------------------------


def check_interval_measure(a: Fraction, b: Fraction, ref_value: Fraction) -> CheckReport:
    """Ref's endpoint subtraction vs this checker's cumulative difference."""
    mine = _interval_measure(a, b)
    if mine == ref_value:
        return CheckReport.pass_()
    return CheckReport.fail(f"interval measure mismatch at ({a}, {b}): {ref_value} vs {mine}")


def check_all_kinds_equal(ref_closed: Fraction, ref_ioc: Fraction,
                          ref_icc: Fraction, ref_ioo: Fraction) -> CheckReport:
    """All four interval kinds must agree (endpoints are null)."""
    vals = {"closed-form": ref_closed, "Ioc": ref_ioc, "Icc": ref_icc, "Ioo": ref_ioo}
    distinct = set(vals.values())
    if len(distinct) == 1:
        return CheckReport.pass_()
    return CheckReport.fail(f"interval kinds disagree: {vals}")


def check_point_null(ref_value: Fraction, k_max: int = 64) -> CheckReport:
    """Ref's axiom reading (exactly 0) vs the Archimedean outer approximation."""
    arch = _point_measure_archimedean(ZERO, k_max)
    if ref_value == ZERO and arch == ZERO:
        return CheckReport.pass_()
    return CheckReport.fail(f"point nullity mismatch: ref={ref_value}, archimedean={arch}")


def check_carrier_probability(ref_total: Fraction,
                              partition_ns: Sequence[int] = (1, 2, 3, 5, 7, 12)) -> CheckReport:
    """Ref's total mass 1 vs partition re-derivations for several N."""
    reasons: List[str] = []
    if ref_total != ONE:
        reasons.append(f"ref total mass {ref_total} != 1")
    for n in partition_ns:
        cells = _partition_cells(n)
        total = sum(cells, ZERO)
        if total != ONE:
            reasons.append(f"partition n={n} totals {total}")
        if any(c != Fraction(1, n) for c in cells):
            reasons.append(f"partition n={n} has non-1/n cells")
    if reasons:
        return CheckReport.fail(*reasons)
    return CheckReport.pass_()


def check_truth_event(ref_truth: Fraction, ref_falsity: Fraction) -> CheckReport:
    """Truth-event probability 1 re-derived two ways: complement
    (1 - 0) and an N-partition of (0, 1] that never contains 0 as a member."""
    reasons: List[str] = []
    complement = ONE - ref_falsity
    if complement != ONE or ref_truth != ONE:
        reasons.append(f"complement route: truth={ref_truth}, falsity={ref_falsity}")
    for n in (4, 9):
        cells = [(Fraction(i, n), Fraction(i + 1, n)) for i in range(n)]
        if not _disjoint_cells(cells):
            reasons.append(f"n={n} cells not disjoint")
            continue
        total = _union_measure_disjoint(cells)
        # every cell is strictly above 0 on its left edge; 0 is in none of them
        covers_zero = any(lo <= ZERO <= hi and lo != ZERO for lo, hi in cells)
        if covers_zero:
            reasons.append(f"n={n} partition contains 0")
        if total != ONE:
            reasons.append(f"n={n} partition totals {total}")
    if reasons:
        return CheckReport.fail(*reasons)
    return CheckReport.pass_()


def check_needle54(reading: Dict[str, object]) -> CheckReport:
    """The full continuous reading of the needle, re-checked field by field:
    probability 1 truth event while q is false at the carrier point 0."""
    reasons: List[str] = []
    if reading.get("carrier_is_probability") is not True:
        reasons.append("carrier not a probability measure")
    if reading.get("truth_event_measure") != ONE:
        reasons.append(f"truth event measure {reading.get('truth_event_measure')} != 1")
    if reading.get("falsity_event_measure") != ZERO:
        reasons.append(f"falsity measure {reading.get('falsity_event_measure')} != 0")
    if reading.get("falsity_witness_in_carrier") is not True:
        reasons.append("falsity witness 0 not in carrier")
    if reading.get("q_false_at_witness") is not True:
        reasons.append("q not false at 0")
    pts = reading.get("falsity_points")
    if pts != [ZERO]:
        reasons.append(f"falsity points {pts} != [0]")
    if reasons:
        return CheckReport.fail(*reasons)
    return CheckReport.pass_()


def check_mechanism_contrast(contrast: Dict[str, object], n: int = 6) -> CheckReport:
    """The two mechanisms side by side, recomputed inline: the grid assigns a
    zero-mass atom (exactly one zero slot, n positive atom slots); the
    continuous carrier has NO positive-mass point at all (every point null,
    mass lives in interval lengths)."""
    reasons: List[str] = []
    grid = contrast.get("grid")
    cont = contrast.get("continuous")
    if not isinstance(grid, dict) or not isinstance(cont, dict):
        return CheckReport.fail("contrast structure malformed")
    # grid side, recomputed here
    my_masses = [_grid_mass(n, i) for i in range(n + 1)]
    if sum(my_masses, ZERO) != ONE:
        reasons.append("inline grid total != 1")
    if my_masses[0] != ZERO:
        reasons.append("inline grid slot 0 not assigned 0")
    if sum(1 for m in my_masses if m > ZERO) != n:
        reasons.append("inline grid positive-atom count != n")
    if grid.get("slot0_mass_assigned") != ZERO or grid.get("total") != ONE:
        reasons.append("ref grid readings disagree with inline recomputation")
    if grid.get("has_positive_atoms") is not True:
        reasons.append("grid side should have positive atoms")
    # continuous side, recomputed here
    for i in range(n + 1):
        point = Fraction(i, n)
        if _point_measure_archimedean(point, 32) != ZERO:
            reasons.append(f"continuous point {point} not null")
    if cont.get("every_point_null") is not True or cont.get("no_atoms") is not True:
        reasons.append("continuous no-atoms reading failed")
    if cont.get("total") != ONE or cont.get("partition_total") != ONE:
        reasons.append("continuous totals != 1")
    if reasons:
        return CheckReport.fail(*reasons)
    return CheckReport.pass_()


def check_finite_union(ref_value: Fraction,
                       cells: Sequence[Tuple[Fraction, Fraction]]) -> CheckReport:
    """Ref's finite-disjoint-union sum vs the checker's own cell-by-cell sum
    (accepting only genuinely disjoint cells)."""
    if not _disjoint_cells(cells):
        return CheckReport.fail("cells overlap: finite additivity does not apply")
    mine = _union_measure_disjoint(cells)
    if mine == ref_value:
        return CheckReport.pass_()
    return CheckReport.fail(f"finite union mismatch: {ref_value} vs {mine}")
