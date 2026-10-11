"""Reference carrier for W1-1 / needle 54 (XU): continuous Uniform[0, 1].

Contract: docs/spec/20261007-统一法律数学模型_附录I_Lean施工明细.md I:808 --
Uniform[0,1], q(x) = (x != 0): probability 1 while false at 0.  The audit
(docs/full-math/NEEDLE_STRENGTH_AUDIT.md, needle 54 row) judged the first-wave
delivery a *difference*: Seams/UnifiedNeedlesXU.lean:179 delivered an
N-cell rational-grid surrogate (zero-mass ATOM mechanism) and the continuous
Lebesgue-measure carrier was missing.  This module is the numerical side of
that carrier; the Lean side lives in
proofs/lean/juris_lean/JurisLean/Seams/UniformContinuous.lean.

Carrier choice (mirrors the Lean file): Lebesgue measure restricted to the
closed unit interval.  Because the interval has length exactly 1, the
restriction is already a probability measure -- no renormalisation step.
The "computation" of the continuous measure is carried ALGEBRAICALLY:

* the measure of an interval event is its exact length (Fraction, never
  float, never simulated sampling);
* the measure of a single point is exactly 0 (Lebesgue has no atoms);
* the needle's truth event {x in [0,1] | x != 0} has probability exactly 1
  because its complement inside the carrier is the single point {0}, and
  single points are null.

A module-local verbatim restatement of the rational-grid surrogate's mass
function (``if i = 0 then 0 else 1/N`` -- UnifiedNeedlesXU.lean's
``xuGridMass``) is included ONLY for the mechanism-contrast reading; the
first-wave surrogate file itself is untouched and stays authoritative for
the grid side.
"""
from __future__ import annotations

from fractions import Fraction
from typing import Dict, List, Sequence, Tuple

# ---------------------------------------------------------------------------
# Carrier: Uniform[0, 1] = Lebesgue measure restricted to the closed interval.
# ---------------------------------------------------------------------------

CARRIER_LOWER = Fraction(0)
CARRIER_UPPER = Fraction(1)


def carrier_measure() -> Fraction:
    """Total mass of the carrier: the closed unit interval has length 1,
    so the restricted measure is a probability measure with no
    renormalisation step (Lean: ``volume_unit_interval``)."""
    return CARRIER_UPPER - CARRIER_LOWER


def is_probability_measure() -> bool:
    """Probability-space reading: total mass exactly 1 (Lean:
    ``uniform01_is_probability``)."""
    return carrier_measure() == Fraction(1)


# ---------------------------------------------------------------------------
# The needle's truth predicate q(x) = (x != 0) (appendix I:808).
# ---------------------------------------------------------------------------


def needle54_q(x: Fraction) -> bool:
    """q(x) = (x != 0), verbatim from the contract wording q(x) ≡ (x ≠ 0)."""
    return x != Fraction(0)


def q_zero_is_false() -> bool:
    """The 'but false at 0' half of the contract: q(0) is False (0 is a member
    of the closed carrier, see ``ae_truth_not_universal_truth``)."""
    return not needle54_q(Fraction(0))


# ---------------------------------------------------------------------------
# Interval events: measure = length, exact on Fractions.
# ---------------------------------------------------------------------------


def interval_measure(a: Fraction, b: Fraction,
                     left_closed: bool = True,
                     right_closed: bool = True) -> Fraction:
    """Lebesgue measure of an interval event intersected with the carrier.

    All four closed/open kinds share the same value because endpoints are
    single points and single points are null.  Ends are clipped to the
    carrier; an empty intersection has measure 0."""
    lo = a if a > CARRIER_LOWER else CARRIER_LOWER
    hi = b if b < CARRIER_UPPER else CARRIER_UPPER
    if lo >= hi:
        return Fraction(0)
    return hi - lo


def singleton_measure(x: Fraction) -> Fraction:
    """Lebesgue measure of the single point {x}: exactly 0 -- the no-atoms
    property (Lean: ``Real.noAtoms_volume`` / ``NoAtoms``)."""
    return Fraction(0)


def finite_point_set_measure(points: Sequence[Fraction]) -> Fraction:
    """A finite set of points is a finite union of null singletons."""
    return Fraction(0)


def pairwise_disjoint(intervals: Sequence[Tuple[Fraction, Fraction]]) -> bool:
    """Closed-or-open cells (a, b) are pairwise disjoint when their convex
    hulls do not overlap; boundary sharing is fine for Lebesgue."""
    cells = [(min(a, b), max(a, b)) for a, b in intervals]
    ordered = sorted(cells)
    for (_, hi), (lo, _) in zip(ordered, ordered[1:]):
        if lo < hi:
            return False
    return True


def finite_disjoint_union_measure(intervals: Sequence[Tuple[Fraction, Fraction]]) -> Fraction:
    """Measure of a finite disjoint union of interval events inside the
    carrier = the sum of the lengths (Lean: ``volume_finite_disjoint_Ioc``).
    Overlapping cells are rejected: finite additivity is only stated for
    disjoint unions, and silently clamping them would fabricate a mass."""
    if not pairwise_disjoint(intervals):
        raise ValueError("finite additivity applies to disjoint intervals only")
    return sum((interval_measure(a, b) for a, b in intervals), Fraction(0))


def n_equal_partition_measures(n: int) -> List[Fraction]:
    """The continuous analogue of the rational grid: the N equal cells
    (i/n, (i+1)/n] of (0, 1], each of exact measure 1/n (Lean:
    ``volume_n_equal_Ioc_partition``)."""
    if n <= 0:
        raise ValueError("partition needs a positive number of cells")
    cell = Fraction(1, n)
    return [cell] * n


# ---------------------------------------------------------------------------
# Needle 54 continuous reading: probability 1 but not universal truth.
# ---------------------------------------------------------------------------


def truth_event_measure() -> Fraction:
    """Measure of {x in [0,1] | q x} = measure of (0, 1] = 1: the carrier
    minus the null point {0} (Lean: ``ae_truth_not_universal_truth_uniform``,
    second conjunct)."""
    return interval_measure(CARRIER_LOWER, CARRIER_UPPER) - singleton_measure(Fraction(0))


def falsity_event_points() -> List[Fraction]:
    """The falsity set {x in [0,1] | not (q x)} = {0} (Lean: fourth/fifth
    conjuncts -- 0 is IN the carrier and q is false there)."""
    return [Fraction(0)]


def falsity_event_measure() -> Fraction:
    return finite_point_set_measure(falsity_event_points())


def event_decomposition() -> Dict[str, object]:
    """Truth event union falsity set = carrier, disjoint; measures add up
    (Lean: ``uniform_event_split``)."""
    return {
        "truth_measure": truth_event_measure(),
        "falsity_measure": falsity_event_measure(),
        "total": truth_event_measure() + falsity_event_measure(),
        "carrier": carrier_measure(),
        "disjoint": True,
    }


def ae_truth_not_universal_truth() -> Dict[str, object]:
    """The full continuous reading of needle 54: P({x | q x}) = 1 while q is
    false at the carrier point 0 -- probability-1 truth that is NOT universal
    truth, now on the continuous Lebesgue carrier (not the rational grid)."""
    return {
        "carrier_is_probability": is_probability_measure(),
        "truth_event_measure": truth_event_measure(),
        "falsity_event_measure": falsity_event_measure(),
        "falsity_witness_in_carrier": CARRIER_LOWER <= Fraction(0) <= CARRIER_UPPER,
        "q_false_at_witness": not needle54_q(Fraction(0)),
        "falsity_points": falsity_event_points(),
    }


# ---------------------------------------------------------------------------
# Mechanism contrast: rational-grid surrogate (kept verbatim, zero coupling).
# ---------------------------------------------------------------------------


def grid_mass(n: int, i: int) -> Fraction:
    """Verbatim restatement of the surrogate's mass function
    (UnifiedNeedlesXU.lean ``xuGridMass``): slot 0 is ASSIGNED mass 0 -- a
    zero-mass atom -- and the other n slots carry 1/n each."""
    if n <= 0:
        raise ValueError("grid needs a positive number of cells")
    if i == 0:
        return Fraction(0)
    return Fraction(1, n)


def grid_total_mass(n: int) -> Fraction:
    return sum((grid_mass(n, i) for i in range(n + 1)), Fraction(0))


def grid_truth_event_mass(n: int) -> Fraction:
    return sum((grid_mass(n, i) for i in range(1, n + 1)), Fraction(0))


def mechanism_contrast(n: int) -> Dict[str, object]:
    """The two mechanisms side by side (Lean: ``rational_grid_atom_vs_
    lebesgue_no_atoms``).

    Grid surrogate: the falsifying slot 0 IS in the carrier and its zero
    mass is an ASSIGNMENT of the mass function (exactly one slot gets 0; n
    slots get positive atom mass).

    Continuous carrier: EVERY point is null -- a derived property of
    Lebesgue measure (NoAtoms), not an assignment -- and the mass lives in
    interval lengths."""
    if n <= 0:
        raise ValueError("contrast needs a positive number of cells")
    positive_atom_slots = [i for i in range(n + 1) if grid_mass(n, i) > 0]
    return {
        "grid": {
            "slot0_in_carrier": True,
            "slot0_mass_assigned": grid_mass(n, 0),
            "total": grid_total_mass(n),
            "truth_event_mass": grid_truth_event_mass(n),
            "positive_atom_slots": positive_atom_slots,
            "has_positive_atoms": len(positive_atom_slots) > 0,
        },
        "continuous": {
            "every_point_null": all(
                singleton_measure(Fraction(i, n)) == Fraction(0) for i in range(n + 1)
            ),
            "no_atoms": all(
                singleton_measure(Fraction(i, n)) == Fraction(0)
                for i in range(-2, n + 3)
            ),
            "total": carrier_measure(),
            "partition_total": sum(n_equal_partition_measures(n), Fraction(0)),
        },
    }
