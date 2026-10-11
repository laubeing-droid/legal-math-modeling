"""Continuous Uniform[0,1] carrier tests (W1-1, needle 54, I:808).

Needle 54 ae_truth_not_universal_truth, continuous version: on the Lebesgue
carrier (volume restricted to the closed unit interval, total mass exactly 1),
the truth event {x in [0,1] | q x} with q(x) = (x != 0) has probability
exactly 1 while q is FALSE at the carrier point 0 -- probability-1 truth that
is not universal truth, now via the atomless Lebesgue mechanism and NOT the
first-wave rational-grid surrogate (zero-mass atom).

The numerical side carries the continuous measure algebraically: exact
Fraction interval lengths, exactly-null single points, no float sampling.

Receipt note (W1-wave batch form): the 60-needle table has no slot in
tools/full_math/spec/REQUIREMENTS.json (217 FullMath ids only), so there is
no validate_binding row for W1:1; the batch receipt is recorded in
.local/agent_W14_uniform_cont_report.md per the W1-wave convention, and this
suite pins the Lean sources by name.
"""
from fractions import Fraction
from pathlib import Path

import pytest

from tools.full_math.implementation import uniform_cont_ref as R
from tools.full_math.implementation import uniform_cont_check as K

ZERO = Fraction(0)
ONE = Fraction(1)

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[2]

LEAN_MODULE = (REPO / 'proofs/lean/juris_lean/JurisLean/Seams/'
               'UniformContinuous.lean')

LEAN_THEOREMS = (
    'ae_truth_not_universal_truth_uniform',
    'uniform01_truth_event',
    'rational_grid_atom_vs_lebesgue_no_atoms',
    'uniform01_is_probability',
    'volume_n_equal_Ioc_partition',
    'volume_finite_disjoint_Ioc',
    'grid_mass_sum_one',
)


# ---------------------------------------------------------------------------
# Source pinning (W1-14 batch receipt anchor form)
# ---------------------------------------------------------------------------


def test_lean_module_pins_needle54_continuous():
    """The Lean contract file exists and declares the continuous needle-54
    theorems by name (main theorem + probability-space reading + mechanism
    contrast)."""
    text = LEAN_MODULE.read_text(encoding='utf-8')
    for name in LEAN_THEOREMS:
        assert f'theorem {name}' in text, name


def test_lean_module_declares_no_sorry():
    text = LEAN_MODULE.read_text(encoding='utf-8')
    assert 'sorry' not in text
    assert 'axiom ' not in text
    assert 'native_decide' not in text


# ---------------------------------------------------------------------------
# Carrier: probability measure, no renormalisation
# ---------------------------------------------------------------------------


def test_carrier_total_mass_is_exactly_one():
    assert R.carrier_measure() == Fraction(1)
    assert R.is_probability_measure() is True


def test_carrier_probability_check_via_partitions():
    report = K.check_carrier_probability(R.carrier_measure())
    assert report.ok, report.reasons


# ---------------------------------------------------------------------------
# Interval events: measure = exact length (Fractions, never floats)
# ---------------------------------------------------------------------------


@pytest.mark.parametrize('a,b', [
    (Fraction(0), Fraction(1)),
    (Fraction(1, 10), Fraction(3, 10)),   # would be inexact in binary floats
    (Fraction(1, 3), Fraction(2, 3)),
    (Fraction(1, 7), Fraction(5, 7)),
    (Fraction(1), Fraction(1)),           # degenerate point interval
])
def test_interval_measure_is_exact_length(a, b):
    assert R.interval_measure(a, b) == b - a
    assert K.check_interval_measure(a, b, R.interval_measure(a, b)).ok


@pytest.mark.parametrize('a,b', [
    (Fraction(-1, 3), Fraction(1, 2)),    # clipped at 0
    (Fraction(1, 4), Fraction(3, 2)),     # clipped at 1
    (Fraction(-2), Fraction(5)),          # fully covers the carrier
])
def test_interval_measure_clips_to_carrier(a, b):
    clipped = R.interval_measure(a, b)
    assert ZERO <= clipped <= ONE
    assert K.check_interval_measure(a, b, clipped).ok


@pytest.mark.parametrize('a,b', [
    (Fraction(1, 5), Fraction(4, 5)),
    (Fraction(0), Fraction(1)),
])
def test_all_interval_kinds_agree_endpoints_are_null(a, b):
    """Closed/half-open/open share the same measure: endpoints are single
    points and single points are null (Lebesgue no-atoms)."""
    closed = R.interval_measure(a, b, True, True)
    ioc = R.interval_measure(a, b, False, True)
    icc = R.interval_measure(a, b, True, True)
    ioo = R.interval_measure(a, b, False, False)
    ico = R.interval_measure(a, b, True, False)
    assert closed == ioc == icc == ioo == ico == b - a
    assert K.check_all_kinds_equal(closed, ioc, icc, ioo).ok


def test_empty_and_reversed_intervals_are_zero():
    assert R.interval_measure(Fraction(1, 2), Fraction(1, 2)) == 0
    assert R.interval_measure(Fraction(3, 4), Fraction(1, 4)) == 0


def test_float_trap_exactness():
    """The classic binary-float trap (0.3 - 0.1 != 0.2) cannot happen: the
    algebra is exact on Fractions by construction."""
    assert R.interval_measure(Fraction(1, 10), Fraction(3, 10)) == Fraction(1, 5)
    assert (Fraction(3, 10) - Fraction(1, 10)) == Fraction(1, 5)
    assert R.n_equal_partition_measures(3) == [Fraction(1, 3)] * 3


# ---------------------------------------------------------------------------
# Single points are null (atomless carrier)
# ---------------------------------------------------------------------------


@pytest.mark.parametrize('x', [Fraction(0), Fraction(1), Fraction(1, 2),
                               Fraction(1, 6), Fraction(5, 6), Fraction(1, 1000)])
def test_single_points_are_exactly_null(x):
    assert R.singleton_measure(x) == Fraction(0)
    assert K.check_point_null(R.singleton_measure(x)).ok


def test_finite_point_sets_are_null():
    pts = [Fraction(i, 7) for i in range(8)]
    assert R.finite_point_set_measure(pts) == Fraction(0)


# ---------------------------------------------------------------------------
# Needle 54 continuous reading: probability 1 but not universal truth
# ---------------------------------------------------------------------------


def test_needle54_truth_event_probability_is_one():
    assert R.truth_event_measure() == Fraction(1)
    assert R.falsity_event_measure() == Fraction(0)
    report = K.check_truth_event(R.truth_event_measure(), R.falsity_event_measure())
    assert report.ok, report.reasons


def test_needle54_full_reading():
    reading = R.ae_truth_not_universal_truth()
    # probability 1 ...
    assert reading['truth_event_measure'] == Fraction(1)
    assert reading['carrier_is_probability'] is True
    # ... but NOT universal truth: q is false at the carrier point 0
    assert reading['falsity_witness_in_carrier'] is True
    assert reading['q_false_at_witness'] is True
    assert reading['falsity_points'] == [Fraction(0)]
    assert reading['falsity_event_measure'] == Fraction(0)
    assert R.q_zero_is_false() is True
    assert R.needle54_q(Fraction(0)) is False
    assert R.needle54_q(Fraction(1, 1000)) is True
    report = K.check_needle54(reading)
    assert report.ok, report.reasons


def test_needle54_event_decomposition():
    d = R.event_decomposition()
    assert d['truth_measure'] == Fraction(1)
    assert d['falsity_measure'] == Fraction(0)
    assert d['total'] == d['carrier'] == Fraction(1)
    assert d['disjoint'] is True


def test_needle54_is_not_universal_truth_on_any_neighborhood():
    """Not-universality is witnessed by points arbitrarily close to 0 from
    the right: every neighborhood of 0 inside the carrier contains points
    where q fails (only 0 itself), while carrying positive measure."""
    for k in (1, 2, 3, 10, 100):
        right = R.interval_measure(Fraction(0), Fraction(1, k))
        assert right == Fraction(1, k)          # positive measure next to the false point
        assert R.needle54_q(Fraction(1, k))     # and q is TRUE there
    assert not R.needle54_q(Fraction(0))        # q fails exactly at 0


# ---------------------------------------------------------------------------
# Finite disjoint unions and the continuous N-equal partition
# ---------------------------------------------------------------------------


def test_finite_disjoint_union_measures():
    third = Fraction(1, 3)
    cells = [((ZERO + i * third), (ZERO + (i + 1) * third)) for i in range(3)]
    val = R.finite_disjoint_union_measure(cells)
    assert val == Fraction(1)
    assert K.check_finite_union(val, cells).ok

    irregular = [(Fraction(0), Fraction(1, 4)), (Fraction(1, 2), Fraction(3, 4))]
    val2 = R.finite_disjoint_union_measure(irregular)
    assert val2 == Fraction(1, 2)
    assert K.check_finite_union(val2, irregular).ok


def test_overlapping_union_is_rejected():
    """Finite additivity applies to DISJOINT unions only; overlapping cells
    must be rejected, not silently clamped (fabricated mass)."""
    overlap = [(Fraction(0), Fraction(1, 2)), (Fraction(1, 4), Fraction(1))]
    with pytest.raises(ValueError):
        R.finite_disjoint_union_measure(overlap)


@pytest.mark.parametrize('n', [1, 2, 3, 4, 7, 12, 100])
def test_n_equal_partition_sums_to_one(n):
    cells = R.n_equal_partition_measures(n)
    assert len(cells) == n
    assert all(c == Fraction(1, n) for c in cells)
    assert sum(cells, Fraction(0)) == Fraction(1)


# ---------------------------------------------------------------------------
# Mechanism contrast: rational-grid surrogate vs continuous carrier
# ---------------------------------------------------------------------------


@pytest.mark.parametrize('n', [1, 3, 6, 10])
def test_grid_mechanism_zero_mass_atom(n):
    """The surrogate's mechanism: slot 0 IS in the carrier and its zero mass
    is an ASSIGNMENT of the mass function (zero-mass atom); the other n
    slots carry positive atom mass."""
    assert R.grid_mass(n, 0) == Fraction(0)
    for i in range(1, n + 1):
        assert R.grid_mass(n, i) == Fraction(1, n)
    assert R.grid_total_mass(n) == Fraction(1)
    assert R.grid_truth_event_mass(n) == Fraction(1)


def test_mechanism_contrast_two_different_mechanisms(n=6):
    """Same proposition, two mechanisms: grid = one ASSIGNED zero-mass atom
    plus n positive atoms; continuous = NO positive-mass point at all (every
    point null by the atomless property), mass in interval lengths."""
    c = R.mechanism_contrast(n)
    assert c['grid']['slot0_mass_assigned'] == Fraction(0)
    assert c['grid']['has_positive_atoms'] is True          # grid HAS atoms
    assert len(c['grid']['positive_atom_slots']) == n
    assert c['continuous']['every_point_null'] is True
    assert c['continuous']['no_atoms'] is True              # continuous has NONE
    assert c['continuous']['total'] == Fraction(1)
    assert c['continuous']['partition_total'] == Fraction(1)
    report = K.check_mechanism_contrast(c, n)
    assert report.ok, report.reasons


def test_mechanisms_are_genuinely_different(n=6):
    """The grid's positive-mass slots would be positive atoms under the
    continuous measure too if they were points -- but every point is null
    there: the two readings assign mass by different mechanisms, and only the
    grid has positive point masses."""
    for i in range(1, n + 1):
        point = Fraction(i, n)
        assert R.grid_mass(n, i) > Fraction(0)
        assert R.singleton_measure(point) == Fraction(0)
