"""Tests for the B11 shared calendar package (calendar_ref + calendar_check).

The reference implementation and the independent checker share no code; the
checker cross-examines every observed output against the standard library's
``datetime``/``calendar`` (a third, genuinely independent oracle) and its
own inline policy recomputation.  The Lean-side closed witnesses (epoch
anchors 1 / 719163 / 730120, the 17 + 38 = 55 segmentation, leap February
29/28 day counts, Q1 91/90, month-end clamping outcomes, D099 strict period
ordering, D100 back-schedule outcomes) are asserted here as plain literals
so the Python side and the Lean decide witnesses stay pinned to the same
numbers.
"""
from __future__ import annotations

import random
from datetime import date, timedelta

import pytest

from tools.full_math.implementation import calendar_check as ck
from tools.full_math.implementation import calendar_ref as uc


# ---------------------------------------------------------------------------
# synthetic materials only: fixed-seed sampler and a synthetic weekend table
# ---------------------------------------------------------------------------


def _sample_dates(count: int, seed: int = 20261011) -> list[tuple[int, int, int]]:
    rng = random.Random(seed)
    out = []
    for _ in range(count):
        d = date(1, 1, 1) + timedelta(days=rng.randrange(0, 738000))
        out.append((d.year, d.month, d.day))
    return out


def _weekend(day: int) -> bool:
    """Synthetic weekend table (epoch day mod 7 in {5, 6}); mirrors the Lean
    ``syntheticWeekend`` witness material — not any real jurisdiction."""
    return day % 7 in (5, 6)


DATES = _sample_dates(300)


# ---------------------------------------------------------------------------
# validity / leap / month lengths
# ---------------------------------------------------------------------------


@pytest.mark.parametrize("y", [1900, 2000, 2023, 2024, 2100, 1, 4, 100, 400])
def test_is_leap_against_stdlib(y):
    ok, reasons = ck.check_is_leap(y, uc.is_leap(y))
    assert ok, reasons


@pytest.mark.parametrize("y,m", [(y, m) for y in (1900, 2000, 2023, 2024)
                                 for m in range(1, 13)])
def test_month_len_against_stdlib(y, m):
    ok, reasons = ck.check_month_len(y, m, uc.month_len(y, m))
    assert ok, reasons


@pytest.mark.parametrize("y,m,d", [
    (2024, 2, 29), (2023, 2, 29), (2023, 2, 28), (2024, 2, 30),
    (2000, 2, 29), (1900, 2, 29), (2100, 2, 29),
    (2024, 4, 31), (2024, 4, 30), (2024, 12, 31), (1, 1, 1), (0, 1, 1),
    (2024, 13, 1), (2024, 0, 1), (2024, 1, 0), (2024, 1, 32),
])
def test_is_valid(y, m, d):
    ok, reasons = ck.check_is_valid(y, m, d, uc.is_valid(y, m, d))
    assert ok, reasons


# ---------------------------------------------------------------------------
# epoch day / order / day counts
# ---------------------------------------------------------------------------


@pytest.mark.parametrize("a", DATES)
def test_to_epoch_day_against_toordinal(a):
    ok, reasons = ck.check_to_epoch_day(a, uc.to_epoch_day(a))
    assert ok, reasons


def test_epoch_anchor_witnesses():
    # Lean witness_epoch_anchors: 0001-01-01 = 1, Unix epoch = 719163,
    # 2000-01-01 = 730120 (same convention as datetime.toordinal).
    assert uc.to_epoch_day((1, 1, 1)) == 1
    assert uc.to_epoch_day((1970, 1, 1)) == 719163
    assert uc.to_epoch_day((2000, 1, 1)) == 730120


@pytest.mark.parametrize("a", DATES[:80])
def test_order_against_datetime(a):
    b = DATES[137]
    ok, reasons = ck.check_date_le(a, b, uc.date_le(a, b))
    assert ok, reasons
    ok, reasons = ck.check_date_le(b, a, uc.date_le(b, a))
    assert ok, reasons


@pytest.mark.parametrize("i", range(120))
def test_days_diff_against_timedelta(i):
    a, b = DATES[i], DATES[i + 7]
    ok, reasons = ck.check_days_diff(a, b, uc.days_diff(a, b))
    assert ok, reasons


def test_days_diff_split_witness():
    # Lean witness_segmentation: 2024-01-15 -> 2024-03-10 cut at 2024-02-01
    # gives 17 + 38 = 55 (leap February accounted for).
    assert uc.days_diff((2024, 1, 15), (2024, 2, 1)) == 17
    assert uc.days_diff((2024, 2, 1), (2024, 3, 10)) == 38
    assert uc.days_diff((2024, 1, 15), (2024, 3, 10)) == 55
    assert (uc.days_diff((2024, 1, 15), (2024, 2, 1))
            + uc.days_diff((2024, 2, 1), (2024, 3, 10))
            == uc.days_diff((2024, 1, 15), (2024, 3, 10)))


def test_feb_and_q1_day_counts():
    # Lean witness_feb_days / witness_q1_counts.
    assert uc.days_diff((2024, 2, 1), (2024, 3, 1)) == 29
    assert uc.days_diff((2023, 2, 1), (2023, 3, 1)) == 28
    assert uc.inclusive_day_count((2024, 2, 1), (2024, 2, 29)) == 29
    assert uc.inclusive_day_count((2023, 2, 1), (2023, 2, 28)) == 28
    assert uc.inclusive_day_count((2024, 1, 1), (2024, 3, 31)) == 91
    assert uc.inclusive_day_count((2023, 1, 1), (2023, 3, 31)) == 90


# ---------------------------------------------------------------------------
# day arithmetic
# ---------------------------------------------------------------------------


@pytest.mark.parametrize("a,n", [(a, n) for a in DATES[:60] for n in (0, 1, 30, 180, 400)])
def test_add_days_against_timedelta(a, n):
    ok, reasons = ck.check_add_days(n, a, uc.add_days(n, a))
    assert ok, reasons


@pytest.mark.parametrize("a,n", [(a, n) for a in DATES[60:110] for n in (0, 1, 17, 90)])
def test_sub_days_and_round_trip(a, n):
    observed = None
    try:
        observed = uc.sub_days(n, a)
    except ValueError:
        observed = None
    ok, reasons = ck.check_sub_days(n, a, observed)
    assert ok, reasons
    if observed is not None:
        ok, reasons = ck.check_round_trip(n, a, observed)
        assert ok, reasons


def test_rollover_witnesses():
    # Lean witness_add_days: across leap Feb and across year end.
    assert uc.add_days(1, (2024, 2, 28)) == (2024, 2, 29)
    assert uc.add_days(1, (2023, 2, 28)) == (2023, 3, 1)
    assert uc.add_days(1, (2023, 12, 31)) == (2024, 1, 1)


def test_pred_succ_inverse_on_samples():
    for a in DATES[:150]:
        if a == (1, 1, 1):
            continue
        assert uc.pred_date(uc.succ_date(a)) == a


def test_sub_days_fail_closed_at_epoch():
    # crossing the epoch 0001-01-01 must fail closed, not clamp silently
    with pytest.raises(ValueError):
        uc.sub_days(10, (1, 1, 3))
    assert uc.sub_days(2, (1, 1, 3)) == (1, 1, 1)


# ---------------------------------------------------------------------------
# month / year arithmetic with end-of-month clamping
# ---------------------------------------------------------------------------


@pytest.mark.parametrize("a,n", [
    ((2024, 1, 31), 1), ((2023, 1, 31), 1), ((2024, 3, 15), 6),
    ((2024, 2, 29), 11), ((2024, 2, 29), 12), ((2023, 12, 31), 1),
    ((2023, 1, 30), 1), ((2024, 5, 31), 12), ((2023, 8, 31), 6),
    ((2024, 10, 31), 2), ((2025, 1, 29), 1), ((2024, 7, 31), 3),
])
def test_add_months_clamping(a, n):
    ok, reasons = ck.check_add_months(n, a, uc.add_months(n, a))
    assert ok, reasons


@pytest.mark.parametrize("a,n", [
    ((2024, 2, 29), 1), ((2024, 2, 29), 4), ((2023, 2, 28), 1),
    ((2024, 6, 15), 2), ((2024, 1, 1), 100),
])
def test_add_years_clamping(a, n):
    ok, reasons = ck.check_add_years(n, a, uc.add_years(n, a))
    assert ok, reasons


def test_clamp_witnesses():
    # Lean witness_clamp_months / witness_addCalYears_1_feb29.
    assert uc.add_months(1, (2024, 1, 31)) == (2024, 2, 29)
    assert uc.add_months(1, (2023, 1, 31)) == (2023, 2, 28)
    assert uc.add_months(6, (2024, 3, 15)) == (2024, 9, 15)
    assert uc.add_years(1, (2024, 2, 29)) == (2025, 2, 28)
    assert uc.add_months(11, (2024, 2, 29)) == (2025, 1, 29)


def test_twelve_months_equal_one_year():
    for a in DATES[:100]:
        ok, reasons = ck.check_months_equal_years(
            a, uc.add_months(12, a), uc.add_years(1, a))
        assert ok, reasons


def test_add_months_zero_identity():
    for a in DATES[:100]:
        assert uc.add_months(0, a) == a
        assert uc.add_years(0, a) == a


def test_clamp_day_idempotent():
    # Lean clampDay_idem: clamping twice equals clamping once.
    for a in DATES[:100]:
        y, m, d = a
        once = uc.clamp_day(y, m, d)
        assert uc.clamp_day(y, m, once) == once


# ---------------------------------------------------------------------------
# business-day roll / periods / back schedules / segmentation
# ---------------------------------------------------------------------------


def test_next_biz_finds_business_day():
    for d in range(739000, 739040):
        ok, reasons = ck.check_next_biz(_weekend, 7, d, uc.next_biz(_weekend, 7, d))
        assert ok, reasons


def test_roll_idempotent():
    for d in range(739000, 739040):
        ok, reasons = ck.check_roll_idempotent(
            _weekend, 7, d, uc.next_biz(_weekend, 7, d))
        assert ok, reasons


def test_d099_strict_period_order_witness():
    # Lean witness_d099_periods: anchor 2024-05-06 (epoch 739012) with
    # lengths 30/60/90/120/180 gives strictly increasing base deadlines.
    anchor = (2024, 5, 6)
    assert uc.to_epoch_day(anchor) == 739012
    lengths = [30, 60, 90, 120, 180]
    observed = [uc.to_epoch_day(uc.period_base_deadline(anchor, n)) for n in lengths]
    assert observed == [739042, 739072, 739102, 739132, 739192]
    ok, reasons = ck.check_period_order(anchor, lengths, observed)
    assert ok, reasons


def test_d099_period_deadline_hits_business_day():
    anchor = (2024, 5, 6)
    for n in (30, 60, 90, 120, 180):
        dl = uc.period_deadline(anchor, n, _weekend, 7)
        assert not _weekend(dl)
        base = uc.to_epoch_day(uc.period_base_deadline(anchor, n))
        assert base <= dl <= base + 7


def test_d100_back_schedule_witness():
    # Lean witness_d100_back: feasible 2024-03-31 minus 30 = 2024-03-01;
    # 0001-01-03 minus 10 reports a conflict (None) instead of a plan.
    assert uc.back_schedule((2024, 3, 31), 30) == (2024, 3, 1)
    assert uc.back_schedule((1, 1, 3), 10) is None


@pytest.mark.parametrize("a,b", [
    ((2024, 1, 15), (2024, 3, 10)),
    ((2023, 11, 20), (2024, 2, 5)),
    ((2024, 2, 1), (2024, 2, 29)),
    ((2023, 12, 1), (2024, 1, 31)),
    ((2024, 5, 6), (2024, 5, 6)),
    ((2024, 7, 1), (2024, 6, 1)),
])
def test_segmentation_contract(a, b):
    ok, reasons = ck.check_segmentation(a, b, uc.segment_by_month(a, b))
    assert ok, reasons


def test_segmentation_witness_55_days():
    segs = uc.segment_by_month((2024, 1, 15), (2024, 3, 10))
    assert [n for _, _, n in segs] == [17, 29, 9]
    assert sum(n for _, _, n in segs) == 55


def test_no_floats_in_module():
    # D095-D103 day counts are integer-exact; guard against float literals
    # sneaking into the reference module.
    import inspect
    src = inspect.getsource(uc)
    for token in src.split():
        if token.replace(".", "").replace("_", "").isdigit() and "." in token:
            # allow docstring-free check: numeric literals with a dot
            pytest.fail(f"float-looking literal in calendar_ref: {token}")
