"""Independent calendar checker for the B11 shared calendar package.

Contract-checks the reference implementation's outputs the way the repo's
independent checkers do (v21/checker.py pattern): this module shares NO code
with ``calendar_ref`` (it never imports it), takes no witness callbacks, and
never uses the main implementation to generate expectations.  Its third
oracle is the standard library's ``datetime.date`` (a genuinely independent
proleptic-Gregorian implementation; ``toordinal`` uses the same 0001-01-01
= 1 convention) plus its own inline recomputation of the policy rules
(end-of-month clamping, one-shot month addition, fuel-bounded business-day
roll, epoch-bounded backward scheduling).

Each ``check_*`` returns ``(ok, reasons)``: ``ok`` is True exactly when the
observed output satisfies the contract on the given input.
"""
from __future__ import annotations

import calendar as _stdcalendar
from datetime import date, timedelta
from typing import Callable, Optional

_Date = tuple[int, int, int]


def _fail(reasons, msg):
    return tuple(reasons) + (msg,)


def _to_dt(a: _Date) -> date:
    return date(a[0], a[1], a[2])


def _from_dt(x: date) -> _Date:
    return (x.year, x.month, x.day)


# ---------------------------------------------------------------------------
# validity / leap / month lengths (checked against the stdlib calendar)
# ---------------------------------------------------------------------------


def check_is_leap(y: int, observed: bool) -> tuple[bool, tuple]:
    reasons = ()
    expected = _stdcalendar.isleap(y)
    if observed != expected:
        reasons = _fail(reasons, f"is_leap({y})={observed} disagrees with "
                                 f"calendar.isleap={expected}")
    return (not reasons, reasons)


def check_month_len(y: int, m: int, observed: int) -> tuple[bool, tuple]:
    reasons = ()
    if not (1 <= m <= 12):
        reasons = _fail(reasons, "month out of 1..12")
        return (not reasons, reasons)
    expected = _stdcalendar.monthrange(y, m)[1]
    if observed != expected:
        reasons = _fail(reasons, f"month_len({y},{m})={observed} disagrees with "
                                 f"calendar.monthrange={expected}")
    return (not reasons, reasons)


def check_is_valid(y: int, m: int, d: int, observed: bool) -> tuple[bool, tuple]:
    reasons = ()
    try:
        date(y, m, d)
        constructible = True
    except ValueError:
        constructible = False
    if observed != constructible:
        reasons = _fail(reasons, f"is_valid({y},{m},{d})={observed} disagrees with "
                                 f"datetime constructibility={constructible}")
    if observed and y < 1:
        reasons = _fail(reasons, "year below the proleptic epoch 0001 accepted")
    return (not reasons, reasons)


# ---------------------------------------------------------------------------
# epoch day / order / day counts (checked against datetime.toordinal)
# ---------------------------------------------------------------------------


def check_to_epoch_day(a: _Date, observed: int) -> tuple[bool, tuple]:
    reasons = ()
    expected = _to_dt(a).toordinal()
    if observed != expected:
        reasons = _fail(reasons, f"to_epoch_day({a})={observed} disagrees with "
                                 f"datetime.toordinal={expected}")
    return (not reasons, reasons)


def check_days_diff(a: _Date, b: _Date, observed: int) -> tuple[bool, tuple]:
    reasons = ()
    expected = (_to_dt(b) - _to_dt(a)).days
    if observed != expected:
        reasons = _fail(reasons, f"days_diff({a},{b})={observed} disagrees with "
                                 f"timedelta.days={expected}")
    return (not reasons, reasons)


def check_inclusive_day_count(a: _Date, b: _Date, observed: int) -> tuple[bool, tuple]:
    reasons = ()
    expected = (_to_dt(b) - _to_dt(a)).days + 1
    if observed != expected:
        reasons = _fail(reasons, f"inclusive_day_count({a},{b})={observed} disagrees "
                                 f"with timedelta.days+1={expected}")
    if observed < 1:
        reasons = _fail(reasons, "inclusive count below 1")
    return (not reasons, reasons)


def check_date_le(a: _Date, b: _Date, observed: bool) -> tuple[bool, tuple]:
    reasons = ()
    expected = _to_dt(a) <= _to_dt(b)
    if observed != expected:
        reasons = _fail(reasons, f"date_le({a},{b})={observed} disagrees with "
                                 f"datetime order={expected}")
    return (not reasons, reasons)


# ---------------------------------------------------------------------------
# day arithmetic (succ/pred/add/sub; checked against timedelta)
# ---------------------------------------------------------------------------


def check_add_days(n: int, a: _Date, observed: _Date) -> tuple[bool, tuple]:
    reasons = ()
    expected = _from_dt(_to_dt(a) + timedelta(days=n))
    if observed != expected:
        reasons = _fail(reasons, f"add_days({n},{a})={observed} disagrees with "
                                 f"timedelta={expected}")
    return (not reasons, reasons)


def check_sub_days(n: int, a: _Date, observed: Optional[_Date]) -> tuple[bool, tuple]:
    reasons = ()
    target = _to_dt(a) - timedelta(days=n)
    if target.toordinal() < 1:
        if observed is not None:
            reasons = _fail(reasons, "back-shift across the calendar epoch returned "
                                     "a date instead of failing closed")
    else:
        if observed is None:
            reasons = _fail(reasons, "feasible back-shift reported as conflict")
        elif observed != _from_dt(target):
            reasons = _fail(reasons, f"sub_days({n},{a})={observed} disagrees with "
                                     f"timedelta={_from_dt(target)}")
    return (not reasons, reasons)


def check_round_trip(n: int, a: _Date,
                     observed: Optional[_Date]) -> tuple[bool, tuple]:
    """倒排往返：先退 n 天再进 n 天回到原日期（Lean ``sub_add_cancel`` 的合同）。"""
    reasons = ()
    if observed is None:
        reasons = _fail(reasons, "infeasible sub_days inside round trip")
        return (not reasons, reasons)
    expected = a
    forward = _from_dt(_to_dt(observed) + timedelta(days=n))
    if forward != expected:
        reasons = _fail(reasons, f"round trip {a} -> {observed} + {n}d = {forward}")
    return (not reasons, reasons)


# ---------------------------------------------------------------------------
# month / year arithmetic with end-of-month clamping
# (independent inline recomputation, no datetime shortcut exists for this policy)
# ---------------------------------------------------------------------------


def _expected_add_months(n: int, a: _Date) -> _Date:
    t = (a[1] - 1) + n
    y2 = a[0] + t // 12
    m2 = t % 12 + 1
    last = _stdcalendar.monthrange(y2, m2)[1]
    return (y2, m2, min(a[2], last))


def check_add_months(n: int, a: _Date, observed: _Date) -> tuple[bool, tuple]:
    reasons = ()
    expected = _expected_add_months(n, a)
    if observed != expected:
        reasons = _fail(reasons, f"add_months({n},{a})={observed} disagrees with "
                                 f"end-of-month clamping rule={expected}")
    # the clamped day never exceeds the source day nor the target month end
    if observed[2] > a[2]:
        reasons = _fail(reasons, "clamped day exceeded the original day")
    if observed[2] > _stdcalendar.monthrange(observed[0], observed[1])[1]:
        reasons = _fail(reasons, "clamped day exceeded the target month end")
    return (not reasons, reasons)


def check_add_years(n: int, a: _Date, observed: _Date) -> tuple[bool, tuple]:
    reasons = ()
    expected = _expected_add_months(12 * n, a)
    if observed != expected:
        reasons = _fail(reasons, f"add_years({n},{a})={observed} disagrees with "
                                 f"12-month clamping rule={expected}")
    if observed[1] != a[1]:
        reasons = _fail(reasons, "year addition moved the month")
    return (not reasons, reasons)


def check_months_equal_years(a: _Date,
                             observed12: _Date,
                             observed_year1: _Date) -> tuple[bool, tuple]:
    """12 个月一次性推进 = 1 年（Lean ``addCalMonths_12_eq_addCalYears_1``）。"""
    reasons = ()
    if observed12 != observed_year1:
        reasons = _fail(reasons, f"add_months(12)={observed12} != "
                                 f"add_years(1)={observed_year1}")
    return (not reasons, reasons)


# ---------------------------------------------------------------------------
# business-day roll / period deadlines / segmentation
# ---------------------------------------------------------------------------


def check_next_biz(holiday: Callable[[int], bool], fuel: int, d: int,
                   observed: int) -> tuple[bool, tuple]:
    reasons = ()
    if not (d <= observed <= d + fuel):
        reasons = _fail(reasons, f"roll {d} -> {observed} escapes the fuel window "
                                 f"[{d}, {d + fuel}]")
    if observed < d + fuel and holiday(observed):
        reasons = _fail(reasons, "roll stopped on a holiday inside the window")
    if observed == d + fuel and holiday(observed) and any(
            not holiday(d + k) for k in range(fuel + 1)):
        reasons = _fail(reasons, "roll hit fuel end although a business day existed "
                                 "in the window")
    return (not reasons, reasons)


def check_roll_idempotent(holiday: Callable[[int], bool], fuel: int, d: int,
                          observed: int) -> tuple[bool, tuple]:
    """顺延幂等：再顺延一次不动（Lean ``roll_idempotent`` 的合同）。"""
    reasons = ()
    twice = observed
    for _ in range(fuel):
        if not holiday(twice):
            break
        twice += 1
    if twice != observed:
        reasons = _fail(reasons, f"roll not idempotent: {observed} -> {twice}")
    return (not reasons, reasons)


def check_period_order(anchor: _Date, lengths: list[int],
                       observed: list[int]) -> tuple[bool, tuple]:
    """同锚点下更长期限 ⇒ 更晚基础期限（Lean ``base_strict_order``）。"""
    reasons = ()
    if len(lengths) != len(observed):
        reasons = _fail(reasons, "lengths/observed arity mismatch")
        return (not reasons, reasons)
    for i in range(len(lengths)):
        expected = _to_dt(anchor).toordinal() + lengths[i]
        if observed[i] != expected:
            reasons = _fail(reasons, f"base deadline for length {lengths[i]} is "
                                     f"{observed[i]}, expected {expected}")
    for i in range(len(lengths) - 1):
        if lengths[i] < lengths[i + 1] and not observed[i] < observed[i + 1]:
            reasons = _fail(reasons, f"strict order broken between lengths "
                                     f"{lengths[i]} and {lengths[i + 1]}")
    return (not reasons, reasons)


def check_back_schedule(deadline: _Date, lead: int,
                        observed: Optional[_Date]) -> tuple[bool, tuple]:
    """倒排冲突判据 + 可执行性（Lean ``backSchedule_none_iff`` /
    ``backSchedule_some_addBack``）。"""
    reasons = ()
    conflict = _to_dt(deadline).toordinal() - lead < 1
    if conflict and observed is not None:
        reasons = _fail(reasons, "infeasible back schedule returned a plan")
    if not conflict:
        if observed is None:
            reasons = _fail(reasons, "feasible back schedule reported a conflict")
        else:
            forward = _from_dt(_to_dt(observed) + timedelta(days=lead))
            if forward != deadline:
                reasons = _fail(reasons, f"back schedule {observed} + {lead}d = "
                                         f"{forward} != deadline {deadline}")
    return (not reasons, reasons)


def check_segmentation(a: _Date, b: _Date,
                       observed: list[tuple[_Date, _Date, int]]) -> tuple[bool, tuple]:
    """分段计息合同：段按自然月、首尾相接、左闭右开计息天数相加 = 整段差
    （Lean ``daysDiff_split`` 的列表形；非末段含月末→次月 1 日的过渡日）。"""
    reasons = ()
    if a >= b:
        # [a, b) convention: a == b is an empty accrual period (zero segments)
        if observed:
            reasons = _fail(reasons, "empty accrual period produced segments")
        return (not reasons, reasons)
    if not observed:
        reasons = _fail(reasons, "nonempty period produced no segments")
        return (not reasons, reasons)
    if observed[0][0] != a:
        reasons = _fail(reasons, "first segment does not start at the period start")
    if observed[-1][1] != b:
        reasons = _fail(reasons, "last segment does not end at the period end")
    total = 0
    for i, (s, e, n) in enumerate(observed):
        if e < s:
            reasons = _fail(reasons, f"segment {i} has reversed endpoints")
        expected_n = (_to_dt(e) - _to_dt(s)).days + (0 if e == b else 1)
        if n != expected_n:
            reasons = _fail(reasons, f"segment {i} day count {n} != accrual "
                                     f"{expected_n}")
        # 段止必须是段起所在月的月末，或者整段末 b
        eom = (s[0], s[1], _stdcalendar.monthrange(s[0], s[1])[1])
        if e != eom and e != b:
            reasons = _fail(reasons, f"segment {i} end {e} is neither the month end "
                                     f"{eom} nor the period end {b}")
        if i + 1 < len(observed) and observed[i + 1][0] != _from_dt(_to_dt(e) + timedelta(days=1)):
            reasons = _fail(reasons, f"segment {i + 1} does not start the day after "
                                     f"segment {i} ends")
        total += n
    whole = (_to_dt(b) - _to_dt(a)).days
    if total != whole:
        reasons = _fail(reasons, f"segment sum {total} != whole period diff {whole}")
    return (not reasons, reasons)
