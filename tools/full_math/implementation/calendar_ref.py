"""Shared calendar construction package for B11 (D095-D103) and the
W2-B N01 backfill — Python side.

Mirrors ``JurisLean.Seams.UnifiedCalendar`` (the Lean construction whose
formal statements are proved there):

* proleptic-Gregorian epoch day ``to_epoch_day`` with the same convention
  as ``datetime.date.toordinal`` (0001-01-01 = day 1); the closed-form
  year term ``days_before_year`` is computed with exact integer arithmetic
  (no floats anywhere);
* ``days_diff`` / inclusive day counts (exact ints);
* day arithmetic via full month/year rollover successor/predecessor
  iteration (``add_days`` = n-fold successor), backward scheduling with a
  conflict report instead of a silently clamped plan;
* month/year addition with the end-of-month clamping rule
  (``clamp_day = min(day, month_len)``) — the same banking-standard choice
  the Lean file discloses, and the same one-shot (non-iterative) month
  semantics: "n months later" takes the same day of the target month when
  it exists, else the target month's last day;
* business-day roll with a table-driven holiday calendar as an EXTERNAL
  parameter and an explicit fuel bound (the Lean ``nextBiz``);
* period specs (anchor / length / holiday / roll fuel) and back schedules.

All functions take/return plain ints and tuples ``(y, m, d)``; the
``CalDate`` alias documents intent. No datetime import here: the reference
implements the arithmetic itself (the independent checker is the one that
cross-examines it against ``datetime``).
"""
from __future__ import annotations

from typing import Callable, Optional

# 年月日三元组（Lean ``CalDate`` 的 Python 侧形状）。
CalDate = tuple[int, int, int]


def is_leap(y: int) -> bool:
    """格雷果里闰年规则（Lean ``JurisLean.FullMath.Numeric.leap`` 的镜像）。"""
    return (y % 4 == 0 and y % 100 != 0) or y % 400 == 0


def year_len(y: int) -> int:
    """年长：闰年 366、平年 365（Lean ``yearLen``）。"""
    return 366 if is_leap(y) else 365


_MONTH_LEN = {1: 31, 2: 28, 3: 31, 4: 30, 5: 31, 6: 30,
              7: 31, 8: 31, 9: 30, 10: 31, 11: 30, 12: 31}


def month_len(y: int, m: int) -> int:
    """月长表；二月按闰年分岔（Lean ``monthLen``，域外月份为 0）。"""
    if m == 2:
        return 29 if is_leap(y) else 28
    return _MONTH_LEN.get(m, 0)


def is_valid(y: int, m: int, d: int) -> bool:
    """有效性：年 ≥ 1 且 1 ≤ 月 ≤ 12 且 1 ≤ 日 ≤ 月长（Lean ``CalDate.Valid``）。"""
    return y >= 1 and 1 <= m <= 12 and 1 <= d <= month_len(y, m)


def days_before_year(y: int) -> int:
    """年起点之前的历元日数（Lean ``daysBeforeYear`` 闭式，纯整数）。"""
    t = y - 1
    return 365 * t + t // 4 - t // 100 + t // 400


def day_of_year(y: int, m: int, d: int) -> int:
    """年内日序 = 前月累计 + 日（Lean ``dayOfYear``）。"""
    return sum(month_len(y, k) for k in range(1, m)) + d


def to_epoch_day(a: CalDate) -> int:
    """日期 → 历元日（0001-01-01 = 1，与 ``datetime.toordinal`` 同约定）。"""
    y, m, d = a
    return days_before_year(y) + day_of_year(y, m, d)


def days_diff(a: CalDate, b: CalDate) -> int:
    """天数差（含 b 不含 a 的差计数；Lean ``daysDiff``，精确整数）。"""
    return to_epoch_day(b) - to_epoch_day(a)


def inclusive_day_count(a: CalDate, b: CalDate) -> int:
    """闭区间含首尾日计数（D095 按日计息的"含头含尾"口径）。"""
    return days_diff(a, b) + 1


def date_le(a: CalDate, b: CalDate) -> bool:
    """历元日序即日期序（Lean 皇冠定理 ``epoch_le_iff_lex`` 的计算侧）。"""
    return to_epoch_day(a) <= to_epoch_day(b)


def succ_date(a: CalDate) -> CalDate:
    """后继日期：日内 +1；月末跳下月 1 日；年末跳下年 1 月 1 日。"""
    y, m, d = a
    if d < month_len(y, m):
        return (y, m, d + 1)
    if m < 12:
        return (y, m + 1, 1)
    return (y + 1, 1, 1)


def pred_date(a: CalDate) -> CalDate:
    """前驱日期：日内 −1；月初退上月末；年初退上年 12 月 31 日。"""
    y, m, d = a
    if 1 < d:
        return (y, m, d - 1)
    if 1 < m:
        return (y, m - 1, month_len(y, m - 1))
    return (y - 1, 12, 31)


def add_days(n: int, a: CalDate) -> CalDate:
    """日加法 = 后继的 n 次迭代（Lean ``addCalDays``；n ≥ 0）。"""
    if n < 0:
        raise ValueError("add_days expects n >= 0")
    for _ in range(n):
        a = succ_date(a)
    return a


def sub_days(n: int, a: CalDate) -> CalDate:
    """日减法 = 前驱的 n 次迭代（Lean ``subCalDays``；适用域=不越过历元，
    越界抛错——与 Lean ``subCalDays_epoch`` 的适用域一致）。"""
    if n < 0:
        raise ValueError("sub_days expects n >= 0")
    if to_epoch_day(a) - n < 1:
        raise ValueError("back-shift crosses the calendar epoch 0001-01-01")
    for _ in range(n):
        a = pred_date(a)
    return a


def clamp_day(y: int, m: int, d: int) -> int:
    """末日钳制：目标月放不下的日压到目标月末（Lean ``clampDay``）。"""
    return min(d, month_len(y, m))


def add_months(n: int, a: CalDate) -> CalDate:
    """月加法（一次性语义，非逐月迭代——与 Lean ``addCalMonths`` 同口径）。"""
    if n < 0:
        raise ValueError("add_months expects n >= 0")
    y, m, d = a
    t = (m - 1) + n
    y2, m2 = y + t // 12, t % 12 + 1
    return (y2, m2, clamp_day(y2, m2, d))


def add_years(n: int, a: CalDate) -> CalDate:
    """年加法（同月同日，末日钳制处理 2/29 → 平年 2/28；Lean ``addCalYears``）。"""
    if n < 0:
        raise ValueError("add_years expects n >= 0")
    y, m, d = a
    return (y + n, m, clamp_day(y + n, m, d))


def next_biz(holiday: Callable[[int], bool], fuel: int, d: int) -> int:
    """带燃料的营业日顺延（Lean ``nextBiz``；节假日表是外部参数）。"""
    for _ in range(fuel):
        if not holiday(d):
            return d
        d += 1
    return d


def segment_by_month(a: CalDate, b: CalDate) -> list[tuple[CalDate, CalDate, int]]:
    """按自然月把期间 [a, b) 切成段（D095 分段计息的结构件）：
    每段 (段起, 段止, 段计息天数)。计息天数为左闭右开口径——非末段含
    "月末→次月 1 日"的过渡日（段天数 = days_diff(段起, 次段起)），末段止于 b
    （b 当日不计息）；各段天数相加恰为 days_diff(a, b)（Lean ``daysDiff_split``
    的列表形）。前提：a ≤ b（否则返回空表，调用方按冲突处理）。"""
    if date_le(b, a):
        return []
    segs: list[tuple[CalDate, CalDate, int]] = []
    cur = a
    while date_le(cur, b):
        y, m, _ = cur
        eom = (y, m, month_len(y, m))
        stop = eom if date_le(eom, b) else b
        accrual = days_diff(cur, stop) + (0 if stop == b else 1)
        segs.append((cur, stop, accrual))
        cur = succ_date(eom)
    return segs


def period_base_deadline(anchor: CalDate, length: int) -> CalDate:
    """基础期限 = 锚点 + length 天（Lean ``PeriodSpec.baseDeadline``）。"""
    return add_days(length, anchor)


def period_deadline(anchor: CalDate, length: int,
                    holiday: Callable[[int], bool], roll_fuel: int) -> int:
    """期限 = 基础期限经营业日顺延（Lean ``PeriodSpec.deadline``，ℤ 历元日）。"""
    return next_biz(holiday, roll_fuel, to_epoch_day(period_base_deadline(anchor, length)))


def back_schedule(deadline: CalDate, lead: int) -> Optional[CalDate]:
    """倒排：从期限日回退 lead 天；越过历元时报冲突 None（Lean ``backSchedule``）。"""
    if lead + 1 <= to_epoch_day(deadline):
        return sub_days(lead, deadline)
    return None
