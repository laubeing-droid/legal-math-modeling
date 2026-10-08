"""诉讼时效中止／中断的确定性计算（民法典 192／194／195 条；P-012／T18／D033 的期间效果面）。

与 Lean 侧 ``JurisLean.Seams.Limitation`` 同一合同（2026-10-08 修正后版本）：

* 194 条（中止）＝**门槛**＋**届满**：障碍发生日落在时效期间最后六个月内才合格；
  合格中止的届满日＝自中止原因消除之日起满六个月——**不是**"冻结剩余长度后继续"
  （反例见 ``test_limitation.py::test_remaining_month_counterexample``）。
* 195 条（中断）：从中断、有关程序终结时起重新起算。
* 范围：本模块只表达普通诉讼时效。保证期间（692 条第 2 款）不适用中止／中断，
  除斥期间等其他期间按各自法源，不把 194 条六个月规则外推给它们。

建模选择与 Lean 同口径：三年＝1095 天、六个月＝180 天（忽略闰年与大小月）；
日标签取整数，无日历库依赖。
"""

from __future__ import annotations

from dataclasses import dataclass

LIMITATION_PERIOD_DAYS = 1095
SIX_MONTHS_DAYS = 180


@dataclass(frozen=True)
class LimitationSchedule:
    """起算日＋期间长度（"知道或应当知道之日"由案卷给，本模块不代认）。"""

    start_day: int
    period_days: int = LIMITATION_PERIOD_DAYS


def natural_expiry(schedule: LimitationSchedule) -> int:
    """无中止／中断时的届满日标签（起算日＋期间）。"""
    return schedule.start_day + schedule.period_days


def obstacle_in_last_six_months(schedule: LimitationSchedule, onset_day: int) -> bool:
    """194 条门槛：障碍发生日落在时效期间的最后六个月内（含窗口左端、不含届满日）。"""
    expiry = natural_expiry(schedule)
    return expiry - SIX_MONTHS_DAYS <= onset_day < expiry


@dataclass(frozen=True)
class SuspensionOutcome:
    """中止计算结果。``basis`` 记录届满日来自哪条规则，供见证与审计面使用。"""

    qualified: bool
    expiry_day: int
    basis: str  # "194-six-months" | "natural"


def suspension_outcome(
    schedule: LimitationSchedule, onset_day: int, removed_day: int
) -> SuspensionOutcome:
    """194 条中止效果。

    fail-closed：消除日早于发生日的输入直接拒（不猜消除日）；门槛外的障碍不合格，
    届满保持自然届满日（194 条不适用），不外推其他期间规则。
    """
    if removed_day < onset_day:
        raise ValueError(f"removed_day {removed_day} before onset_day {onset_day}")
    if obstacle_in_last_six_months(schedule, onset_day):
        return SuspensionOutcome(True, removed_day + SIX_MONTHS_DAYS, "194-six-months")
    return SuspensionOutcome(False, natural_expiry(schedule), "natural")


def interrupt_restart(at_day: int, period_days: int = LIMITATION_PERIOD_DAYS) -> LimitationSchedule:
    """195 条中断：从中断、有关程序终结时起重新起算（旧期间经过全部作废）。"""
    return LimitationSchedule(start_day=at_day, period_days=period_days)
