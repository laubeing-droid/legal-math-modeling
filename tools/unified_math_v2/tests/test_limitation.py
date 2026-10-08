"""诉讼时效中止／中断合同测试（民法典 194／195 条；与 ``JurisLean.Seams.Limitation`` 同合同）。

核心反例（2026-10-08 审查指定）：原期间只剩一个月时发生合格障碍、次日消除，
届满按"消除后满六个月"计，不得只续算剩余一个月。
"""

import pytest

from unified.limitation import (
    LIMITATION_PERIOD_DAYS,
    SIX_MONTHS_DAYS,
    LimitationSchedule,
    interrupt_restart,
    natural_expiry,
    obstacle_in_last_six_months,
    suspension_outcome,
)


def _schedule(start_day: int = 0) -> LimitationSchedule:
    return LimitationSchedule(start_day=start_day)


def test_natural_expiry_is_start_plus_period():
    assert natural_expiry(_schedule(10)) == 10 + LIMITATION_PERIOD_DAYS
    assert LIMITATION_PERIOD_DAYS == 1095  # 三年，忽略闰年
    assert SIX_MONTHS_DAYS == 180


def test_remaining_month_counterexample():
    """审查指定反例：剩余一个月（30 天）＋障碍次日消除 → 届满＝消除日＋180＝1246。

    "冻结剩余长度续算"会给 1066＋30＝1096 或停在自然届满 1095，两者都错。
    """
    s = _schedule(0)
    onset = LIMITATION_PERIOD_DAYS - 30  # 剩一个月时发生障碍
    removed = onset + 1  # 次日消除
    assert obstacle_in_last_six_months(s, onset)
    out = suspension_outcome(s, onset, removed)
    assert out.qualified
    assert out.basis == "194-six-months"
    assert out.expiry_day == removed + SIX_MONTHS_DAYS == 1246
    assert out.expiry_day != natural_expiry(s)          # 不是自然届满 1095
    assert out.expiry_day != removed + 30               # 不是"续算剩余一个月" 1096


def test_qualified_suspension_always_at_least_natural():
    """Lean ``suspension_never_shortens`` 的同面枚举：合格中止的届满 ≥ 自然届满。"""
    s = _schedule(0)
    expiry = natural_expiry(s)
    for onset in range(expiry - SIX_MONTHS_DAYS, expiry, 15):
        for removed in (onset, onset + 7, expiry + 60):
            out = suspension_outcome(s, onset, removed)
            assert out.expiry_day >= expiry


def test_gate_boundary_inclusive_left_exclusive_right():
    s = _schedule(0)
    expiry = natural_expiry(s)
    assert obstacle_in_last_six_months(s, expiry - SIX_MONTHS_DAYS)  # 左端含
    assert obstacle_in_last_six_months(s, expiry - 1)                # 最后一天
    assert not obstacle_in_last_six_months(s, expiry - SIX_MONTHS_DAYS - 1)
    assert not obstacle_in_last_six_months(s, expiry)                # 已届满
    assert not obstacle_in_last_six_months(s, -10)                   # 起算前


def test_obstacle_outside_window_keeps_natural_expiry():
    """门槛外障碍不合格：届满保持自然届满日（fail-closed，不外推）。"""
    s = _schedule(0)
    out = suspension_outcome(s, expiry := natural_expiry(s) - SIX_MONTHS_DAYS - 1, expiry + 5)
    assert not out.qualified
    assert out.basis == "natural"
    assert out.expiry_day == natural_expiry(s)


def test_inverted_window_rejected():
    with pytest.raises(ValueError):
        suspension_outcome(_schedule(0), 1000, 999)


def test_interrupt_restarts_wholesale():
    """195 条：中断后旧期间经过全部作废，从事件日重起整个期间。"""
    restarted = interrupt_restart(1000)
    assert natural_expiry(restarted) == 1000 + LIMITATION_PERIOD_DAYS
    assert natural_expiry(restarted) > natural_expiry(_schedule(0))
    assert natural_expiry(interrupt_restart(1000, period_days=60)) == 1060
