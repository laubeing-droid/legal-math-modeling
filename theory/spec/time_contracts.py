#!/usr/bin/env python3
"""Time contracts (P-012, P-094, P-095).

Limitation causes (P-012): commence/suspend/interrupt/extend with their
status transitions — interruption restarts the clock from a new commence
day, suspension freezes it, and only listed causes act. Term computation
(P-094): the anchor is selected by rule before any elapsed-day math; a
missing anchor is UNKNOWN. Commencement matrix (P-095): (period kind,
event kind) cells looked up in an explicit table; an empty cell is
UNKNOWN, never improvised.
"""

from __future__ import annotations

from dataclasses import dataclass
from enum import Enum
from typing import Dict, Optional, Tuple


class LimitationCause(str, Enum):
    """P-012 A55: the four causes that move a limitation clock."""

    COMMENCE = "COMMENCE"
    SUSPEND = "SUSPEND"
    INTERRUPT = "INTERRUPT"
    EXTEND = "EXTEND"


@dataclass(frozen=True)
class LimitationClock:
    """State of the limitation clock at a moment."""

    running: bool
    elapsed_days: int
    commenced_day: Optional[int] = None


def apply_limitation_cause(clock: LimitationClock, cause: LimitationCause, day: int) -> LimitationClock:
    """Only the four listed causes act; each has one defined transition."""

    if cause is LimitationCause.COMMENCE:
        if clock.running or clock.commenced_day is not None:
            return clock
        return LimitationClock(running=True, elapsed_days=0, commenced_day=day)
    if cause is LimitationCause.SUSPEND:
        return clock if not clock.running else LimitationClock(running=False, elapsed_days=clock.elapsed_days, commenced_day=clock.commenced_day)
    if cause is LimitationCause.INTERRUPT:
        if clock.commenced_day is None:
            return clock  # 未起算的钟无从中断
        # 悬置不阻断中断：中断丢弃已过时效期间并自新起算日重启。
        return LimitationClock(running=True, elapsed_days=0, commenced_day=day)
    # EXTEND never shortens; extension is recorded by the caller's window,
    # the clock itself is unchanged here.
    return clock


@dataclass(frozen=True)
class AnchorRule:
    """P-094 B14: rule selecting the computation anchor event."""

    event_key: str


def select_anchor(
    rules: Tuple[AnchorRule, ...], events: Dict[str, int]
) -> Optional[int]:
    """First rule whose event exists yields the anchor; otherwise UNKNOWN."""

    for rule in rules:
        if rule.event_key in events:
            return events[rule.event_key]
    return None


def days_elapsed(anchor_day: Optional[int], at_day: int) -> Optional[int]:
    """Elapsed days from a known anchor; no anchor, no number."""

    if anchor_day is None:
        return None
    return max(0, at_day - anchor_day)


@dataclass(frozen=True)
class CommencementCell:
    """P-095 B23: one matrix cell: (period kind, event kind) -> rule id."""

    period_kind: str
    event_kind: str
    rule_id: str


def lookup_commencement(
    matrix: Tuple[CommencementCell, ...], period_kind: str, event_kind: str
) -> Optional[str]:
    """Explicit-table lookup; empty cells stay UNKNOWN (fail-closed)."""

    for cell in matrix:
        if cell.period_kind == period_kind and cell.event_kind == event_kind:
            return cell.rule_id
    return None
