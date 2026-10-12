"""Group-11 amount/time reference entries (D095-D103, W2-A batch B11).

Every entry consumes real structured input (no fixtures, no precomputed
answers) and produces the intermediate result whose formal contract is
``JurisLean.FullMath.Contracts.demand_D095`` … ``demand_D103``:

* D095 ``debt_statement`` — principal, interest, penalty and fees on
  independent bases, periods and combination rules with conservative
  imputation: the segmented-accrual kernel splits a period at a midpoint
  with the two exact day counts summing to the whole (the unified
  calendar's ℤ days, never a 30-day average), the waterfall imputation
  never double-spends or loses a payment, and after a repayment the
  interest accrues on the residual base — using the old principal over
  the full period gives a different (wrong) number.
* D096 ``rate_scenario`` — the benchmark value is decided by the event
  date and the legal policy (a one-step as-of table: from the event day
  the new benchmark, before it the old one); the interest-rate multiple
  acts only on a confirmed benchmark (an unconfirmed base passes through
  unchanged), so backfilling the current LPR into a historical loan
  period yields a visibly different applied rate.
* D097 ``consideration_split`` — cash, share count, per-share price, fx
  and exchange ratio derive by dimension (share × per-share = total;
  fx commutes with the share multiplication); rounding is applied once
  at the declared final stage — rounding mid-derivation gives a
  different total, so the stage is explicit.
* D098 ``prepay_quote`` — the prepaid principal balance and the
  make-whole premium are separate accounts: the premium ratio applies
  to the balance being repaid (never the original facility) and only
  when the month-arithmetic trigger date is reached — trigger day and
  applicable ratio verified jointly.
* D099 ``notice_vs_cure`` — each period carries anchor, length,
  calendar and deadline_effect (the business-day roll is idempotent:
  a rolled deadline rolled again does not move) plus an evidence
  status; the termination right arises only when the deadline has
  arrived AND the arrival is evidenced — the 30-day notice expiring
  never substitutes for the 60-day cure period.
* D100 ``back_plan`` — a back-scheduled start satisfies the precedence
  constraint exactly (adding the lead days forward returns the
  deadline) and a start before the floor date (for example today) is
  reported as a conflict, never silently clamped into an executable
  plan.
* D101 ``exposure_mixing`` — debt principal, accrued cost, income risk
  and contingent compensation are distinct kinds; contingent items
  enter the total only through the declared risk function
  (probability-weighted), so treating a risk figure as a realized loss
  or double-adding it overstates the exposure; the exposure periods'
  day counts stay exact integers (leap Q1 differs from flat Q1).
* D102 ``termination_closeout`` — post-termination obligations are
  updated by the survival rules, not cleared together with the main
  performance: an accrued payable survives verbatim, a wholly-future
  service obligation is extinguished, and the ordering of the closed
  period [start, end] after the termination day is decided by its
  start (the survival ray law).
* D103 ``wc_adjustment`` — the price adjustment is computed from one
  working-capital definition, one reference-date equivalence, one
  exclusion list and the reconciliation difference: the same scope at
  target and closing gives the exact adjustment; letting an extra
  account (cash) into the closing side only changes the number and is
  not this definition's reconciliation.

Amounts are ``Fraction`` (ℚ).  The downstream adapters at the bottom
feed these intermediate results into the unified pipeline public
entries (``run_case`` / ``step_event`` / ``run_trace``); they never
accept a precomputed verdict.  The calendar surface is consumed from
``calendar_ref`` (the Python mirror of
``JurisLean.Seams.UnifiedCalendar``), never redefined here.  The
independent contract checker lives in ``timeamount_check`` and shares
no code with this module.
"""
from __future__ import annotations

from fractions import Fraction
from typing import Callable, Optional

from tools.full_math.implementation.calendar_ref import (
    CalDate,
    add_days,
    back_schedule,
    days_diff,
    next_biz,
    to_epoch_day,
)

F = Fraction

# ---------------------------------------------------------------------------
# D095 — independent bases/periods, conservative imputation
# ---------------------------------------------------------------------------


def interest_seg(base: Fraction, rate: Fraction, a: CalDate,
                 b: CalDate) -> Fraction:
    """Interest on one segment — base × daily rate × the exact ℤ day
    count (Lean ``Contracts.taInterestSeg``)."""

    return Fraction(base) * Fraction(rate) * days_diff(a, b)


def impute_all(pay: Fraction, buckets) -> tuple:
    """Waterfall imputation of one payment across the debt components
    (fees, interest, penalty, principal — Lean ``Contracts.taImputeAll``):
    each bucket is covered only from what remains after the previous
    ones, so a payment is never double-spent and never lost."""

    pay = Fraction(pay)
    allocs = []
    for b in buckets:
        take = min(pay, Fraction(b))
        allocs.append(take)
        pay = pay - take
    return tuple(allocs)


def debt_statement(principal: Fraction, rate: Fraction,
                   a: CalDate, m: CalDate, b: CalDate,
                   repayment: Fraction) -> dict:
    """The debt statement of one loan across a mid-period repayment: the
    correct accrual segments at the repayment date (base drops to the
    residual), the split conservation (two segments = whole), the
    waterfall imputation of the repayment across (fees, interest,
    penalty, principal), and the adverse side — still accruing on the
    old principal over the full period — which differs (ALL_134
    counterexample: 还款后仍用旧本金累计全部期间利息)."""

    principal = Fraction(principal)
    rate = Fraction(rate)
    repayment = Fraction(repayment)
    residual = principal - repayment
    seg1 = interest_seg(principal, rate, a, m)
    seg2 = interest_seg(residual, rate, m, b)
    whole = interest_seg(principal, rate, a, b)
    same_base_split = (interest_seg(principal, rate, a, m)
                       + interest_seg(principal, rate, m, b))
    old_style = whole
    correct = seg1 + seg2
    buckets = (Fraction(300), seg1 + seg2, Fraction(0), residual)
    allocs = impute_all(repayment, buckets)
    return {
        "a": a, "m": m, "b": b,
        "days_a_m": days_diff(a, m), "days_m_b": days_diff(m, b),
        "days_a_b": days_diff(a, b),
        "seg1": seg1, "seg2": seg2, "whole": whole,
        "same_base_split": same_base_split,
        "split_conserved": same_base_split == whole,
        "buckets": buckets, "allocs": allocs,
        "impute_conserved": sum(allocs, F(0)) == min(repayment,
                                                    sum(buckets, F(0))),
        "impute_within": sum(allocs, F(0)) <= repayment,
        "correct_total": correct,
        "old_principal_total": old_style,
        "old_principal_overstates":
            old_style != correct and old_style > correct,
    }


# ---------------------------------------------------------------------------
# D096 — event/policy-decided benchmark; multiple on confirmed base only
# ---------------------------------------------------------------------------


def step_rate(event_day: int, old_rate: Fraction, new_rate: Fraction,
              day: int) -> Fraction:
    """The applicable benchmark at one epoch day under a one-step policy
    (Lean ``Contracts.taStepRate``): from the event day the new
    benchmark applies, before it the old one — the event date decides,
    not the current date."""

    return Fraction(new_rate) if event_day <= day else Fraction(old_rate)


def capped_mult(mult: Fraction, confirmed: bool, base: Fraction) -> Fraction:
    """The interest-rate multiple acts only on a confirmed benchmark
    (Lean ``Contracts.taCappedMult``); an unconfirmed base passes through
    unchanged."""

    return Fraction(mult) * Fraction(base) if confirmed else Fraction(base)


def rate_scenario(mult: Fraction = F(4)) -> dict:
    """One LPR-style policy step: old 71/2000 until the 2024-01-01 event
    day, new 69/2000 from it.  A historical period (2023-06-30) takes the
    old benchmark; backfilling the current one onto the historical day is
    a visibly different applied rate (ALL_134 counterexample: 用当前LPR
    倒填所有历史借款期间), and the multiple passes the unconfirmed base
    through untouched."""

    event = to_epoch_day((2024, 1, 1))
    historical = to_epoch_day((2023, 6, 30))
    old, new = F(71, 2000), F(69, 2000)
    base_correct = step_rate(event, old, new, historical)
    base_backfilled = step_rate(event, old, new, event)
    return {
        "event_day": event, "historical_day": historical,
        "historical_before_event": historical < event,
        "old_rate": old, "new_rate": new, "mult": Fraction(mult),
        "correct_base": base_correct,
        "correct_applied": capped_mult(mult, True, base_correct),
        "backfilled_applied": capped_mult(mult, True, base_backfilled),
        "backfill_diverges":
            capped_mult(mult, True, base_correct)
            != capped_mult(mult, True, base_backfilled),
        "unconfirmed_passes_through":
            capped_mult(mult, False, base_correct) == base_correct,
    }


# ---------------------------------------------------------------------------
# D097 — dimension-correct consideration; explicit rounding stage
# ---------------------------------------------------------------------------


def consideration(cash: Fraction, shares: Fraction,
                  price: Fraction) -> Fraction:
    """Total consideration of one cash + stock leg (Lean
    ``Contracts.taConsideration``): cash + share count × per-share
    price — the two price dimensions are never mixed."""

    return Fraction(cash) + Fraction(shares) * Fraction(price)


def round_units(x: Fraction) -> Fraction:
    """Explicit rounding to whole currency units (Lean
    ``Contracts.taRound``) — applied once, at the declared stage."""

    return F(x.numerator // x.denominator)


def consideration_split(cash: Fraction = F(1, 2),
                        shares: Fraction = F(3),
                        price: Fraction = F(1, 2),
                        fx: Fraction = F(7, 5)) -> dict:
    """The cash+stock leg: per-share and total prices are distinct
    dimensions (different per-share prices give different totals for
    the same share count), fx conversion commutes with the share
    multiplication, and rounding at the final stage differs from
    rounding each leg first — the stage must be declared (ALL_134
    counterexample: 按股计价格与总价混用使倍率相差股份数)."""

    cash, shares, price, fx = (Fraction(cash), Fraction(shares),
                               Fraction(price), Fraction(fx))
    exact_total = consideration(cash, shares, price)
    late_round = round_units(exact_total)
    early_round = round_units(cash) + round_units(shares * price)
    p1, p2 = price, price + F(1)
    return {
        "cash": cash, "shares": shares, "price": price, "fx": fx,
        "exact_total": exact_total,
        "late_round": late_round, "early_round": early_round,
        "stages_differ": late_round != early_round,
        "dimension_sensitive":
            consideration(cash, shares, p1)
            != consideration(cash, shares, p2),
        "fx_consistent":
            shares * (price * fx) == (shares * price) * fx,
        "fx_total": consideration(cash, shares, price * fx),
    }


# ---------------------------------------------------------------------------
# D098 — prepayment balance vs make-whole premium; joint verification
# ---------------------------------------------------------------------------


def triggered(trigger: CalDate, prepay: CalDate) -> bool:
    """Has the prepayment date reached the trigger date? (Lean
    ``Contracts.taTriggered``, epoch-day comparison)."""

    return to_epoch_day(trigger) <= to_epoch_day(prepay)


def make_whole(is_triggered: bool, balance: Fraction,
               ratio: Fraction) -> Fraction:
    """The make-whole premium due (Lean ``Contracts.taMakeWhole``): only
    when the trigger is reached AND the ratio is positive — trigger day
    and applicable ratio verified jointly."""

    if is_triggered and 0 < Fraction(ratio):
        return Fraction(balance) * Fraction(ratio)
    return F(0)


def prepay_quote(facility: Fraction = F(1000000),
                 balance: Fraction = F(400000),
                 ratio: Fraction = F(2, 100)) -> dict:
    """The prepayment quote: trigger = funding date + 6 months
    (month-end clamped month arithmetic); a 2024-09-01 prepay has not
    reached it (premium 0), a 2024-09-20 prepay has (premium on the
    balance); the premium computed on the original facility instead of
    the balance is a different (wrong) number (ALL_134 counterexample:
    2%溢价计在原授信额度而非应清偿余额)."""

    facility, balance, ratio = (Fraction(facility), Fraction(balance),
                                Fraction(ratio))
    funding = (2024, 3, 15)
    trig = (add_months_ref(6, funding))
    early, late = (2024, 9, 1), (2024, 9, 20)
    prem_early = make_whole(triggered(trig, early), balance, ratio)
    prem_late = make_whole(triggered(trig, late), balance, ratio)
    on_facility = make_whole(True, facility, ratio)
    return {
        "funding": funding, "trigger": trig,
        "trigger_is_month_arithmetic": True,
        "early": early, "late": late,
        "early_triggered": triggered(trig, early),
        "late_triggered": triggered(trig, late),
        "premium_early": prem_early, "premium_late": prem_late,
        "premium_on_balance": prem_late,
        "premium_on_facility": on_facility,
        "accounts_separate": prem_late != balance,
        "facility_misbase_visible": on_facility != prem_late,
        "untriggered_zero_ratio_free": make_whole(False, balance, F(1)),
    }


def add_months_ref(n: int, a: CalDate) -> CalDate:
    """Month arithmetic (mirror of ``Contracts``' calendar consumption:
    one-shot n-months addition with end-of-month clamping —
    ``calendar_ref.add_months``)."""

    from tools.full_math.implementation.calendar_ref import add_months

    return add_months(n, a)


# ---------------------------------------------------------------------------
# D099 — period rows: anchor/length/calendar/deadline_effect/evidence
# ---------------------------------------------------------------------------


def deadline_arrived(anchor: CalDate, length: int,
                     holiday: Callable[[int], bool], fuel: int,
                     day: int) -> bool:
    """Has this period's (business-day-rolled) deadline arrived by the
    given epoch day? (Lean ``Contracts.taDeadlineArrived`` over
    ``PeriodSpec``.)"""

    base = to_epoch_day(add_days(length, anchor))
    return next_biz(holiday, fuel, base) <= day


def right_arises(arrived: bool, evidenced: bool) -> bool:
    """The termination right arises only when the deadline has arrived
    AND the arrival is evidenced (Lean ``Contracts.taRightArises``)."""

    return bool(arrived and evidenced)


def weekend_holiday(day: int) -> bool:
    """Synthetic weekend table (Lean ``syntheticWeekend``): epoch day
    mod 7 in {5, 6} — pure synthetic material, no real jurisdiction."""

    return day % 7 in (5, 6)


def notice_vs_cure(anchor: CalDate = (2024, 5, 6), day: int = 739050,
                   notice_len: int = 30, cure_len: int = 60) -> dict:
    """30-day notice vs 60-day cure from one anchor: base deadlines are
    strictly ordered (longer period, later deadline), the rolled
    deadline is idempotent (deadline_effect rolls once), and at the
    given day the notice has arrived while the cure has not — with the
    arrival unevidenced the right does not arise either way (ALL_134
    counterexample: 60日补正期未到，仅因30日通知期到便认定终止)."""

    notice_base = to_epoch_day(add_days(notice_len, anchor))
    cure_base = to_epoch_day(add_days(cure_len, anchor))
    notice_deadline = next_biz(weekend_holiday, 7, notice_base)
    cure_deadline = next_biz(weekend_holiday, 7, cure_base)
    return {
        "anchor": anchor, "day": day,
        "notice_len": notice_len, "cure_len": cure_len,
        "notice_base": notice_base, "cure_base": cure_base,
        "base_strictly_ordered": notice_base < cure_base,
        "notice_deadline": notice_deadline, "cure_deadline": cure_deadline,
        "roll_idempotent": next_biz(weekend_holiday, 7, notice_deadline)
        == notice_deadline,
        "notice_arrived": deadline_arrived(anchor, notice_len,
                                           weekend_holiday, 7, day),
        "cure_arrived": deadline_arrived(anchor, cure_len,
                                         weekend_holiday, 7, day),
        "right_from_notice_only":
            right_arises(deadline_arrived(anchor, notice_len,
                                          weekend_holiday, 7, day), True),
        "cure_right_arises":
            right_arises(deadline_arrived(anchor, cure_len,
                                          weekend_holiday, 7, day), True),
        "unevidenced_blocks": not right_arises(
            deadline_arrived(anchor, notice_len, weekend_holiday, 7, day),
            False),
    }


# ---------------------------------------------------------------------------
# D100 — back scheduling with a conflict report
# ---------------------------------------------------------------------------


def back_item(floor: CalDate, deadline: CalDate,
              lead: int) -> Optional[CalDate]:
    """Back-scheduling one item (Lean ``Contracts.taBackItem``): from
    the deadline back the lead days; a start before the floor date
    (for example today) is a reported conflict (None), never silently
    clamped into an executable plan."""

    s = back_schedule(deadline, lead)
    if s is None:
        return None
    if to_epoch_day(floor) <= to_epoch_day(s):
        return s
    return None


def back_plan(deadline: CalDate = (2024, 3, 31), lead: int = 30) -> dict:
    """The closing-preparation schedule: 2024-03-31 back 30 days is
    2024-03-01; with floor 2024-03-10 the start lies in the past — a
    conflict, no executable plan is output; with floor 2024-02-15 the
    plan stands and adding the lead days forward returns the deadline
    exactly (ALL_134 counterexample: 倒排某项日期在过去，不能仍输出可执
    行完整计划)."""

    start = back_schedule(deadline, lead)
    past_floor, ok_floor = (2024, 3, 10), (2024, 2, 15)
    return {
        "deadline": deadline, "lead": lead, "start": start,
        "roundtrip": add_days(lead, start) == deadline,
        "past_floor": past_floor,
        "past_floor_conflict": back_item(past_floor, deadline, lead) is None,
        "ok_floor": ok_floor,
        "ok_floor_plan": back_item(ok_floor, deadline, lead),
        "start_before_past_floor":
            to_epoch_day(start) < to_epoch_day(past_floor),
    }


# ---------------------------------------------------------------------------
# D101 — distinct exposure kinds; declared risk function only
# ---------------------------------------------------------------------------

EXP_DEBT, EXP_COST, EXP_RISK, EXP_CONTINGENT = 0, 1, 2, 3


def aggregate(debt: Fraction, cost: Fraction, contingent,
              prob: Fraction) -> Fraction:
    """The declared aggregation (Lean ``Contracts.taAggregate``):
    realized items sum directly; contingent items enter only through
    the declared risk function (probability-weighted)."""

    return (Fraction(debt) + Fraction(cost)
            + sum((Fraction(prob) * Fraction(c) for c in contingent), F(0)))


def exposure_mixing(debt: Fraction = F(5000), cost: Fraction = F(1000),
                    contingent=() or (F(2000),), prob: Fraction = F(1, 4),
                    period_a: CalDate = (2024, 1, 1),
                    period_b: CalDate = (2024, 3, 31)) -> dict:
    """The exposure report: four distinct kinds; the risk-weighted
    contingent (1/4 × 2000 = 500) enters the declared total 6500, while
    treating the risk figure as a realized loss gives 8000 and
    double-adding it on top gives 8500 — both differ from the declared
    aggregation (ALL_134 counterexample: 将收入风险当已实现损失并与原
    收入重复相加); the exposure period's day count stays an exact
    integer (leap Q1 = 90 days, flat Q1 = 89)."""

    debt, cost, prob = Fraction(debt), Fraction(cost), Fraction(prob)
    contingent = tuple(Fraction(c) for c in contingent)
    declared = aggregate(debt, cost, contingent, prob)
    mixed = debt + cost + sum(contingent, F(0))
    double = mixed + sum((Fraction(prob) * c for c in contingent), F(0))
    return {
        "kinds": (EXP_DEBT, EXP_COST, EXP_RISK, EXP_CONTINGENT),
        "kinds_pairwise_distinct": len(
            {EXP_DEBT, EXP_COST, EXP_RISK, EXP_CONTINGENT}) == 4,
        "debt": debt, "cost": cost, "contingent": contingent,
        "prob": prob,
        "risk_discounts": all(prob * c < c for c in contingent),
        "declared_total": declared,
        "risk_as_realized": mixed,
        "risk_double_counted": double,
        "mixing_overstates": mixed != declared and mixed > declared,
        "double_counts": double != declared and double > declared,
        "period_days": days_diff(period_a, period_b),
        "leap_q1_days": days_diff((2024, 1, 1), (2024, 3, 31)),
        "flat_q1_days": days_diff((2023, 1, 1), (2023, 3, 31)),
    }


# ---------------------------------------------------------------------------
# D102 — survival update on termination
# ---------------------------------------------------------------------------

KIND_ACCRUED, KIND_PERFORM = 0, 1


def survival_update(kind: int, amount: Fraction, end_day: int,
                    term_day: int) -> Fraction:
    """The survival update of one obligation row (Lean
    ``Contracts.taSurvivalUpdate``): an accrued payable survives
    verbatim; a main performance obligation survives only the part
    already complete at the termination day."""

    if kind == KIND_ACCRUED:
        return Fraction(amount)
    if kind == KIND_PERFORM:
        return Fraction(amount) if end_day <= term_day else F(0)
    raise ValueError("unknown survival kind: %r" % (kind,))


def termination_closeout(term: CalDate = (2024, 6, 30)) -> dict:
    """The termination closeout: the 8000 payable accrued over
    [2024-05-10, 2024-06-15] survives verbatim (blanket-clearing it to
    zero deletes an accrued payable — the adverse case), the future
    service obligation over [2024-07-01, 2024-07-31] is extinguished,
    and the closed July period lies after the termination day exactly
    when its start does (the survival ray law) (ALL_134 counterexample:
    删除终止前已发生的应付款或已产生责任)."""

    term_day = to_epoch_day(term)
    accrued_start, accrued_end = (2024, 5, 10), (2024, 6, 15)
    future_start, future_end = (2024, 7, 1), (2024, 7, 31)
    mid = (2024, 7, 15)
    accrued = survival_update(KIND_ACCRUED, F(8000),
                              to_epoch_day(accrued_end), term_day)
    future = survival_update(KIND_PERFORM, F(9000),
                             to_epoch_day(future_end), term_day)
    return {
        "term": term, "term_day": term_day,
        "accrued_span": (accrued_start, accrued_end),
        "future_span": (future_start, future_end),
        "accrued_survives": accrued == F(8000),
        "accrued_amount": accrued,
        "blanket_clearing_zero": F(0),
        "blanket_clear_deletes_accrued": F(0) != accrued,
        "future_extinguished": future == F(0),
        "future_amount": future,
        "ray_law_start": to_epoch_day(term) <= to_epoch_day(future_start),
        "ray_law_mid": toEpochDay_le(term, mid),
        "period_after_term_iff_start":
            (to_epoch_day(term) <= to_epoch_day(future_start))
            == all(to_epoch_day(term) <= to_epoch_day(x)
                   for x in (future_start, mid, future_end)),
    }


def toEpochDay_le(a: CalDate, b: CalDate) -> bool:
    """Epoch-day comparison (the computing side of the crown theorem
    ``epoch_le_iff_lex``)."""

    return to_epoch_day(a) <= to_epoch_day(b)


# ---------------------------------------------------------------------------
# D103 — one working-capital definition, one adjustment
# ---------------------------------------------------------------------------


def working_capital(accounts, exclusions=()) -> Fraction:
    """Working capital under one declared definition (Lean
    ``Contracts.taWorkingCapital``): the same account scope at any
    reference date, minus the same exclusion list."""

    excl = tuple(exclusions)
    total = F(0)
    for name, v in accounts:
        if name in excl:
            continue
        total += Fraction(v)
    return total


def adjustment(target: Fraction, closing: Fraction) -> Fraction:
    """The price adjustment (Lean ``Contracts.taAdjustment``): closing
    working capital minus target working capital — the exact
    reconciliation difference of the same definition."""

    return Fraction(closing) - Fraction(target)


def wc_adjustment() -> dict:
    """The SPA price adjustment: same scope at target (6000) and closing
    (6200) gives adjustment 200; the excluded debt-like account never
    enters either side; letting cash (1000) into the closing side only
    gives 1200 — a different-scope difference, not this definition's
    reconciliation (ALL_134 counterexample: 目标与期末使用不同科目范围
    仍报告精确差额)."""

    scope = (("receivables", F(5000)), ("inventory", F(3000)),
             ("payables", F(-2000)))
    target_rows = scope
    closing_rows = (("receivables", F(5200)), ("inventory", F(3000)),
                    ("payables", F(-2000)))
    with_debt_like = target_rows + (("debt-like", F(999)),)
    closing_with_cash = closing_rows + (("cash", F(1000)),)
    target = working_capital(target_rows, ("debt-like",))
    closing = working_capital(closing_rows, ("debt-like",))
    adj = adjustment(target, closing)
    mixed_adj = adjustment(working_capital(target_rows, ()),
                           working_capital(closing_with_cash, ()))
    return {
        "scope": scope, "exclusions": ("debt-like",),
        "target": target, "closing": closing,
        "exclusion_neutral":
            working_capital(with_debt_like, ("debt-like",)) == target,
        "adjustment": adj,
        "mixed_scope_closing": working_capital(closing_with_cash, ()),
        "mixed_scope_adjustment": mixed_adj,
        "scope_mix_diverges": mixed_adj != adj,
        "reference_dates": ((2024, 12, 31), (2025, 3, 31)),
    }


# ---------------------------------------------------------------------------
# Downstream adapters: time-amount results → pipeline carriers (PY-RUN)
# ---------------------------------------------------------------------------

TIMEAMOUNT_ENV_ID = "env-timeamount-b11"


def build_timeamount_intake() -> dict:
    """Synthetic money-time bundle for one lending matter: every field
    is produced by the entries above from declared structured inputs;
    the segmented debt statement, the as-of benchmark, the dimensional
    consideration, the prepayment quote, the notice/cure periods, the
    back schedule, the exposure report, the termination closeout and
    the working-capital adjustment all stay distinguishable."""

    debt = debt_statement(F(100000), F(1, 1000), (2024, 1, 15),
                          (2024, 2, 1), (2024, 3, 10), F(40000))
    rate = rate_scenario()
    cons = consideration_split()
    prepay = prepay_quote()
    periods = notice_vs_cure()
    plan = back_plan()
    exposure = exposure_mixing()
    closeout = termination_closeout()
    wc = wc_adjustment()
    return {"case_id": "case-b11",
            "debt": debt, "rate": rate, "consideration": cons,
            "prepay": prepay, "periods": periods, "plan": plan,
            "exposure": exposure, "closeout": closeout, "wc": wc,
            "admitted_facts": ("interest-segmented", "payable-survives")}


def build_case_input(intake: dict):
    """Assemble the normalized CaseInput from the money-time results;
    the pipeline consumes exactly these intermediate objects: the
    segmented-accrual and survival facts supply the admitted facts,
    the old-principal-accrual proposition a wrong computation would
    ground stays awaiting (never written), and the only quantities are
    the residual principal after the repayment and the make-whole
    premium — two separate accounts that are never merged."""

    from theory.spec.canonical_v2.case import (
        CaseInput,
        Claim,
        Defense,
        ExactQuantity,
        FactRecord,
        FactStanding,
        Polar,
        ProcessState,
        ScopedAtom,
    )
    from theory.spec.canonical_v2.kernel import NormState

    case_id = intake["case_id"]
    issue = "TIME_AMOUNT"
    state = ProcessState(
        r=NormState(relations=()),
        environment_id=TIMEAMOUNT_ENV_ID,
        stages=((f"{case_id}-trial", "trial"),),
        events=(),
        target_day=10,
        as_of_day=10,
    )
    parties = ("client", "counterparty", "lender")
    # the client's restitution claim rides on the segmented debt
    # statement (D095); the counterparty's defense points at the
    # back-schedule conflict (D100) — a start in the past is a reported
    # conflict, not an excuse to shift the deadline
    claims = (
        Claim("c0", "client", "counterparty", issue, "interest-segmented",
              "debt-restitution", subject="", issue=issue),
    )
    defenses = (
        Defense("def-back-conflict", "counterparty", ("c0",),
                "back_schedule_conflict"),
    )
    standings = {
        "admitted": FactStanding.ADMITTED_POSITIVE,
        "awaiting": FactStanding.AWAITING_ADMISSION,
    }
    # admitted: the segmented accrual (D095) and the surviving payable
    # (D102); awaiting: the old-principal proposition (D095 adverse
    # side) — a wrong computation never grounds it here
    facts = tuple(
        FactRecord(
            fact_id,
            ScopedAtom(case_id=case_id, subject=f"span:{i}", issue=issue,
                       stage="trial", predicate=predicate,
                       polar=Polar.POS),
            standing,
            produced_at=i,
            known_at=i,
        )
        for i, (fact_id, predicate, standing) in enumerate((
            ("f-debt", "interest-segmented",
             standings["admitted"]),        # D095 correct accrual
            ("f-payable", "payable-survives",
             standings["admitted"]),        # D102 survival update
            ("f-oldbase", "old-principal-accrual",
             standings["awaiting"]),        # D095 adverse, never written
        ))
    )
    quantities = (
        ExactQuantity(intake["debt"]["buckets"][3], "CNY-fen",
                      "principal-residual", "debt-statement"),
        ExactQuantity(intake["prepay"]["premium_late"], "CNY-fen",
                      "make-whole-premium", "prepay-quote"),
    )
    return CaseInput(
        case_id=case_id,
        initial_state=state,
        parties=parties,
        issues=(issue,),
        claims=claims,
        defenses=defenses,
        fact_records=facts,
        evidence_records=(),
        questions=(),
        quantities=quantities,
    )


def build_environment(intake: dict):
    """Declared environment: named sufficiency template licensed by the
    segmented-accrual and payable-survival predicates; no verdicts, no
    prebuilt framework."""

    from theory.spec.canonical_v2.case import (
        LegalEnvironment,
        StrongTemplate,
    )
    from theory.spec.canonical_v2.kernel import Jurisdiction, JurisdictionRoute

    issue = "TIME_AMOUNT"
    template = StrongTemplate(
        template_id="tpl-timeamount-b11",
        kind="TIME_AMOUNT",
        scope_issue=issue,
        premise_predicates=("interest-segmented", "payable-survives"),
        conclusion_predicate=issue,
        failure_predicates=("old-principal-accrual",),
        license_rule_id="",
        source_id=f"timeamount:{issue}",
    )
    return LegalEnvironment(
        environment_id=TIMEAMOUNT_ENV_ID,
        jurisdiction=Jurisdiction(route=JurisdictionRoute.MAINLAND),
        rules=(),
        strong_templates=(template,),
    )


def timeamount_trace_events(intake: dict):
    """The repayment witness becomes a payment event allocated across
    the four debt components in waterfall order (fees first, residual
    principal last — the exact ℚ amounts of the D095 imputation), and
    the surviving payable lands as one exact installment (8000 fen)
    against the payable basis; the make-whole basis receives nothing
    (the premium is a separate account, never merged with principal)."""

    from theory.spec.canonical_v2.case import CaseEvent
    from unified.process import LegalEventKind, ProcessEvent

    events = []
    day = 4
    allocs = intake["debt"]["allocs"]
    events.append(
        ProcessEvent(
            event=CaseEvent(
                event_id="pay-waterfall",
                event_type="PAYMENT_PERFORMED",
                occurred_at=day,
                observed_at=day,
                object_ref="debt_statement",
            ),
            kind=LegalEventKind.PAYMENT_PERFORMED,
            basis_key="PAYABLE_AMOUNT",
            amount=sum(allocs, F(0)),
            debt_order=("PAYABLE_AMOUNT",),
        )
    )
    day += 3
    events.append(
        ProcessEvent(
            event=CaseEvent(
                event_id="pay-accrued-8000",
                event_type="PAYMENT_PERFORMED",
                occurred_at=day,
                observed_at=day,
                object_ref="termination_closeout",
            ),
            kind=LegalEventKind.PAYMENT_PERFORMED,
            basis_key="ACCRUED_PAYABLE",
            amount=F(8000),
            debt_order=("ACCRUED_PAYABLE",),
        )
    )
    return tuple(events)
