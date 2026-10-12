"""Independent contract checker for group-11 amount/time entries
(D095-D103, W2-A batch B11).

This module deliberately re-derives every expected value from the demand
contract with its own inline logic (while-scans, its own month/day
arithmetic, Fraction arithmetic); it shares no code with
``timeamount_ref`` (it never imports that module, nor ``calendar_ref``),
takes no witness callbacks, and never uses the main implementation to
generate expectations.  Its third-party oracle is the standard
library's ``datetime.date`` (a genuinely independent proleptic-Gregorian
implementation; ``toordinal`` uses the same 0001-01-01 = 1 convention as
the unified calendar).  Each ``check_D1XX`` returns ``(ok, reasons)``:
``ok`` is True exactly when the observed intermediate result satisfies
the demand's contract on the given structured input.
"""
from __future__ import annotations

import calendar as _stdcalendar
from datetime import date, timedelta
from fractions import Fraction

_Date = tuple[int, int, int]


def _fail(reasons, msg):
    return tuple(reasons) + (msg,)


def _ord(a: _Date) -> int:
    """The epoch day of a date, by the independent stdlib oracle."""

    return date(a[0], a[1], a[2]).toordinal()


def _from_ord(n: int) -> _Date:
    d = date.fromordinal(n)
    return (d.year, d.month, d.day)


def _add_months(n: int, a: _Date) -> _Date:
    """One-shot n-month addition with end-of-month clamping, recomputed
    from the stdlib month lengths."""

    y, m, d = a
    idx = (y * 12 + (m - 1)) + n
    ny, nm = idx // 12, idx % 12 + 1
    last = _stdcalendar.monthrange(ny, nm)[1]
    return (ny, nm, min(d, last))


def _is_weekend(n: int) -> bool:
    """The synthetic weekend table recomputed: epoch day mod 7 in {5, 6}."""

    return n % 7 in (5, 6)


def _next_biz(n: int, fuel: int = 7) -> int:
    """Fuel-bounded business-day roll over the synthetic weekend table."""

    while fuel > 0 and _is_weekend(n):
        n += 1
        fuel -= 1
    return n


def _waterfall(pay: Fraction, buckets) -> tuple:
    """The waterfall imputation recomputed with an explicit while scan."""

    allocs = []
    i = 0
    while i < len(buckets):
        take = min(pay, Fraction(buckets[i]))
        allocs.append(take)
        pay = pay - take
        i += 1
    return tuple(allocs)


# ---------------------------------------------------------------------------
# D095
# ---------------------------------------------------------------------------


def check_D095(principal: Fraction, rate: Fraction, a: _Date, m: _Date,
               b: _Date, repayment: Fraction, out: dict):
    reasons = ()
    # exact day counts by the stdlib oracle
    days_a_m = (date(*m) - date(*a)).days
    days_m_b = (date(*b) - date(*m)).days
    days_a_b = (date(*b) - date(*a)).days
    if out["days_a_m"] != days_a_m or out["days_m_b"] != days_m_b \
            or out["days_a_b"] != days_a_b:
        reasons = _fail(reasons, "the day counts diverge from the stdlib "
                                 "date differences")
    if days_a_m + days_m_b != days_a_b:
        reasons = _fail(reasons, "the split points do not tile the whole "
                                 "period (test input broken)")
    principal = Fraction(principal)
    rate = Fraction(rate)
    repayment = Fraction(repayment)
    # segment values: base × rate × exact days
    seg1 = principal * rate * days_a_m
    seg2 = (principal - repayment) * rate * days_m_b
    whole = principal * rate * days_a_b
    if out["seg1"] != seg1 or out["seg2"] != seg2 or out["whole"] != whole:
        reasons = _fail(reasons, "a segment diverges from base × rate × "
                                 "exact days")
    if out["split_conserved"] is not (seg1 + principal * rate * days_m_b
                                      == whole):
        reasons = _fail(reasons, "the split-conservation verdict diverged")
    # the correct total is the segmented accrual on the residual base
    if out["correct_total"] != seg1 + seg2:
        reasons = _fail(reasons, "the correct total does not accrue on the "
                                 "residual base after the repayment")
    if out["old_principal_total"] != whole:
        reasons = _fail(reasons, "the old-principal total diverged")
    if repayment > 0 and days_m_b > 0 and rate > 0:
        if whole == seg1 + seg2:
            reasons = _fail(reasons, "the adverse side collapsed (test "
                                     "input broken)")
        if out["old_principal_overstates"] is not (whole > seg1 + seg2):
            reasons = _fail(reasons, "the old-principal overstatement "
                                     "verdict diverged")
    # waterfall imputation: no double-spend, no loss
    buckets = tuple(Fraction(x) for x in out["buckets"])
    expected_allocs = _waterfall(repayment, buckets)
    if out["allocs"] != expected_allocs:
        reasons = _fail(reasons, "the waterfall allocations diverged from "
                                 "the while-scan recomputation")
    total_alloc = sum(expected_allocs, Fraction(0))
    if total_alloc > repayment:
        reasons = _fail(reasons, "the imputation double-spent the payment")
    if total_alloc != min(repayment, sum(buckets, Fraction(0))):
        reasons = _fail(reasons, "the imputation lost part of the payment")
    j = 0
    while j < len(buckets):
        if expected_allocs[j] > buckets[j]:
            reasons = _fail(reasons, "an allocation exceeded its bucket")
        j += 1
    if out["impute_conserved"] is not True:
        reasons = _fail(reasons, "the imputation-conservation verdict "
                                 "misreported")
    if out["impute_within"] is not True:
        reasons = _fail(reasons, "the imputation bound misreported")
    return not reasons, reasons


# ---------------------------------------------------------------------------
# D096
# ---------------------------------------------------------------------------


def check_D096(mult: Fraction, out: dict):
    reasons = ()
    event = _ord((2024, 1, 1))
    historical = _ord((2023, 6, 30))
    if out["event_day"] != event or out["historical_day"] != historical:
        reasons = _fail(reasons, "the epoch days diverge from the stdlib "
                                 "toordinal oracle")
    if historical >= event:
        reasons = _fail(reasons, "the historical day is not before the "
                                 "event day (test input broken)")
    if out["historical_before_event"] is not True:
        reasons = _fail(reasons, "the historical day was placed at or "
                                 "after the event")
    old, new = Fraction(71, 2000), Fraction(69, 2000)
    if out["old_rate"] != old or out["new_rate"] != new:
        reasons = _fail(reasons, "the policy step rates diverged")
    mult = Fraction(mult)
    # as-of selection: the event date decides, not the current date
    if out["correct_base"] != old:
        reasons = _fail(reasons, "the historical period did not take the "
                                 "old benchmark (as-of selection broken)")
    if out["correct_applied"] != mult * old:
        reasons = _fail(reasons, "the applied rate on the historical "
                                 "period diverged")
    if out["backfilled_applied"] != mult * new:
        reasons = _fail(reasons, "the backfilled applied rate diverged")
    if old == new:
        reasons = _fail(reasons, "the policy step is degenerate (test "
                                 "input broken)")
    if out["backfill_diverges"] is not (mult * old != mult * new):
        reasons = _fail(reasons, "the backfill divergence verdict "
                                 "diverged")
    if out["unconfirmed_passes_through"] is not True:
        reasons = _fail(reasons, "the multiple acted on an unconfirmed "
                                 "benchmark")
    return not reasons, reasons


# ---------------------------------------------------------------------------
# D097
# ---------------------------------------------------------------------------


def check_D097(out: dict):
    reasons = ()
    cash, shares, price, fx = (out["cash"], out["shares"], out["price"],
                               out["fx"])
    cash, shares, price, fx = (Fraction(cash), Fraction(shares),
                               Fraction(price), Fraction(fx))
    exact = cash + shares * price
    if out["exact_total"] != exact:
        reasons = _fail(reasons, "the exact total diverged from cash + "
                                 "shares × per-share price")
    # rounding: floor of the Fraction, applied at the declared stage
    def _floor(x: Fraction) -> Fraction:
        return Fraction(x.numerator // x.denominator)
    if out["late_round"] != _floor(exact):
        reasons = _fail(reasons, "the final-stage rounding diverged from "
                                 "the floor")
    if out["early_round"] != _floor(cash) + _floor(shares * price):
        reasons = _fail(reasons, "the mid-stage rounding diverged")
    if _floor(exact) == _floor(cash) + _floor(shares * price):
        reasons = _fail(reasons, "the two rounding stages coincide (test "
                                 "input broken)")
    if out["stages_differ"] is not True:
        reasons = _fail(reasons, "the rounding-stage difference was "
                                 "reported absent — the stage is not "
                                 "explicit")
    # dimension sensitivity: a different per-share price moves the total
    if shares == 0:
        reasons = _fail(reasons, "the share count is zero (test input "
                                 "broken)")
    if out["dimension_sensitive"] is not True:
        reasons = _fail(reasons, "two different per-share prices gave "
                                 "the same total (dimension mixing)")
    # fx commutes with the share multiplication
    if out["fx_consistent"] is not (shares * (price * fx)
                                    == (shares * price) * fx):
        reasons = _fail(reasons, "the fx-consistency verdict diverged")
    if out["fx_total"] != cash + shares * (price * fx):
        reasons = _fail(reasons, "the fx-converted total diverged")
    return not reasons, reasons


# ---------------------------------------------------------------------------
# D098
# ---------------------------------------------------------------------------


def check_D098(facility: Fraction, balance: Fraction, ratio: Fraction,
               out: dict):
    reasons = ()
    facility = Fraction(facility)
    balance = Fraction(balance)
    ratio = Fraction(ratio)
    # trigger = funding date + 6 months (month-end clamped), by the
    # stdlib month lengths
    trig = _add_months(6, out["funding"])
    if out["trigger"] != trig:
        reasons = _fail(reasons, "the trigger date diverged from the "
                                 "6-month month arithmetic")
    early, late = out["early"], out["late"]
    trig_ord, early_ord, late_ord = _ord(trig), _ord(early), _ord(late)
    if out["early_triggered"] is not (trig_ord <= early_ord):
        reasons = _fail(reasons, "the early-prepay trigger verdict "
                                 "diverged")
    if out["late_triggered"] is not (trig_ord <= late_ord):
        reasons = _fail(reasons, "the late-prepay trigger verdict "
                                 "diverged")
    if not (early_ord < trig_ord <= late_ord):
        reasons = _fail(reasons, "the prepay dates do not straddle the "
                                 "trigger (test input broken)")
    if out["premium_early"] != 0:
        reasons = _fail(reasons, "a prepay before the trigger carried a "
                                 "make-whole premium")
    if out["premium_late"] != balance * ratio:
        reasons = _fail(reasons, "the triggered premium diverged from "
                                 "balance × ratio")
    if out["premium_on_facility"] != facility * ratio:
        reasons = _fail(reasons, "the facility-based premium diverged")
    if facility == balance or ratio == 0:
        reasons = _fail(reasons, "the misbase case is degenerate (test "
                                 "input broken)")
    if out["facility_misbase_visible"] is not (facility * ratio
                                               != balance * ratio):
        reasons = _fail(reasons, "the premium computed on the original "
                                 "facility was conflated with the "
                                 "balance-based premium")
    if out["untriggered_zero_ratio_free"] != 0:
        reasons = _fail(reasons, "an untriggered quote still depended "
                                 "on the ratio")
    if out["accounts_separate"] is not True:
        reasons = _fail(reasons, "the premium and the balance were "
                                 "merged into one account")
    return not reasons, reasons


# ---------------------------------------------------------------------------
# D099
# ---------------------------------------------------------------------------


def check_D099(out: dict):
    reasons = ()
    anchor, day = out["anchor"], out["day"]
    notice_len, cure_len = out["notice_len"], out["cure_len"]
    if notice_len >= cure_len:
        reasons = _fail(reasons, "the notice period is not shorter than "
                                 "the cure period (test input broken)")
    notice_base = _ord(anchor) + notice_len
    cure_base = _ord(anchor) + cure_len
    if out["notice_base"] != notice_base or out["cure_base"] != cure_base:
        reasons = _fail(reasons, "the base deadlines diverge from the "
                                 "stdlib day counts")
    if out["base_strictly_ordered"] is not (notice_base < cure_base):
        reasons = _fail(reasons, "the period strict order diverged "
                                 "(longer period, later deadline)")
    notice_deadline = _next_biz(notice_base)
    cure_deadline = _next_biz(cure_base)
    if out["notice_deadline"] != notice_deadline \
            or out["cure_deadline"] != cure_deadline:
        reasons = _fail(reasons, "the rolled deadlines diverged from "
                                 "the weekend-table roll")
    if out["roll_idempotent"] is not (_next_biz(notice_deadline)
                                      == notice_deadline):
        reasons = _fail(reasons, "the deadline_effect roll is not "
                                 "idempotent")
    if not (notice_deadline <= day < cure_deadline):
        reasons = _fail(reasons, "the given day does not fall between "
                                 "the two deadlines (test input broken)")
    if out["notice_arrived"] is not True:
        reasons = _fail(reasons, "the notice deadline was reported "
                                 "unarrived")
    if out["cure_arrived"] is not False:
        reasons = _fail(reasons, "the cure deadline was reported "
                                 "arrived (the 60-day cure substituted "
                                 "by the 30-day notice)")
    # evidence status: either missing blocks the right
    def _right(arrived: bool, evidenced: bool) -> bool:
        return bool(arrived and evidenced)
    if out["right_from_notice_only"] is not True:
        reasons = _fail(reasons, "the arrived+evidenced notice right "
                                 "did not arise")
    if out["cure_right_arises"] is not False:
        reasons = _fail(reasons, "the termination right arose while the "
                                 "cure period had not expired")
    if out["unevidenced_blocks"] is not True:
        reasons = _fail(reasons, "an unevidenced arrival produced the "
                                 "right (evidence state ignored)")
    return not reasons, reasons


# ---------------------------------------------------------------------------
# D100
# ---------------------------------------------------------------------------


def check_D100(out: dict):
    reasons = ()
    deadline, lead = out["deadline"], out["lead"]
    deadline_ord = _ord(deadline)
    start_ord = deadline_ord - lead
    if out["start"] != _from_ord(start_ord):
        reasons = _fail(reasons, "the back-scheduled start diverged "
                                 "from the stdlib day subtraction")
    if out["roundtrip"] is not (_ord(_from_ord(start_ord)) + lead
                                == deadline_ord):
        reasons = _fail(reasons, "the forward roundtrip did not return "
                                 "the deadline (precedence constraint "
                                 "broken)")
    past_floor, ok_floor = out["past_floor"], out["ok_floor"]
    if _ord(past_floor) <= start_ord:
        reasons = _fail(reasons, "the past floor does not lie after the "
                                 "start (test input broken)")
    if _ord(ok_floor) > start_ord:
        reasons = _fail(reasons, "the ok floor lies after the start "
                                 "(test input broken)")
    if out["past_floor_conflict"] is not True:
        reasons = _fail(reasons, "a start date in the past still "
                                 "yielded an executable plan (no "
                                 "conflict report)")
    if out["ok_floor_plan"] != _from_ord(start_ord):
        reasons = _fail(reasons, "the feasible plan diverged from the "
                                 "back-scheduled start")
    if out["start_before_past_floor"] is not True:
        reasons = _fail(reasons, "the start/floor order verdict diverged")
    return not reasons, reasons


# ---------------------------------------------------------------------------
# D101
# ---------------------------------------------------------------------------


def check_D101(out: dict):
    reasons = ()
    debt, cost, prob = (Fraction(out["debt"]), Fraction(out["cost"]),
                        Fraction(out["prob"]))
    contingent = tuple(Fraction(c) for c in out["contingent"])
    kinds = out["kinds"]
    if len(kinds) != 4 or len(set(kinds)) != 4:
        reasons = _fail(reasons, "the four exposure kinds are not "
                                 "pairwise distinct")
    if out["kinds_pairwise_distinct"] is not True:
        reasons = _fail(reasons, "the kind-distinctness verdict diverged")
    if not (0 < prob < 1):
        reasons = _fail(reasons, "the declared risk function is not a "
                                 "probability (test input broken)")
    # a probability-weighted contingent is strictly less than the same
    # amount realized
    j = 0
    discount_expected = True
    while j < len(contingent):
        if contingent[j] <= 0 or prob * contingent[j] >= contingent[j]:
            discount_expected = False
        j += 1
    if out["risk_discounts"] is not discount_expected:
        reasons = _fail(reasons, "the risk-discount verdict diverged "
                                 "(a risk figure is not a realized loss)")
    declared = debt + cost + sum((prob * c for c in contingent),
                                 Fraction(0))
    mixed = debt + cost + sum(contingent, Fraction(0))
    double = mixed + sum((prob * c for c in contingent), Fraction(0))
    if out["declared_total"] != declared:
        reasons = _fail(reasons, "the declared aggregation diverged "
                                 "from the risk-function recomputation")
    if out["risk_as_realized"] != mixed:
        reasons = _fail(reasons, "the risk-as-realized total diverged")
    if out["risk_double_counted"] != double:
        reasons = _fail(reasons, "the double-counted total diverged")
    if mixed == declared:
        reasons = _fail(reasons, "the mixing case is degenerate (test "
                                 "input broken)")
    if out["mixing_overstates"] is not (mixed != declared
                                        and mixed > declared):
        reasons = _fail(reasons, "the mixing-overstatement verdict "
                                 "diverged")
    if out["double_counts"] is not (double != declared
                                    and double > declared):
        reasons = _fail(reasons, "the double-counting verdict diverged")
    # exposure periods stay exact integers (leap vs flat first quarter)
    leap_q1 = (date(2024, 3, 31) - date(2024, 1, 1)).days
    flat_q1 = (date(2023, 3, 31) - date(2023, 1, 1)).days
    if out["leap_q1_days"] != leap_q1 or out["flat_q1_days"] != flat_q1:
        reasons = _fail(reasons, "the exposure period day counts "
                                 "diverge from the stdlib oracle")
    if out["period_days"] != leap_q1:
        reasons = _fail(reasons, "the period day count diverged")
    return not reasons, reasons


# ---------------------------------------------------------------------------
# D102
# ---------------------------------------------------------------------------


def check_D102(out: dict):
    reasons = ()
    term_day = _ord(out["term"])
    if out["term_day"] != term_day:
        reasons = _fail(reasons, "the termination day diverges from the "
                                 "stdlib toordinal oracle")
    accrued_start, accrued_end = out["accrued_span"]
    future_start, future_end = out["future_span"]
    accrued_end_ord = _ord(accrued_end)
    future_start_ord, future_end_ord = _ord(future_start), _ord(future_end)
    if not (accrued_end_ord <= term_day):
        reasons = _fail(reasons, "the accrued payable does not complete "
                                 "before the termination (test input "
                                 "broken)")
    if not (term_day < future_start_ord):
        reasons = _fail(reasons, "the future obligation does not start "
                                 "after the termination (test input "
                                 "broken)")
    # survival rules: accrued survives verbatim; wholly-future
    # performance is extinguished
    if out["accrued_amount"] != Fraction(8000):
        reasons = _fail(reasons, "the accrued payable did not survive "
                                 "verbatim")
    if out["accrued_survives"] is not True:
        reasons = _fail(reasons, "the accrued-survival verdict "
                                 "misreported")
    if out["future_amount"] != 0:
        reasons = _fail(reasons, "the wholly-future performance "
                                 "obligation was not extinguished")
    if out["future_extinguished"] is not True:
        reasons = _fail(reasons, "the future-extinguish verdict "
                                 "misreported")
    if out["blanket_clearing_zero"] != Fraction(0):
        reasons = _fail(reasons, "the blanket-clearing figure diverged")
    if out["blanket_clear_deletes_accrued"] is not True:
        reasons = _fail(reasons, "blanket clearing was not distinguished "
                                 "from the survival update (an accrued "
                                 "payable deleted)")
    # survival ray law: the closed period lies after the termination
    # day exactly when its start does
    ray_expected = all(term_day <= x for x in
                       (future_start_ord, term_day + 15, future_end_ord))
    if out["ray_law_start"] is not (term_day <= future_start_ord):
        reasons = _fail(reasons, "the ray-law start verdict diverged")
    if out["period_after_term_iff_start"] is not (
            (term_day <= future_start_ord) == ray_expected):
        reasons = _fail(reasons, "the survival ray law diverged (the "
                                 "closed period's position is not "
                                 "decided by its start)")
    return not reasons, reasons


# ---------------------------------------------------------------------------
# D103
# ---------------------------------------------------------------------------


def check_D103(out: dict):
    reasons = ()
    exclusions = out["exclusions"]

    def _wc(accounts) -> Fraction:
        total = Fraction(0)
        i = 0
        while i < len(accounts):
            name, value = accounts[i]
            keep = True
            j = 0
            while j < len(exclusions):
                if name == exclusions[j]:
                    keep = False
                j += 1
            if keep:
                total += Fraction(value)
            i += 1
        return total

    if out["target"] != _wc(out["scope"]):
        reasons = _fail(reasons, "the target working capital diverged "
                                 "from the while-scan recomputation")
    if out["closing"] != _wc(tuple((n, v) for n, v in
                                   [("receivables", Fraction(5200)),
                                    ("inventory", Fraction(3000)),
                                    ("payables", Fraction(-2000))])):
        reasons = _fail(reasons, "the closing working capital diverged")
    if out["adjustment"] != out["closing"] - out["target"]:
        reasons = _fail(reasons, "the adjustment is not the closing-minus-"
                                 "target reconciliation difference")
    if out["exclusion_neutral"] is not True:
        reasons = _fail(reasons, "an excluded account moved the working "
                                 "capital under its own exclusion")
    mixed_closing = _wc(tuple(list(out["scope"])
                              + [("cash", Fraction(1000))]))
    # (the mixed side swaps in the closing receivables too)
    mixed_closing = _wc((("receivables", Fraction(5200)),
                         ("inventory", Fraction(3000)),
                         ("payables", Fraction(-2000)),
                         ("cash", Fraction(1000))))
    if out["mixed_scope_closing"] != mixed_closing:
        reasons = _fail(reasons, "the mixed-scope closing diverged")
    if out["mixed_scope_adjustment"] != (mixed_closing
                                         - _wc(out["scope"])):
        reasons = _fail(reasons, "the mixed-scope adjustment diverged")
    if out["mixed_scope_adjustment"] == out["adjustment"]:
        reasons = _fail(reasons, "the scope mixing is degenerate (test "
                                 "input broken)")
    if out["scope_mix_diverges"] is not True:
        reasons = _fail(reasons, "a different account scope still "
                                 "reported this definition's exact "
                                 "difference")
    return not reasons, reasons
