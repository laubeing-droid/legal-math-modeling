"""Independent contract checker for group-09 M&A entries (D077-D086).

This module deliberately re-derives every expected value from the demand
contract with its own inline logic (while-scans, negated-condition forms);
it shares no code with ``mna_ref`` (it never imports that module),
takes no witness callbacks, and never uses the main implementation to
generate expectations.  Each ``check_D0XX`` returns ``(ok, reasons)``:
``ok`` is True exactly when the observed intermediate result satisfies
the demand's contract on the given structured input.
"""
from __future__ import annotations

from fractions import Fraction
from typing import Sequence


def _fail(reasons, msg):
    return tuple(reasons) + (msg,)


# ---------------------------------------------------------------------------
# D077
# ---------------------------------------------------------------------------

_SIGNING, _BRINGDOWN = 0, 1


def _verdict(row, t):
    if t == _SIGNING:
        return row[2]
    return row[3]


def check_D077(rows: Sequence[tuple], times: Sequence[int], out: dict):
    reasons = ()
    # one separate verdict per (row, time) pair — the per-time map
    i = 0
    while i < len(rows):
        j = 0
        while j < len(times):
            expected = _verdict(rows[i], times[j])
            if out["verdicts"].get((rows[i][0], times[j])) != expected:
                reasons = _fail(reasons,
                                f"verdict for ({rows[i][0]!r}, t={times[j]}) "
                                "diverges from the row's own per-time "
                                "status")
            j += 1
        i += 1
    if len(out["per_row_per_time"]) != len(rows) * len(times):
        reasons = _fail(reasons, "the verdict list is not one entry per "
                                 "(row, time) pair")
    # the bring-down standard is the row's own field
    i = 0
    while i < len(rows):
        if out["standards"].get(rows[i][0]) != rows[i][1]:
            reasons = _fail(reasons,
                            f"standard of {rows[i][0]!r} diverges from its "
                            "own row field")
        i += 1
    # adverse case: true at signing, false at closing — two different
    # verdicts; signing truth never proves closing truth
    adverse = out["adverse_row"]
    if adverse[2] is True and adverse[3] is False:
        if out["adverse_split"] != (True, False):
            reasons = _fail(reasons, "the adverse row's split verdict "
                                     "diverged")
        if out["signing_true_proves_nothing"] is not True:
            reasons = _fail(reasons, "signing truth was read as proving "
                                     "closing truth")
    else:
        reasons = _fail(reasons, "the adverse witness row is not "
                                 "(signing true, closing false)")
    return not reasons, reasons


# ---------------------------------------------------------------------------
# D078
# ---------------------------------------------------------------------------


def _hit(scope_key, clause_key, is_exception, dispro):
    if scope_key == clause_key and is_exception is True:
        return dispro
    return True


def check_D078(scope_key: str, clause_key: str, is_exception: bool,
               dispro: bool, out: dict):
    reasons = ()
    if out["hit"] is not _hit(scope_key, clause_key, is_exception, dispro):
        reasons = _fail(reasons, "the scoped MAE evaluation diverges from "
                                 "the main-definition/exception/proviso "
                                 "rule")
    # the four scoped outcomes, independently re-derived
    if out["main_event"] is not _hit(clause_key, clause_key, False, False):
        reasons = _fail(reasons, "a main-definition event failed to hit")
    if out["in_scope_exception"] is not _hit(clause_key, clause_key, True,
                                            False):
        reasons = _fail(reasons, "an in-scope exception without "
                                 "disproportionate impact was not excluded")
    if out["in_scope_dispro"] is not _hit(clause_key, clause_key, True, True):
        reasons = _fail(reasons, "the disproportionate-impact proviso "
                                 "failed to put the event back in the "
                                 "main definition")
    if out["out_of_scope"] is not _hit("scope-other", clause_key, True,
                                       False):
        reasons = _fail(reasons, "an out-of-scope exception changed the "
                                 "outcome")
    # the modifier is load-bearing: losing the proviso clause merges the
    # two conclusions
    a = _hit(clause_key, clause_key, True, True)
    b = _hit(clause_key, clause_key, True, False)
    if out["modifier_load_bearing"] is not (a != b):
        reasons = _fail(reasons, "the modifier-load-bearing verdict "
                                 "diverged")
    if a == b:
        reasons = _fail(reasons, "the disproportionate-impact modifier "
                                 "changed nothing (the proviso clause was "
                                 "lost)")
    return not reasons, reasons


# ---------------------------------------------------------------------------
# D079
# ---------------------------------------------------------------------------

_ACTUAL, _CONSTRUCTIVE, _INVESTIGATED = 0, 1, 2


def _kn(rows, group, kind):
    i = 0
    while i < len(rows):
        if rows[i][0] == group and rows[i][1] == kind:
            return rows[i][2]
        i += 1
    return None


def check_D079(rows: Sequence[tuple], out: dict):
    reasons = ()
    tags = out["tags"]
    i = 0
    while i < len(tags):
        j = 0
        while j < len(tags):
            if i != j and tags[i] == tags[j]:
                reasons = _fail(reasons,
                                f"knowledge standards {i} and {j} share "
                                "one tag")
            j += 1
        i += 1
    if tuple(tags) != (_ACTUAL, _CONSTRUCTIVE, _INVESTIGATED):
        reasons = _fail(reasons, "the three knowledge tags diverge from "
                                 "the declared typed three")
    # the lookups are keyed by (group, standard)
    if out["employee_actual"] != _kn(rows, "employee", _ACTUAL):
        reasons = _fail(reasons, "the employee actual-knowledge lookup "
                                 "diverged")
    if out["management_investigated"] != _kn(rows, "management",
                                             _INVESTIGATED):
        reasons = _fail(reasons, "the management investigated-knowledge "
                                 "lookup diverged")
    # adverse case: an employee row answers no management query
    has_mgmt = False
    i = 0
    while i < len(rows):
        if rows[i][0] == "management" and rows[i][1] == _INVESTIGATED:
            has_mgmt = True
        i += 1
    if not has_mgmt and out["management_investigated"] is not None:
        reasons = _fail(reasons, "an employee's actual knowledge was read "
                                 "as the management's investigated "
                                 "knowledge")
    if out["employee_is_not_management"] is not (
            out["management_investigated"] is None):
        reasons = _fail(reasons, "the employee-is-not-management verdict "
                                 "diverged")
    # a different standard tag is a different record — never one boolean
    if out["kind_changes_record"] is not True:
        reasons = _fail(reasons, "the knowledge standard was collapsed "
                                 "into one undifferentiated field")
    return not reasons, reasons


# ---------------------------------------------------------------------------
# D080
# ---------------------------------------------------------------------------


def _legal(exception, precond):
    return exception is True and precond is True


def check_D080(acts: Sequence[tuple], out: dict):
    reasons = ()
    # the truth table: only (true, true) is legal
    for e in (False, True):
        for p in (False, True):
            if out["truth_table"].get((e, p)) is not _legal(e, p):
                reasons = _fail(reasons,
                                f"truth-table entry ({e}, {p}) diverged")
    # the legal set is the two-gate filter of the candidate table
    expected = []
    i = 0
    while i < len(acts):
        if _legal(acts[i][1], acts[i][2]):
            expected.append(acts[i])
        i += 1
    if tuple(out["legal"]) != tuple(expected):
        reasons = _fail(reasons, "the legal action set diverges from the "
                                 "two-gate filter")
    # no-exception rows never enter (the general ban is not erased)
    i = 0
    while i < len(acts):
        if acts[i][1] is False and acts[i] in tuple(out["legal"]):
            reasons = _fail(reasons, "a no-exception action entered the "
                                     "legal set (the ban was erased)")
        i += 1
    # an exception without its precondition never enters
    i = 0
    while i < len(acts):
        if acts[i][1] is True and acts[i][2] is False \
                and acts[i] in tuple(out["legal"]):
            reasons = _fail(reasons, "an exception action without its "
                                     "precondition entered the legal set")
        i += 1
    if out["ban_not_erased"] is not True:
        reasons = _fail(reasons, "the ban-not-erased verdict diverged")
    if out["exception_needs_precond"] is not True:
        reasons = _fail(reasons, "the exception-needs-precondition verdict "
                                 "diverged")
    return not reasons, reasons


# ---------------------------------------------------------------------------
# D081
# ---------------------------------------------------------------------------


def _can(day, window_end, matched):
    if day <= window_end:
        return False
    if matched is True:
        return False
    return True


def check_D081(day: int, notice_day: int, window_end: int, rec_changed: bool,
               matched: bool, out: dict):
    reasons = ()
    # the evaluation day carries its own event order: the notice
    # precedes it
    if out["notice_order_ok"] is not (notice_day <= day):
        reasons = _fail(reasons, "the notice-order verdict diverged")
    if out["terminable"] is not _can(day, window_end, matched):
        reasons = _fail(reasons, "the termination feasibility diverges "
                                 "from the window/order rule")
    # adverse case: no terminable state before the window expires —
    # not by notice, not by a changed recommendation
    probe_day = day if day <= window_end else window_end
    if out["terminable_before_expiry"] is not _can(probe_day, window_end,
                                                   matched):
        reasons = _fail(reasons, "the pre-expiry termination verdict "
                                 "diverged")
    if day <= window_end and out["terminable"] is not False:
        reasons = _fail(reasons, "a terminable state was generated before "
                                 "the matching window expired")
    if rec_changed is True and day <= window_end \
            and out["terminable"] is not False:
        reasons = _fail(reasons, "a changed recommendation terminated the "
                                 "deal inside the window")
    # the boundary day itself is still inside the window; after it, only
    # an unmatched deal is terminable
    if out["boundary_day_not_terminable"] is not True:
        reasons = _fail(reasons, "the boundary day was read as already "
                                 "terminable")
    if out["after_window_unmatched"] is not True:
        reasons = _fail(reasons, "an unmatched deal after the window "
                                 "failed to be terminable")
    if out["after_window_matched"] is not False:
        reasons = _fail(reasons, "a matched deal after the window was "
                                 "still terminable")
    return not reasons, reasons


# ---------------------------------------------------------------------------
# D082
# ---------------------------------------------------------------------------


def _superior(price, floor, in_window):
    return floor < Fraction(price) and in_window is True


def _intervening(unforeseen, in_window):
    return unforeseen is True and in_window is True


def check_D082(price: Fraction, floor: Fraction, unforeseen: bool,
               out: dict):
    reasons = ()
    if out["superior_in_window"] is not _superior(price, floor, True):
        reasons = _fail(reasons, "the in-window superior-offer verdict "
                                 "diverged")
    if out["superior_out_window"] is not False:
        reasons = _fail(reasons, "a superior offer was qualified outside "
                                 "its time bound")
    if out["intervening_in_window"] is not _intervening(unforeseen, True):
        reasons = _fail(reasons, "the in-window intervening-event verdict "
                                 "diverged")
    if out["intervening_out_window"] is not False:
        reasons = _fail(reasons, "an intervening event was qualified "
                                 "outside its time bound")
    # adverse case: an equal (non-better) new offer is neither superior
    # nor (as a mere offer) intervening — the every-new-offer shortcut
    # is rejected
    if out["equal_price_not_superior"] is not True:
        reasons = _fail(reasons, "a non-better new offer was qualified "
                                 "as superior")
    if _intervening(unforeseen, True) is False \
            and out["intervening_in_window"] is not False:
        reasons = _fail(reasons, "a foreseeable new offer was counted as "
                                 "an intervening event")
    if Fraction(out["price"]) == Fraction(out["floor"]) \
            and out["prices_differ"]:
        reasons = _fail(reasons, "equal prices were reported as "
                                 "differing")
    if out["prices_differ"] is not (Fraction(price) != Fraction(floor)):
        reasons = _fail(reasons, "the price-difference verdict diverged")
    return not reasons, reasons


# ---------------------------------------------------------------------------
# D083
# ---------------------------------------------------------------------------


def _allowed(ordinary, consent, prohibited):
    return prohibited is False and (ordinary is True or consent is True)


def check_D083(rows: Sequence[tuple], out: dict):
    reasons = ()
    if len(out["decisions"]) != len(rows):
        reasons = _fail(reasons, "the decision record dropped an action")
    # the three inputs stay separate record fields, and the verdict is
    # the conjunction of the necessary gates
    i = 0
    while i < len(rows):
        action, ordinary, consent, prohibited = rows[i]
        row = out["decisions"][i]
        if row["action"] != action or row["ordinary"] is not ordinary \
                or row["consent"] is not consent \
                or row["prohibited"] is not prohibited:
            reasons = _fail(reasons,
                            f"decision {i} altered an input field")
        if row["allowed"] is not _allowed(ordinary, consent, prohibited):
            reasons = _fail(reasons,
                            f"decision {i} diverges from the "
                            "all-necessary-gates rule")
        i += 1
    # adverse case: one consent receipt never exempts an independent
    # prohibition
    i = 0
    while i < len(rows):
        if rows[i][3] is True and out["decisions"][i]["allowed"] is True:
            reasons = _fail(reasons, "a consent receipt exempted an "
                                     "independent prohibition")
        i += 1
    if out["consent_never_exempts_prohibition"] is not True:
        reasons = _fail(reasons, "the consent-never-exempts verdict "
                                 "diverged")
    if out["no_gate_no_action"] is not True:
        reasons = _fail(reasons, "the no-gate-no-action verdict diverged")
    return not reasons, reasons


# ---------------------------------------------------------------------------
# D084
# ---------------------------------------------------------------------------


def _remedies(closing_alive, wants_sp, wants_term):
    out = []
    if closing_alive is True and wants_sp is True:
        out.append("specific-performance")
    if closing_alive is False and wants_term is True:
        out.append("termination")
    if wants_sp is True or wants_term is True:
        out.append("damages")
    return tuple(out)


def check_D084(out: dict):
    reasons = ()
    for alive in (False, True):
        for sp in (False, True):
            for term in (False, True):
                expected = _remedies(alive, sp, term)
                if out["combos"].get((alive, sp, term)) != expected:
                    reasons = _fail(reasons,
                                    f"combo (alive={alive}, sp={sp}, "
                                    f"term={term}) diverged from the "
                                    "compatibility policy")
    # the both-requested witnesses
    if out["alive_both"] != _remedies(True, True, True):
        reasons = _fail(reasons, "the alive-both witness diverged")
    if out["dead_both"] != _remedies(False, True, True):
        reasons = _fail(reasons, "the dead-both witness diverged")
    # adverse case: mutually exclusive remedies never jointly listed
    if out["mutually_exclusive"] is not True:
        reasons = _fail(reasons, "mutually exclusive remedies were "
                                 "jointly listed as available")
    i = 0
    keys = list(out["combos"].keys())
    while i < len(keys):
        v = out["combos"][keys[i]]
        if "specific-performance" in v and "termination" in v:
            reasons = _fail(reasons, "specific performance and termination "
                                     "were both listed for one closing "
                                     "state")
        i += 1
    # damages stay compatible with either remedy
    if out["damages_compatible"] is not True:
        reasons = _fail(reasons, "the damages-compatibility verdict "
                                 "diverged")
    return not reasons, reasons


# ---------------------------------------------------------------------------
# D085
# ---------------------------------------------------------------------------


def _payout(vested, separated, price):
    if vested is True and separated is True:
        return Fraction(price)
    return Fraction(0)


def check_D085(records: Sequence[tuple], out: dict):
    reasons = ()
    if len(out["records"]) != len(records):
        reasons = _fail(reasons, "the equity ledger dropped a record")
    i = 0
    while i < len(records):
        kind, vested, separated, price = records[i]
        row = out["records"][i]
        # every field is read from the same record
        if row["kind"] != kind or row["vested"] is not vested \
                or row["separated"] is not separated \
                or Fraction(row["price"]) != Fraction(price):
            reasons = _fail(reasons,
                            f"record {i} altered an award field")
        if Fraction(row["payout"]) != _payout(vested, separated, price):
            reasons = _fail(reasons,
                            f"record {i} payout diverges from the "
                            "double-trigger rule")
        i += 1
    # adverse case: no second trigger — the payout is exactly zero
    if Fraction(out["witness_no_second_trigger"]) != Fraction(0):
        reasons = _fail(reasons, "full double-trigger compensation was "
                                 "paid without the second trigger")
    if out["no_second_trigger_zero"] is not True:
        reasons = _fail(reasons, "the no-second-trigger-zero verdict "
                                 "diverged")
    if Fraction(out["witness_paid"]) != Fraction(7, 4):
        reasons = _fail(reasons, "the vested both-trigger witness payout "
                                 "diverged from the exact price")
    if out["fields_are_one_record"] is not True:
        reasons = _fail(reasons, "the vesting and separation fields were "
                                 "collapsed into one")
    return not reasons, reasons


# ---------------------------------------------------------------------------
# D086
# ---------------------------------------------------------------------------


def _status(rows, entity, period, prop):
    i = 0
    while i < len(rows):
        if rows[i][0] == entity and rows[i][1] == period \
                and rows[i][2] == prop:
            return rows[i][3]
        i += 1
    return None


def _witness(a, b):
    if a == b:
        return ()
    return ("entity/period",)


def check_D086(rows: Sequence[tuple], entity: str, period: str, prop: str,
               structure_status, out: dict):
    reasons = ()
    # the lookup is keyed on both entity and period
    if out["disclosure"] != _status(rows, entity, period, prop):
        reasons = _fail(reasons, "the disclosure lookup diverges from the "
                                 "same-key table scan")
    if out["structure_status"] is not structure_status:
        reasons = _fail(reasons, "the structure-side status was altered")
    # the witness is empty exactly when the two carriers agree
    if out["witness"] != _witness(structure_status, out["disclosure"]):
        reasons = _fail(reasons, "the difference witness diverges from the "
                                 "same-key comparison")
    if structure_status == out["disclosure"] and out["witness"] != ():
        reasons = _fail(reasons, "a witness was produced for agreeing "
                                 "carriers")
    if structure_status != out["disclosure"] and out["witness"] == ():
        reasons = _fail(reasons, "differing same-key carriers produced no "
                                 "difference witness")
    # adverse case: an unknown disclosure entry is never warranted-true
    if out["unknown_not_warranted"] is not True:
        reasons = _fail(reasons, "an unknown disclosure entry was read as "
                                 "a warranted-true row")
    if _status(rows, entity, period, prop) is None \
            and out["disclosure"] is True:
        reasons = _fail(reasons, "an unknown (no-row) disclosure entry "
                                 "was reported as true")
    if out["same_key_agrees"] is not True:
        reasons = _fail(reasons, "the same-key self-comparison produced a "
                                 "witness")
    return not reasons, reasons
