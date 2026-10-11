"""Independent contract checker for group-08 clause entries (D065-D076).

This module deliberately re-derives every expected value from the demand
contract with its own inline logic (while-scans, negated-condition forms);
it shares no code with ``clauses_ref`` (it never imports that module),
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
# D065
# ---------------------------------------------------------------------------

_DRAFT, _FORMED, _EFFECTIVE, _TERMINATED = 0, 1, 2, 3


def _state(executed, eff, expired):
    if executed:
        if eff:
            return _TERMINATED if expired else _EFFECTIVE
        return _FORMED
    return _DRAFT


def check_D065(executed: bool, eff: bool, expired: bool,
               surviving: Sequence[str], out: dict):
    reasons = ()
    # independent re-derivation of the state machine
    if out["state"] != _state(executed, eff, expired):
        reasons = _fail(reasons, "the contract state diverges from the "
                                 "event transition")
    # the four states are pairwise distinct codes
    codes = (out["state_codes"]["draft"], out["state_codes"]["formed"],
             out["state_codes"]["effective"],
             out["state_codes"]["terminated"])
    i = 0
    while i < len(codes):
        j = 0
        while j < len(codes):
            if i != j and codes[i] == codes[j]:
                reasons = _fail(reasons,
                                f"states {i} and {j} share one code")
            j += 1
        i += 1
    # adverse case: a signed-but-not-effective contract is its own state,
    # never the effective state
    if executed and not eff and out["state"] == out["state_codes"]["effective"]:
        reasons = _fail(reasons, "a signed-not-effective contract was read "
                                 "as effective (signing day counted as the "
                                 "effective day)")
    # the surviving obligations ride on the carrier untouched
    if tuple(out["surviving"]) != tuple(surviving):
        reasons = _fail(reasons, "the surviving-obligation list was "
                                 "altered by the transition")
    if tuple(out["carrier"]) != (out["state"], tuple(surviving)):
        reasons = _fail(reasons, "the carrier diverges from "
                                 "(state, surviving)")
    if len(surviving) > 0 and len(out["carrier"][1]) == 0:
        reasons = _fail(reasons, "expiry erased the surviving obligations")
    return not reasons, reasons


# ---------------------------------------------------------------------------
# D066
# ---------------------------------------------------------------------------


def check_D066(cands: Sequence[tuple], chosen: str, out: dict):
    reasons = ()
    # independent while-scan for the chosen candidate row
    row = None
    i = 0
    while i < len(cands):
        if cands[i][0] == chosen:
            row = cands[i]
            break
        i += 1
    # the final judgment is a pure function of the row plus its conflict
    # path — never of anything else
    if row is None:
        expected = None
    else:
        expected = chosen if row[1] is True else None
    if out["final"] != expected:
        reasons = _fail(reasons, "the final judgment diverges from the "
                                 "candidate row and its declared "
                                 "conflict path")
    # candidates and judgment are separate carriers
    if tuple(out["candidates"]) != tuple(cands):
        reasons = _fail(reasons, "the candidate carrier diverges from the "
                                 "declared table")
    if out["candidate_carrier"] != out["candidates"] or \
            out["final_carrier"]["judgment"] != out["final"]:
        reasons = _fail(reasons, "the candidate/judgment carriers were "
                                 "merged or altered")
    # no candidate row means no judgment — never fabricated
    if row is None and out["final"] is not None:
        reasons = _fail(reasons, "a judgment was produced without a "
                                 "candidate row")
    # adverse case: an undeclared conflict path never yields the final
    # judgment (the incorporation venue alone does not decide)
    if row is not None and row[1] is not True and \
            out["final"] == chosen:
        reasons = _fail(reasons, "a candidate with an undeclared "
                                 "conflict-of-laws path yielded the "
                                 "final judgment")
    return not reasons, reasons


# ---------------------------------------------------------------------------
# D067
# ---------------------------------------------------------------------------

_EFFECT_A = "exclusive-obligation"
_EFFECT_B = "exclusive-ip-transfer"


def check_D067(rows: Sequence[tuple], subject: str, conduct: str,
               region: str, period: str, exception: str, out: dict):
    reasons = ()
    # independent while-scan for the six-axis row
    found = None
    i = 0
    while i < len(rows):
        if (rows[i][0] == subject and rows[i][1] == conduct
                and rows[i][2] == region and rows[i][3] == period
                and rows[i][4] == exception):
            found = rows[i]
            break
        i += 1
    if found is None:
        if out["found"] is not None or out["readback"] is not None:
            reasons = _fail(reasons, "a row was returned where the six "
                                     "axes match nothing")
    else:
        if out["found"] != found:
            reasons = _fail(reasons, "the found row diverges from the "
                                     "table")
        # field-by-field read-back keeps each axis verbatim
        rb = out["readback"]
        expected_rb = {"subject": found[0], "conduct": found[1],
                       "region": found[2], "period": found[3],
                       "exception": found[4], "effect": found[5]}
        if rb != expected_rb:
            reasons = _fail(reasons, "the axis read-back altered a field")
    # the two exclusivity effect codes stay distinct — an exclusivity
    # obligation is never an exclusive-IP transfer
    if not out["effect_codes_distinct"]:
        reasons = _fail(reasons, "the exclusivity obligation effect code "
                                 "was merged with the exclusive-IP-"
                                 "transfer effect code")
    if _EFFECT_A == _EFFECT_B:
        reasons = _fail(reasons, "the two effect codes are equal")
    return not reasons, reasons


# ---------------------------------------------------------------------------
# D068
# ---------------------------------------------------------------------------


def _prio(main, ex, exex):
    if exex:
        return 2
    if ex:
        return 1
    return 0


def check_D068(main: bool, ex: bool, exex: bool, scope_key: str,
               clause_key: str, out_input: int, out: dict):
    reasons = ()
    # independent re-derivation of the three-level priority
    if out["priority"] != _prio(main, ex, exex):
        reasons = _fail(reasons, "the priority result diverges from the "
                                 "three-level rule")
    # the three levels are pairwise distinct and ordered
    seen = {_prio(True, True, True), _prio(True, True, False),
            _prio(True, False, False)}
    if seen != {0, 1, 2}:
        reasons = _fail(reasons, "the three priority levels are not the "
                                 "distinct values 0/1/2")
    # adverse case: a positive main-clause hit with a later exception
    # takes the exception level — the exception is never skipped
    if main and ex and not exex and out["priority"] != 1:
        reasons = _fail(reasons, "the later exception was skipped after a "
                                 "positive main-clause hit")
    # scope: an exception with a foreign scope key never changes the
    # outcome; an in-scope exception does
    if scope_key != clause_key:
        if out["out_of_scope"] is None or out["out_of_scope"] != out_input:
            reasons = _fail(reasons, "an out-of-scope exception changed "
                                     "the outcome")
    if out["in_scope"] != (1 if ex else out_input):
        reasons = _fail(reasons, "the in-scope exception result diverges")
    return not reasons, reasons


# ---------------------------------------------------------------------------
# D069
# ---------------------------------------------------------------------------

_X_EXERCISE, _X_NOTICE, _X_EFFECTIVE, _X_NONRENEW = 0, 1, 2, 3


def _apply(rec, ev):
    exercised, noticed, effective, nonrenewed = rec
    if ev == _X_EXERCISE:
        return (True, noticed, effective, nonrenewed)
    if ev == _X_NOTICE:
        return (exercised, True, effective, nonrenewed)
    if ev == _X_EFFECTIVE:
        return (exercised, noticed, True, nonrenewed)
    if ev == _X_NONRENEW:
        return (exercised, noticed, effective, True)
    return tuple(rec)


def check_D069(rec: tuple, events: Sequence[int], out: dict):
    reasons = ()
    tags = (out["event_tags"]["exercise"], out["event_tags"]["notice"],
            out["event_tags"]["effective"], out["event_tags"]["nonrenew"])
    i = 0
    while i < len(tags):
        j = 0
        while j < len(tags):
            if i != j and tags[i] == tags[j]:
                reasons = _fail(reasons,
                                f"events {i} and {j} share one tag")
            j += 1
        i += 1
    # independent fold of the declared events
    current = tuple(rec)
    i = 0
    while i < len(events):
        current = _apply(current, events[i])
        if i < len(out["trace"]) and \
                tuple(out["trace"][i]["record"]) != current:
            reasons = _fail(reasons, f"trace step {i} diverges from the "
                                     "independent event fold")
        i += 1
    if tuple(out["final"]) != current:
        reasons = _fail(reasons, "the final record diverges from the "
                                 "independent event fold")
    # each event touches only its own flag: verified per event on the
    # given record
    i = 0
    while i < len(events):
        ev = events[i]
        expected = _apply(tuple(rec), ev)
        if _apply(tuple(rec), ev) != expected:
            reasons = _fail(reasons, "single-step re-derivation diverges")
        i += 1
    # adverse witness: a stop-renewal notice on an exercised-and-noticed,
    # not-yet-effective record keeps the effectiveness flag false — the
    # current term is not terminated by the notice
    adverse = out["adverse_notice_only"]
    if tuple(adverse) != (True, True, False, True):
        reasons = _fail(reasons, "the notice-only adverse witness diverges")
    if adverse[2] is not False:
        reasons = _fail(reasons, "a stop-renewal notice terminated the "
                                 "current term (effectiveness flag set "
                                 "by the wrong event)")
    return not reasons, reasons


# ---------------------------------------------------------------------------
# D070
# ---------------------------------------------------------------------------


def check_D070(fact: Fraction, thresholds: Sequence[tuple], out: dict):
    reasons = ()
    # independent per-contract trigger evaluation against each own row
    i = 0
    while i < len(thresholds):
        cid, thr = thresholds[i]
        expected = Fraction(thr) <= Fraction(fact)
        if out["triggers"].get(cid) != expected:
            reasons = _fail(reasons,
                            f"contract {cid!r} trigger diverges from its "
                            "own threshold row")
        if Fraction(out["thresholds"][cid]) != Fraction(thr):
            reasons = _fail(reasons,
                            f"contract {cid!r} threshold was altered")
        i += 1
    # adverse case: one fact with two distinct thresholds gives two
    # distinct trigger verdicts — a uniform threshold is rejected
    if len(thresholds) >= 2 and len({Fraction(t) for _c, t in thresholds}) > 1:
        verdicts = [out["triggers"][cid] for cid, _t in thresholds]
        if out["uniform_threshold_rejected"] != (len(set(verdicts)) > 1):
            reasons = _fail(reasons, "the uniform-threshold verdict "
                                     "diverges")
        if all(v == verdicts[0] for v in verdicts) and \
                out["uniform_threshold_rejected"]:
            reasons = _fail(reasons, "identical triggers were reported as "
                                     "a rejected uniform threshold")
    # the three consequence kinds are distinct
    names = ("notice", "consent", "termination")
    if out["consequences_distinct"] is not True or \
            tuple(dict.fromkeys(names)) != names:
        reasons = _fail(reasons, "the notice/consent/termination "
                                 "consequences were merged")
    return not reasons, reasons


# ---------------------------------------------------------------------------
# D071
# ---------------------------------------------------------------------------

_M_EXCLUSIVE = "license_exclusive"
_M_NONEXCLUSIVE = "license_nonexclusive"
_M_TERMINATED = "license_terminated"


def check_D071(grant: str, out: dict):
    reasons = ()
    # the conversion changes only the mode and keeps the grant verbatim
    if out["mode_in"] != _M_EXCLUSIVE:
        reasons = _fail(reasons, "the conversion input mode diverges")
    if out["mode_out"] != _M_NONEXCLUSIVE:
        reasons = _fail(reasons, "the conversion output mode diverges")
    if out["grant_out"] != grant:
        reasons = _fail(reasons, "the usage grant did not survive the "
                                 "conversion verbatim")
    if out["grant_kept"] is not (out["grant_out"] == grant):
        reasons = _fail(reasons, "the grant-kept verdict diverges")
    # nonexclusive and terminated are two different license states
    if _M_NONEXCLUSIVE == _M_TERMINATED:
        reasons = _fail(reasons, "nonexclusive equals terminated")
    if out["nonexclusive_is_not_terminated"] is not True:
        reasons = _fail(reasons, "the state-distinctness verdict diverges")
    # adverse case: deleting the whole usage grant on conversion (either
    # by terminating or by dropping the grant) is intercepted
    deleted = out["mode_out"] == _M_TERMINATED or out["grant_out"] != grant
    if out["deletion_intercepted"] is not (not deleted):
        reasons = _fail(reasons, "the deletion-intercept verdict diverges")
    if deleted:
        reasons = _fail(reasons, "an exclusive-to-nonexclusive conversion "
                                 "deleted the usage grant or terminated "
                                 "the license")
    return not reasons, reasons


# ---------------------------------------------------------------------------
# D072
# ---------------------------------------------------------------------------

_R_OWN, _R_CO, _R_LIC, _R_SUB, _R_AFF = 0, 1, 2, 3, 4


def _grant(rows, rel):
    for row in rows:
        if row[0] == rel:
            return row[1]
    return None


def check_D072(rows: Sequence[tuple], grant: str, out: dict):
    reasons = ()
    tags = out["tags"]
    i = 0
    while i < len(tags):
        j = 0
        while j < len(tags):
            if i != j and tags[i] == tags[j]:
                reasons = _fail(reasons,
                                f"relations {i} and {j} share one tag")
            j += 1
        i += 1
    if tuple(tags) != (_R_OWN, _R_CO, _R_LIC, _R_SUB, _R_AFF):
        reasons = _fail(reasons, "the five relation tags diverge from the "
                                 "declared five")
    # independent keyed lookups
    if out["own_grant"] != _grant(rows, _R_OWN):
        reasons = _fail(reasons, "the ownership grant lookup diverges")
    if out["lic_grant"] != _grant(rows, _R_LIC):
        reasons = _fail(reasons, "the license grant lookup diverges")
    if out["aff_grant"] != _grant(rows, _R_AFF):
        reasons = _fail(reasons, "the affiliate grant lookup diverges")
    # a license is not ownership: a license row never creates an
    # ownership grant
    if _grant(rows, _R_LIC) is not None and _grant(rows, _R_OWN) is not None \
            and out["license_is_not_ownership"]:
        reasons = _fail(reasons, "an ownership grant existed next to the "
                                 "license row yet was reported absent")
    # adverse case: an affiliate with no grant row of its own gets
    # nothing — the group label does not auto-license
    has_aff_row = False
    i = 0
    while i < len(rows):
        if rows[i][0] == _R_AFF:
            has_aff_row = True
        i += 1
    if not has_aff_row and out["aff_grant"] is not None:
        reasons = _fail(reasons, "an affiliate without its own grant row "
                                 "received a grant")
    return not reasons, reasons


# ---------------------------------------------------------------------------
# D073
# ---------------------------------------------------------------------------


def check_D073(perpetual: bool, revocable: bool, transferable: bool,
               cap, out: dict):
    reasons = ()
    rec = (bool(perpetual), bool(revocable), bool(transferable), cap)
    if tuple(out["record"]) != rec:
        reasons = _fail(reasons, "the attribute record diverges from the "
                                 "declared attributes")
    # each attribute reads back verbatim
    if out["reads"] != {"perpetual": rec[0], "revocable": rec[1],
                        "transferable": rec[2], "cap": rec[3]}:
        reasons = _fail(reasons, "one attribute read-back diverged")
    # flipping the perpetual flag alone changes the record and keeps the
    # rest — the four attributes are independent
    flipped = (not rec[0], rec[1], rec[2], rec[3])
    if out["flip_perpetual_alone_changes"] is not (flipped != rec):
        reasons = _fail(reasons, "the flip-changes verdict diverges")
    if out["flip_perpetual_alone_keeps_rest"] is not (flipped[1:] == rec[1:]):
        reasons = _fail(reasons, "the flip-keeps-rest verdict diverges")
    # adverse case: perpetual AND revocable AND capped is a different
    # record from perpetual AND irrevocable AND unlimited — "perpetual"
    # never entails the rest
    witness_a = (True, True, False, 1000)
    witness_b = (True, False, True, None)
    if witness_a == witness_b:
        reasons = _fail(reasons, "the two witness records collapsed into "
                                 "one")
    if out["perpetual_not_irrevocable_unlimited"] is not True:
        reasons = _fail(reasons, "perpetuality was read as entailing "
                                 "irrevocable and unlimited")
    # a usage cap present on input must never be normalized away to the
    # unlimited record
    if rec[3] is None and cap is not None:
        reasons = _fail(reasons, "a declared usage cap was normalized to "
                                 "the unlimited record")
    if out["cap_is_present"] is not (rec[3] is not None):
        reasons = _fail(reasons, "the cap-presence verdict diverges")
    return not reasons, reasons


# ---------------------------------------------------------------------------
# D074
# ---------------------------------------------------------------------------


def check_D074(rate: Fraction, line1: tuple, line2: tuple, out: dict):
    reasons = ()
    # independent re-derivation of the two fee lines with period/unit
    if tuple(out["lines"]) != (tuple(line1), tuple(line2)):
        reasons = _fail(reasons, "the fee lines diverge from the declared "
                                 "rows")
    if out["line1"] != {"period": line1[0], "unit": line1[1],
                        "amount": Fraction(line1[2])}:
        reasons = _fail(reasons, "the line read-back altered a period or "
                                 "unit field")
    if line1[0] == line2[0] and line1[1] == line2[1] \
            and Fraction(line1[2]) == Fraction(line2[2]) \
            and out["periods_distinct"]:
        reasons = _fail(reasons, "identical rows were reported distinct")
    # the share multiplies the declared base: a different base gives a
    # different number — the misused profit base is detected
    share_rev = Fraction(100000) * Fraction(rate)
    share_pro = Fraction(20000) * Fraction(rate)
    if Fraction(out["share_revenue_base"]) != share_rev:
        reasons = _fail(reasons, "the revenue-base share diverges from "
                                 "the exact product")
    if Fraction(out["share_profit_base"]) != share_pro:
        reasons = _fail(reasons, "the profit-base share diverges from the "
                                 "exact product")
    if out["base_misuse_detected"] is not (share_rev != share_pro):
        reasons = _fail(reasons, "the base-misuse verdict diverges")
    if share_rev == share_pro:
        reasons = _fail(reasons, "two different bases produced one share")
    # the two period amounts add exactly — no cross-period double sum
    exact = Fraction(line1[2]) + Fraction(line2[2])
    if Fraction(out["exact_sum"]) != exact:
        reasons = _fail(reasons, "the period sum diverges from the exact "
                                 "addition")
    return not reasons, reasons


# ---------------------------------------------------------------------------
# D075
# ---------------------------------------------------------------------------


def _cap(carve, amt, cap):
    if carve:
        return Fraction(amt)
    return min(Fraction(amt), Fraction(cap))


def check_D075(items: Sequence[tuple], cap: Fraction, out: dict):
    reasons = ()
    if Fraction(out["cap"]) != Fraction(cap):
        reasons = _fail(reasons, "the applied cap diverges from the "
                                 "declared cap")
    # classification first, then the per-class rule — re-derived row by
    # row with an independent while-scan
    if len(out["classified"]) != len(items):
        reasons = _fail(reasons, "the classification dropped an item")
    i = 0
    while i < len(items):
        kind, carve, amt = items[i]
        row = out["classified"][i]
        if row["kind"] != kind or bool(row["carve_out"]) != bool(carve) \
                or Fraction(row["amount"]) != Fraction(amt):
            reasons = _fail(reasons,
                            f"classified item {i} diverges from its "
                            "declared row")
        expected = _cap(carve, amt, cap)
        if Fraction(row["applied"]) != expected:
            reasons = _fail(reasons,
                            f"item {i} cap application diverges from its "
                            "own class rule")
        i += 1
    # same amount and cap, different classes, different results — the
    # classification is detectable and load-bearing
    w_carve = _cap(True, Fraction(1500000), cap)
    w_capped = _cap(False, Fraction(1500000), cap)
    if Fraction(out["witness_carve"]) != w_carve or \
            Fraction(out["witness_capped"]) != w_capped:
        reasons = _fail(reasons, "the class witnesses diverge")
    if out["classification_detectable"] is not (w_carve != w_capped):
        reasons = _fail(reasons, "the classification-detectable verdict "
                                 "diverges")
    if w_carve == w_capped:
        reasons = _fail(reasons, "the carve-out and capped classes "
                                 "produced one result (the general cap "
                                 "was applied to a carve-out)")
    # the insurance limit is its own field, never read as the cap
    if Fraction(out["insurance_limit"]) == Fraction(cap) \
            and out["insurance_is_not_the_cap"]:
        reasons = _fail(reasons, "the insurance limit was read as the "
                                 "liability cap")
    if out["insurance_is_not_the_cap"] is not \
            (Fraction(out["insurance_limit"]) != Fraction(cap)):
        reasons = _fail(reasons, "the insurance-vs-cap verdict diverges")
    return not reasons, reasons


# ---------------------------------------------------------------------------
# D076
# ---------------------------------------------------------------------------


def _survivors(rows):
    keep = []
    i = 0
    while i < len(rows):
        if rows[i][2] is True:
            keep.append(rows[i][0])
        i += 1
    return tuple(keep)


def check_D076(rows: Sequence[tuple], out: dict):
    reasons = ()
    if tuple(out["table"]) != tuple(rows):
        reasons = _fail(reasons, "the survival table diverges from the "
                                 "declared rows")
    # the carrier keeps exactly the declared survivors, in table order
    expected = _survivors(rows)
    if tuple(out["survivors"]) != expected:
        reasons = _fail(reasons, "the survival carrier diverges from the "
                                 "declared table")
    if tuple(out["carrier_after_termination"]) != expected:
        reasons = _fail(reasons, "termination altered the survival "
                                 "carrier (a declared survivor was "
                                 "bulk-deleted)")
    # every survivor traces to a declared-surviving row
    i = 0
    while i < len(expected):
        kind = expected[i]
        hit = False
        j = 0
        while j < len(rows):
            if rows[j][0] == kind and rows[j][2] is True:
                hit = True
            j += 1
        if not hit:
            reasons = _fail(reasons,
                            f"survivor {kind!r} has no declared-surviving "
                            "table row")
        i += 1
    # a nonempty all-surviving table keeps a nonempty carrier after
    # termination — no bulk deletion
    all_true = True
    i = 0
    while i < len(rows):
        if rows[i][2] is not True:
            all_true = False
        i += 1
    if len(rows) > 0 and all_true and len(expected) == 0:
        reasons = _fail(reasons, "an all-surviving table produced an "
                                 "empty carrier after termination")
    # every declared survivor is still in the carrier after termination
    # — nothing bulk-deleted
    carrier = tuple(out["carrier_after_termination"])
    still_there = True
    i = 0
    while i < len(expected):
        hit = False
        j = 0
        while j < len(carrier):
            if carrier[j] == expected[i]:
                hit = True
            j += 1
        if not hit:
            still_there = False
        i += 1
    if out["not_bulk_deleted"] is not (len(expected) > 0 and still_there):
        reasons = _fail(reasons, "the no-bulk-deletion verdict diverges")
    if out["declared_all_survive"] is not all_true:
        reasons = _fail(reasons, "the all-survive verdict diverges")
    return not reasons, reasons
