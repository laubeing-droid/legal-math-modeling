"""Independent contract checker for group-10 enterprise-data entries
(D087-D094).

This module deliberately re-derives every expected value from the demand
contract with its own inline logic (while-scans, negated-condition
forms); it shares no code with ``data_ref`` (it never imports that
module), takes no witness callbacks, and never uses the main
implementation to generate expectations.  Each ``check_D0XX`` returns
``(ok, reasons)``: ``ok`` is True exactly when the observed intermediate
result satisfies the demand's contract on the given structured input.
"""
from __future__ import annotations

from fractions import Fraction
from typing import Sequence


def _fail(reasons, msg):
    return tuple(reasons) + (msg,)


# ---------------------------------------------------------------------------
# D087
# ---------------------------------------------------------------------------


def _snapshot(rows, key, t, field):
    i = 0
    while i < len(rows):
        if rows[i][0] == key and rows[i][2] == t and rows[i][1] == field:
            return rows[i][3]
        i += 1
    return None


def check_D087(rows: Sequence[tuple], key: str, field: str, out: dict):
    reasons = ()
    table = tuple(rows) + tuple(out["snapshots"])
    # the join is keyed on the (subject key, valid time) pair
    if out["hit_t0"] != _snapshot(table, key, 0, field):
        reasons = _fail(reasons, "the t=0 snapshot diverges from the "
                                 "same-key same-time table scan")
    if out["hit_t1"] != _snapshot(table, key, 1, field):
        reasons = _fail(reasons, "the t=1 snapshot diverges from the "
                                 "same-key same-time table scan")
    # adverse cases: renamed key, same-name other company, other time
    if out["renamed_key_miss"] is not None:
        reasons = _fail(reasons, "a renamed key answered the registry "
                                 "join (pre-rename name mixed in)")
    if _snapshot(table, "acme-renamed-co", 0, field) is not None \
            and out["renamed_key_miss"] is None:
        reasons = _fail(reasons, "the renamed-key miss diverged")
    if out["namesake_key_miss"] is not None:
        reasons = _fail(reasons, "a same-name other company's row "
                                 "answered the join")
    if out["other_time_miss"] is not None:
        reasons = _fail(reasons, "an out-of-snapshot time answered the "
                                 "join")
    # different snapshot values are different records
    if out["snapshots"][0][3] != out["snapshots"][1][3] \
            and out["different_times_different_records"] is not True:
        reasons = _fail(reasons, "two different snapshot values were "
                                 "collapsed into one record")
    if _snapshot(table, key, 0, field) == _snapshot(table, key, 1, field):
        reasons = _fail(reasons, "the two snapshot times returned the "
                                 "same value (the snapshots do not "
                                 "differ as declared)")
    return not reasons, reasons


# ---------------------------------------------------------------------------
# D088
# ---------------------------------------------------------------------------


def _hop(edges, parent, child, etype):
    i = 0
    while i < len(edges):
        e = edges[i]
        if e[0] == parent and e[1] == child and e[2] == etype:
            return True
        i += 1
    return False


def _stake(start, chain):
    chain = tuple(chain)
    if len(chain) == 0:
        return Fraction(1)
    if len(chain) == 1:
        return Fraction(0) if chain[-1][1] == start else Fraction(chain[0][2])
    head = Fraction(chain[0][2])
    if chain[-1][1] == start:
        return Fraction(0)
    return head * _stake(start, chain[1:])


def check_D088(p: Fraction, q: Fraction, out: dict):
    reasons = ()
    if out["holding_hop"] is not _hop(out["edges"], "sub-co", "mid-co",
                                      "holding"):
        reasons = _fail(reasons, "the typed holding-edge hop diverged")
    # adverse case: the same parties under a service edge never connect
    if out["service_hop_miss"] is not False:
        reasons = _fail(reasons, "a service-typed edge answered the "
                                 "holding penetration query")
    if _hop(out["edges"], "sub-co", "mid-co", "service") is not False:
        reasons = _fail(reasons, "the service-edge miss diverged")
    # the chain compounds its own ratios; the empty chain is the entity
    if Fraction(out["chain_stake"]) != _stake("sub-co", out["chain"]):
        reasons = _fail(reasons, "the compounded chain stake diverges "
                                 "from the edge-ratio product")
    if Fraction(out["chain_stake"]) != Fraction(p) * Fraction(q):
        reasons = _fail(reasons, "the chain stake is not the product of "
                                 "its own edge ratios")
    if Fraction(out["empty_chain"]) != Fraction(1):
        reasons = _fail(reasons, "the empty chain is not the entity "
                                 "itself (1)")
    # adverse case: a cycle never multiplies its way to phantom equity
    if Fraction(out["cyclic_stake"]) != Fraction(0):
        reasons = _fail(reasons, "a holding cycle compounded phantom "
                                 "equity instead of 0")
    if Fraction(p) > 0 and Fraction(q) > 0 \
            and Fraction(out["cyclic_stake"]) == Fraction(p) * Fraction(q):
        reasons = _fail(reasons, "the guarded cyclic stake equals the "
                                 "unguarded product (the guard was "
                                 "lost)")
    # control is a separate boolean verdict on the stake
    if out["control_half"] is not True:
        reasons = _fail(reasons, "a stake of 1/2 failed the control "
                                 "verdict")
    if out["control_quarter"] is not False:
        reasons = _fail(reasons, "a stake of 1/4 passed the control "
                                 "verdict")
    if out["control_of_chain"] is not (Fraction(1, 2)
                                       <= Fraction(out["chain_stake"])):
        reasons = _fail(reasons, "the control verdict diverged from the "
                                 "separate-boolean rule")
    if out["chain_and_control_separate"] is not True:
        reasons = _fail(reasons, "the chain stake and the control "
                                 "verdict were merged into one value")
    return not reasons, reasons


# ---------------------------------------------------------------------------
# D089
# ---------------------------------------------------------------------------


def _case_row(rows, ent, case_id):
    i = 0
    while i < len(rows):
        if rows[i][0] == ent and rows[i][1] == case_id:
            return (rows[i][2], Fraction(rows[i][3]), rows[i][4])
        i += 1
    return None


def _case_keys(rows, ent):
    acc = []
    i = 0
    while i < len(rows):
        row = rows[i]
        if row[0] == ent and row[1] not in acc:
            acc.insert(0, row[1])
        i += 1
    return tuple(acc)


def check_D089(rows: Sequence[tuple], ent: str, out: dict):
    reasons = ()
    # the keyed join returns the row's own role, amount and text
    if out["keyed_case_1"] != _case_row(rows, ent, "case-1"):
        reasons = _fail(reasons, "the keyed case row diverges from the "
                                 "(enterprise, case) table scan")
    expected = _case_row(rows, ent, "case-1")
    if expected is not None and len(expected) == 3:
        # the original text is carried through verbatim
        texts = [r[4] for r in rows if r[0] == ent and r[1] == "case-1"]
        if expected[2] not in texts:
            reasons = _fail(reasons, "the keyed row's text is not one "
                                     "of the table's own texts")
    # adverse cases: another case or another enterprise never answers
    if out["other_case_miss"] is not None:
        reasons = _fail(reasons, "a row of another case answered the "
                                 "keyed join")
    if out["other_ent_miss"] is not None:
        reasons = _fail(reasons, "a row of another enterprise answered "
                                 "the keyed join")
    # the deduplicated case roster
    if tuple(out["case_keys"]) != _case_keys(rows, ent):
        reasons = _fail(reasons, "the deduplicated case roster diverges "
                                 "from the first-witness scan")
    same_case_docs = [r for r in rows
                      if r[0] == ent and r[1] == "case-1"]
    if len(same_case_docs) >= 2 \
            and tuple(out["case_keys"]).count("case-1") != 1:
        reasons = _fail(reasons, "the same case under two documents "
                                 "was counted as more than one case")
    # different documents remain different records
    if out["docs_are_distinct_records"] is not True:
        reasons = _fail(reasons, "two different documents were collapsed "
                                 "into one record")
    return not reasons, reasons


# ---------------------------------------------------------------------------
# D090
# ---------------------------------------------------------------------------

_RESTRICT, _DISHONEST, _TERMINATED, _CLEARED = 0, 1, 2, 3


def _ec(rows, subject, kind):
    i = 0
    while i < len(rows):
        if rows[i][0] == subject and rows[i][1] == kind:
            return rows[i][2]
        i += 1
    return None


def check_D090(subject: str, out: dict):
    reasons = ()
    tags = out["tags"]
    i = 0
    while i < len(tags):
        j = 0
        while j < len(tags):
            if i != j and tags[i] == tags[j]:
                reasons = _fail(reasons,
                                f"procedure kinds {i} and {j} share one "
                                "tag")
            j += 1
        i += 1
    if tuple(tags) != (_RESTRICT, _DISHONEST, _TERMINATED, _CLEARED):
        reasons = _fail(reasons, "the four procedure tags diverge from "
                                 "the declared typed four")
    # a termination row answers only the termination query
    rows = ((subject, _TERMINATED, True),)
    if out["terminated_hit"] != _ec(rows, subject, _TERMINATED):
        reasons = _fail(reasons, "the termination lookup diverged")
    if out["dishonest_miss"] is not None:
        reasons = _fail(reasons, "a termination record answered the "
                                 "dishonesty query")
    if out["restrict_miss"] is not None:
        reasons = _fail(reasons, "a termination record answered the "
                                 "restriction query")
    if out["debt_cleared_miss"] is not None:
        reasons = _fail(reasons, "a termination record answered the "
                                 "debt-extinction query")
    if out["kind_changes_record"] is not True:
        reasons = _fail(reasons, "the procedure kind was collapsed into "
                                 "one undifferentiated field")
    return not reasons, reasons


# ---------------------------------------------------------------------------
# D091
# ---------------------------------------------------------------------------

_CASE, _TARGET, _UNPAID, _PAID = 0, 1, 2, 3


def _amt(rows, debt, kind):
    total = Fraction(0)
    i = 0
    while i < len(rows):
        if rows[i][0] == debt and rows[i][1] == kind:
            total += Fraction(rows[i][2])
        i += 1
    return total


def check_D091(u: Fraction, t: Fraction, w: Fraction, out: dict):
    reasons = ()
    tags = out["tags"]
    i = 0
    while i < len(tags):
        j = 0
        while j < len(tags):
            if i != j and tags[i] == tags[j]:
                reasons = _fail(reasons,
                                f"amount kinds {i} and {j} share one tag")
            j += 1
        i += 1
    rows = tuple(out["rows"])
    if tuple(tags) != (_CASE, _TARGET, _UNPAID, _PAID):
        reasons = _fail(reasons, "the four amount tags diverge from the "
                                 "declared typed four")
    # the aggregation is keyed on (debt key, amount kind)
    if Fraction(out["unpaid_total"]) != _amt(rows, "debt-1", _UNPAID):
        reasons = _fail(reasons, "the unpaid total diverges from the "
                                 "kind-and-debt-keyed scan")
    if Fraction(out["unpaid_total"]) != Fraction(u):
        reasons = _fail(reasons, "rows of other keys or kinds entered "
                                 "the unpaid total")
    if Fraction(out["target_total"]) != _amt(rows, "debt-1", _TARGET):
        reasons = _fail(reasons, "the target total diverges from the "
                                 "kind-and-debt-keyed scan")
    # adverse case: the unpaid amount is never added into the target
    if Fraction(out["target_total"]) != Fraction(t):
        reasons = _fail(reasons, "the execution-target total absorbed "
                                 "the unfulfilled amount")
    if Fraction(_amt(rows, "debt-2", _UNPAID)) != Fraction(w):
        reasons = _fail(reasons, "the debt-2 unpaid total diverged")
    if out["other_debt_never_merges"] is not True:
        reasons = _fail(reasons, "another debt key's rows merged into "
                                 "the debt-1 total")
    # the cross-kind sum is no single-kind aggregation's output
    if Fraction(out["cross_kind_sum"]) != Fraction(t) + Fraction(u):
        reasons = _fail(reasons, "the cross-kind sum diverged")
    i = 0
    while i < len(tags):
        if Fraction(out["cross_kind_sum"]) == _amt(rows, "debt-1", tags[i]):
            reasons = _fail(reasons,
                            f"the cross-kind sum equals the kind-{i} "
                            "total (the wrong 'total debt' is an "
                            "aggregation output)")
        i += 1
    if out["cross_sum_is_no_kind_total"] is not True:
        reasons = _fail(reasons, "the cross-sum-is-no-kind-total verdict "
                                 "diverged")
    return not reasons, reasons


# ---------------------------------------------------------------------------
# D092
# ---------------------------------------------------------------------------

_EFF, _REV = 0, 1


def _current(row):
    return row[4] == _EFF


def _provenance(row):
    return (row[0], row[1], row[2], row[3])


def _current_list(rows, subject):
    out = []
    i = 0
    while i < len(rows):
        if rows[i][1] == subject and _current(rows[i]) is True:
            out.append(rows[i])
        i += 1
    return tuple(out)


def check_D092(out: dict):
    reasons = ()
    revoked = out["revoked"]
    effective = out["effective"]
    # the verdict reads the record's own status tag
    if out["revoked_current"] is not _current(revoked):
        reasons = _fail(reasons, "the revoked record's validity verdict "
                                 "diverged")
    if out["effective_current"] is not _current(effective):
        reasons = _fail(reasons, "the effective record's validity "
                                 "verdict diverged")
    # adverse case: a revoked penalty never reads as a current
    # violation conclusion
    if out["revoked_current"] is not False:
        reasons = _fail(reasons, "a revoked penalty stayed marked as a "
                                 "current violation conclusion")
    # the provenance chain rides on the same record
    if tuple(out["revoked_provenance"]) != _provenance(revoked):
        reasons = _fail(reasons, "the provenance chain diverged from "
                                 "the record's own fields")
    if out["tags_distinct"] is not True:
        reasons = _fail(reasons, "the effective and revoked tags are "
                                 "not distinct")
    # the current list keeps the effective row and drops the revoked
    if tuple(out["current_of_acme"]) != _current_list(out["rows"],
                                                      "acme-co"):
        reasons = _fail(reasons, "the current-penalty list diverges "
                                 "from the status-filtered scan")
    if revoked in tuple(out["current_of_acme"]):
        reasons = _fail(reasons, "the revoked row entered the current "
                                 "list")
    if effective not in tuple(out["current_of_acme"]):
        reasons = _fail(reasons, "the effective row was dropped from "
                                 "the current list")
    return not reasons, reasons


# ---------------------------------------------------------------------------
# D093
# ---------------------------------------------------------------------------


def _row_at(rows, code, t):
    i = 0
    while i < len(rows):
        row = rows[i]
        if row[0] == code and row[4] <= t <= row[5]:
            return row
        i += 1
    return None


def check_D093(out: dict):
    reasons = ()
    rows = tuple(out["rows"])
    old = out["old"]
    new = out["new"]
    # each time point hits its own versioned row, whole-row returned
    if out["at_5"] != _row_at(rows, "ct-0101", 5):
        reasons = _fail(reasons, "the t=5 lookup diverged")
    if out["at_5"] != old:
        reasons = _fail(reasons, "the t=5 lookup did not return the old "
                                 "window's whole row")
    if out["at_15"] != _row_at(rows, "ct-0101", 15):
        reasons = _fail(reasons, "the t=15 lookup diverged")
    if out["at_15"] != new:
        reasons = _fail(reasons, "the t=15 lookup did not return the "
                                 "new window's whole row")
    # adverse case: the old address never answers after its window
    if out["old_not_at_15"] is not True:
        reasons = _fail(reasons, "the old delivery address answered "
                                 "outside its validity window")
    if _row_at((old,), "ct-0101", 15) is not None \
            and out["old_only_miss"] is not None:
        reasons = _fail(reasons, "the old-only miss diverged")
    if out["old_only_miss"] is not None:
        reasons = _fail(reasons, "a lone expired row answered the "
                                 "versioned join")
    if out["other_code_miss"] is not None:
        reasons = _fail(reasons, "another court code answered the join")
    if out["after_window_miss"] is not None:
        reasons = _fail(reasons, "an out-of-window time answered the "
                                 "join")
    # the rename made a version, not a second court
    if out["one_court_two_versions"] is not True:
        reasons = _fail(reasons, "the district rename produced two "
                                 "courts (or collapsed the versions)")
    if not (old[0] == new[0] and old[1] == new[1] and old != new):
        reasons = _fail(reasons, "the two version rows do not share "
                                 "code and organ while differing as "
                                 "records")
    return not reasons, reasons


# ---------------------------------------------------------------------------
# D094
# ---------------------------------------------------------------------------


def _rep(rep_rows, case_id, firm):
    i = 0
    while i < len(rep_rows):
        if rep_rows[i][0] == case_id and rep_rows[i][1] == firm:
            return True
        i += 1
    return False


def _served(service_rows, firm, client):
    i = 0
    while i < len(service_rows):
        if service_rows[i][0] == firm and service_rows[i][1] == client:
            return True
        i += 1
    return False


def check_D094(out: dict):
    reasons = ()
    rep_rows = tuple(out["rep_rows"])
    service_rows = tuple(out["service_rows"])
    # the representation query cites the edge table only
    if out["rep_hit"] is not _rep(rep_rows, "acme-case-1", "law-a"):
        reasons = _fail(reasons, "the representation-edge lookup "
                                 "diverged")
    if out["rep_other_case_miss"] is not False:
        reasons = _fail(reasons, "a case with no edge answered the "
                                 "representation query")
    if out["rep_other_firm_miss"] is not False:
        reasons = _fail(reasons, "a firm with no edge answered the "
                                 "representation query")
    if out["rep_empty_miss"] is not False:
        reasons = _fail(reasons, "an empty edge table answered the "
                                 "representation query")
    # adverse case: the service table never answers the rep query and
    # vice versa — each relation cites its own table
    if out["service_table_does_not_answer_rep"] is not False:
        reasons = _fail(reasons, "a service row answered the "
                                 "representation query")
    if out["service_hit"] is not _served(service_rows, "law-a",
                                         "acme-co"):
        reasons = _fail(reasons, "the service-record lookup diverged")
    if out["service_other_firm_miss"] is not False:
        reasons = _fail(reasons, "a firm with no service row answered "
                                 "the service query")
    if out["rep_table_does_not_answer_service"] is not False:
        reasons = _fail(reasons, "a representation edge answered the "
                                 "service query")
    # the reverse inference passes only through the case-1 edge
    if out["inferred_case_1"] is not (_served(service_rows, "law-a",
                                              "acme-co")
                                      and _rep(rep_rows, "acme-case-1",
                                               "law-a")):
        reasons = _fail(reasons, "the case-1 inference diverged from "
                                 "the service-plus-edge rule")
    # adverse case: serving the client never implies representing its
    # other cases
    if out["not_inferred_case_2"] is not False:
        reasons = _fail(reasons, "serving the client implied "
                                 "representing case-2 (no edge)")
    if out["not_inferred_case_3"] is not False:
        reasons = _fail(reasons, "serving the client implied "
                                 "representing case-3 (no edge)")
    if _rep(rep_rows, "acme-case-2", "law-a") is False \
            and out["not_inferred_case_2"] is not False:
        reasons = _fail(reasons, "the case-2 no-inference verdict "
                                 "diverged")
    return not reasons, reasons
