"""Independent contract checker for group-05 criminal entries (D037-D046).

This module deliberately re-derives every expected value from the demand
contract with its own inline logic (while-scans, negated-condition forms);
it shares no code with ``criminal_ref`` (it never imports that module),
takes no witness callbacks, and never uses the main implementation to
generate expectations.  Each ``check_D0XX`` returns ``(ok, reasons)``:
``ok`` is True exactly when the observed intermediate result satisfies the
demand's contract on the given structured input.
"""
from __future__ import annotations

from fractions import Fraction
from typing import Sequence


def _fail(reasons, msg):
    return tuple(reasons) + (msg,)


# ---------------------------------------------------------------------------
# D037
# ---------------------------------------------------------------------------


def check_D037(cands: Sequence[tuple], out: dict):
    reasons = ()
    # independent while-scan: the label set is exactly the all-true rows
    expected = []
    i = 0
    while i < len(cands):
        if cands[i][1] is True and cands[i][2] is True and cands[i][3] is True:
            expected.append(cands[i][0])
        i += 1
    if tuple(out["labels"]) != tuple(expected):
        reasons = _fail(reasons, "the label set diverges from the "
                                 "policy-true candidate rows")
    # bidirectional mapping: every label traces to an all-true row, and
    # every all-true row is a label
    for l in out["labels"]:
        hit = False
        i = 0
        while i < len(cands):
            if (cands[i][0] == l and cands[i][1] is True
                    and cands[i][2] is True and cands[i][3] is True):
                hit = True
            i += 1
        if not hit:
            reasons = _fail(reasons,
                            f"label {l!r} has no all-true candidate row")
    for row in cands:
        if row[1] is True and row[2] is True and row[3] is True \
                and row[0] not in out["labels"]:
            reasons = _fail(reasons,
                            f"legitimate candidate {row[0]!r} was dropped "
                            "from the label set")
    # the adverse case: a second legitimate candidate must be visible as
    # dropped by the single-label carrier, never silently lost
    single = tuple(out["labels"])[:1]
    if tuple(out["single_label_carrier"]) != single:
        reasons = _fail(reasons, "the single-label carrier diverges")
    if len(expected) >= 2:
        if not out["dropped_by_single_label"]:
            reasons = _fail(reasons, "the second legitimate label vanished "
                                     "silently (single-label interface)")
        for l in expected[1:]:
            if l not in out["dropped_by_single_label"]:
                reasons = _fail(reasons,
                                f"label {l!r} was dropped without a trace")
    return not reasons, reasons


# ---------------------------------------------------------------------------
# D038
# ---------------------------------------------------------------------------


def check_D038(dict_rows: Sequence[tuple], n: int, out: dict):
    reasons = ()
    # independent while-scan for the id lookup
    hit = None
    i = 0
    while i < len(dict_rows):
        if dict_rows[i][0] == n:
            hit = dict_rows[i]
            break
        i += 1
    if hit is None:
        if out["registered"]:
            reasons = _fail(reasons, "an unregistered id was reported as "
                                     "registered")
        if out["decode_id"] is not None or out["roundtrip_ok"]:
            reasons = _fail(reasons, "an unregistered id produced a "
                                     "citation (not fail-closed)")
        return not reasons, reasons
    if not out["registered"] or out["row"] != hit:
        reasons = _fail(reasons, "the registered row diverges from the "
                                 "dictionary")
    # the found row carries its own three typed fields verbatim
    if (out["fields"]["id"] != hit[0] or
            out["fields"]["article"] != hit[1] or
            out["fields"]["clause"] != hit[2]):
        reasons = _fail(reasons, "one of the three typed fields was altered")
    # independent decode by (article, clause) under declared uniqueness
    decode = None
    key_hits = []
    i = 0
    while i < len(dict_rows):
        if dict_rows[i][1] == hit[1] and dict_rows[i][2] == hit[2]:
            key_hits.append(dict_rows[i][0])
            if decode is None:
                decode = dict_rows[i][0]
        i += 1
    if out["decode_id"] != decode:
        reasons = _fail(reasons, "the decode diverges from the (article, "
                                 "clause) lookup")
    if out["frozen_unique"] != (len(set(key_hits)) == 1):
        reasons = _fail(reasons, "the frozen-uniqueness witness diverges")
    if len(set(key_hits)) == 1 and out["roundtrip_ok"] != (decode == n):
        reasons = _fail(reasons, "the roundtrip verdict diverges")
    # roundtrip must actually close: decode returns the encoded id
    if len(set(key_hits)) == 1 and decode != n:
        reasons = _fail(reasons, "encode/decode did not return the same id")
    return not reasons, reasons


# ---------------------------------------------------------------------------
# D039
# ---------------------------------------------------------------------------

_TERM, _LIFE, _DEATH = 1, 2, 3


def check_D039(rows: Sequence[tuple], out: dict):
    reasons = ()
    # independent while-scan of the sum-type discipline
    all_terms = True
    poisoned = False
    has_life = False
    has_death = False
    total = 0
    i = 0
    while i < len(rows):
        kind, months = rows[i]
        if kind == _LIFE:
            has_life = True
        if kind == _DEATH:
            has_death = True
        if kind != _TERM or months is None:
            all_terms = False
            poisoned = True
        else:
            total += months
        i += 1
    if out["all_terms"] != all_terms:
        reasons = _fail(reasons, "the all-terms verdict diverges")
    if out["poisoned"] != poisoned:
        reasons = _fail(reasons, "the poisoned verdict diverges")
    if out["has_life"] != has_life or out["has_death"] != has_death:
        reasons = _fail(reasons, "the life/death flags diverge")
    # the aggregate exists only for an all-terms ledger, and equals the
    # exact month sum
    if all_terms:
        if out["total"] != total:
            reasons = _fail(reasons, "the term total diverges from the "
                                     "exact month sum")
        if rows and out["average"] != Fraction(total, len(rows)):
            reasons = _fail(reasons, "the average diverges from the exact "
                                     "ratio")
    else:
        if out["total"] is not None or out["average"] is not None:
            reasons = _fail(reasons, "a mixed-kind ledger produced a numeric "
                                     "aggregate (ordinary addition mixed "
                                     "penalty kinds)")
    return not reasons, reasons


# ---------------------------------------------------------------------------
# D040
# ---------------------------------------------------------------------------

_WITH = (0, 1, 2)
_WITHOUT = (0, 1)


def check_D040(hits_with: int, hits_without: int, out: dict):
    reasons = ()
    # the two budgets are the declared fixed ones and differ
    if tuple(out["with"]["budget"]) != _WITH or \
            tuple(out["without"]["budget"]) != _WITHOUT:
        reasons = _fail(reasons, "the feature budgets are not the declared "
                                 "fixed ones")
    if out["budgets_equal"]:
        reasons = _fail(reasons, "the with/without configs were merged")
    if out["lengths_equal"] != (len(_WITH) == len(_WITHOUT)):
        reasons = _fail(reasons, "the length comparison diverges")
    # the statute feature sits only in the with budget — a statute-free
    # label for the with budget is exactly the adverse mislabeling
    if out["with"]["statute_free"]:
        reasons = _fail(reasons, "the with-statute budget was labeled "
                                 "statute-free (gold-label score passed "
                                 "off as independent capability)")
    if out["without"]["statute_free"] is not (2 not in _WITHOUT):
        reasons = _fail(reasons, "the without-statute free-label diverges")
    # each score is normalized by its own budget length
    if out["with"]["score"] != Fraction(hits_with, len(_WITH)):
        reasons = _fail(reasons, "the with score diverges from its own "
                                 "denominator")
    if out["without"]["score"] != Fraction(hits_without, len(_WITHOUT)):
        reasons = _fail(reasons, "the without score diverges from its own "
                                 "denominator")
    # the same hit count under the two denominators gives different
    # numbers — mixed denominators are detected, not averaged away
    if out["scores_equal"] != (out["with"]["score"] == out["without"]["score"]):
        reasons = _fail(reasons, "the score comparison diverges")
    if out["same_hits_other_denominator"] != \
            Fraction(hits_with, len(_WITHOUT)):
        reasons = _fail(reasons, "the same-hits recount diverges from the "
                                 "other budget's denominator")
    if out["mixing_denominators_detected"] != \
            (Fraction(hits_with, len(_WITH)) !=
             Fraction(hits_with, len(_WITHOUT))):
        reasons = _fail(reasons, "the denominator-mixing verdict diverges")
    if out["mixing_denominators_detected"] is False and \
            Fraction(hits_with, len(_WITH)) != \
            Fraction(hits_with, len(_WITHOUT)):
        reasons = _fail(reasons, "denominator mixing was not detected")
    if hits_with == len(_WITH) and out["with"]["score"] != Fraction(1):
        reasons = _fail(reasons, "a full-budget hit must score exactly 1")
    return not reasons, reasons


# ---------------------------------------------------------------------------
# D041
# ---------------------------------------------------------------------------


def check_D041(register: Sequence[tuple], rows: Sequence[tuple], out: dict):
    reasons = ()
    # independent per-person check against the register
    expected_checks = []
    i = 0
    while i < len(rows):
        person = rows[i][0]
        found = None
        j = 0
        while j < len(register):
            if register[j][0] == person:
                found = register[j]
            j += 1
        expected_checks.append({"person": person, "ok": rows[i] == found})
        i += 1
    if tuple(out["checks"]) != tuple(expected_checks):
        reasons = _fail(reasons, "the per-person checks diverge from the "
                                 "register lookups")
    if out["all_ok"] != all(c["ok"] for c in expected_checks):
        reasons = _fail(reasons, "the overall verdict diverges")
    # the case total is the exact sum of the per-defendant penalties
    total = 0
    i = 0
    while i < len(rows):
        total += rows[i][3]
        i += 1
    if out["total"] != total:
        reasons = _fail(reasons, "the case total diverges from the exact sum")
    # a failed per-person check can never hide behind a preserved total
    if not all(c["ok"] for c in expected_checks) and out["all_ok"]:
        reasons = _fail(reasons, "a swapped assignment was reported as "
                                 "per-person correct despite a preserved "
                                 "total")
    return not reasons, reasons


# ---------------------------------------------------------------------------
# D042
# ---------------------------------------------------------------------------


def check_D042(required: Sequence[str], verdicts: dict, relation_ok: bool,
               scores: Sequence[Fraction], out: dict):
    reasons = ()
    # independent while-scan: pending = undetermined required defendants
    pending = []
    all_correct = True
    i = 0
    while i < len(required):
        if verdicts.get(required[i]) is None:
            pending.append(required[i])
            all_correct = False
        elif verdicts.get(required[i]) is not True:
            all_correct = False
        i += 1
    if tuple(out["pending"]) != tuple(pending):
        reasons = _fail(reasons, "the pending carrier diverges (an "
                                 "undetermined defendant was not listed "
                                 "explicitly)")
    if out["all_defendants_correct"] != all_correct:
        reasons = _fail(reasons, "the all-correct verdict diverges")
    if out["relation_consistency"] != bool(relation_ok):
        reasons = _fail(reasons, "the relation consistency flag diverges")
    if out["case_correct"] != bool(all_correct and relation_ok):
        reasons = _fail(reasons, "CaseCorrect diverges from its definition "
                                 "(all determined-true AND relation "
                                 "consistency)")
    # a high average coexists with not-all-correct — the average never
    # certifies per-person correctness
    if scores:
        average = Fraction(0)
        i = 0
        while i < len(scores):
            average += scores[i]
            i += 1
        average = average / len(scores)
        if out["average"] != average:
            reasons = _fail(reasons, "the reported average diverges")
        if not all_correct and out["all_defendants_correct"]:
            reasons = _fail(reasons, "a pending defendant was certified "
                                     "correct (the average was read as "
                                     "per-person correctness)")
    return not reasons, reasons


# ---------------------------------------------------------------------------
# D043
# ---------------------------------------------------------------------------


def check_D043(rec: tuple, txt: tuple, out: dict):
    reasons = ()
    # independent field-by-field read-back
    mismatches = []
    if txt[0] != rec[0]:
        mismatches.append("kind")
    if txt[1] != rec[1]:
        mismatches.append("months")
    if txt[2] != rec[2]:
        mismatches.append("fine")
    if tuple(out["mismatches"]) != tuple(mismatches):
        reasons = _fail(reasons, "the read-back mismatch list diverges from "
                                 "the field-by-field comparison")
    if out["projections_equal"] != (txt == rec):
        reasons = _fail(reasons, "the projection-equality flag diverges")
    # matching text must read back empty
    if txt == rec and out["mismatches"]:
        reasons = _fail(reasons, "a matching text was reported with "
                                 "mismatches")
    # a mis-written field must be found by name — never averaged away
    if txt[2] != rec[2] and "fine" not in out["mismatches"]:
        reasons = _fail(reasons, "a mis-written fine was not found on "
                                 "read-back")
    return not reasons, reasons


# ---------------------------------------------------------------------------
# D044
# ---------------------------------------------------------------------------


def check_D044(paths: Sequence[tuple], conclusions: Sequence[tuple],
               out: dict):
    reasons = ()
    # independent while-scans for the certified/unbacked split
    certified = []
    unbacked = []
    i = 0
    while i < len(conclusions):
        found = False
        j = 0
        while j < len(paths):
            if paths[j] == conclusions[i]:
                found = True
            j += 1
        if found:
            certified.append(conclusions[i])
        else:
            unbacked.append(conclusions[i])
        i += 1
    if tuple(out["certified"]) != tuple(certified):
        reasons = _fail(reasons, "the certified carrier diverges from the "
                                 "verbatim intersection")
    if tuple(out["unbacked"]) != tuple(unbacked):
        reasons = _fail(reasons, "the unbacked carrier diverges")
    if out["all_certified"] != (not unbacked):
        reasons = _fail(reasons, "the all-certified verdict diverges")
    if out["certified_equals_conclusions"] != \
            (tuple(certified) == tuple(conclusions)):
        reasons = _fail(reasons, "the equality verdict diverges")
    # a pathless crime is never certified — no string-similarity shortcut
    for c in unbacked:
        if c in out["certified"]:
            reasons = _fail(reasons,
                            f"pathless crime {c!r} was certified")
    if unbacked and out["all_certified"]:
        reasons = _fail(reasons, "a text with a pathless crime was reported "
                                 "fully certified")
    return not reasons, reasons


# ---------------------------------------------------------------------------
# D045
# ---------------------------------------------------------------------------


def check_D045(items: Sequence[tuple], out: dict):
    reasons = ()
    # independent single-pass while-scan: attribution gate + first-seen
    # source dedup, exact Fractions
    counted = []
    total = Fraction(0)
    raw = Fraction(0)
    unattributed = []
    duplicates = []
    i = 0
    while i < len(items):
        src, okp, oka, oks, amt = items[i]
        if not (okp and oka and oks):
            unattributed.append(src)
            i += 1
            continue
        raw += Fraction(amt)
        seen = False
        j = 0
        while j < len(counted):
            if counted[j] == src:
                seen = True
            j += 1
        if seen:
            duplicates.append(src)
        else:
            counted.append(src)
            total += Fraction(amt)
        i += 1
    if out["total"] != total:
        reasons = _fail(reasons, "the deduplicated total diverges from the "
                                 "first-seen exact sum")
    if out["attributed_sum_without_dedup"] != raw:
        reasons = _fail(reasons, "the raw attributed sum diverges")
    if tuple(out["counted_sources"]) != tuple(counted):
        reasons = _fail(reasons, "the counted sources diverge")
    if tuple(out["duplicate_sources_skipped"]) != tuple(duplicates):
        reasons = _fail(reasons, "the duplicate-source record diverges")
    if tuple(out["unattributed_skipped"]) != tuple(unattributed):
        reasons = _fail(reasons, "the unattributed record diverges")
    # an unattributed item never enters, and the same loot in two records
    # is added exactly once — the raw double count must stay visible
    for src in unattributed:
        if src in out["counted_sources"]:
            reasons = _fail(reasons,
                            f"unattributed source {src!r} was counted")
    if duplicates and out["total"] == out["attributed_sum_without_dedup"]:
        reasons = _fail(reasons, "the duplicate loot was added twice (the "
                                 "total equals the undeduplicated sum)")
    if duplicates and not out["duplicate_sources_skipped"]:
        reasons = _fail(reasons, "the same-source double count was not "
                                 "recorded as skipped")
    return not reasons, reasons


# ---------------------------------------------------------------------------
# D046
# ---------------------------------------------------------------------------

_DECLARED_VERSION = 1975


def check_D046(queries: Sequence[tuple], rows: Sequence[tuple], out: dict):
    reasons = ()
    # independent re-derivation of every branch: in-version all-hold →
    # allowed; anything else → explicit pending
    for version, element_ok, exception_ok, use_ok, observed in queries:
        if version == _DECLARED_VERSION and element_ok and exception_ok \
                and use_ok:
            expected = True
        else:
            expected = None
        if observed != expected:
            reasons = _fail(reasons,
                            f"the branch for ({version!r}, {element_ok!r}, "
                            f"{exception_ok!r}, {use_ok!r}) diverges from "
                            "the allow-or-pending rule")
    # the CN carrier keeps exactly the CN-keyed rows
    cn = []
    i = 0
    while i < len(rows):
        if rows[i][0] == "CN":
            cn.append(rows[i])
        i += 1
    if tuple(out["cn"]) != tuple(cn):
        reasons = _fail(reasons, "the CN carrier diverges from the "
                                 "jurisdiction-keyed filter")
    if out["leak"]:
        reasons = _fail(reasons, "a foreign-keyed row leaked into the CN "
                                 "carrier (a US label became a CN "
                                 "conclusion)")
    for r in out["cn"]:
        if r[0] != "CN":
            reasons = _fail(reasons,
                            f"row {r!r} sits in the CN carrier without a "
                            "CN key")
    # verbatim-identical label and boolean under different keys stay two
    # distinct rows: both survive in the keyed carriers
    i = 0
    while i < len(rows):
        j = 0
        while j < len(rows):
            if i != j and rows[i][0] != rows[j][0] \
                    and rows[i][1:] == rows[j][1:]:
                combined = tuple(out["cn"]) + tuple(out["foreign_rows"])
                if rows[i] not in combined or rows[j] not in combined:
                    reasons = _fail(reasons, "verbatim-identical payloads "
                                             "under different jurisdiction "
                                             "keys were merged")
            j += 1
        i += 1
    return not reasons, reasons
