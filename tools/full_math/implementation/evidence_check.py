"""Independent contract checker for group-03 evidence/events (D019-D028).

This module deliberately re-derives every expected value from the demand
contract with its own inline logic (while-scans, negated-condition forms);
it shares no code with ``evidence_ref`` (it never imports that module),
takes no witness callbacks, and never uses the main implementation to
generate expectations.  Each ``check_D0XX`` returns ``(ok, reasons)``:
``ok`` is True exactly when the observed intermediate result satisfies the
demand's contract on the given structured input.
"""
from __future__ import annotations

from typing import Sequence


def _fail(reasons, msg):
    return tuple(reasons) + (msg,)


# ---------------------------------------------------------------------------
# D019
# ---------------------------------------------------------------------------


def check_D019(source: Sequence[str], triggers: Sequence[tuple],
               out: dict):
    reasons = ()
    # independent while-scan of the spans that point back into the source
    i = 0
    while i < len(triggers):
        trigger, label, actors, obj, quoted, st, en = triggers[i]
        if not (0 <= st <= en <= len(source)):
            return False, (f"span of trigger {trigger!r} leaves the source "
                           "bounds",)
        expected = []
        j = st
        while j < en:
            expected.append(source[j])
            j += 1
        expected = tuple(expected)
        if quoted:
            k = 0
            while k < len(out["events"]):
                if out["events"][k]["trigger"] == trigger:
                    return False, (f"quoted-hypothesis trigger {trigger!r} "
                                   "became an occurred event",)
                k += 1
            blocked = [b[0] for b in out["quoted_blocked"]]
            if trigger not in blocked:
                reasons = _fail(reasons,
                                f"quoted trigger {trigger!r} was not blocked")
        else:
            hit = None
            k = 0
            while k < len(out["events"]):
                if out["events"][k]["trigger"] == trigger:
                    hit = out["events"][k]
                    break
                k += 1
            if hit is None:
                reasons = _fail(reasons,
                                f"asserted trigger {trigger!r} lost its event")
            else:
                if hit["span"] != expected:
                    reasons = _fail(reasons,
                                    f"span of {trigger!r} does not point "
                                    "back into the source")
                if hit["start"] != st or hit["end"] != en \
                        or hit["span_length"] != en - st:
                    reasons = _fail(reasons,
                                    f"span coordinates of {trigger!r} were "
                                    "altered")
                if hit["type"] != label or tuple(hit["actors"]) != \
                        tuple(actors) or hit["object"] != obj:
                    reasons = _fail(reasons,
                                    f"event fields of {trigger!r} were "
                                    "altered")
        i += 1
    # label map is collision-free: one trigger carries exactly one type
    seen = {}
    i = 0
    while i < len(triggers):
        trigger, label = triggers[i][0], triggers[i][1]
        if trigger in seen and seen[trigger] != label:
            reasons = _fail(reasons,
                            f"label collision on trigger {trigger!r} was "
                            "accepted")
        seen[trigger] = label
        i += 1
    if out.get("labels") is not None:
        for trigger, label in seen.items():
            if out["labels"].get(trigger) != label:
                reasons = _fail(reasons,
                                f"registered label for {trigger!r} diverges")
    return not reasons, reasons


# ---------------------------------------------------------------------------
# D020
# ---------------------------------------------------------------------------


def check_D020(edges: Sequence[tuple], case_id: str, out: dict):
    reasons = ()
    # independent while-scan of the edges bound to this case
    expected = []
    i = 0
    while i < len(edges):
        if edges[i][0] == case_id:
            expected.append(edges[i])
        i += 1
    if tuple(out["bound"]) != tuple(expected):
        reasons = _fail(reasons, "bound edges are not the case-keyed rows")
    # every bound edge carries this case's key verbatim (no positional
    # default); the outside carrier keeps the rest with their own keys
    for e in out["bound"]:
        if e[0] != case_id:
            reasons = _fail(reasons,
                            f"edge {e!r} was bound to the case by position")
    if tuple(out["outside"]) != tuple(e for e in edges if e[0] != case_id):
        reasons = _fail(reasons, "outside rows were altered or dropped")
    # the prior-case victim (any row of another case) is never in the bound
    for e in edges:
        if e[0] != case_id and e in out["bound"]:
            reasons = _fail(reasons,
                            f"row {e!r} of another case entered this case's "
                            "bindings")
    # per-edge fields (person, object, stage, standing) stay verbatim
    for e in out["bound"]:
        if len(e) != 5 or e not in edges:
            reasons = _fail(reasons,
                            f"bound edge {e!r} lost its per-edge fields")
    return not reasons, reasons


# ---------------------------------------------------------------------------
# D021
# ---------------------------------------------------------------------------


def check_D021(items: Sequence[tuple], out: dict):
    reasons = ()
    timeline = out["timeline"]
    pending = out["pending"]
    # independent while-scan: dated items as (day, event id), sorted
    dated = []
    i = 0
    while i < len(items):
        if items[i][1] is not None:
            dated.append((items[i][1], items[i][0]))
        i += 1
    expected_order = tuple(eid for _d, eid in sorted(dated))
    if tuple(out["order"]) != expected_order:
        reasons = _fail(reasons, "timeline order is not the day partial "
                                 "order")
    if len(timeline) != len(dated):
        reasons = _fail(reasons, "timeline did not carry exactly the dated "
                                 "events")
    # topological validity: consecutive days are non-decreasing
    i = 1
    while i < len(timeline):
        if timeline[i - 1]["day"] > timeline[i]["day"]:
            reasons = _fail(reasons, "timeline is not a topological order of "
                                     "the day order")
            break
        i += 1
    # undated events stay unknown and never received an invented date
    undated = []
    i = 0
    while i < len(items):
        if items[i][1] is None:
            undated.append(items[i][0])
        i += 1
    if sorted(p["event"] for p in pending) != sorted(undated):
        reasons = _fail(reasons, "pending carrier is not exactly the undated "
                                 "events")
    for p in pending:
        if p["day"] is not None or p["status"] != "unknown":
            reasons = _fail(reasons,
                            f"undated event {p['event']!r} was given an "
                            "invented date")
    for entry in timeline:
        if entry["event"] in undated:
            reasons = _fail(reasons,
                            f"undated event {entry['event']!r} entered the "
                            "dated timeline")
    return not reasons, reasons


# ---------------------------------------------------------------------------
# D022
# ---------------------------------------------------------------------------


def check_D022(claims: Sequence[tuple], contrary: Sequence[tuple],
               out: dict):
    reasons = ()
    contrary_set = {frozenset(pair) for pair in contrary}
    # independent double while-scan of all ordered claim pairs
    expected = []
    ambiguity_pairs = []
    i = 0
    while i < len(claims):
        j = 0
        while j < len(claims):
            if i != j:
                sa, da, ca = claims[i]
                sb, db, cb = claims[j]
                if ca == cb:
                    j += 1
                    continue
                witness = f"{ca}!={cb}"
                if sa == sb and da == db and frozenset((ca, cb)) \
                        in contrary_set and witness:
                    expected.append((sa, da, ca, cb))
                else:
                    ambiguity_pairs.append((ca, cb))
            j += 1
        i += 1
    got = [(c["subject"], c["day"], c["propositions"][0],
            c["propositions"][1]) for c in out["conflicts"]]
    if sorted(got) != sorted(expected):
        reasons = _fail(reasons,
                        "reported conflicts are not the same-subject/"
                        "same-time declared-contrary pairs")
    for c in out["conflicts"]:
        # every reported conflict carries a nonempty witness
        if not c["witness"]:
            reasons = _fail(reasons, "a conflict was reported without a "
                                     "witness")
        if frozenset(c["propositions"]) not in contrary_set:
            reasons = _fail(reasons, "a conflict was reported without a "
                                     "declared contrary pair")
    # different-time claims never become same-time conflicts: the reported
    # conflict must be backed by a same-subject, same-day claim pair
    for c in out["conflicts"]:
        backed = False
        i = 0
        while i < len(claims):
            j = 0
            while j < len(claims):
                if i != j and claims[i][0] == c["subject"] \
                        and claims[j][0] == c["subject"] \
                        and claims[i][2] == c["propositions"][0] \
                        and claims[j][2] == c["propositions"][1] \
                        and claims[i][1] == c["day"] \
                        and claims[j][1] == c["day"]:
                    backed = True
                j += 1
            i += 1
        if not backed:
            reasons = _fail(reasons,
                            "a conflict was reported without a same-subject, "
                            "same-day claim pair (different-time claims were "
                            "judged a same-time conflict)")
    # both readings are preserved in the ambiguity carrier
    if out["ambiguities"] is not None:
        kept = {a["readings"] for a in out["ambiguities"]}
        for pair in ambiguity_pairs:
            if pair not in kept and (pair[1], pair[0]) not in kept:
                reasons = _fail(reasons,
                                f"ambiguous reading pair {pair!r} was not "
                                "preserved")
    return not reasons, reasons


# ---------------------------------------------------------------------------
# D023
# ---------------------------------------------------------------------------


def check_D023(record: Sequence[tuple], query: str, scope: Sequence[str],
               out: dict):
    reasons = ()
    # independent while-scans for the two separate carriers
    ids = []
    i = 0
    while i < len(record):
        ids.append(record[i][0])
        i += 1
    in_record = query in ids
    negative = False
    i = 0
    while i < len(record):
        if record[i][0] == query and record[i][1] is False:
            negative = True
        i += 1
    if out["in_record"] != in_record:
        reasons = _fail(reasons, "record membership was misreported")
    if out["negative_evidence"] != negative:
        reasons = _fail(reasons, "negative-evidence carrier was misreported")
    # missing never entails the negation: no explicit negative record means
    # negation_inferred stays False even when the query is absent
    if not negative and out["negation_inferred_from_missing"]:
        reasons = _fail(reasons,
                        "a missing record was read as the negated proposition")
    if not in_record and out["carrier"] == "negative-record":
        reasons = _fail(reasons, "no-record query was filed as negative "
                                 "evidence")
    # negative queries are granted only inside the declared scope
    if out["negative_allowed_in_scope"] != (query in scope):
        reasons = _fail(reasons, "negative-query scope grant diverges")
    return not reasons, reasons


# ---------------------------------------------------------------------------
# D024
# ---------------------------------------------------------------------------


def check_D024(links: Sequence[tuple], source_length: int, out: dict):
    reasons = ()
    # independent while-scan: a support passes iff bounds legal and the
    # proposition is present; irrelevant citations are rejected
    expected = {}
    rejected = []
    i = 0
    while i < len(links):
        answer, span_id, st, en, prop = links[i]
        if 0 <= st <= en <= source_length and prop:
            expected.setdefault(answer, []).append(
                (span_id, st, en, prop))
        else:
            rejected.append((answer, span_id))
        i += 1
    got = {a: tuple((e["span"], e["start"], e["end"], e["proposition"])
                    for e in v)
           for a, v in out["supports"].items()}
    for answer, spans in expected.items():
        if tuple(sorted(got.get(answer, ()))) != tuple(sorted(spans)):
            reasons = _fail(reasons,
                            f"supports of {answer!r} diverge from the "
                            "contract check")
    for answer in got:
        if answer not in expected:
            reasons = _fail(reasons,
                            f"answer {answer!r} invented supports")
    # bounds of every passing span are legal
    for answer, spans in got.items():
        for span_id, st, en, _prop in spans:
            if not (0 <= st <= en <= source_length):
                reasons = _fail(reasons,
                                f"span {span_id!r} passed with illegal bounds")
    # irrelevant citations never pass
    for answer, span_id in rejected:
        for spans in got.values():
            for entry in spans:
                if entry[0] == span_id:
                    reasons = _fail(reasons,
                                    f"irrelevant citation {span_id!r} passed "
                                    "the support check")
    if sorted(e["span"] for e in out["rejected_irrelevant"]) != \
            sorted(span_id for _a, span_id in rejected):
        reasons = _fail(reasons, "rejection carrier diverges")
    # redundant supports (distinct spans, same answer) are all retained
    per_answer = {}
    i = 0
    while i < len(links):
        if links[i][4]:
            per_answer.setdefault(links[i][0], set()).add(links[i][1])
        i += 1
    for answer, span_ids in per_answer.items():
        got_ids = {e[0] for e in got.get(answer, ())}
        if got_ids != set(span_ids):
            reasons = _fail(reasons,
                            f"redundant supports of {answer!r} were not all "
                            "retained")
    return not reasons, reasons


# ---------------------------------------------------------------------------
# D025
# ---------------------------------------------------------------------------

_FOUR = ("yes", "no", "unknown", "conflict")


def check_D025(out_status: str, out_branch: dict, default: str):
    reasons = ()
    # the projection is the identity on the four-value set
    if out_status not in _FOUR:
        reasons = _fail(reasons, f"status {out_status!r} left the four-value "
                                 "set")
    # unknown and conflict are intercepted: the branch is the declared
    # default, never a negated conclusion
    if out_status in ("unknown", "conflict"):
        if out_branch["definite"]:
            reasons = _fail(reasons,
                            f"non-definite status {out_status!r} was treated "
                            "as definite")
        if out_branch["branch"] != "default":
            reasons = _fail(reasons,
                            f"status {out_status!r} entered an if-branch as "
                            "False")
        if out_branch["value"] != default:
            reasons = _fail(reasons, "intercepted branch did not fall back "
                                     "to the declared default")
    elif out_status == "yes" and out_branch["value"] == "denied":
        reasons = _fail(reasons, "yes was coerced into a negated conclusion")
    elif out_status == "no" and out_branch["value"] == "affirmed":
        reasons = _fail(reasons, "no was coerced into an affirming conclusion")
    return not reasons, reasons


# ---------------------------------------------------------------------------
# D026
# ---------------------------------------------------------------------------


def check_D026(records: Sequence[tuple], out: dict):
    reasons = ()
    # independent while-scan: every record keeps kind/content/source/use
    # (matched by (kind, content) — content alone is not a record key)
    i = 0
    while i < len(records):
        k, c, s, u = records[i]
        hit = None
        j = 0
        while j < len(out["records"]):
            if out["records"][j]["content"] == c \
                    and out["records"][j]["kind"] == k:
                hit = out["records"][j]
                break
            j += 1
        if hit is None:
            reasons = _fail(reasons, f"record {c!r} vanished from the "
                                     "classification")
        elif (hit["kind"], hit["source"], hit["use"]) != (k, s, u):
            reasons = _fail(reasons,
                            f"record {c!r} lost its kind/source/use fields")
        i += 1
    # asserted records are never promoted to adjudicated: an adjudicated
    # slot exists only for the explicit court-registry entries
    explicit = sorted(r[1] for r in records if r[0] == "adjudicated")
    if sorted(out["explicit_adjudications"]) != explicit:
        reasons = _fail(reasons, "adjudicated slots are not the explicit "
                                 "court-registry entries")
    for k, c, s, _u in records:
        if k == "asserted" and s != "court-registry":
            i = 0
            promoted = False
            while i < len(out["records"]):
                if out["records"][i]["content"] == c and \
                        out["records"][i]["kind"] == "adjudicated":
                    promoted = True
                i += 1
            if promoted:
                reasons = _fail(reasons,
                                f"asserted record {c!r} was implicitly "
                                "promoted to adjudicated")
            refused = [p["content"] for p in out["refused_promotions"]]
            if c not in refused:
                reasons = _fail(reasons,
                                f"asserted record {c!r} was not flagged as a "
                                "refused promotion")
    return not reasons, reasons


# ---------------------------------------------------------------------------
# D027
# ---------------------------------------------------------------------------


def check_D027(draft: Sequence[str], admitted: Sequence[str],
               conditional: Sequence[str], tamper: Sequence[str],
               out_section: dict, out_delta: dict):
    reasons = ()
    # independent while-scans for the three carriers
    included = []
    pending = []
    i = 0
    while i < len(draft):
        p = draft[i]
        hit = False
        j = 0
        while j < len(admitted):
            if admitted[j] == p:
                hit = True
            j += 1
        j = 0
        while j < len(conditional):
            if conditional[j] == p:
                hit = True
            j += 1
        if hit:
            included.append(p)
        else:
            pending.append(p)
        i += 1
    if tuple(out_section["included"]) != tuple(included):
        reasons = _fail(reasons, "section is not the admitted-or-conditional "
                                 "subset")
    if tuple(out_section["pending"]) != tuple(pending):
        reasons = _fail(reasons, "pending carrier is not exactly the "
                                 "unsupported draft items")
    # pending items are retained, never silently dropped
    if sorted(out_section["pending"]) != sorted(pending):
        reasons = _fail(reasons, "pending items were dropped")
    # tampering an unconfirmed item into established fails semantically
    tampered = []
    i = 0
    while i < len(pending):
        j = 0
        while j < len(tamper):
            if tamper[j] == pending[i]:
                tampered.append(pending[i])
            j += 1
        i += 1
    if tuple(out_delta["delta"]) != tuple(tampered):
        reasons = _fail(reasons, "semantic delta is not the tampered pending "
                                 "set")
    if out_delta["semantic_difference_failed"] != bool(tampered):
        reasons = _fail(reasons, "semantic-difference verdict diverges")
    if tampered and not out_delta["delta"]:
        reasons = _fail(reasons, "an established-rewrite was not detected")
    return not reasons, reasons


# ---------------------------------------------------------------------------
# D028
# ---------------------------------------------------------------------------


def check_D028(acts: Sequence[tuple], case_id: str,
               history_rules: Sequence[tuple], out: dict):
    reasons = ()
    # independent while-scan: charges are this case's non-historical acts
    expected = []
    history = []
    i = 0
    while i < len(acts):
        if acts[i][0] == case_id and acts[i][3] is False:
            expected.append(acts[i])
        if acts[i][3] is True:
            history.append(acts[i])
        i += 1
    if tuple(out["charges"]) != tuple(expected):
        reasons = _fail(reasons, "charge list is not this case's "
                                 "non-historical acts")
    # every charge carries this case's scope verbatim
    for a in out["charges"]:
        if a[0] != case_id or len(a) != 4:
            reasons = _fail(reasons,
                            f"charge {a!r} lost its (case, event) scope")
    # historical acts never enter the current list directly
    for a in history:
        if a in out["charges"]:
            reasons = _fail(reasons,
                            f"historical act {a[2]!r} entered the current "
                            "charge list directly")
    if tuple(out["blocked_direct_history"]) != tuple(history):
        reasons = _fail(reasons, "blocked-history carrier diverges")
    # history enters only through the named rule channel
    expected_channel = tuple(r[0] for r in history_rules if r[1] is True)
    if tuple(h["rule"] for h in out["history_channel"]) != expected_channel:
        reasons = _fail(reasons, "history channel is not the declared rule "
                                 "set")
    for h in out["history_channel"]:
        declared = False
        i = 0
        while i < len(history_rules):
            if history_rules[i][0] == h["rule"]:
                declared = True
            i += 1
        if not declared:
            reasons = _fail(reasons,
                            f"channel entry {h['rule']!r} is not a declared "
                            "rule")
        if h["act_scope"] != case_id:
            reasons = _fail(reasons, "channel entry lost the current-case "
                                     "scope")
    return not reasons, reasons
