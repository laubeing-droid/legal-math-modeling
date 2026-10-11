"""Independent contract checker for group-02 sourcing (D009-D018).

This module deliberately re-derives every expected value from the demand
contract with its own inline logic; it shares no code with
``sourcing_ref`` (it never imports that module), takes no witness
callbacks, and never uses the main implementation to generate
expectations.  Each ``check_D00X`` returns ``(ok, reasons)``: ``ok`` is
True exactly when the observed intermediate result satisfies the demand's
contract on the given structured input.
"""
from __future__ import annotations

from typing import Callable, Sequence


def _fail(reasons, msg):
    return tuple(reasons) + (msg,)


# ---------------------------------------------------------------------------
# D009
# ---------------------------------------------------------------------------


def _slice_while(source: Sequence[str], start: int, end: int) -> tuple:
    """Checker-local slice derivation (while-scan, no slicing syntax)."""
    out = []
    i = start
    while i < end:
        out.append(source[i])
        i += 1
    return tuple(out)


def check_D009(source: Sequence[str], start: int, end: int, out: dict):
    reasons = ()
    if not (0 <= start <= end <= len(source)):
        return False, ("coordinates outside the source bounds",)
    expected = _slice_while(source, start, end)
    if out["span"] != expected:
        reasons = _fail(reasons, "quoted_span is not the source slice")
    if out["start"] != start or out["end"] != end:
        reasons = _fail(reasons, "provenance coordinates were altered")
    if out["length"] != end - start:
        reasons = _fail(reasons, "span length is not end - start")
    # the recorded span reads back verbatim from the source at its coords
    if _slice_while(source, out["start"], out["end"]) != tuple(out["span"]):
        reasons = _fail(reasons, "provenance readback does not restore the span")
    if out["source_length"] != len(source):
        reasons = _fail(reasons, "source length was misreported")
    return not reasons, reasons


def check_D009_version(src: dict, quoted: dict, observed_accepts: bool):
    reasons = ()
    keys_equal = (src["published"] == quoted["published"]
                  and src["effective"] == quoted["effective"]
                  and src["repeal"] == quoted["repeal"])
    if observed_accepts != keys_equal:
        reasons = _fail(reasons, "version check is not the cache-key equality")
    if not keys_equal and observed_accepts:
        reasons = _fail(reasons, "a mismatched version was accepted")
    return not reasons, reasons


# ---------------------------------------------------------------------------
# D010
# ---------------------------------------------------------------------------


def check_D010(rules: Sequence[tuple], out: dict):
    reasons = ()
    # independent while-scan for the applicable members of the frozen base
    expected = []
    i = 0
    while i < len(rules):
        if rules[i][1]:
            expected.append(rules[i][0])
        i += 1
    if tuple(out["hits"]) != tuple(expected):
        reasons = _fail(reasons, "hits are not the predicate-true rules of the frozen base")
    hit_set = set(out["hits"])
    ids = {r[0] for r in rules}
    outside = hit_set - ids
    if outside:
        reasons = _fail(reasons, f"hits left the frozen rule base: {sorted(outside)}")
    # full-applicability claim needs independent candidate coverage
    i = 0
    while i < len(rules):
        if rules[i][1] and rules[i][0] not in hit_set:
            reasons = _fail(reasons, f"applicable rule {rules[i][0]!r} missed by the result")
            break
        i += 1
    if out.get("certificate") is not None:
        covered = True
        i = 0
        while i < len(rules):
            if rules[i][1] and rules[i][0] not in hit_set:
                covered = False
                break
            i += 1
        if out["certificate"] != covered:
            reasons = _fail(reasons, "certificate is not the coverage verdict")
    # similar but inapplicable rules never enter the result
    i = 0
    while i < len(rules):
        if not rules[i][1] and rules[i][0] in hit_set:
            reasons = _fail(reasons, f"inapplicable rule {rules[i][0]!r} entered the result")
            break
        i += 1
    return not reasons, reasons


# ---------------------------------------------------------------------------
# D011
# ---------------------------------------------------------------------------


def check_D011(old: dict, new: dict, day: int, out: dict):
    reasons = ()
    # negated-condition derivation of applicability (independent form)
    def _applies(v):
        if day < v["effective"]:
            return False
        return not (v["repeal"] is not None and day >= v["repeal"])

    if out["new_applies"] != _applies(new):
        reasons = _fail(reasons, "new version applicability is not the effective-time decision")
    if out["old_applies"] != _applies(old):
        reasons = _fail(reasons, "old version applicability is not the effective-time decision")
    if out["judged_by"] != "effective":
        reasons = _fail(reasons, "decision was not made by the legal-effect time")
    # the two timelines are stored separately
    if tuple(out["registration_times"]) != (old["published"], new["published"]):
        reasons = _fail(reasons, "registration times were not preserved")
    if tuple(out["effect_times"]) != (old["effective"], new["effective"]):
        reasons = _fail(reasons, "legal-effect times were not preserved")
    # the adverse case: a later-uploaded old text is judged at the event
    # day by ITS effective time, not by its upload date
    if new["published"] < old["published"] and day < new["effective"]:
        if out["new_applies"]:
            reasons = _fail(reasons, "a later effective date was overridden by an earlier upload")
    return not reasons, reasons


# ---------------------------------------------------------------------------
# D012
# ---------------------------------------------------------------------------


def check_D012(defs: Sequence[tuple], cites: Sequence[tuple], term: str,
               fuel: int, out: dict):
    reasons = ()
    # independent iterative chase with an explicit countdown
    current = term
    countdown = fuel
    expected = None
    hops = 0
    path = []
    while True:
        if countdown == 0:
            expected = {"status": "rejected", "reason": "fuel_exhausted",
                        "meaning": None, "excluded": None}
            break
        hit = None
        i = 0
        while i < len(defs):
            if defs[i][0] == current:
                hit = defs[i]
                break
            i += 1
        if hit is not None:
            expected = {"status": "resolved", "reason": None,
                        "meaning": hit[1], "excluded": bool(hit[2])}
            break
        ref = None
        i = 0
        while i < len(cites):
            if cites[i][0] == current:
                ref = cites[i]
                break
            i += 1
        if ref is None:
            expected = {"status": "rejected", "reason": "unregistered",
                        "meaning": None, "excluded": None}
            break
        path.append(current)
        current = ref[1]
        countdown -= 1
        hops += 1
    if out["status"] != expected["status"]:
        reasons = _fail(reasons, f"chase status {out['status']!r} != {expected['status']!r}")
    if out["status"] == "resolved":
        if out["meaning"] != expected["meaning"]:
            reasons = _fail(reasons, "resolved meaning left the declared definition table")
        # the qualifier (exclusion flag) must survive resolution
        if out["excluded"] != expected["excluded"]:
            reasons = _fail(reasons, "definition qualifier was dropped by the interpreter")
    elif expected["reason"] is not None and out.get("reason") != expected["reason"]:
        reasons = _fail(reasons, f"rejection reason {out.get('reason')!r} != {expected['reason']!r}")
    if out["hops"] != hops or tuple(out["path"]) != tuple(path):
        reasons = _fail(reasons, "chase path bookkeeping diverged")
    return not reasons, reasons


# ---------------------------------------------------------------------------
# D013
# ---------------------------------------------------------------------------


def check_D013(score: dict, a: str, b: str, target_features: Sequence[str],
               relevant: Sequence[str], out: dict):
    reasons = ()
    sa, sb = score[a], score[b]
    if out["a_before_b"] != (sa > sb) or out["b_before_a"] != (sb > sa):
        reasons = _fail(reasons, "ranking comparator does not agree with the designated score")
    if sa > sb and out["b_before_a"]:
        reasons = _fail(reasons, "score order antisymmetry violated")
    if out["same_rank"] != (sa == sb):
        reasons = _fail(reasons, "equal scores were not ranked equally")
    # the transfer copy is licensed exactly by the feature witness
    if "copied" in out:
        missing = []
        i = 0
        while i < len(relevant):
            f = relevant[i]
            j = 0
            found = False
            while j < len(target_features):
                if target_features[j] == f:
                    found = True
                    break
                j += 1
            if not found:
                missing.append(f)
            i += 1
        if out["copied"] != (not missing):
            reasons = _fail(reasons, "copy decision is not the feature-witness verdict")
        if tuple(out["missing_features"]) != tuple(missing):
            reasons = _fail(reasons, "missing relevant features were misreported")
        if tuple(out["witness"]) != tuple(relevant):
            reasons = _fail(reasons, "preservation witness does not list the relevant features")
    return not reasons, reasons


# ---------------------------------------------------------------------------
# D014
# ---------------------------------------------------------------------------


def check_D014(corpus: Sequence[str], pool: Sequence[str],
               relevant: Callable[[str], bool], out: dict):
    reasons = ()
    # independent while-scan of the pool by the relevance definition
    expected = []
    i = 0
    while i < len(pool):
        if relevant(pool[i]):
            expected.append(pool[i])
        i += 1
    returned = tuple(out["returned"])
    if returned != tuple(expected):
        reasons = _fail(reasons, "returned is not the pool filtered by the relevance definition")
    pool_set = set(pool)
    # subset conjunct: every returned item is pool-internal and relevant
    for s in returned:
        if s not in pool_set:
            reasons = _fail(reasons, f"returned item {s!r} is outside the judged pool")
        elif not relevant(s):
            reasons = _fail(reasons, f"returned item {s!r} is not relevant")
    # corpus-wide no-miss claim: refused while a relevant corpus item is
    # outside the judged pool
    claimable = True
    for item in corpus:
        if item not in pool_set and relevant(item):
            claimable = False
            break
    if out["claim_ok"] != claimable:
        reasons = _fail(reasons, "corpus completeness claim is not the coverage verdict")
    return not reasons, reasons


# ---------------------------------------------------------------------------
# D015
# ---------------------------------------------------------------------------


def check_D015(cites: Sequence[tuple], prop_id: str, out: dict):
    reasons = ()
    # independent edge generation: only pro-stance citations produce edges
    expected_edges = []
    i = 0
    while i < len(cites):
        if cites[i][2]:
            expected_edges.append((cites[i][0], prop_id))
        i += 1
    if tuple(out["edges"]) != tuple(expected_edges):
        reasons = _fail(reasons, "approved edges are not the pro-stance citations")
    # a real case number with con stance is never a positive basis
    edge_sources = {e[0] for e in out["edges"]}
    i = 0
    while i < len(cites):
        if not cites[i][2] and cites[i][0] in edge_sources:
            reasons = _fail(reasons, f"con-stance citation {cites[i][0]!r} became a positive basis")
            break
        i += 1
    # every citation keeps its span verbatim in the registry
    if len(out["registry"]) != len(cites):
        reasons = _fail(reasons, "citation registry count changed")
    for obs, c in zip(out["registry"], cites):
        if obs[0] != c[0] or tuple(obs[1]) != tuple(c[1]) or obs[2] != bool(c[2]):
            reasons = _fail(reasons, f"citation {c[0]!r} lost its span or stance")
    return not reasons, reasons


# ---------------------------------------------------------------------------
# D016
# ---------------------------------------------------------------------------


def check_D016(overruled: Sequence[tuple], case: str, issue: str, day: int,
               out: dict):
    reasons = ()
    # independent while-scan for blocking overrules of exactly this issue
    blocking = []
    i = 0
    while i < len(overruled):
        o = overruled[i]
        if o[0] == case and o[1] == issue and day >= o[2]:
            blocking.append(o)
        i += 1
    if out["valid"] != (not blocking):
        reasons = _fail(reasons, "validity is not the per-issue citation-day decision")
    if tuple(out["blocking_overrules"]) != tuple(blocking):
        reasons = _fail(reasons, "blocking overrules were misreported")
    if out["case"] != case or out["issue"] != issue or out["as_of"] != day:
        reasons = _fail(reasons, "validity record lost its (case, issue, day) key")
    return not reasons, reasons


# ---------------------------------------------------------------------------
# D017
# ---------------------------------------------------------------------------


def check_D017(cands: Sequence[tuple], name: str, out: dict):
    reasons = ()
    # independent first-hit scan of the candidate table
    row = None
    i = 0
    while i < len(cands):
        if cands[i][0] == name:
            row = cands[i]
            break
        i += 1
    if row is None:
        if out["status"] != "pending" or out["branch"] is not None:
            reasons = _fail(reasons, "an unregistered framework was invented")
        return not reasons, reasons
    flags = [bool(x) for x in row[1:]]
    if out["branch"] != row:
        reasons = _fail(reasons, "the candidate branch was dropped or altered")
    if tuple(out["flags"]) != tuple(flags):
        reasons = _fail(reasons, "applicability condition flags were altered")
    all_true = all(flags)
    if out["status"] != ("selected" if all_true else "pending"):
        reasons = _fail(reasons, "selection is not the four-condition conjunction")
    # a single true condition is never sufficient (adverse: US party or
    # English contract alone does not select the UCC)
    if flags[0] and not flags[1] and out["status"] == "selected":
        reasons = _fail(reasons, "jurisdiction alone selected the framework")
    if not flags[0] and all(flags[1:]) and out["status"] == "selected":
        reasons = _fail(reasons, "subject condition alone selected the framework")
    return not reasons, reasons


# ---------------------------------------------------------------------------
# D018
# ---------------------------------------------------------------------------


def check_D018(a: dict, b: dict, out: dict):
    reasons = ()
    expected = []
    if a["subjects"] != b["subjects"]:
        expected.append("subjects")
    if a["threshold"] != b["threshold"]:
        expected.append("threshold")
    if a["timing"] != b["timing"]:
        expected.append("timing")
    if a["effect"] != b["effect"]:
        expected.append("effect")
    if tuple(out["difference_witness"]) != tuple(expected):
        reasons = _fail(reasons, "difference witness is not the dimension-wise diff")
    if out["equivalent"] != (not expected):
        reasons = _fail(reasons, "equivalence verdict contradicts the difference witness")
    if tuple(out["preserved"]) != ("subjects", "threshold", "timing", "effect"):
        reasons = _fail(reasons, "comparison did not declare all four preserved dimensions")
    # the adverse case: equal thresholds with different effects must be
    # distinguished, never reported as equivalent
    if (a["threshold"] == b["threshold"] and a["effect"] != b["effect"]
            and out["equivalent"]):
        reasons = _fail(reasons, "equal filing thresholds were conflated with equal effects")
    return not reasons, reasons
