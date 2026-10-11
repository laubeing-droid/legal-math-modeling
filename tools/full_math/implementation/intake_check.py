"""Independent contract checker for group-01 intake (D001-D008).

This module deliberately re-derives every expected value from the demand
contract with its own inline logic; it shares no code with
``intake_ref`` (it never imports that module), takes no witness
callbacks, and never uses the main implementation to generate
expectations.  Each ``check_D00X`` returns ``(ok, reasons)``: ``ok`` is
True exactly when the observed intermediate result satisfies the demand's
contract on the given structured input.
"""
from __future__ import annotations

from typing import Sequence

# checker-local route alphabet (independent of the entry module)
_CIVIL, _CRIMINAL, _PARALLEL, _PENDING = "civil", "criminal", "parallel", "pending"
_FLAG_TO_ROUTE = {
    (True, True): _PARALLEL,
    (True, False): _CIVIL,
    (False, True): _CRIMINAL,
    (False, False): _PENDING,
}


def _fail(reasons, msg):
    return tuple(reasons) + (msg,)


# ---------------------------------------------------------------------------
# D001
# ---------------------------------------------------------------------------


def check_D001(scope: Sequence[str], paragraphs: Sequence[str], out: dict):
    reasons = ()
    scope_set = set(scope)
    topics, residual, objects = out["topics"], out["residual"], out["objects"]
    # (i) topics(out) ⊆ Topics_scope
    for t in topics:
        if t not in scope_set:
            reasons = _fail(reasons, f"topic {t!r} outside declared scope")
    # (ii) every confirmed parallel issue is present with its own object
    confirmed = [p for p in paragraphs if p in scope_set]
    if sorted(topics) != sorted(confirmed):
        reasons = _fail(reasons, "confirmed issues not fully/classified 1:1")
    if set(objects.keys()) != set(confirmed):
        reasons = _fail(reasons, "demand-object table is not one-per-issue")
    for issue, obj in objects.items():
        if obj["demand_object"] != issue:
            reasons = _fail(reasons, f"object for {issue!r} is not the canonical key")
        if obj["occurrences"] != confirmed.count(issue):
            reasons = _fail(reasons, f"occurrence count for {issue!r} wrong")
    # (iii) unclassified paragraphs land in residual
    unclassified = [p for p in paragraphs if p not in scope_set]
    if sorted(residual) != sorted(unclassified):
        reasons = _fail(reasons, "residual is not exactly the unclassified set")
    return not reasons, reasons


# ---------------------------------------------------------------------------
# D002
# ---------------------------------------------------------------------------


def check_D002(table: Sequence[tuple], scenario: str, facts: Sequence[str],
               out: dict):
    reasons = ()
    # independent route derivation: first declared hit by index minimum
    hits = [i for i in range(len(table)) if table[i][0] == scenario]
    if hits:
        expected = _FLAG_TO_ROUTE[(bool(table[hits[0]][1]), bool(table[hits[0]][2]))]
    else:
        expected = _PENDING
    if out["route"] != expected:
        reasons = _fail(reasons, f"route {out['route']!r} != table semantics {expected!r}")
    if out["route"] not in set(_FLAG_TO_ROUTE.values()):
        reasons = _fail(reasons, "route outside the four-label alphabet")
    # classification must not rewrite admitted facts
    if list(out["facts"]) != list(facts):
        reasons = _fail(reasons, "admitted facts were changed by classification")
    # parallel is not forced into either/or
    for entry in table:
        if entry[0] == scenario and entry[1] and entry[2]:
            if out["route"] != _PARALLEL:
                reasons = _fail(reasons, "declared parallel was split into either/or")
    return not reasons, reasons


# ---------------------------------------------------------------------------
# D003
# ---------------------------------------------------------------------------


def check_D003(bindings: Sequence[tuple], person: str, matter: str,
               stage: str, out: dict):
    reasons = ()
    matches = [i for i in range(len(bindings))
               if bindings[i][0] == person and bindings[i][1] == matter
               and bindings[i][2] == stage]
    if matches:
        b = bindings[matches[0]]
        if out["binding"] != b:
            reasons = _fail(reasons, "resolved binding is not the declared table row")
        if out["index"] != matches[0]:
            reasons = _fail(reasons, "provenance index wrong")
        if out["key"] != (b[0], b[1], b[2], b[3]):
            reasons = _fail(reasons, "typed key is not the four declared fields")
    else:
        if out["binding"] is not None:
            reasons = _fail(reasons, "an undeclared binding was invented")
    # typed-field distinctness over the whole table: rows differing only
    # in role (or person) must carry different keys
    keys = {(b[0], b[1], b[2], b[3]) for b in bindings}
    if len(keys) != len(set(keys)):
        reasons = _fail(reasons, "typed keys collapsed inside the table")
    return not reasons, reasons


# ---------------------------------------------------------------------------
# D004
# ---------------------------------------------------------------------------


def check_D004(per_defendant: dict, required: Sequence[str], observed_ok: bool):
    reasons = ()
    expected = True
    for d in required:
        if not per_defendant.get(d, False):
            expected = False
            break
    if observed_ok != expected:
        reasons = _fail(reasons, "case correctness is not all-required-defendants")
    return not reasons, reasons


def check_D004_swap(sentences: dict, u: str, v: str, observed: bool):
    reasons = ()
    swapped = dict(sentences)
    if u in swapped and v in swapped:
        swapped[u], swapped[v] = sentences[v], sentences[u]
    total_same = sum(sentences.values()) == sum(swapped.values())
    differs = any(sentences[k] != swapped[k] for k in sentences)
    expected = total_same and differs
    if observed != expected:
        reasons = _fail(reasons, "swap detection is not total-invariant+per-defendant-fail")
    return not reasons, reasons


# ---------------------------------------------------------------------------
# D005
# ---------------------------------------------------------------------------


def check_D005(snapshot: Sequence[tuple], code_a, code_b, name: str,
               at_day: int, out: dict):
    reasons = ()
    # independent code lookups (while-scan)
    def _by_code(c):
        i = 0
        while i < len(snapshot):
            if snapshot[i][0] == c:
                return snapshot[i]
            i += 1
        return None

    ra, rb = _by_code(code_a), _by_code(code_b)
    if out.get("by_code_a") != ra or out.get("by_code_b") != rb:
        reasons = _fail(reasons, "code-keyed lookup left the independent table")
    # same name, different codes: never merged
    if ra is not None and rb is not None:
        if ra[1] == rb[1] and ra[0] == rb[0]:
            reasons = _fail(reasons, "distinct codes merged into one record")
    # alias join equals independent table semantics
    valid = [r for r in snapshot if r[1] == name and r[2] <= at_day]
    expected_key = valid[0][0] if valid else None
    if out.get("alias_key") != expected_key:
        reasons = _fail(reasons, "alias join is not the independent table semantics")
    return not reasons, reasons


# ---------------------------------------------------------------------------
# D006
# ---------------------------------------------------------------------------


def check_D006(entities: Sequence[tuple], rules: Sequence[tuple], out: dict):
    reasons = ()
    expected_edges = set()
    for r in rules:
        expected_edges.add((r[0], r[1][0]))
    observed = set(out["edges"])
    if observed != expected_edges or len(out["edges"]) != len(rules):
        reasons = _fail(reasons, "responsibility edges are not exactly the declared rules")
    # identity merges iff canonical codes are equal — a shared address
    # (or any other locator field) never propagates identity
    merge_decisions = out["merge_decisions"]
    for i in range(len(entities)):
        for j in range(len(entities)):
            a, b = entities[i], entities[j]
            expected_merge = a[0] == b[0]
            observed_merge = merge_decisions[(a[0], b[0])]
            if observed_merge != expected_merge:
                reasons = _fail(reasons,
                                f"merge decision for ({a[0]}, {b[0]}) is not code equality")
    return not reasons, reasons


# ---------------------------------------------------------------------------
# D007
# ---------------------------------------------------------------------------


def check_D007(court_table: Sequence[tuple], code: str, sources: Sequence[dict],
               day: int, exclusions: Sequence[str], slot: str, out: dict):
    reasons = ()
    found = None
    for entry in court_table:
        if entry[0] == code:
            found = entry
            break
    if out.get("court") != found:
        reasons = _fail(reasons, "court code resolution left the declared table")
    # independent applicable-source derivation (negated condition form)
    applicable = [v for v in sources
                  if not (day < v["effective"]
                          or (v["repeal"] is not None and day >= v["repeal"]))]
    if applicable:
        expected = ("applies", applicable[0])
    elif slot in set(exclusions):
        expected = ("notApplicable", "excluded")
    else:
        expected = ("pending", None)
    if out.get("jurisdiction") != expected:
        reasons = _fail(reasons, "jurisdiction is not the separate applicable-rule decision")
    return not reasons, reasons


# ---------------------------------------------------------------------------
# D008
# ---------------------------------------------------------------------------


def check_D008(rows: Sequence[dict], out: dict):
    reasons = ()
    claims = out["claims"]
    if len(claims) != len(rows):
        reasons = _fail(reasons, "claim count changed")
    for row, claim in zip(rows, claims):
        for field in ("claimant", "respondent", "basis", "object", "remedy",
                      "scope"):
            if not row.get(field) or claim[field] != row[field]:
                reasons = _fail(reasons, f"field {field} lost or emptied")
        if claim["party_pair"] != (row["claimant"], row["respondent"]):
            reasons = _fail(reasons, "amount key is not the named party pair")
        if not isinstance(claim["amount_fen"], int) or claim["amount_fen"] < 0:
            reasons = _fail(reasons, "amount is not a nonnegative integer fen value")
    # difference preservation: differing object ⇒ differing records
    for i in range(len(claims)):
        for j in range(i + 1, len(claims)):
            if rows[i].get("object") != rows[j].get("object") and claims[i] == claims[j]:
                reasons = _fail(reasons, "two claims differing in object merged")
    # ordered party pair: no claim equals its own swap when the parties differ
    for claim in claims:
        a, r = claim["claimant"], claim["respondent"]
        if a != r and claim["party_pair"] == (r, a):
            reasons = _fail(reasons, "claimant/respondent order was lost")
    return not reasons, reasons
