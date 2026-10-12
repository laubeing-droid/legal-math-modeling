"""Independent contract checker for group-12 drafting/delivery entries
(D104-D115).

This module deliberately re-derives every expected value from the demand
contract with its own inline logic (while-scans, negated-condition
forms); it shares no code with ``drafting_ref`` (it never imports that
module), takes no witness callbacks, and never uses the main
implementation to generate expectations.  Each ``check_D1XX`` returns
``(ok, reasons)``: ``ok`` is True exactly when the observed intermediate
result satisfies the demand's contract on the given structured input.
"""
from __future__ import annotations

from fractions import Fraction


def _fail(reasons, msg):
    return tuple(reasons) + (msg,)


def _first_value(doc, key):
    i = 0
    while i < len(doc):
        if doc[i][0] == key:
            return doc[i][1]
        i += 1
    return None


def _rows_except(doc, key):
    out = []
    i = 0
    while i < len(doc):
        if doc[i][0] != key:
            out.append(doc[i])
        i += 1
    return tuple(out)


# ---------------------------------------------------------------------------
# D104
# ---------------------------------------------------------------------------


def check_D104(req: str, src: str, asmp: str, out: dict):
    reasons = ()
    stances = ("admitted", "denied", "reserved")
    # the three explicit stances each cover the mandatory request
    for label, field in (("covered_admit", "admitted"),
                         ("covered_deny", "denied"),
                         ("covered_reserve", "reserved")):
        expected = field in stances and src != "" and asmp != ""
        if out[label] is not expected:
            reasons = _fail(reasons, "the " + field
                            + " stance coverage diverged from the "
                              "explicit-stance rule")
    # adverse cases: narrative copy, no source, no assumption
    if out["narrative_copy_misses"] is not True:
        reasons = _fail(reasons, "a narrative copy (no stance) was "
                                 "accepted as an answer")
    if out["no_source_misses"] is not True:
        reasons = _fail(reasons, "an answer without a source was "
                                 "accepted")
    if out["no_assumption_misses"] is not True:
        reasons = _fail(reasons, "an answer without an assumption was "
                                 "accepted")
    if len(set(stances)) != 3 and out["stances_distinct"] is not False:
        reasons = _fail(reasons, "the stance labels are not pairwise "
                                 "distinct but reported distinct")
    if len(set(stances)) == 3 and out["stances_distinct"] is not True:
        reasons = _fail(reasons, "the three stance labels were reported "
                                 "non-distinct")
    return not reasons, reasons


# ---------------------------------------------------------------------------
# D105
# ---------------------------------------------------------------------------


def check_D105(out: dict):
    reasons = ()
    registry = out["registry"]
    # every section grounded in the same one registry
    for label, seg in (("fact_seg_grounded", out["facts"]),
                       ("reason_seg_grounded", out["reasons"]),
                       ("ruling_seg_grounded", out["ruling"])):
        expected = True
        j = 0
        while j < len(seg):
            if seg[j] not in registry:
                expected = False
            j += 1
        if out[label] is not expected:
            reasons = _fail(reasons, "section grounding diverged from "
                                     "the same-registry rule")
    # the chain is cited level by level
    cited = out["cited"]
    expected = True
    for dep in out["deps"]:
        if dep[0] in cited and dep[1] not in cited:
            expected = False
    if out["chain_deps_met"] is not expected:
        reasons = _fail(reasons, "the upstream-dependency rule diverged")
    # adverse: gold-standard proposition outside the registry
    if "gold-9" in registry:
        reasons = _fail(reasons, "the gold-standard proposition entered "
                                 "the file's own registry")
    if out["gold_standard_not_grounded"] is not True:
        reasons = _fail(reasons, "a gold-standard proposition outside "
                                 "the registry was accepted as grounded")
    # adverse: ruling cites the result without its argument
    skip_cited = ("fact-1", "res-1")
    skip_expected = False
    for dep in out["deps"]:
        if dep[0] in skip_cited and dep[1] not in skip_cited:
            skip_expected = True
    if out["skip_upstream_fails"] is not skip_expected:
        reasons = _fail(reasons, "a ruling skipping its argument-level "
                                 "upstream dependency passed")
    return not reasons, reasons


# ---------------------------------------------------------------------------
# D106
# ---------------------------------------------------------------------------


def check_D106(amt: Fraction, out: dict):
    reasons = ()
    claims = out["claims"]
    docs = out["docs"]
    # the covering holds for the full mapping
    expected = True
    i = 0
    while i < len(claims):
        if claims[i] not in docs:
            expected = False
        i += 1
    if out["full_cover"] is not expected:
        reasons = _fail(reasons, "the identity-preserving covering "
                                 "diverged")
    # the two same-amount claims of different objects are distinct rows
    if claims[0][0] == claims[1][0]:
        reasons = _fail(reasons, "the two claims share one id (not "
                                 "different objects)")
    if out["rows_distinct"] is not True:
        reasons = _fail(reasons, "two same-amount claims of different "
                                 "objects were collapsed into one row")
    # adverse: omission — the dropped claim row must break the covering
    omission_covers = True
    i = 0
    while i < len(claims):
        if claims[i] not in (claims[0],):
            omission_covers = False
        i += 1
    if omission_covers:
        reasons = _fail(reasons, "dropping a claim row still covered "
                                 "every claim (test input broken)")
    if out["omission_misses"] is not (not omission_covers):
        reasons = _fail(reasons, "an omitted claim row still counted as "
                                 "covered")
    # adverse: amount-keyed merge — no merged row equals any claim row
    merged = out["merged"]
    merge_covers = True
    i = 0
    while i < len(claims):
        if claims[i] not in merged:
            merge_covers = False
        i += 1
    if merge_covers:
        reasons = _fail(reasons, "the merged row covered every claim "
                                 "(test input broken)")
    if out["merge_misses"] is not (not merge_covers):
        reasons = _fail(reasons, "an amount-keyed merged row was "
                                 "accepted as covering the claim list")
    return not reasons, reasons


# ---------------------------------------------------------------------------
# D107
# ---------------------------------------------------------------------------


def check_D107(t: int, src: str, out: dict):
    reasons = ()
    kinds = out["kinds"]
    # four kinds pairwise distinct
    pairwise = True
    i = 0
    while i < len(kinds):
        j = i + 1
        while j < len(kinds):
            if kinds[i] == kinds[j]:
                pairwise = False
            j += 1
        i += 1
    if pairwise is not True:
        reasons = _fail(reasons, "the four change kinds are not "
                                 "pairwise distinct")
    if out["kinds_pairwise_distinct"] is not pairwise:
        reasons = _fail(reasons, "the kind-distinctness verdict "
                                 "diverged")
    # the posture row answers only the posture channel, with its own
    # time and source
    rows = out["rows"]
    if len(rows) != 1 or rows[0][0] != 2:
        reasons = _fail(reasons, "the alert row is not an "
                                 "enforcement-posture row")
    else:
        row = rows[0]
        if out["posture_hit"] != (row[1], row[2], row[3]):
            reasons = _fail(reasons, "the posture lookup diverged from "
                                     "the kind-keyed scan")
        if out["posture_hit"][1] != t or out["posture_hit"][2] != src:
            reasons = _fail(reasons, "the posture row lost its own "
                                     "time or source")
        if out["statute_miss"] is not None:
            reasons = _fail(reasons, "a posture row answered the "
                                     "statute channel (temporarily "
                                     "not enforced read as repealed)")
        if out["case_effect_miss"] is not None:
            reasons = _fail(reasons, "a posture row answered the "
                                     "case-effect channel")
        if out["reform_miss"] is not None:
            reasons = _fail(reasons, "a posture row answered the "
                                     "reform-plan channel")
    if out["posture_label_ne_repealed"] is not True:
        reasons = _fail(reasons, "the 'temporarily not enforced' label "
                                 "was conflated with 'repealed'")
    return not reasons, reasons


# ---------------------------------------------------------------------------
# D108
# ---------------------------------------------------------------------------


def check_D108(out: dict):
    reasons = ()
    memo = out["memo"]
    # all four required slots present with non-empty content
    for slot in ("section", "conclusion", "citation", "numeric"):
        value = _first_value(memo, slot)
        if value is None or value == "":
            reasons = _fail(reasons, "required memo slot " + slot +
                            " missing or empty")
    if out["slots_ok"] is not True:
        reasons = _fail(reasons, "the complete memo failed the slot "
                                 "gate")
    # the conclusion keeps its assumptions
    if "assumption-1" not in ("assumption-1", "concl-1"):
        reasons = _fail(reasons, "the conclusion ground truth lost its "
                                 "assumption")
    if out["assumptions_met"] is not True:
        reasons = _fail(reasons, "the kept-assumption conclusion was "
                                 "rejected")
    # the numeric read-back equals the verified value
    if out["numeric_readback"] != "900-fen":
        reasons = _fail(reasons, "the numeric slot read-back diverged "
                                 "from the verified 900-fen")
    # adverse: dropped assumption
    if out["dropped_assumption_fails"] is not True:
        reasons = _fail(reasons, "a conclusion with the assumption "
                                 "dropped passed the business contract")
    # adverse: missing numeric slot
    no_numeric = out["memo_no_numeric"]
    j = 0
    has_numeric = False
    while j < len(no_numeric):
        if no_numeric[j][0] == "numeric" and no_numeric[j][1] != "":
            has_numeric = True
        j += 1
    if has_numeric:
        reasons = _fail(reasons, "the no-numeric memo still carries a "
                                 "numeric slot")
    if out["missing_numeric_fails"] is not True:
        reasons = _fail(reasons, "a memo missing the numeric slot "
                                 "passed the gate")
    return not reasons, reasons


# ---------------------------------------------------------------------------
# D109
# ---------------------------------------------------------------------------


def check_D109(organ: str, vote: str, item: str, safeguard: str,
               out: dict):
    reasons = ()
    fields, flag = out["fields"], out["approval_flag"]
    # the draft keeps the four governance fields
    if fields != (organ, vote, item, safeguard):
        reasons = _fail(reasons, "the draft lost one of organ/vote/"
                                 "item/safeguard")
    if flag is not False:
        reasons = _fail(reasons, "the draft carries an actual-approval "
                                 "flag (a draft is not an approval "
                                 "event)")
    if out["fields_preserved"] is not True:
        reasons = _fail(reasons, "the field-preservation verdict "
                                 "diverged")
    # approval only via a recorded approval event for the very item
    if out["empty_events_never_approve"] is not True:
        reasons = _fail(reasons, "an empty event list approved the "
                                 "item")
    if out["approval_event_approves"] is not True:
        reasons = _fail(reasons, "the recorded approval event failed "
                                 "to approve the item")
    if out["worded_draft_never_approves"] is not True:
        reasons = _fail(reasons, "draft wording 'resolved' counted as "
                                 "an approval event")
    # independent re-derivation of the event predicate
    marker = "approved:" + item
    if marker == item + "-worded-as-resolved":
        reasons = _fail(reasons, "the approval marker collides with "
                                 "draft wording (test input broken)")
    return not reasons, reasons


# ---------------------------------------------------------------------------
# D110
# ---------------------------------------------------------------------------


def check_D110(out: dict):
    reasons = ()
    base = list(out["base"])
    # the put lens law on any base document: put then get returns the
    # value
    for term in (("term-1", "v1"), ("client", "new-co")):
        expected_doc = [(term[0], term[1])] + list(
            _rows_except(base, term[0]))
        if _first_value(expected_doc, term[0]) != term[1]:
            reasons = _fail(reasons, "the put-then-get lens law "
                                     "diverged for " + term[0])
    if out["verified_term_readback"] != "v1":
        reasons = _fail(reasons, "the verified termsheet value did not "
                                 "read back exactly")
    if out["put_law_on_any_base"] is not True:
        reasons = _fail(reasons, "the put lens law was reported "
                                 "failing")
    # unauthorized region preserved: the client-key transform keeps the
    # term-1 row untouched
    expected_transform = [("client", "new-co"), ("term-1", "v1")]
    if out["unauthorized_region_preserved"] is not True:
        reasons = _fail(reasons, "the template transform touched a "
                                 "region outside its authorization")
    if list(out["transformed"]) != expected_transform:
        reasons = _fail(reasons, "the transformed document diverged "
                                 "from the region-preserving result")
    if out["term1_untouched"] is not True:
        reasons = _fail(reasons, "the term-1 value changed under a "
                                 "client-key transform")
    # stale placeholder detection, no false positive after update
    if out["stale_detected"] is not True:
        reasons = _fail(reasons, "the stale old-client placeholder "
                                 "went undetected")
    if out["updated_not_flagged"] is not True:
        reasons = _fail(reasons, "the updated client field was "
                                 "false-flagged as stale")
    # mutually exclusive clauses flagged together only
    pair = [("exclusive-deal", "yes"), ("open-license", "yes")]
    pair_expected = (_first_value(pair, "exclusive-deal") is not None
                     and _first_value(pair, "open-license") is not None)
    if out["exclusive_pair_flagged"] is not pair_expected:
        reasons = _fail(reasons, "the mutual-exclusion verdict "
                                 "diverged")
    if out["single_clause_not_flagged"] is not True:
        reasons = _fail(reasons, "a single exclusive clause was "
                                 "flagged as a conflict")
    return not reasons, reasons


# ---------------------------------------------------------------------------
# D111
# ---------------------------------------------------------------------------


def _spread(edges, zone):
    acc = list(zone)
    i = 0
    while i < len(edges):
        src = edges[i][0]
        tgt = edges[i][1]
        inside = False
        j = 0
        while j < len(zone):
            if zone[j] == src:
                inside = True
            j += 1
        if inside and tgt not in acc:
            acc.append(tgt)
        i += 1
    return tuple(acc)


def _defined(doc, edges, key):
    i = 0
    while i < len(edges):
        if edges[i][0] == key:
            value = _first_value(doc, edges[i][1])
            return "" if value is None else value
        i += 1
    value = _first_value(doc, key)
    return "" if value is None else value


def check_D111(out: dict):
    reasons = ()
    edges = out["edges"]
    # one spread step, then the closed zone (independent re-derivation)
    if out["zone1"] != _spread(edges, ("def-1",)):
        reasons = _fail(reasons, "the one-step affected zone diverged")
    if out["zone2"] != _spread(edges, out["zone1"]):
        reasons = _fail(reasons, "the dependency closure diverged")
    zone2 = _spread(edges, _spread(edges, ("def-1",)))
    if zone2 != ("def-1", "clause-2", "outcome-3"):
        reasons = _fail(reasons, "the closed zone is not the declared "
                                 "def-1 → clause-2 → outcome-3 chain")
    if "def-1" not in zone2 or "clause-2" not in zone2 \
            or "outcome-3" not in zone2:
        reasons = _fail(reasons, "the closure lost a chain member")
    if out["outside_zone"] is not ("preamble-9" not in zone2):
        reasons = _fail(reasons, "the outside-zone verdict diverged")
    # outside observation unchanged across the edit
    if out["outside_observation_unchanged"] is not True:
        reasons = _fail(reasons, "a protected observation outside the "
                                 "affected zone changed")
    # the defined term's effective value moves with the definition edit
    def_edges = (("clause-2", "def-1"),)
    before = [("def-1", "v1"), ("clause-2", "text-cites-def-1")]
    after = [("def-1", "v2")] + list(_rows_except(before, "def-1"))
    if _defined(before, def_edges, "clause-2") != "v1":
        reasons = _fail(reasons, "the pre-edit effective value "
                                 "diverged")
    if _defined(after, def_edges, "clause-2") != "v2":
        reasons = _fail(reasons, "the post-edit effective value "
                                 "diverged")
    if out["effective_before"] != "v1" or out["effective_after"] != "v2":
        reasons = _fail(reasons, "the effective-value pair diverged "
                                 "from the definition-edge resolution")
    if out["text_unchanged"] is not True:
        reasons = _fail(reasons, "the citing text itself was reported "
                                 "changed (only the effect moves)")
    if out["effect_changed"] is not True:
        reasons = _fail(reasons, "a definition edit left the effective "
                                 "legal effect unchanged")
    if _first_value(after, "clause-2") != "text-cites-def-1":
        reasons = _fail(reasons, "the citing text row did not survive "
                                 "the edit verbatim")
    return not reasons, reasons


# ---------------------------------------------------------------------------
# D112
# ---------------------------------------------------------------------------


def check_D112(out: dict):
    reasons = ()
    # agreeing documents: all values the same one value
    agree = (out["schedule"], out["agreement"])
    agree_vals = []
    i = 0
    while i < len(agree):
        value = _first_value(list(agree[i]), "commitment-amount")
        if value is not None:
            agree_vals.append(value)
        i += 1
    if len(agree_vals) != 2:
        reasons = _fail(reasons, "the agreeing pair does not carry two "
                                 "commitment values")
    agree_same = True
    i = 0
    while i < len(agree_vals):
        j = 0
        while j < len(agree_vals):
            if agree_vals[i] != agree_vals[j]:
                agree_same = False
            j += 1
        i += 1
    if out["agree_all_same"] is not agree_same:
        reasons = _fail(reasons, "the agreement verdict diverged")
    if out["agree_values"] != tuple(agree_vals):
        reasons = _fail(reasons, "the agreeing value list diverged")
    # diverging documents: the difference stays explicit
    diverge = (out["schedule"], out["final_version"])
    diverge_vals = []
    i = 0
    while i < len(diverge):
        value = _first_value(list(diverge[i]), "commitment-amount")
        if value is not None:
            diverge_vals.append(value)
        i += 1
    if len(diverge_vals) != 2 or diverge_vals[0] == diverge_vals[1]:
        reasons = _fail(reasons, "the diverging pair does not carry "
                                 "two different commitment values")
    if out["diverge_values"] != tuple(diverge_vals):
        reasons = _fail(reasons, "the diverging value list diverged")
    if out["diverge_not_all_same"] is not True:
        reasons = _fail(reasons, "a 500-fen vs 800-fen difference was "
                                 "reported consistent (silently "
                                 "overwritten)")
    if out["difference_visible"] is not ("500-fen" != "800-fen"):
        reasons = _fail(reasons, "the two commitment amounts were "
                                 "conflated")
    return not reasons, reasons


# ---------------------------------------------------------------------------
# D113
# ---------------------------------------------------------------------------


def check_D113(amount: Fraction, out: dict):
    reasons = ()
    role, negated, exception, amt = out["term"]
    if amt != Fraction(amount):
        reasons = _fail(reasons, "the term's numeric component "
                                 "diverged")
    # the controlled translation preserves all four components
    translated = out["translated"]
    if translated[0] != "EN-" + role or translated[1] is not negated \
            or translated[2] != "EN-" + exception \
            or translated[3] != Fraction(amt):
        reasons = _fail(reasons, "the translation did not preserve "
                                 "role/negation/exception/numeric")
    if out["role_preserved"] is not True:
        reasons = _fail(reasons, "role preservation misreported")
    if out["negation_preserved"] is not True:
        reasons = _fail(reasons, "negation preservation misreported")
    if out["exception_preserved"] is not True:
        reasons = _fail(reasons, "exception preservation misreported")
    if out["amount_preserved"] is not True:
        reasons = _fail(reasons, "numeric preservation misreported")
    # the modal flip is a role change
    if out["may_to_shall_flips_role"] is not True:
        reasons = _fail(reasons, "the may→shall flip left the role "
                                 "unchanged")
    if out["role_labels_distinct"] is not True:
        reasons = _fail(reasons, "discretionary and obligation were "
                                 "conflated")
    if out["drop_negation_flips"] is not True:
        reasons = _fail(reasons, "the negation drop left the boolean "
                                 "unchanged")
    # free-text exception yields no auto translation
    if out["free_text_manual_review"] is not True:
        reasons = _fail(reasons, "a free-text-exception term was "
                                 "auto-translated instead of kept for "
                                 "manual review")
    if out["controlled_translates"] is not True:
        reasons = _fail(reasons, "a controlled term produced no "
                                 "translation")
    return not reasons, reasons


# ---------------------------------------------------------------------------
# D114
# ---------------------------------------------------------------------------


def check_D114(out: dict):
    reasons = ()
    props = out["props"]
    points = out["points"]
    # every proposition sourced
    i = 0
    while i < len(props):
        if props[i][1] == "":
            reasons = _fail(reasons, "an unsourced proposition entered "
                                     "the summary")
        i += 1
    if out["sourced"] is not True:
        reasons = _fail(reasons, "the source gate misreported")
    # every key point covered by a same-id proposition
    covered = True
    j = 0
    while j < len(points):
        hit = False
        i = 0
        while i < len(props):
            if props[i][0] == points[j]:
                hit = True
            i += 1
        if not hit:
            covered = False
        j += 1
    if out["covered"] is not covered:
        reasons = _fail(reasons, "the coverage verdict diverged")
    # adverse: dropping the exception breaks coverage
    support_only = out["props"][:1]
    drop_covered = True
    j = 0
    while j < len(points):
        hit = False
        i = 0
        while i < len(support_only):
            if support_only[i][0] == points[j]:
                hit = True
            i += 1
        if not hit:
            drop_covered = False
        j += 1
    if drop_covered:
        reasons = _fail(reasons, "the dropped-exception case still "
                                 "covered every key point")
    if out["dropped_exception_fails"] is not True:
        reasons = _fail(reasons, "a summary without its key exception "
                                 "was reported complete")
    if out["unsourced_fails"] is not True:
        reasons = _fail(reasons, "an unsourced proposition passed the "
                                 "source gate")
    return not reasons, reasons


# ---------------------------------------------------------------------------
# D115
# ---------------------------------------------------------------------------


def check_D115(out: dict):
    reasons = ()
    rows = out["rows"]
    # the passing deliverable: dl- prefix, non-empty, well-formed,
    # clean
    if not out["gate_passes"]:
        reasons = _fail(reasons, "the honest deliverable failed the "
                                 "gate")
    if out["rows"] == ():
        reasons = _fail(reasons, "the passing deliverable has an empty "
                                 "body")
    # the key-table read-back equals the verified value
    if out["key_readback"] != "900-fen":
        reasons = _fail(reasons, "the key-table read-back diverged "
                                 "from the verified 900-fen")
    # adverse: empty body
    if out["empty_body_fails"] is not True:
        reasons = _fail(reasons, "an existing file with an empty body "
                                 "passed the gate")
    # adverse: wrong name format
    if out["wrong_name_fails"] is not True:
        reasons = _fail(reasons, "a name without the dl- prefix passed "
                                 "the gate")
    # adverse: internal scratch exposed in annotations
    scratch = (("internal-scratch", "draft-notes"),)
    scratch_clean = True
    i = 0
    while i < len(scratch):
        if scratch[i][0] == "internal-scratch":
            scratch_clean = False
        i += 1
    if scratch_clean:
        reasons = _fail(reasons, "the internal-scratch probe was "
                                 "reported clean")
    if out["scratch_annotation_fails"] is not True:
        reasons = _fail(reasons, "an annotation exposing internal "
                                 "scratch work passed the gate")
    return not reasons, reasons
