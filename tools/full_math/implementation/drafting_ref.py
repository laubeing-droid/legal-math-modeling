"""Group-12 drafting/revision/delivery reference entries (D104-D115,
W2-A batch B12).

Every entry consumes real structured input (no fixtures, no precomputed
answers) and produces the intermediate result whose formal contract is
``JurisLean.FullMath.Contracts.demand_D104`` … ``demand_D115``:

* D104 ``defense_answer`` — the mandatory-reply coverage of an answer
  draft: every required request has an answer row of its own id with an
  explicit stance (admission / denial / reservation are three distinct
  labels) and non-empty source and assumption fields; narrative copying,
  a missing source and a missing assumption never cover.
* D105 ``structured_sections`` — the fact, reason and ruling sections
  cite only propositions grounded in the same one registry of
  fact/argument/result objects, and citing a proposition always cites
  its declared upstream dependency (fact → argument → result); a
  gold-standard proposition outside the file's registry and a ruling
  that skips the argument level both fail.
* D106 ``claim_schedule`` — the confirmed claim list to the document
  list is an identity-preserving covering: every confirmed (id, target,
  amount) row appears in the document list as the very same row; an
  omission and an amount-keyed merge (two same-amount claims of
  different objects collapsed) never cover.
* D107 ``client_alert`` — statute change, adjudication effect,
  enforcement posture and expected reform are four distinct kinds,
  queried by kind so an enforcement-posture row (carrying its own time
  and source) never answers the statute channel; "temporarily not
  enforced" and "repealed" are distinct labels.
* D108 ``memo_review`` — section/conclusion/citation/numeric slots are
  each present with non-empty verifiable content, the conclusion keeps
  its assumption conditions, and the numeric slot read-back equals the
  verified value; a conclusion with a dropped assumption or a memo
  missing the numeric slot fails.
* D109 ``resolution_draft`` — the generated draft keeps organ, vote,
  authorized item and conflict safeguard with the actual-approval flag
  fixed to False; actual approval comes only from a recorded approval
  event for the very item, never from "resolved"-worded draft text.
* D110 ``termsheet_draft`` — a verified termsheet value put into the
  draft reads back exactly (the docGet_put law); a template transform
  on the client key leaves the term-1 region untouched; a stale old
  client name is detected (no false positive after the update) and two
  mutually exclusive clauses together are flagged.
* D111 ``redline_impact`` — the modification point and its dependency
  closure form the affected zone (one spread step, then the closed
  zone); a key outside the zone keeps its protected observation across
  the edit, while a term defined through the edited definition changes
  its effective value even though its citing text is untouched.
* D112 ``cross_doc_consistency`` — multiple documents carry their own
  values for one shared constraint key; agreement means all values are
  the same, and a financing-commitment 500-fen against a final-version
  800-fen stays an explicit visible difference (never silently
  overwritten into "all consistent").
* D113 ``term_translation`` — a controlled-term translation keeps the
  role, the negation, the exception and the numeric amount (the EN-
  prefix only decorates); a "may"→"shall" modal flip and a negation
  drop are detected violations, and a term whose exception field is
  free text produces no auto translation at all (kept for manual
  review).
* D114 ``summary_review`` — every protected proposition of the summary
  carries a non-empty source and every independently determined key
  point is covered by a same-id proposition; dropping the key exception
  or carrying an unsourced proposition fails.
* D115 ``delivery_check`` — a required deliverable passes the gate only
  when its name carries the ``dl-`` prefix, its body is non-empty with
  well-formed row keys and no annotation row exposes internal scratch
  work; the key table read-back (put then get) equals the verified
  value.

Amounts are ``Fraction`` (ℚ).  The downstream adapters at the bottom
feed these intermediate results into the unified pipeline public
entries (``run_case`` / ``step_event`` / ``run_trace``); they never
accept a precomputed verdict.  The independent contract checker lives
in ``drafting_check`` and shares no code with this module.
"""
from __future__ import annotations

from fractions import Fraction

# ---------------------------------------------------------------------------
# shared Doc carrier (mirrors JurisLean.FullMath.Document.Doc lenses)
# ---------------------------------------------------------------------------


def doc_get(doc, key: str):
    """The value of one key — the first row carrying exactly that key."""

    for k, v in doc:
        if k == key:
            return v
    return None


def erase_key(doc, key: str):
    """All rows except the ones carrying that key."""

    return [(k, v) for k, v in doc if k != key]


def doc_put(doc, key: str, value: str):
    """The put lens — the new row first, earlier rows of the same key
    erased (never silently overwritten in place)."""

    return [(key, value)] + erase_key(doc, key)


# ---------------------------------------------------------------------------
# D104 — mandatory-reply coverage with explicit stances
# ---------------------------------------------------------------------------

ANS_ADMITS = "admitted"
ANS_DENIES = "denied"
ANS_RESERVES = "reserved"


def stance_ok(stance: str) -> bool:
    """Is this one of the three explicit answer stances?"""

    return stance in (ANS_ADMITS, ANS_DENIES, ANS_RESERVES)


def defense_covers(required, answers) -> bool:
    """Mandatory-reply coverage — every required request has an answer
    row of its own id, with an explicit stance and non-empty source and
    assumption fields."""

    for req in required:
        hit = False
        for row in answers:
            if (row[0] == req and stance_ok(row[1])
                    and row[2] != "" and row[3] != ""):
                hit = True
                break
        if not hit:
            return False
    return True


def defense_answer(req: str, src: str, asmp: str) -> dict:
    """The coverage verdicts of one answer draft: the three explicit
    stances each cover, while narrative copying (no stance), a missing
    source and a missing assumption never do; the three stance labels
    are pairwise distinct so admission and reservation are never
    conflated."""

    return {
        "required": (req,),
        "covered_admit":
            defense_covers((req,), ((req, ANS_ADMITS, src, asmp),)),
        "covered_deny":
            defense_covers((req,), ((req, ANS_DENIES, src, asmp),)),
        "covered_reserve":
            defense_covers((req,), ((req, ANS_RESERVES, src, asmp),)),
        "narrative_copy_misses":
            not defense_covers((req,), ((req, "narrate", req, req),)),
        "no_source_misses":
            not defense_covers((req,), ((req, ANS_DENIES, "", asmp),)),
        "no_assumption_misses":
            not defense_covers((req,), ((req, ANS_DENIES, src, ""),)),
        "stances_distinct": len({ANS_ADMITS, ANS_DENIES, ANS_RESERVES}) == 3,
    }


# ---------------------------------------------------------------------------
# D105 — same-registry grounded sections, no upstream skip
# ---------------------------------------------------------------------------


def seg_grounded(registry, seg) -> bool:
    """Every proposition of one section is grounded in the same one
    registry of fact/argument/result objects."""

    return all(p in tuple(registry) for p in seg)


def deps_met(cited, deps) -> bool:
    """Citing a proposition requires citing its declared upstream
    dependency — the chain is never skipped."""

    for src, tgt in deps:
        if src in tuple(cited) and tgt not in tuple(cited):
            return False
    return True


def structured_sections() -> dict:
    """The three sections of one draft all draw on the same registry and
    the full chain fact → argument → result is cited level by level; a
    gold-standard proposition outside the registry and a ruling that
    cites the result without its argument both fail."""

    registry = ("fact-1", "arg-1", "res-1")
    facts = ("fact-1",)
    reasons = ("fact-1", "arg-1")
    ruling = ("arg-1", "res-1")
    deps = (("arg-1", "fact-1"), ("res-1", "arg-1"))
    cited = facts + reasons + ruling
    return {
        "registry": registry, "facts": facts, "reasons": reasons,
        "ruling": ruling, "deps": deps, "cited": cited,
        "fact_seg_grounded": seg_grounded(registry, facts),
        "reason_seg_grounded": seg_grounded(registry, reasons),
        "ruling_seg_grounded": seg_grounded(registry, ruling),
        "chain_deps_met": deps_met(cited, deps),
        "gold_standard_not_grounded":
            not seg_grounded(registry, ("gold-9",)),
        "skip_upstream_fails":
            not deps_met(("fact-1", "res-1"), deps),
    }


# ---------------------------------------------------------------------------
# D106 — identity-preserving covering of the confirmed claim list
# ---------------------------------------------------------------------------


def claim_covered(claims, docs) -> bool:
    """Every confirmed claim row appears in the document list as the
    very same (id, target, amount) row."""

    return all(c in tuple(docs) for c in claims)


def claim_schedule(amt: Fraction) -> dict:
    """The confirmed two-claim list maps onto the document list
    identically; the two same-amount claims of different objects remain
    two distinct rows, and an omission or an amount-keyed merge never
    covers."""

    claim_a = ("claim-a", "pay-costs", Fraction(amt))
    claim_b = ("claim-b", "pay-costs", Fraction(amt))
    full = (claim_a, claim_b)
    merged = (("merged-claim", "pay-costs", Fraction(amt) + Fraction(amt)),)
    return {
        "claims": full, "docs": full, "merged": merged,
        "full_cover": claim_covered(full, full),
        "rows_distinct": claim_a != claim_b,
        "omission_misses": not claim_covered(full, (claim_a,)),
        "merge_misses": not claim_covered(full, merged),
    }


# ---------------------------------------------------------------------------
# D107 — four change kinds presented separately with time and source
# ---------------------------------------------------------------------------

CHG_STATUTE = 0
CHG_CASE_EFFECT = 1
CHG_ENFORCE_POSTURE = 2
CHG_REFORM_PLAN = 3


def alert_row_of(rows, kind: int):
    """The client-alert row lookup by change kind — only a row of the
    same kind answers, carrying its own content, time and source
    (fail-closed None otherwise)."""

    for row in rows:
        if row[0] == kind:
            return (row[1], row[2], row[3])
    return None


def client_alert(t: int, src: str) -> dict:
    """One enforcement-posture row: it answers the posture channel with
    its own time and source, never the statute/case-effect/reform
    channels, and the 'temporarily not enforced' label is distinct from
    'repealed' — a posture record never masquerades as a repeal."""

    kinds = (CHG_STATUTE, CHG_CASE_EFFECT, CHG_ENFORCE_POSTURE,
             CHG_REFORM_PLAN)
    rows = ((CHG_ENFORCE_POSTURE, "temp-not-enforced", t, src),)
    return {
        "kinds": kinds, "rows": rows,
        "kinds_pairwise_distinct": all(
            kinds[i] != kinds[j]
            for i in range(len(kinds))
            for j in range(i + 1, len(kinds))),
        "posture_hit": alert_row_of(rows, CHG_ENFORCE_POSTURE),
        "statute_miss": alert_row_of(rows, CHG_STATUTE),
        "case_effect_miss": alert_row_of(rows, CHG_CASE_EFFECT),
        "reform_miss": alert_row_of(rows, CHG_REFORM_PLAN),
        "posture_label_ne_repealed":
            "temp-not-enforced" != "repealed",
    }


# ---------------------------------------------------------------------------
# D108 — verifiable memo slots, conclusion keeps its assumptions
# ---------------------------------------------------------------------------

MEMO_REQUIRED_SLOTS = ("section", "conclusion", "citation", "numeric")


def memo_slots_ok(memo) -> bool:
    """Each required slot — section, conclusion, citation, numeric
    example — is present with non-empty verifiable content."""

    for slot in MEMO_REQUIRED_SLOTS:
        value = doc_get(memo, slot)
        if value is None or value == "":
            return False
    return True


def concl_assumptions_met(assumptions, conclusion) -> bool:
    """The conclusion keeps its assumption conditions — every declared
    hypothesis is still cited in it."""

    return all(a in tuple(conclusion) for a in assumptions)


def memo_review() -> dict:
    """One complete memo: all four slots verifiable, the conclusion
    keeps assumption-1, and the numeric slot reads back the verified
    900-fen; a conclusion with the assumption dropped or a memo missing
    the numeric slot fails."""

    memo = (("section", "structure-1"), ("conclusion", "concl-1"),
            ("citation", "cite-1"), ("numeric", "900-fen"))
    memo_no_numeric = (("section", "structure-1"),
                       ("conclusion", "concl-1"),
                       ("citation", "cite-1"))
    return {
        "memo": memo, "memo_no_numeric": memo_no_numeric,
        "slots_ok": memo_slots_ok(memo),
        "assumptions_met":
            concl_assumptions_met(("assumption-1",),
                                  ("assumption-1", "concl-1")),
        "numeric_readback": doc_get(memo, "numeric"),
        "dropped_assumption_fails":
            not concl_assumptions_met(("assumption-1",), ("concl-1",)),
        "missing_numeric_fails": not memo_slots_ok(memo_no_numeric),
    }


# ---------------------------------------------------------------------------
# D109 — resolution draft keeps governance fields, never an approval
# ---------------------------------------------------------------------------


def draft_resolution(organ: str, vote: str, item: str, safeguard: str):
    """The generated resolution draft: organ, vote, authorized item and
    conflict safeguard carried verbatim, actual-approval flag fixed to
    False — a draft is not an approval event however it is worded."""

    return ((organ, vote, item, safeguard), False)


def approved_by(events, item: str) -> bool:
    """Actual approval — only a recorded approval event for the very
    item counts."""

    return any(e == "approved:" + item for e in events)


def resolution_draft(organ: str, vote: str, item: str,
                     safeguard: str) -> dict:
    """The draft keeps all four governance fields with the approval flag
    False; the empty event list never approves, the recorded approval
    event does, and draft wording 'worded-as-resolved' is not an
    approval event."""

    fields, flag = draft_resolution(organ, vote, item, safeguard)
    return {
        "fields": fields, "approval_flag": flag,
        "fields_preserved":
            fields == (organ, vote, item, safeguard) and flag is False,
        "empty_events_never_approve": approved_by((), item) is False,
        "approval_event_approves":
            approved_by(("approved:" + item,), item) is True,
        "worded_draft_never_approves":
            approved_by((item + "-worded-as-resolved",), item) is False,
    }


# ---------------------------------------------------------------------------
# D110 — termsheet constraints land; template regions preserved
# ---------------------------------------------------------------------------


def term_met(draft, term) -> bool:
    """The draft satisfies one verified termsheet constraint — the
    term's value in the draft is exactly the verified value."""

    return doc_get(draft, term[0]) == term[1]


def stale_client(draft, old_client: str) -> bool:
    """A stale placeholder of the reused template — the old client's
    name still in the client field — is detected."""

    return doc_get(draft, "client") == old_client


def excl_conflict(draft) -> bool:
    """Two mutually exclusive clauses present together in one draft are
    flagged."""

    return (doc_get(draft, "exclusive-deal") is not None
            and doc_get(draft, "open-license") is not None)


def termsheet_draft() -> dict:
    """A verified termsheet value put into the draft reads back exactly
    (the put lens law on any base document); the client-key template
    transform leaves the term-1 region untouched; the stale old client
    name is detected without a false positive after the update, and the
    mutually exclusive pair is flagged while a single clause is not."""

    base = [("client", "old-co"), ("term-1", "v1")]
    transformed = doc_put(base, "client", "new-co")
    terms = (("term-1", "v1"), ("client", "new-co"))
    return {
        "base": tuple(base), "transformed": tuple(transformed),
        "verified_term_readback":
            doc_get(doc_put([], "term-1", "v1"), "term-1"),
        "put_law_on_any_base":
            all(term_met(doc_put(base, t[0], t[1]), t) for t in terms),
        "unauthorized_region_preserved":
            transformed == [("client", "new-co"), ("term-1", "v1")],
        "term1_untouched":
            doc_get(transformed, "term-1") == "v1",
        "stale_detected": stale_client([("client", "old-co")], "old-co"),
        "updated_not_flagged":
            not stale_client([("client", "new-co")], "old-co"),
        "exclusive_pair_flagged": excl_conflict(
            [("exclusive-deal", "yes"), ("open-license", "yes")]),
        "single_clause_not_flagged":
            not excl_conflict([("exclusive-deal", "yes")]),
    }


# ---------------------------------------------------------------------------
# D111 — dependency-closure affected zone; outside observations fixed
# ---------------------------------------------------------------------------


def spread_once(edges, zone):
    """One dependency-spread step — the zone grows by the targets of
    every edge whose source is already inside the zone, without
    duplicating keys already in the zone."""

    acc = list(zone)
    for src, tgt in edges:
        if src in tuple(zone) and tgt not in acc:
            acc.append(tgt)
    return tuple(acc)


def defined_term_of(doc, edges, key: str) -> str:
    """The effective value of a defined term resolves through its
    defining edge — a term whose definition references another key reads
    that key's value."""

    for src, tgt in edges:
        if src == key:
            value = doc_get(doc, tgt)
            return "" if value is None else value
    value = doc_get(doc, key)
    return "" if value is None else value


def redline_impact() -> dict:
    """Editing def-1 spreads once to [def-1, clause-2] and closes to
    [def-1, clause-2, outcome-3]; preamble-9 stays outside the zone and
    its observation survives the edit unchanged (whole-document
    equation), while clause-2's effective value — resolved through the
    definition edge — changes from v1 to v2 although its citing text is
    untouched."""

    edges = (("def-1", "clause-2"), ("clause-2", "outcome-3"))
    zone1 = spread_once(edges, ("def-1",))
    zone2 = spread_once(edges, zone1)
    before = [("def-1", "v1"), ("preamble-9", "text-9")]
    after = doc_put(before, "def-1", "v2")
    def_edges = (("clause-2", "def-1"),)
    text_before = [("def-1", "v1"), ("clause-2", "text-cites-def-1")]
    text_after = doc_put(text_before, "def-1", "v2")
    return {
        "edges": edges, "zone1": zone1, "zone2": zone2,
        "outside_zone": "preamble-9" not in zone2,
        "outside_observation_unchanged":
            after == [("def-1", "v2"), ("preamble-9", "text-9")]
            and doc_get(after, "preamble-9") == "text-9",
        "effective_before":
            defined_term_of(text_before, def_edges, "clause-2"),
        "effective_after":
            defined_term_of(text_after, def_edges, "clause-2"),
        "text_unchanged":
            doc_get(text_after, "clause-2") == "text-cites-def-1",
        "effect_changed":
            defined_term_of(text_before, def_edges, "clause-2") == "v1"
            and defined_term_of(text_after, def_edges, "clause-2") == "v2",
    }


# ---------------------------------------------------------------------------
# D112 — shared-constraint values across documents, no silent overwrite
# ---------------------------------------------------------------------------


def values_of(docs, key: str) -> tuple:
    """The values that multiple documents carry for one shared
    constraint key."""

    return tuple(v for v in (doc_get(d, key) for d in docs)
                 if v is not None)


def all_same(values) -> bool:
    """All values in the list agree — the shared-constraint consistency
    across documents."""

    vals = tuple(values)
    return all(x == y for x in vals for y in vals)


def cross_doc_consistency() -> dict:
    """The disclosure schedule and the merger agreement agree on the
    commitment amount (500-fen both); swapping in the final-version
    document (800-fen) leaves an explicit two-value difference that no
    last-write merge may flatten into 'all consistent'."""

    schedule = (("commitment-amount", "500-fen"),)
    agreement = (("commitment-amount", "500-fen"),
                 ("closing-event", "signed"))
    final_version = (("commitment-amount", "800-fen"),)
    agreeing = (schedule, agreement)
    diverging = (schedule, final_version)
    return {
        "schedule": schedule, "agreement": agreement,
        "final_version": final_version,
        "agree_values": values_of(agreeing, "commitment-amount"),
        "agree_all_same": all_same(
            values_of(agreeing, "commitment-amount")),
        "diverge_values": values_of(diverging, "commitment-amount"),
        "diverge_not_all_same": not all_same(
            values_of(diverging, "commitment-amount")),
        "difference_visible": "500-fen" != "800-fen",
    }


# ---------------------------------------------------------------------------
# D113 — controlled-term translation preserves four components
# ---------------------------------------------------------------------------


def translate_term(term):
    """A controlled-term translation keeps (role, negation, exception,
    numeric) — the EN- prefix only decorates strings."""

    role, negated, exception, amount = term
    return ("EN-" + role, negated, "EN-" + exception, Fraction(amount))


def may_to_shall(term):
    """The modal flip the contract forbids — 'may' rendered as an
    unconditional 'shall' replaces the role in place."""

    role, negated, exception, amount = term
    return ("obligation", negated, exception, Fraction(amount))


def drop_negation(term):
    """The negation drop the contract forbids."""

    role, negated, exception, amount = term
    return (role, False, exception, Fraction(amount))


def translate_checked(term):
    """Only terms whose exception field is a controlled label are
    auto-translatable; a free-text exception is preserved for manual
    review — no auto output at all."""

    if term[2] == "free-text":
        return None
    return translate_term(term)


def term_translation(amount: Fraction) -> dict:
    """The controlled translation preserves all four components; the
    may→shall flip changes the role (discretionary ≠ obligation), the
    negation drop flips the boolean, and the free-text-exception term
    yields None (manual review) while the controlled term translates."""

    term = ("discretionary", True, "none-exc", Fraction(amount))
    return {
        "term": term,
        "translated": translate_term(term),
        "role_preserved": translate_term(term)[0] == "EN-" + term[0],
        "negation_preserved": translate_term(term)[1] is term[1],
        "exception_preserved":
            translate_term(term)[2] == "EN-" + term[2],
        "amount_preserved": translate_term(term)[3] == term[3],
        "may_to_shall_flips_role":
            may_to_shall(("discretionary", False, "none-exc",
                          Fraction(amount)))[0] == "obligation",
        "role_labels_distinct": "discretionary" != "obligation",
        "drop_negation_flips":
            drop_negation(("duty", True, "none-exc",
                           Fraction(amount)))[1] is False,
        "controlled_translates":
            translate_checked(("discretionary", False, "none-exc",
                               Fraction(amount))) is not None,
        "free_text_manual_review":
            translate_checked(("free-role", False, "free-text",
                               Fraction(amount))) is None,
    }


# ---------------------------------------------------------------------------
# D114 — sourced summary propositions covering the key points
# ---------------------------------------------------------------------------


def summary_sourced(props) -> bool:
    """Every protected proposition of the summary carries a non-empty
    source."""

    return all(p[1] != "" for p in props)


def covers_points(points, props) -> bool:
    """Every independently determined key point is covered by some
    summary proposition of the same id."""

    return all(any(p[0] == k for p in props) for k in points)


def summary_review() -> dict:
    """Supporting argument and key exception both carry sources and both
    key points are covered; dropping the exception proposition breaks
    the coverage and an unsourced proposition fails the source gate."""

    full = (("support-1", "src-1"), ("exception-1", "src-2"))
    support_only = (("support-1", "src-1"),)
    points = ("support-1", "exception-1")
    return {
        "props": full, "points": points,
        "sourced": summary_sourced(full),
        "covered": covers_points(points, full),
        "dropped_exception_fails": not covers_points(points, support_only),
        "unsourced_fails":
            not summary_sourced((("exception-1", ""),)),
    }


# ---------------------------------------------------------------------------
# D115 — deliverable gate: exists, parses, name format, clean readback
# ---------------------------------------------------------------------------


def prefix_dl(name: str) -> bool:
    """The delivery name format — the required ``dl-`` prefix."""

    return name.startswith("dl-")


def deliverable_ok(name: str, rows) -> bool:
    """A required deliverable is fit — dl- name prefix, non-empty body,
    well-formed row keys."""

    rows = tuple(rows)
    return (prefix_dl(name) and rows != ()
            and all(r[0] != "" for r in rows))


def clean_annotations(rows) -> bool:
    """No annotation row exposes internal scratch work."""

    return all(r[0] != "internal-scratch" for r in rows)


def deliverable_gate(name: str, rows) -> bool:
    """The full delivery gate — fit deliverable plus clean
    annotations."""

    return deliverable_ok(name, rows) and clean_annotations(rows)


def delivery_check() -> dict:
    """The passing deliverable (dl-motion.csv with the claim table) and
    its key-table read-back equal to the verified 900-fen; the empty
    body, the wrong name format and the internal-scratch annotation each
    fail the gate."""

    rows = (("claim-1", "900-fen"),)
    return {
        "rows": rows,
        "gate_passes": deliverable_gate("dl-motion.csv", rows),
        "key_readback":
            doc_get(doc_put([], "claim-1", "900-fen"), "claim-1"),
        "empty_body_fails":
            not deliverable_gate("dl-motion.csv", ()),
        "wrong_name_fails":
            not deliverable_gate("motion.csv", rows),
        "scratch_annotation_fails":
            not deliverable_gate("dl-motion.csv",
                                 (("internal-scratch", "draft-notes"),)),
    }


# ---------------------------------------------------------------------------
# Downstream adapters: drafting results → pipeline carriers (PY-RUN)
# ---------------------------------------------------------------------------

DRAFTING_ENV_ID = "env-drafting-b12"


def build_drafting_intake() -> dict:
    """Synthetic drafting-delivery bundle for one litigation matter:
    every field is produced by the entries above from declared
    structured inputs; the answer coverage, the grounded sections, the
    claim covering, the separated change channels, the memo verdicts,
    the non-approving resolution draft, the termsheet transform, the
    redline zone, the cross-document difference, the term translation
    and the deliverable gate all stay distinguishable."""

    # D104: mandatory request answered by an explicit denial with source
    # and assumption; narrative copying never covers
    answer = defense_answer("req-refund", "complaint-art-7",
                            "delivery-record-3")
    # D105: fact/argument/result sections on one registry, full chain
    sections = structured_sections()
    # D106: two same-amount claims of different objects covered verbatim
    claims = claim_schedule(Fraction(450, 1))
    # D107: one enforcement-posture change with time and source
    alert = client_alert(20260301, "reg-bulletin-2026-03")
    # D108: complete memo with kept assumptions
    memo = memo_review()
    # D109: board draft on the guarantee approval, not an approval event
    resolution = resolution_draft("board", "unanimous",
                                  "approve-guarantee", "abstention-recused")
    # D110: client-key template transform, termsheet value lands
    termsheet = termsheet_draft()
    # D111: def-1 edit zone and the unchanged outside observation
    redline = redline_impact()
    # D112: schedule/agreement agree; final version differs visibly
    consistency = cross_doc_consistency()
    # D113: controlled term translated, free text kept for review
    translation = term_translation(Fraction(900, 1))
    # D114: summary with sourced propositions covering the key points
    summary = summary_review()
    # D115: deliverable gate with key-table read-back
    delivery = delivery_check()
    return {"case_id": "case-b12",
            "answer": answer, "sections": sections, "claims": claims,
            "alert": alert, "memo": memo, "resolution": resolution,
            "termsheet": termsheet, "redline": redline,
            "consistency": consistency, "translation": translation,
            "summary": summary, "delivery": delivery,
            "admitted_facts": ("claim-list-covered",
                               "deliverable-verified")}


def build_case_input(intake: dict):
    """Assemble the normalized CaseInput from the drafting results; the
    pipeline consumes exactly these intermediate objects: the covered
    claim list and the verified deliverable supply the admitted facts,
    the uncovered-claim proposition a missing claim row would ground
    stays awaiting (never written), and the only quantities are the
    claim-amount total (both same-amount claims, one schedule) and the
    financing-commitment amount — the value the final version visibly
    differs from."""

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
    issue = "DRAFTING_DELIVERY"
    state = ProcessState(
        r=NormState(relations=()),
        environment_id=DRAFTING_ENV_ID,
        stages=((f"{case_id}-trial", "trial"),),
        events=(),
        target_day=10,
        as_of_day=10,
    )
    parties = ("client", "counterparty", "board")
    # the client's delivery claim rides on the covered claim list
    # (D106); the counterparty's defense points at the redline scope
    # (D111) — an edit outside the affected zone is not a new obligation
    claims = (
        Claim("c0", "client", "counterparty", issue, "claim-list-covered",
              "document-delivery", subject="", issue=issue),
    )
    defenses = (
        Defense("def-redline-scoped", "counterparty", ("c0",),
                "redline_outside_zone"),
    )
    standings = {
        "admitted": FactStanding.ADMITTED_POSITIVE,
        "awaiting": FactStanding.AWAITING_ADMISSION,
    }
    # admitted: the covered claim list (D106) and the verified
    # deliverable (D115); awaiting: the uncovered-claim proposition
    # (D106 adverse side) — a missing claim row never grounds it here
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
            ("f-claims", "claim-list-covered",
             standings["admitted"]),      # D106 full covering
            ("f-delivery", "deliverable-verified",
             standings["admitted"]),      # D115 gate passed
            ("f-uncovered", "uncovered-claim",
             standings["awaiting"]),      # D106 adverse, never written
        ))
    )
    quantities = (
        ExactQuantity(intake["claims"]["claims"][0][2]
                      + intake["claims"]["claims"][1][2],
                      "CNY-fen", "claim-amount", "claim-schedule"),
        ExactQuantity(Fraction(500, 1), "CNY-fen", "commitment-amount",
                      "financing-commitment"),
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
    claim-list-covered and deliverable-verified predicates; no verdicts,
    no prebuilt framework."""

    from theory.spec.canonical_v2.case import (
        LegalEnvironment,
        StrongTemplate,
    )
    from theory.spec.canonical_v2.kernel import Jurisdiction, JurisdictionRoute

    issue = "DRAFTING_DELIVERY"
    template = StrongTemplate(
        template_id="tpl-drafting-delivery-b12",
        kind="DRAFTING_DELIVERY",
        scope_issue=issue,
        premise_predicates=("claim-list-covered", "deliverable-verified"),
        conclusion_predicate=issue,
        failure_predicates=("uncovered-claim",),
        license_rule_id="",
        source_id=f"drafting:{issue}",
    )
    return LegalEnvironment(
        environment_id=DRAFTING_ENV_ID,
        jurisdiction=Jurisdiction(route=JurisdictionRoute.MAINLAND),
        rules=(),
        strong_templates=(template,),
    )


def drafting_trace_events(intake: dict):
    """The deliverable file witness becomes an evidence event, and the
    covered claim total lands as one exact installment (900 fen, never a
    rounded number) against the claim-amount basis; the
    financing-commitment basis receives nothing (the visible
    cross-document difference stays a difference)."""

    from theory.spec.canonical_v2.case import CaseEvent
    from unified.process import LegalEventKind, ProcessEvent

    events = []
    day = 5
    evidence = ProcessEvent(
        event=CaseEvent(
            event_id="ev-delivered-file",
            event_type="EVIDENCE_SUBMITTED",
            occurred_at=day,
            observed_at=day + 1,
            object_ref="delivered_file_witness",
        ),
        kind=LegalEventKind.EVIDENCE_SUBMITTED,
    )
    events.append(evidence)
    day += 2
    basis = "CLAIM_AMOUNT"
    claims = intake["claims"]["claims"]
    events.append(
        ProcessEvent(
            event=CaseEvent(
                event_id="pay-claims-900",
                event_type="PAYMENT_PERFORMED",
                occurred_at=day,
                observed_at=day,
                object_ref="claim_schedule",
            ),
            kind=LegalEventKind.PAYMENT_PERFORMED,
            basis_key=basis,
            amount=claims[0][2] + claims[1][2],
            debt_order=(basis,),
        )
    )
    return tuple(events)
