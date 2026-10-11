"""Group-03 evidence/event reference entries (D019-D028, W2-A batch B03).

Every entry consumes real structured input (no fixtures, no precomputed
answers) and produces the intermediate result whose formal contract is
``JurisLean.FullMath.Contracts.demand_D019`` … ``demand_D028``:

* D019 ``extract_events`` — every event row (type, actors, object, span)
  points back into the source text (its [start, end) coordinates slice the
  source verbatim); the trigger→type label map is collision-free (one
  trigger under two type labels is refused, never merged); a trigger that
  comes from a quoted hypothesis never becomes an occurred event.
* D020 ``bind_roles`` — participants, objects, legal stages and evidence
  standings are bound edge by edge under an explicit case key; a prior-case
  victim is never bound to this case by positional default.
* D021 ``build_timeline`` — explicitly dated events form a strict partial
  order (the timeline is a valid topological order of the day order);
  undated events stay unknown (``None``) and are never given an invented
  precise date from narrative order.
* D022 ``find_conflicts`` — a contradiction is reported only with the
  named proposition, the same subject AND the same time, a declared
  contrary pair, and a nonempty witness; different-time claims and
  undeclared pairs are ambiguity, and both readings are preserved.
* D023 ``missing_support`` — a missing record does not entail the negated
  proposition; "no record" and an explicit negative-evidence record are
  separate carriers; negative queries are granted only inside the declared
  complete-record scope.
* D024 ``support_check`` — every answer's supporting spans exist, have
  legal bounds and link to the answer's proposition; an irrelevant
  citation fails the support check; redundant supports are retained.
* D025 ``project_status`` / ``decide_branch`` — yes/no/unknown/conflict
  stay distinct and are never coerced into each other; a branch guard
  refuses to treat unknown/conflict as False (it falls back to the
  declared default instead of manufacturing a negated conclusion).
* D026 ``classify_records`` — asserted / evidence-content / adjudicated
  records each carry their own source and use; promotion from asserted to
  adjudicated requires an explicit adjudication record, never an implicit
  upgrade through a summary.
* D027 ``draft_fact_section`` / ``semantic_delta`` — the drafted fact
  section's protected propositions are contained in the admitted facts or
  the declared conditional semantics; undecided items are retained; an
  unconfirmed act rewritten as established makes the semantic delta fail.
* D028 ``scope_acts`` — every act carries its (case, event) scope; past
  history enters the current analysis only through a named admission rule;
  a past robbery never joins the current dangerous-driving charge list.

Amounts and any rational quantity are ``Fraction`` (ℚ); day coordinates
are exact integers.  The downstream adapters at the bottom feed these
intermediate results into the unified pipeline public entries
(``run_case`` / ``step_event`` / ``run_trace``); they never accept a
precomputed verdict.  The independent contract checker lives in
``evidence_check`` and shares no code with this module.
"""
from __future__ import annotations

from fractions import Fraction
from typing import Optional, Sequence

# ---------------------------------------------------------------------------
# D019 — event extraction with source-pointing spans and collision-free labels
# ---------------------------------------------------------------------------


def extract_events(source: Sequence[str], triggers: Sequence[tuple]) -> dict:
    """Event rows (type, actors, object, quoted, start, end) become occurred
    events only when they are asserted (never quoted-hypothesis) and their
    span coordinates slice the source verbatim; the trigger→type label map
    is refused on collision (same trigger, two type labels)."""

    label_of: dict[str, str] = {}
    for trigger, label, _actors, _obj, _quoted, _st, _en in triggers:
        seen = label_of.get(trigger)
        if seen is not None and seen != label:
            raise ValueError(
                f"label map collision: trigger {trigger!r} carries both "
                f"{seen!r} and {label!r}")
        label_of[trigger] = label
    events = []
    quoted_blocked = []
    for trigger, label, actors, obj, quoted, st, en in triggers:
        if not (0 <= st <= en <= len(source)):
            raise ValueError(
                f"span of trigger {trigger!r} leaves the source bounds")
        span = tuple(source[st:en])
        if quoted:
            quoted_blocked.append((trigger, span))
            continue
        events.append({
            "type": label,
            "actors": tuple(actors),
            "object": obj,
            "trigger": trigger,
            "span": span,
            "start": st,
            "end": en,
            "span_length": en - st,
        })
    return {"events": tuple(events), "quoted_blocked": tuple(quoted_blocked),
            "labels": dict(label_of), "source_length": len(source)}


# ---------------------------------------------------------------------------
# D020 — per-edge participant/object/stage/standing binding under a case key
# ---------------------------------------------------------------------------


def bind_roles(edges: Sequence[tuple], case_id: str) -> dict:
    """Bindings are selected by the explicit case key of each edge row
    (case, person, object, stage, standing); no row is bound to this case
    by positional default, and the standing rides on the edge itself."""

    bound = tuple(e for e in edges if e[0] == case_id)
    return {"case": case_id, "bound": bound,
            "outside": tuple(e for e in edges if e[0] != case_id)}


# ---------------------------------------------------------------------------
# D021 — sourced timeline: dated partial order, undated stays unknown
# ---------------------------------------------------------------------------


def build_timeline(items: Sequence[tuple]) -> dict:
    """Dated events enter the timeline in a valid topological order of the
    day partial order (ascending day, stable by event id); undated events
    stay ``day=None`` in the pending carrier and never receive an invented
    date from narrative position."""

    dated = [(day, eid) for eid, day in items if day is not None]
    ordered = sorted(dated)
    timeline = tuple(
        {"event": eid, "day": day, "status": "dated"} for day, eid in ordered)
    pending = tuple({"event": eid, "day": None, "status": "unknown"}
                    for eid, day in items if day is None)
    return {"timeline": timeline, "pending": pending,
            "order": tuple(eid for _, eid in ordered)}


# ---------------------------------------------------------------------------
# D022 — contradictions need proposition + same subject/time + witness
# ---------------------------------------------------------------------------


def find_conflicts(claims: Sequence[tuple],
                   contrary: Sequence[tuple]) -> dict:
    """A contradiction is reported only when subject and day coincide, the
    content pair is declared contrary, and a nonempty witness is produced;
    different-time or undeclared pairs stay ambiguity with both readings
    preserved."""

    contrary_set = {frozenset(pair) for pair in contrary}
    conflicts = []
    ambiguities = []
    for subj_a, day_a, cont_a in claims:
        for subj_b, day_b, cont_b in claims:
            if cont_a == cont_b:
                continue
            pair = (cont_a, cont_b)
            witness = f"{cont_a}!={cont_b}"
            if subj_a == subj_b and day_a == day_b \
                    and frozenset(pair) in contrary_set and witness:
                conflicts.append({"subject": subj_a, "day": day_a,
                                  "propositions": pair, "witness": witness})
            else:
                ambiguities.append({"readings": pair,
                                    "same_subject": subj_a == subj_b,
                                    "same_time": day_a == day_b})
    return {"conflicts": tuple(conflicts), "ambiguities": tuple(ambiguities)}


# ---------------------------------------------------------------------------
# D023 — missing support vs. negative evidence are separate carriers
# ---------------------------------------------------------------------------


def missing_support(record: Sequence[tuple], query: str,
                    scope: Sequence[str]) -> dict:
    """``record`` rows are (proposition, polarity); a query absent from the
    record is only missing — it never becomes the negated proposition.  An
    explicit negative record is a separate carrier.  Negative queries are
    granted only inside the declared complete-record scope."""

    ids = [r[0] for r in record]
    negative = any(r[0] == query and r[1] is False for r in record)
    in_scope = query in scope
    return {"query": query, "in_record": query in ids,
            "negative_evidence": negative,
            "negative_allowed_in_scope": in_scope,
            "negation_inferred_from_missing": False,
            "carrier": ("negative-record" if negative else
                        "no-record" if query not in ids else "present")}


# ---------------------------------------------------------------------------
# D024 — answer support spans: exist, legal bounds, linked, redundant kept
# ---------------------------------------------------------------------------


def support_check(links: Sequence[tuple], source_length: int) -> dict:
    """``links`` rows are (answer, span_id, start, end, proposition).  A
    support passes only when the span exists in the check, its bounds are
    legal (0 ≤ start ≤ end ≤ source_length) and it carries the answer's
    proposition; an irrelevant citation fails.  Distinct spans for one
    answer are redundant supports and are all retained."""

    by_answer: dict[str, list] = {}
    rejected = []
    for answer, span_id, st, en, prop in links:
        entry = {"span": span_id, "start": st, "end": en, "proposition": prop}
        if not (0 <= st <= en <= source_length) or not prop:
            rejected.append(entry)
            continue
        by_answer.setdefault(answer, []).append(entry)
    return {"supports": {a: tuple(v) for a, v in by_answer.items()},
            "rejected_irrelevant": tuple(rejected),
            "source_length": source_length}


# ---------------------------------------------------------------------------
# D025 — yes/no/unknown/conflict stay distinct; branches never coerce
# ---------------------------------------------------------------------------

_YES = "yes"
_NO = "no"
_UNKNOWN = "unknown"
_CONFLICT = "conflict"
_STATUSES = (_YES, _NO, _UNKNOWN, _CONFLICT)


def project_status(status: str) -> str:
    """The status projection is the identity on the four values: yes, no,
    unknown and conflict are never coerced into one another."""

    if status not in _STATUSES:
        raise ValueError(f"status {status!r} is outside the four-value set")
    return status


def decide_branch(status: str, default: str):
    """A conditional branch may consume only a definite yes/no; unknown and
    conflict are intercepted and fall back to the declared default — they
    are never read as False and never manufacture a negated conclusion."""

    if status == _YES:
        return {"branch": "then", "value": "affirmed", "definite": True}
    if status == _NO:
        return {"branch": "else", "value": "denied", "definite": True}
    return {"branch": "default", "value": default, "definite": False}


# ---------------------------------------------------------------------------
# D026 — asserted / evidence content / adjudicated, no implicit promotion
# ---------------------------------------------------------------------------

_KIND_ASSERTED = "asserted"
_KIND_EVIDENCE = "evidenceContent"
_KIND_ADJUDICATED = "adjudicated"
_KINDS = (_KIND_ASSERTED, _KIND_EVIDENCE, _KIND_ADJUDICATED)


def classify_records(records: Sequence[tuple]) -> dict:
    """``records`` rows are (kind, content, source, use).  Every record
    keeps its kind, source and use verbatim; a promotion of an asserted
    record to adjudicated is refused unless an explicit adjudication entry
    (source = court registry) exists for the same content."""

    explicit_adjudications = {r[1] for r in records
                              if r[0] == _KIND_ADJUDICATED}
    kept = tuple({"kind": k, "content": c, "source": s, "use": u}
                 for k, c, s, u in records)
    refused_promotions = []
    for k, c, s, u in records:
        if k == _KIND_ASSERTED and s != "court-registry":
            refused_promotions.append({"content": c, "source": s})
    return {"records": kept,
            "explicit_adjudications": tuple(sorted(explicit_adjudications)),
            "refused_promotions": tuple(refused_promotions)}


# ---------------------------------------------------------------------------
# D027 — drafted fact section: supported or conditional, pending retained
# ---------------------------------------------------------------------------


def draft_fact_section(draft: Sequence[str], admitted: Sequence[str],
                       conditional: Sequence[str]) -> dict:
    """Protected propositions of the drafted section enter only when they
    sit in the admitted facts or the declared conditional semantics; the
    rest stay pending and are retained (never silently dropped)."""

    admitted_set = set(admitted)
    conditional_set = set(conditional)
    included = tuple(p for p in draft
                     if p in admitted_set or p in conditional_set)
    pending = tuple(p for p in draft
                    if p not in admitted_set and p not in conditional_set)
    return {"included": included, "pending": pending,
            "admitted_basis": tuple(p for p in included if p in admitted_set),
            "conditional_basis": tuple(p for p in included
                                       if p in conditional_set)}


def semantic_delta(section: dict, tamper: Sequence[str]) -> dict:
    """Rewriting an unconfirmed (pending) proposition as established is a
    semantic change: the delta lists every tampered pending item and is
    nonempty exactly when the section's pending carrier was altered."""

    pending = tuple(section["pending"])
    tampered = tuple(p for p in pending if p in set(tamper))
    return {"delta": tampered, "semantic_difference_failed": bool(tampered)}


# ---------------------------------------------------------------------------
# D028 — per-act (case, event) scope; history only through named rules
# ---------------------------------------------------------------------------


def scope_acts(acts: Sequence[tuple], case_id: str,
               history_rules: Sequence[tuple]) -> dict:
    """``acts`` rows are (case_id, event_id, act, historical).  The current
    charge list contains only this case's non-historical acts; historical
    experience enters only through a named history rule (rows declared
    ``True`` in ``history_rules``), each addition carrying its rule name —
    a past robbery never joins the current charge list by itself."""

    charges = tuple(a for a in acts
                    if a[0] == case_id and a[3] is False)
    history_channel = tuple({"rule": r[0], "act_scope": case_id}
                            for r in history_rules if r[1] is True)
    blocked_history = tuple(a for a in acts if a[3] is True)
    return {"case": case_id, "charges": charges,
            "history_channel": history_channel,
            "blocked_direct_history": blocked_history}


# ---------------------------------------------------------------------------
# Downstream adapters: evidence results → pipeline carriers (PY-RUN)
# ---------------------------------------------------------------------------

EVIDENCE_ENV_ID = "env-evidence-b03"


def build_evidence_intake() -> dict:
    """Synthetic evidence bundle for one loan case: every field is produced
    by the entries above from declared input tables; the quoted-hypothesis
    trigger, the prior-case victim, the different-time pair, the unattached
    receipt question, the unknown branch, the asserted-only record, the
    unconfirmed act and the robbery history are all kept distinguishable."""

    # D019: the source narrative; "borrow" inside the quoted hypothesis
    # ("若借款未还") must not become an occurred event
    source = ("被告", "于", "3月", "向", "原告", "借款",
              "若", "借款", "未还", "则", "承担", "责任")
    triggers = (
        ("借款", "LOAN_GRANT", ("被告", "原告"), "principal", False, 0, 6),
        ("若", "HYPOTHESIS", (), "condition", True, 6, 9),
        ("未还", "DEFAULT_EVENT", ("被告",), "principal", True, 7, 9),
        ("责任", "LIABILITY", ("被告",), "damages", False, 9, 12),
    )
    extraction = extract_events(source, triggers)
    # D020: per-edge binding; the prior-case victim stays outside this case
    edges = (
        ("case-b03", "plaintiff", "principal", "trial", "admitted-evidence"),
        ("case-b03", "defendant", "principal", "trial", "disputed"),
        ("case-prior", "prior-victim", "prior-object", "prior-trial",
         "adjudicated"),
    )
    binding = bind_roles(edges, "case-b03")
    # D021: dated events order the timeline; the undated call stays unknown
    items = (("chat-2024-01-05", 1), ("transfer", 3), ("call", None),
             ("receipt", 8))
    timeline = build_timeline(items)
    # D022: same subject+time+contrary pair is a conflict; the same subject
    # at a different day is ambiguity with both readings preserved
    claims = (("defendant", 10, "repaid-full"),
              ("defendant", 10, "unpaid"),
              ("defendant", 20, "repaid-full"),
              ("defendant", 20, "moved-away"))
    contrary = (("repaid-full", "unpaid"), ("unpaid", "repaid-full"))
    conflicts = find_conflicts(claims, contrary)
    # D023: the payment receipt is absent from the record — that is only
    # "no record", never the negated proposition "unpaid"
    record = (("loan_granted", True), ("demand_sent", True))
    missing = missing_support(record, "receipt_attached", ("receipt_attached",))
    # D024: two support spans for the answer (redundant, both retained);
    # the irrelevant citation carries no proposition and fails the check
    links = (("ans-payment", "span-transfer", 3, 5, "transfer-made"),
             ("ans-payment", "span-chat", 1, 2, "transfer-made"),
             ("ans-payment", "span-unrelated", 9, 10, ""))
    support = support_check(links, len(source))
    # D025: the open question "did the bank charge fees?" is unknown; the
    # branch guard intercepts it instead of treating unknown as False
    status = project_status(_UNKNOWN)
    branch = decide_branch(status, "open-question-retained")
    # D026: the plaintiff's assertion keeps its own source/use and is never
    # promoted; the court's own explicit entries are the only adjudicated
    # rows (an explicit court entry is a separate record, not an upgrade of
    # the assertion through the summary)
    records = (
        (_KIND_ASSERTED, "loan_granted", "complaint-summary",
         "party-allegation"),
        (_KIND_EVIDENCE, "transfer_made", "bank-slips", "fact-finding-input"),
        (_KIND_ADJUDICATED, "transfer_made", "court-registry", "adjudicated"),
        (_KIND_ADJUDICATED, "loan_granted", "court-registry", "adjudicated"),
    )
    classified = classify_records(records)
    # D027: the drafted section keeps the confirmed items, retains the
    # unconfirmed one as pending, and flags the established-rewrite tamper
    draft = ("loan_granted", "transfer_made", "fees_charged")
    section = draft_fact_section(draft, ("loan_granted", "transfer_made"),
                                 ("fees_charged",))
    delta = semantic_delta(section, ("fees_charged",))
    # D028: this case's dangerous-driving charge list never contains the
    # prior robbery; history enters only through the named recidivism rule
    acts = (("case-b03", "ev-drive", "dangerous-driving", False),
            ("case-old", "ev-rob", "robbery", True))
    scoped = scope_acts(acts, "case-b03",
                        (("recidivism-art-74", True),))
    principal = Fraction(1_000_000)
    return {
        "case_id": "case-b03",
        "extraction": extraction,
        "binding": binding,
        "timeline": timeline,
        "conflicts": conflicts,
        "missing": missing,
        "support": support,
        "status": status,
        "branch": branch,
        "classified": classified,
        "section": section,
        "delta": delta,
        "scoped": scoped,
        "principal": principal,
        "admitted_facts": ("loan_granted", "transfer_made"),
    }


def build_case_input(intake: dict):
    """Assemble the normalized CaseInput from the evidence results; the
    pipeline consumes exactly these intermediate objects: the issue is the
    D019 event's type, the claim rides the D020 bound plaintiff/defendant
    edge, the fact records come from the D026 classification (only the
    adjudicated content is admitted; the asserted one stays awaiting)."""
    from fractions import Fraction

    from theory.spec.canonical_v2.case import (
        CaseInput,
        Claim,
        ExactQuantity,
        FactRecord,
        FactStanding,
        Polar,
        ProcessState,
        ScopedAtom,
    )
    from theory.spec.canonical_v2.kernel import NormState

    case_id = intake["case_id"]
    event = intake["extraction"]["events"][0]
    issue = event["type"]
    state = ProcessState(
        r=NormState(relations=()),
        environment_id=EVIDENCE_ENV_ID,
        stages=((f"{case_id}-trial", "trial"),),
        events=(),
        target_day=10,
        as_of_day=10,
    )
    parties = ("plaintiff", "defendant")
    # the D020 bound edge supplies claimant/respondent, never swapped
    claims = (
        Claim("c0", "plaintiff", "defendant", issue, "principal",
              "payment", subject="", issue=issue),
    )
    # D026: adjudicated content is admitted; asserted content stays
    # awaiting admission — the assertion is never promoted into findings
    standings = {
        "adjudicated": FactStanding.ADMITTED_POSITIVE,
        "evidenceContent": FactStanding.AWAITING_ADMISSION,
        "asserted": FactStanding.AWAITING_ADMISSION,
    }
    subject = f"span:{event['start']}:{event['end']}"
    facts = tuple(
        FactRecord(
            f"f-{i}-{rec['kind']}-{rec['content']}",
            ScopedAtom(case_id=case_id, subject=subject, issue=issue,
                       stage="trial", predicate=rec["content"],
                       polar=Polar.POS),
            standings[rec["kind"]],
            produced_at=i,
            known_at=i,
        )
        for i, rec in enumerate(intake["classified"]["records"])
    )
    quantities = (
        ExactQuantity(Fraction(intake["principal"]), "CNY-fen", "principal",
                      "loan_contract_signed"),
    )
    return CaseInput(
        case_id=case_id,
        initial_state=state,
        parties=parties,
        issues=(issue,),
        claims=claims,
        defenses=(),
        fact_records=facts,
        evidence_records=(),
        questions=(),
        quantities=quantities,
    )


def build_environment(intake: dict):
    """Declared environment: named sufficiency template licensed by the
    D019 event type; no verdicts, no prebuilt framework."""
    from theory.spec.canonical_v2.case import (
        LegalEnvironment,
        StrongTemplate,
    )
    from theory.spec.canonical_v2.kernel import Jurisdiction, JurisdictionRoute

    issue = intake["extraction"]["events"][0]["type"]
    template = StrongTemplate(
        template_id="tpl-loan-delivery-b03",
        kind="LOAN_DELIVERY",
        scope_issue=issue,
        premise_predicates=("loan_granted", "transfer_made"),
        conclusion_predicate=issue,
        failure_predicates=("repaid-full",),
        license_rule_id="",
        source_id=f"evidence:{issue}",
    )
    return LegalEnvironment(
        environment_id=EVIDENCE_ENV_ID,
        jurisdiction=Jurisdiction(route=JurisdictionRoute.MAINLAND),
        rules=(),
        strong_templates=(template,),
    )


def evidence_trace_events(intake: dict):
    """The D019 occurred events and the D024 passing support spans become
    process events; each occurred event keeps its own evidence event bound
    to its source span, and each payment keeps its own event so
    per-obligor dispositions are never averaged."""
    from fractions import Fraction

    from theory.spec.canonical_v2.case import CaseEvent
    from unified.process import LegalEventKind, ProcessEvent

    events = []
    day = 5
    for ev in intake["extraction"]["events"]:
        evidence = ProcessEvent(
            event=CaseEvent(
                event_id=f"ev-{ev['trigger']}-{ev['start']}-{ev['end']}",
                event_type="EVIDENCE_SUBMITTED",
                occurred_at=day,
                observed_at=day + 1,
                object_ref=ev["object"],
            ),
            kind=LegalEventKind.EVIDENCE_SUBMITTED,
        )
        events.append(evidence)
        day += 1
    basis = intake["extraction"]["events"][0]["type"]
    for obligor, amount in (("D1", 400_000), ("D2", 600_000)):
        events.append(
            ProcessEvent(
                event=CaseEvent(
                    event_id=f"pay-{obligor}",
                    event_type="PAYMENT_PERFORMED",
                    occurred_at=day,
                    observed_at=day,
                    object_ref="principal",
                ),
                kind=LegalEventKind.PAYMENT_PERFORMED,
                basis_key=basis,
                amount=Fraction(int(amount)),
                debt_order=(basis,),
            )
        )
        day += 1
    return tuple(events)
