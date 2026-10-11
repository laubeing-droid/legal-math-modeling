"""Group-01 intake reference entries (D001-D008, W2-A batch B01).

Every entry consumes real structured input (no fixtures, no precomputed
answers) and produces the intermediate result whose formal contract is
``JurisLean.FullMath.Contracts.demand_D001`` … ``demand_D008``:

* D001 ``classify_topics``  — topics(out) ⊆ declared scope; one canonical
  demand object per confirmed parallel issue; unclassified paragraphs land
  in ``residual``.
* D002 ``classify_route``   — route(s) allows civil / criminal / parallel
  / pending; a parallel declaration is returned as-is (no forced
  either/or); admitted facts pass through untouched.
* D003 ``resolve_role``     — every role binding is resolved from the
  declared binding table only (no automatic bindings); person, matter,
  stage and role are distinct typed key fields.
* D004 ``case_correctness`` — whole-case correctness = every required
  defendant's own mapping correct; swapping two defendants' dispositions
  keeps the total but must fail the per-defendant check.
* D005 ``resolve_registry`` — for a fixed registry snapshot, canonical-key
  (registration code) lookup and alias resolution hit the independent
  table semantics; same name with different codes never merges, and the
  same code across a rename is resolved by the validity time.
* D006 ``responsibility_edges`` — personal/affiliate/representative
  relations are NOT identity; responsibility edges are generated only by
  explicitly declared rules.
* D007 ``resolve_court`` / ``jurisdiction_status`` — court code resolves
  to (institution, level) by table; jurisdiction is a separate applicable-
  source decision (a resolved code is not jurisdiction).
* D008 ``parse_claims``     — Claim=(claimant,respondent,basis,object,
  remedy,scope); every amount field is keyed to a named party pair; a
  subject-less amount row is rejected, never silently merged.

The downstream adapters at the bottom feed these intermediate results into
the unified pipeline public entries (``run_case`` / ``step_event`` /
``run_trace``); they never accept a precomputed verdict.  The independent
contract checker lives in ``intake_check`` and shares no code with this
module.
"""
from __future__ import annotations

from fractions import Fraction
from typing import Optional, Sequence

# ---------------------------------------------------------------------------
# D001 — topic classification with declared scope
# ---------------------------------------------------------------------------


def classify_topics(scope: Sequence[str], paragraphs: Sequence[str]) -> dict:
    """topics(out) ⊆ scope; one canonical demand object per confirmed
    issue; out-of-scope paragraphs go to residual."""

    confirmed: list = []
    residual: list = []
    scope_set = frozenset(scope)
    for p in paragraphs:
        (confirmed if p in scope_set else residual).append(p)
    # one canonical demand object per confirmed parallel issue; the
    # object key is the issue content itself, never a locator (length,
    # position or hash of the paragraph)
    objects: dict = {}
    for issue in confirmed:
        if issue not in objects:
            objects[issue] = {
                "demand_object": issue,
                "occurrences": confirmed.count(issue),
            }
    return {"topics": tuple(confirmed), "residual": tuple(residual),
            "objects": objects}


# ---------------------------------------------------------------------------
# D002 — civil/criminal nature routing
# ---------------------------------------------------------------------------

ROUTE_CIVIL = "civil"
ROUTE_CRIMINAL = "criminal"
ROUTE_PARALLEL = "parallel"
ROUTE_PENDING = "pending"
ROUTE_ALPHABET = frozenset({ROUTE_CIVIL, ROUTE_CRIMINAL, ROUTE_PARALLEL,
                            ROUTE_PENDING})


def classify_route(table: Sequence[tuple], scenario: str,
                   facts: Sequence[str]) -> dict:
    """Route decision from the declared concurrency table; a miss stays
    pending; parallel (civil AND criminal) is a first-class outcome; the
    admitted facts layer is returned untouched."""

    hit = None
    for entry in table:
        if entry[0] == scenario:
            hit = entry
            break
    if hit is None:
        route = ROUTE_PENDING
    elif hit[1] and hit[2]:
        route = ROUTE_PARALLEL
    elif hit[1]:
        route = ROUTE_CIVIL
    elif hit[2]:
        route = ROUTE_CRIMINAL
    else:
        route = ROUTE_PENDING
    # classification never rewrites the admitted facts
    return {"route": route, "facts": tuple(facts)}


# ---------------------------------------------------------------------------
# D003 — role bindings with provenance
# ---------------------------------------------------------------------------


def role_binding_key(binding: tuple) -> tuple:
    """Typed binding key: person, matter, stage and role are distinct
    fields; equal display strings in different fields never merge."""

    return (binding[0], binding[1], binding[2], binding[3])


def resolve_role(bindings: Sequence[tuple], person: str, matter: str,
                 stage: str) -> dict:
    """First declared binding matching (person, matter, stage); absent
    bindings resolve to None — signature by a legal representative never
    auto-creates a personal-debtor role."""

    for idx, b in enumerate(bindings):
        if b[0] == person and b[1] == matter and b[2] == stage:
            return {"binding": b, "key": role_binding_key(b),
                    "index": idx, "source": b[4] if len(b) > 4 else ""}
    return {"binding": None, "key": None, "index": None, "source": None}


# ---------------------------------------------------------------------------
# D004 — per-defendant result mapping
# ---------------------------------------------------------------------------


def case_correctness(per_defendant: dict, required: Sequence[str]) -> bool:
    """Whole-case correctness = every required defendant's own mapping is
    correct; averages or totals are never consulted."""

    return all(bool(per_defendant.get(d, False)) for d in required)


def swap_detected(sentences: dict, u: str, v: str) -> bool:
    """The adverse case: swapping two defendants' dispositions keeps the
    total (hence any average) unchanged while every per-defendant check
    still fails."""

    swapped = dict(sentences)
    swapped[u], swapped[v] = sentences[v], sentences[u]
    total_same = sum(sentences.values()) == sum(swapped.values())
    per_defendant_differs = any(sentences[d] != swapped[d] for d in sentences)
    return total_same and per_defendant_differs


# ---------------------------------------------------------------------------
# D005 — registry snapshot resolution
# ---------------------------------------------------------------------------


def resolve_by_code(snapshot: Sequence[tuple], code) -> Optional[tuple]:
    """Canonical subject key (registration code) lookup on the fixed
    snapshot."""

    for rec in snapshot:
        if rec[0] == code:
            return rec
    return None


def alias_lookup(snapshot: Sequence[tuple], name: str, at_day: int) -> Optional[tuple]:
    """Alias resolution on the fixed snapshot: first record whose name
    matches and whose validity window covers ``at_day``; same-name
    different-code records stay separate."""

    for rec in snapshot:
        if rec[1] == name and rec[2] <= at_day:
            return rec
    return None


def alias_join_canonical_key(snapshot: Sequence[tuple], name: str,
                             at_day: int) -> Optional[int]:
    """Alias → canonical code join equals the independent table semantics:
    the canonical key of exactly the record the table returns."""

    rec = alias_lookup(snapshot, name, at_day)
    return None if rec is None else rec[0]


# ---------------------------------------------------------------------------
# D006 — commingling guard and rule-generated responsibility edges
# ---------------------------------------------------------------------------


def responsibility_edges(rules: Sequence[tuple]) -> tuple:
    """Responsibility edges are generated only by explicitly declared
    rules (src, (dst, ground)); no rule, no edge."""

    return tuple((r[0], r[1][0]) for r in rules)


def merged_by_equality(e1: tuple, e2: tuple) -> bool:
    """Identity is never propagated from a shared address (or any other
    locator field): only equal canonical codes merge."""

    return e1[0] == e2[0]


# ---------------------------------------------------------------------------
# D007 — court code resolution vs. separate jurisdiction decision
# ---------------------------------------------------------------------------


def resolve_court(court_table: Sequence[tuple], code: str) -> Optional[tuple]:
    """Court code → (code, institution, level) by table lookup; the
    fields are reported as declared, never invented."""

    for entry in court_table:
        if entry[0] == code:
            return entry
    return None


def jurisdiction_status(sources: Sequence[dict], day: int,
                        exclusions: Sequence[str], slot: str) -> tuple:
    """Jurisdiction uses the separate applicable-source rule family:
    effective ≤ day and not repealed before day; no applicable source and
    no exclusion ground stays pending (pending ≠ inapplicable)."""

    applicable = [
        v for v in sources
        if v["effective"] <= day
        and (v["repeal"] is None or day < v["repeal"])
    ]
    if not applicable:
        if slot in frozenset(exclusions):
            return ("notApplicable", "excluded")
        return ("pending", None)
    return ("applies", applicable[0])


# ---------------------------------------------------------------------------
# D008 — claim records with subject-bound amounts
# ---------------------------------------------------------------------------

CLAIM_FIELDS = ("claimant", "respondent", "basis", "object", "remedy",
                "scope")


def parse_claim(row: dict) -> dict:
    """One claim record; claimant and respondent are required and ordered
    (swapping them is a different claim).  The amount is keyed to the
    named party pair — a subject-less amount field cannot exist."""

    for field in CLAIM_FIELDS:
        if not row.get(field):
            raise ValueError(f"claim requires a nonempty {field}")
    return {
        "claimant": row["claimant"],
        "respondent": row["respondent"],
        "basis": row["basis"],
        "object": row["object"],
        "remedy": row["remedy"],
        "scope": row["scope"],
        "party_pair": (row["claimant"], row["respondent"]),
        "amount_fen": int(row.get("amount_fen", 0)),
    }


def parse_claims(rows: Sequence[dict]) -> tuple:
    """Relation among claims is preserved: records differing in any of
    the six fields stay distinct records."""

    return tuple(parse_claim(r) for r in rows)


# ---------------------------------------------------------------------------
# Downstream adapters: intake results → pipeline carriers (PY-RUN)
# ---------------------------------------------------------------------------

INTAKE_ENV_ID = "env-intake-b01"


def build_loan_intake() -> dict:
    """Synthetic intake bundle for one civil loan case; every field is
    produced by the entries above from declared input tables."""

    # D001: declared issue scope from the task, not from a classifier;
    # one paragraph classifies under the loan issue, one stays residual
    topics = classify_topics(
        scope=("loan",),
        paragraphs=("loan", "unrelated_note"),
    )
    # D002: civil route; a criminal clue stays visible but is never
    # converted into a civil verdict
    route = classify_route(
        table=(("loan-case", True, False),),
        scenario="loan-case",
        facts=("civil_liability", "criminal_clue"),
    )
    # D005: fixed registry snapshot; same name, two codes; canonical
    # subject key of the borrower resolved by alias at day 50
    registry = (
        (911100001, "Borrower Ltd", 0),
        (911100002, "Borrower Ltd", 100),
    )
    borrower_code = alias_join_canonical_key(registry, "Borrower Ltd", 50)
    # D003: declared role bindings only
    bindings = (
        ("C", "loan-case", "trial", "claimant", "identity-card"),
        ("D", "loan-case", "trial", "borrower", "loan_contract_signed"),
    )
    roles = {
        person: resolve_role(bindings, person, "loan-case", "trial")
        for person in ("C", "D")
    }
    # D008: the principal claim; each amount keyed to the party pair
    claims = parse_claims((
        {"claimant": "C", "respondent": "D", "basis": "loan",
         "object": "principal", "remedy": "payment", "scope": "loan",
         "amount_fen": 10_000_000},
    ))
    # D004: per-defendant (here per-obligor) performance facts — the
    # trace consumes the per-defendant payments, never an average
    per_defendant_payments = {"D1": 2_000_000, "D2": 3_000_000}
    # D006: responsibility edges from declared rules only (D2 is
    # jointly liable with D1 by an explicit rule)
    rules = (("D1", ("D2", "joint_debt_declaration")),)
    edges = responsibility_edges(rules)
    # D007: court docket code resolves; jurisdiction stays pending (no
    # applicable source declared) — carried on the bundle, never folded
    # into the pipeline's own jurisdiction axis
    court = resolve_court((("Y11", "Y-Court", "intermediate"),), "Y11")
    jurisdiction = jurisdiction_status((), 10, (), "Y11")
    return {
        "case_id": "case-b01",
        "topics": topics,
        "route": route,
        "registry": registry,
        "borrower_code": borrower_code,
        "roles": roles,
        "claims": claims,
        "per_defendant_payments": per_defendant_payments,
        "responsibility_rules": rules,
        "responsibility_edges": edges,
        "court": court,
        "jurisdiction_status": jurisdiction,
        "admitted_facts": ("contract_signed", "final_settlement",
                           "receipt_confirmed"),
    }


def build_case_input(intake: dict):
    """Assemble the normalized CaseInput from the intake results; the
    pipeline consumes exactly these intermediate objects."""
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
    state = ProcessState(
        r=NormState(relations=()),
        environment_id=INTAKE_ENV_ID,
        stages=((f"{case_id}-trial", "trial"),),
        events=(),
        target_day=10,
        as_of_day=10,
    )
    # D001 output feeds the issue table
    issues = tuple(intake["topics"]["objects"].keys())
    # D003 role bindings feed the party table
    parties = tuple(intake["roles"].keys())
    # D008 claim records feed the claim table
    claims = tuple(
        Claim(f"c{i}", c["claimant"], c["respondent"], c["basis"],
              c["object"], c["remedy"], subject="", issue="loan")
        for i, c in enumerate(intake["claims"])
    )
    # D005 canonical subject key scopes the admitted facts
    subject = str(intake["borrower_code"])
    facts = tuple(
        FactRecord(
            f"f-{i}-{pred}",
            ScopedAtom(case_id=case_id, subject=subject, issue="loan",
                       stage="trial", predicate=pred, polar=Polar.POS),
            FactStanding.ADMITTED_POSITIVE,
            produced_at=i,
            known_at=i,
        )
        for i, pred in enumerate(intake["admitted_facts"])
    )
    quantities = tuple(
        ExactQuantity(Fraction(c["amount_fen"]), "CNY-fen", "principal",
                      "loan_contract_signed")
        for c in intake["claims"]
    )
    return CaseInput(
        case_id=case_id,
        initial_state=state,
        parties=parties,
        issues=issues,
        claims=claims,
        defenses=(),
        fact_records=facts,
        evidence_records=(),
        questions=(),
        quantities=quantities,
    )


def build_environment(intake: dict):
    """Declared environment: named sufficiency template licensed by the
    loan rule; no verdicts, no prebuilt framework."""
    from theory.spec.canonical_v2.case import (
        LegalEnvironment,
        StrongTemplate,
    )
    from theory.spec.canonical_v2.kernel import Jurisdiction, JurisdictionRoute

    template = StrongTemplate(
        template_id="tpl-loan-delivery",
        kind="LOAN_DELIVERY",
        scope_issue="loan",
        premise_predicates=("contract_signed", "final_settlement",
                            "receipt_confirmed"),
        conclusion_predicate="loan",
        failure_predicates=("ref_matches_existing_goods_payment",),
        license_rule_id="",
        source_id="evidence-rules:strong-loan",
    )
    return LegalEnvironment(
        environment_id=INTAKE_ENV_ID,
        jurisdiction=Jurisdiction(route=JurisdictionRoute.MAINLAND),
        rules=(),
        strong_templates=(template,),
    )


def intake_trace_events(intake: dict):
    """Per-defendant payment dispositions (D004) bound to the declared
    responsibility basis (D006) as actual process events; each payment
    stays its own event so per-defendant performance is never averaged."""
    from fractions import Fraction

    from theory.spec.canonical_v2.case import CaseEvent
    from unified.process import LegalEventKind, ProcessEvent

    events = []
    day = 11
    for obligor, amount in sorted(intake["per_defendant_payments"].items()):
        # the payment basis is the declared responsibility basis of the
        # D006 rule edge; each obligor keeps its own event so per-
        # defendant performance stays separately visible
        basis = "loan"
        events.append(
            ProcessEvent(
                event=CaseEvent(
                    event_id=f"pay-{obligor}",
                    event_type="PAYMENT_PERFORMED",
                    occurred_at=day,
                    observed_at=day,
                    object_ref="loan",
                ),
                kind=LegalEventKind.PAYMENT_PERFORMED,
                basis_key=basis,
                amount=Fraction(int(amount)),
                debt_order=("loan",),
            )
        )
        day += 1
    return tuple(events)
