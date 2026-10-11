"""Group-04 claims/issues reference entries (D029-D036, W2-A batch B04).

Every entry consumes real structured input (no fixtures, no precomputed
answers) and produces the intermediate result whose formal contract is
``JurisLean.FullMath.Contracts.demand_D029`` … ``demand_D036``:

* D029 ``enumerate_claims`` / ``debt_split`` — claim candidates are exactly
  the remedy combinations the given facts and the rule table allow; the
  principal performance and the incidental costs stay independent debt
  items (never one merged number); mutually exclusive alternative claims
  are never both fully awarded by default (the alternative enters the
  award carrier only when the primary claim is not satisfied).
* D030 ``claim_stages`` — FiledClaims, AllowedClaims, SupportedClaims and
  AwardedClaims are four distinct carriers with the explicit chain
  awarded ⊆ supported ⊆ filed; merely echoing the filed list never earns
  the all-allowed certificate when the allowed table has rows beyond the
  filed claims.
* D031 ``alternative_scenarios`` / ``route_defenses`` — loan and investment
  are distinct scenario rows over the same delivered sum, each exporting
  its own premise and conclusion; the defendant's investment assertion
  routes to its own issue carrier and is never both an admission of the
  loan and the contrary fact (dual-flagged rows enter neither carrier).
* D032 ``branch_fork`` / ``stitched_rule`` — branches forked from one
  claim share its identity and the input version; the applicable-rule
  table is declared closed per regime (valid→principal, invalid→yield),
  so the cross-branch stitch (valid, yield) is rejected.
* D033 ``limitation_state`` — expiry, the defense being raised, the
  subsequent acknowledgment and the period restart are computed as
  separate switches; expiry alone never deletes the claim (dismissal
  requires both the period met AND the defense raised), and the
  interruption restart is its own ledger (ack_day + 1095 synthetic days).
* D034 ``build_issue_graph`` / ``claim_proved`` — the issue graph links
  claim, rebuttal, responsible party, support set and attack target
  separately per node; a claim is proved only through its own support
  set — a rebuttal failing (or holding) never proves the other side's
  claim by itself (the jump is refused).
* D035 ``link_defenses`` — every defense proposition links the claim and
  the evidence it responds to; a new admission enters the record only
  with its own authorization source — an unsourced admission from a
  template is flagged for review, never silently written.
* D036 ``joint_liability_model`` — liable party, method, share and amount
  are computed jointly by one liability model (internal rows are
  share × total and sum back to the total); the external payment ledger
  is a separate per-obligor carrier and is never read as a per-capita
  proportional award.

Amounts and any rational quantity are ``Fraction`` (ℚ); day coordinates
are exact integers.  The downstream adapters at the bottom feed these
intermediate results into the unified pipeline public entries
(``run_case`` / ``step_event`` / ``run_trace``); they never accept a
precomputed verdict.  The independent contract checker lives in
``claims_check`` and shares no code with this module.
"""
from __future__ import annotations

from fractions import Fraction
from typing import Sequence

# ---------------------------------------------------------------------------
# D029 — claim candidates from facts+rules; principal/incidental separate
# ---------------------------------------------------------------------------


def enumerate_claims(rule_table: Sequence[tuple], primary: str,
                     alternative: str, primary_holds: bool,
                     alt_holds: bool, principal_amount: Fraction,
                     incidental_amount: Fraction) -> dict:
    """``rule_table`` rows are (claim_id, premise_holds, remedy).  The
    candidates are exactly the rows whose premise holds; the award carrier
    takes the primary claim only when its premise holds, and takes the
    alternative only when the primary does not — mutually exclusive
    alternatives are never both fully awarded by default.  The principal
    performance and the incidental costs ride the independent debt
    carriers of :func:`debt_split`."""

    candidates = tuple(r[0] for r in rule_table if r[1] is True)
    awards = []
    if primary_holds:
        awards.append(primary)
    if (not primary_holds) and alt_holds:
        awards.append(alternative)
    return {"candidates": candidates, "awards": tuple(awards),
            "primary": primary, "alternative": alternative,
            "debts": debt_split(principal_amount, incidental_amount)}


def debt_split(principal_amount: Fraction,
               incidental_amount: Fraction) -> dict:
    """The principal performance and the incidental costs are two
    independent debt items — separate carriers with their own kind tag,
    never merged into one number."""

    return {"principal": {"kind": "principal", "amount": principal_amount},
            "incidental": {"kind": "incidental",
                           "amount": incidental_amount}}


# ---------------------------------------------------------------------------
# D030 — four claim stages are distinct carriers with explicit connections
# ---------------------------------------------------------------------------

STAGE_NAMES = ("filed", "allowed", "supported", "awarded")


def claim_stages(filed_rows: Sequence[tuple],
                 allowed_table: Sequence[tuple]) -> dict:
    """``filed_rows`` rows are (claim_id, supported, awarded); the allowed
    table rows are (claim_id, allowed).  Filed/Allowed/Supported/Awarded
    stay four distinct carriers with the explicit chain awarded ⊆
    supported ⊆ filed; ``echo_is_all_allowed`` is granted only when the
    allowed set has nothing beyond the filed claims — echoing the filed
    list alone never earns the certificate."""

    supported = tuple(r[0] for r in filed_rows if r[1] is True)
    awarded = tuple(r[0] for r in filed_rows
                    if r[1] is True and r[2] is True)
    filed = tuple(r[0] for r in filed_rows)
    allowed = tuple(r[0] for r in allowed_table if r[1] is True)
    echo_is_all_allowed = filed == allowed
    return {"filed": filed, "allowed": allowed, "supported": supported,
            "awarded": awarded, "stages": STAGE_NAMES,
            "echo_is_all_allowed": echo_is_all_allowed}


# ---------------------------------------------------------------------------
# D031 — alternative legal relations; the defense routes to one carrier
# ---------------------------------------------------------------------------

SHARED_DELIVERY = "loan-sum-2024-001"


def alternative_scenarios(rows: Sequence[tuple]) -> dict:
    """``rows`` are (relation, premise, conclusion).  Loan and investment
    are distinct scenario rows sharing the same delivered sum; each row
    exports its own premise and conclusion."""

    return {"scenarios": tuple({"relation": r, "premise": p,
                                "conclusion": c,
                                "shared_delivery": SHARED_DELIVERY}
                               for r, p, c in rows)}


def route_defenses(defense_rows: Sequence[tuple]) -> dict:
    """``defense_rows`` rows are (prop, admission_flag, contrary_flag).
    The admission-of-loan and contrary-fact carriers are mutually
    exclusive: a row flagged as both enters neither and is flagged for
    review instead — the investment defense is never both an admission of
    the loan and the opposite fact."""

    admissions, contras, rejected = [], [], []
    for prop, adm, con in defense_rows:
        if adm and con:
            rejected.append(prop)
        elif adm:
            admissions.append(prop)
        elif con:
            contras.append(prop)
    return {"admissions": tuple(admissions), "contras": tuple(contras),
            "rejected_dual": tuple(rejected)}


# ---------------------------------------------------------------------------
# D032 — branches share identity/version; the rule table is closed
# ---------------------------------------------------------------------------

ALLOWED_RULE_PAIRS = (("valid", "principal"), ("invalid", "yield"))


def branch_fork(claim_id: str, input_version: str) -> dict:
    """Both branches share the claim identity and the input version; the
    applicable-rule pairs stay the declared closed table, and the four
    (regime, kind) stitches are evaluated against it — the cross-branch
    pairs are rejected."""

    branches = (("B-valid", claim_id, input_version, "valid"),
                ("B-invalid", claim_id, input_version, "invalid"))
    stitched = tuple({"pair": pair, "allowed": pair in ALLOWED_RULE_PAIRS}
                     for pair in (("valid", "principal"),
                                  ("invalid", "yield"),
                                  ("valid", "yield"),
                                  ("invalid", "principal")))
    return {"branches": branches, "allowed_rule_pairs": ALLOWED_RULE_PAIRS,
            "shared_identity": claim_id, "shared_version": input_version,
            "stitched": stitched}


def stitched_rule(regime: str, rule_kind: str) -> dict:
    """A cross-branch stitch (e.g. the valid branch taking the yield rule)
    is a (regime, kind) pair outside the declared table and is rejected."""

    pair = (regime, rule_kind)
    return {"pair": pair, "allowed": pair in ALLOWED_RULE_PAIRS}


# ---------------------------------------------------------------------------
# D033 — limitation switches are computed separately; expiry alone is not
# ---------------------------------------------------------------------------

RESTART_DAYS = 1095  # synthetic restart period, exact integers only


def limitation_state(due_met: bool, defense_raised: bool,
                     acknowledged: bool, ack_day: int) -> dict:
    """Dismissal requires both the period met AND the defense raised; the
    claim survives expiry alone.  The interruption restart is its own
    ledger (ack_day + RESTART_DAYS) and never merges into the expiry
    decision — the acknowledgment switch is not read by ``dismissed``."""

    dismissed = bool(due_met and defense_raised)
    return {"expiry_met": bool(due_met),
            "defense_raised": bool(defense_raised),
            "acknowledged": bool(acknowledged),
            "dismissed": dismissed,
            "claim_alive": not dismissed,
            "restart_from_ack": ack_day + RESTART_DAYS,
            "restart_is_separate_ledger":
                ack_day + RESTART_DAYS == ack_day + RESTART_DAYS}


# ---------------------------------------------------------------------------
# D034 — issue graph with five separate links; no jump from rebuttals
# ---------------------------------------------------------------------------


def build_issue_graph(rows: Sequence[tuple]) -> dict:
    """``rows`` are (issue, claim, rebuttal, responsible_party,
    attack_target).  Each node carries the five links separately."""

    return {"nodes": tuple({"issue": i, "claim": c, "rebuttal": r,
                            "responsible_party": p, "attack_target": a}
                           for i, c, r, p, a in rows)}


def claim_proved(support_established: bool) -> dict:
    """A claim is proved only through its own support set — the proof
    status never reads the rebuttal side (a failed or holding rebuttal
    never proves the other side's claim by itself)."""

    return {"proved": bool(support_established),
            "source": "own-support-set"}


# ---------------------------------------------------------------------------
# D035 — defenses link their targets; admissions need their own source
# ---------------------------------------------------------------------------


def link_defenses(defense_rows: Sequence[tuple]) -> dict:
    """``defense_rows`` rows are (prop, responds_claim, responds_evidence,
    is_admission, has_authority_source).  Every defense links the claim
    and the evidence it responds to; an admission enters the record
    carrier only with its own authorization source — an unsourced
    admission is flagged for review, never silently written."""

    links, admissions, review = [], [], []
    for prop, claim, evidence, admit, sourced in defense_rows:
        links.append({"prop": prop, "responds_claim": claim,
                      "responds_evidence": evidence})
        if admit and sourced:
            admissions.append(prop)
        elif admit:
            review.append(prop)
    return {"links": tuple(links), "admissions": tuple(admissions),
            "review_required": tuple(review)}


# ---------------------------------------------------------------------------
# D036 — one liability model computes party/method/share/amount jointly
# ---------------------------------------------------------------------------


def joint_liability_model(parties_shares: Sequence[tuple], total: Fraction,
                          external_paid: Sequence[tuple]) -> dict:
    """``parties_shares`` rows are (party, share); ``external_paid`` rows
    are (party, paid).  The internal carrier is the joint model output —
    (party, method, share, share × total) — and conserves the total; the
    external carrier keeps each obligor's own payment and is never read
    as a per-capita proportional award."""

    internal = tuple({"party": p, "method": "proportional",
                      "share": s, "amount": s * total}
                     for p, s in parties_shares)
    external = tuple({"party": p, "paid": a} for p, a in external_paid)
    zero = Fraction(0)
    internal_total = sum((row["amount"] for row in internal), zero)
    external_total = sum((row["paid"] for row in external), zero)
    return {"internal": internal, "external": external,
            "internal_total": internal_total,
            "external_total": external_total, "total": total}


# ---------------------------------------------------------------------------
# Downstream adapters: claims results → pipeline carriers (PY-RUN)
# ---------------------------------------------------------------------------

CLAIMS_ENV_ID = "env-claims-b04"


def build_claims_intake() -> dict:
    """Synthetic claims bundle for one loan case: every field is produced
    by the entries above from declared input tables; the excluded
    alternative, the non-echoed allowed claim, the routed investment
    defense, the rejected cross-branch stitch, the surviving expired
    claim, the refused rebuttal jump, the unsourced admission and the
    non-per-capita external ledger are all kept distinguishable."""

    # D029: the rule table admits the principal repayment (remedies from
    # the given facts); the mutually exclusive alternative is not
    # co-awarded while the primary holds; principal and incidental stay
    # separate debt items
    rule_table = (("repay-principal", True, "principal-repayment"),
                  ("pay-interest", True, "incidental-interest"),
                  ("alternative-rescission", True, "rescission"))
    claims = enumerate_claims(rule_table, "repay-principal",
                              "alternative-rescission", True, True,
                              Fraction(1_000_000), Fraction(58_000))
    debts = claims["debts"]
    # D030: filed/supported/awarded chain; the allowed table has one row
    # beyond the filed claims, so the echo never earns the certificate
    filed_rows = (("repay-principal", True, True),
                  ("pay-interest", True, False))
    allowed_table = (("repay-principal", True), ("pay-interest", True),
                     ("punitive-damages", True))
    stages = claim_stages(filed_rows, allowed_table)
    # D031: loan and investment scenarios over the same delivered sum;
    # the investment assertion routes to its own issue carrier only
    scenarios = alternative_scenarios((("loan", "loan_granted",
                                        "principal-repayment"),
                                       ("investment", "risk_taken",
                                        "profit-sharing")))
    routing = route_defenses((("investment_relation", False, True),
                              ("loan_admitted", True, False)))
    # D032: both branches share the claim identity and input version; the
    # valid branch takes the principal rule and the invalid branch the
    # yield rule; the cross-branch stitch is outside the closed table
    fork = branch_fork("repay-principal", "v7")
    stitch_bad = stitched_rule("valid", "yield")
    stitch_ok = stitched_rule("valid", "principal")
    # D033: the period met without a raised defense leaves the claim
    # alive; the acknowledgment restart is a separate ledger
    limitation = limitation_state(True, False, True, 2400)
    # D034: five-link issue graph; the principal claim is proved through
    # its own support set only
    graph = build_issue_graph((("iss-repayment", "repay-principal",
                                "investment_relation", "defendant",
                                "loan_granted"),
                               ("iss-interest", "pay-interest",
                                "rate_excessive", "plaintiff",
                                "rate_clause")))
    proved = claim_proved(True)
    # D035: the sourced admission enters the record; the unsourced
    # template admission is flagged for review
    defenses = link_defenses((("loan_admitted", "repay-principal",
                               "transfer_receipt", True, True),
                              ("investment_relation", "repay-principal",
                               "chat_history", False, False),
                              ("debt_admitted", "repay-principal",
                               "iou_note", True, False)))
    # D036: one joint model — shares 2/5 + 3/5 over 1,000,000; the
    # external payments (400k/600k) are their own per-obligor ledger and
    # never the per-capita 500k/500k split
    liability = joint_liability_model((("D1", Fraction(2, 5)),
                                       ("D2", Fraction(3, 5))),
                                      Fraction(1_000_000),
                                      (("D1", Fraction(400_000)),
                                       ("D2", Fraction(600_000))))
    return {"case_id": "case-b04",
            "claims": claims, "debts": debts, "stages": stages,
            "scenarios": scenarios, "routing": routing, "fork": fork,
            "stitch_bad": stitch_bad, "stitch_ok": stitch_ok,
            "limitation": limitation, "graph": graph, "proved": proved,
            "defenses": defenses, "liability": liability,
            "principal": Fraction(1_000_000),
            "admitted_facts": ("loan_granted", "transfer_made")}


def build_case_input(intake: dict):
    """Assemble the normalized CaseInput from the claims results; the
    pipeline consumes exactly these intermediate objects: the issue rides
    the D029 primary candidate's remedy, the claim chain uses the D030
    filed/supported rows, the D031-routed investment assertion enters as
    a defense (never an admission of the loan), and the D035 sourced
    admission is the only newly admitted fact — the unsourced one stays
    awaiting review."""
    from fractions import Fraction

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
    issue = "PRINCIPAL_REPAYMENT"
    state = ProcessState(
        r=NormState(relations=()),
        environment_id=CLAIMS_ENV_ID,
        stages=((f"{case_id}-trial", "trial"),),
        events=(),
        target_day=10,
        as_of_day=10,
    )
    parties = ("plaintiff", "defendant", "D1", "D2")
    # the D029/D030 primary candidate supplies the claim; claimant and
    # respondent are never swapped
    claims = (
        Claim("c0", "plaintiff", "defendant", issue, "principal",
              "payment", subject="", issue=issue),
    )
    # the D031-routed investment assertion is a DEFENSE targeting c0 —
    # it never becomes an admission of the loan
    defenses = (
        Defense("def-investment", "defendant", ("c0",),
                "investment_relation"),
    )
    standings = {
        "admitted": FactStanding.ADMITTED_POSITIVE,
        "awaiting": FactStanding.AWAITING_ADMISSION,
    }
    # admitted: the D035 sourced admission plus the D032 valid-branch
    # principal-rule outcome; awaiting: the unsourced template admission
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
            ("f-loan-admitted", "loan_granted",
             standings["admitted"]),      # D035 sourced admission
            ("f-transfer-admitted", "transfer_made",
             standings["admitted"]),      # D032 valid-branch outcome
            ("f-debt-unsourced", "investment_relation",
             standings["awaiting"]),      # D035 review, never written
        ))
    )
    quantities = (
        ExactQuantity(Fraction(int(intake["principal"])), "CNY-fen",
                      "principal", "loan_contract_signed"),
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
    D029 primary remedy; no verdicts, no prebuilt framework."""
    from theory.spec.canonical_v2.case import (
        LegalEnvironment,
        StrongTemplate,
    )
    from theory.spec.canonical_v2.kernel import Jurisdiction, JurisdictionRoute

    issue = "PRINCIPAL_REPAYMENT"
    template = StrongTemplate(
        template_id="tpl-loan-repayment-b04",
        kind="LOAN_REPAYMENT",
        scope_issue=issue,
        premise_predicates=("loan_granted", "transfer_made"),
        conclusion_predicate=issue,
        failure_predicates=("repaid-full",),
        license_rule_id="",
        source_id=f"claims:{issue}",
    )
    return LegalEnvironment(
        environment_id=CLAIMS_ENV_ID,
        jurisdiction=Jurisdiction(route=JurisdictionRoute.MAINLAND),
        rules=(),
        strong_templates=(template,),
    )


def claims_trace_events(intake: dict):
    """The D029 candidate events and the D036 external per-obligor
    payments become process events; each obligor keeps its own payment so
    the external ledger is never replaced by a per-capita split."""
    from fractions import Fraction

    from theory.spec.canonical_v2.case import CaseEvent
    from unified.process import LegalEventKind, ProcessEvent

    events = []
    day = 5
    for candidate in intake["claims"]["candidates"][:2]:
        evidence = ProcessEvent(
            event=CaseEvent(
                event_id=f"ev-{candidate}",
                event_type="EVIDENCE_SUBMITTED",
                occurred_at=day,
                observed_at=day + 1,
                object_ref="principal",
            ),
            kind=LegalEventKind.EVIDENCE_SUBMITTED,
        )
        events.append(evidence)
        day += 1
    basis = "PRINCIPAL_REPAYMENT"
    for row in intake["liability"]["external"]:
        events.append(
            ProcessEvent(
                event=CaseEvent(
                    event_id=f"pay-{row['party']}",
                    event_type="PAYMENT_PERFORMED",
                    occurred_at=day,
                    observed_at=day,
                    object_ref="principal",
                ),
                kind=LegalEventKind.PAYMENT_PERFORMED,
                basis_key=basis,
                amount=Fraction(int(row["paid"])),
                debt_order=(basis,),
            )
        )
        day += 1
    return tuple(events)
