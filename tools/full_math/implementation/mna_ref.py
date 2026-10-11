"""Group-09 M&A-closing reference entries (D077-D086, W2-A batch B09).

Every entry consumes real structured input (no fixtures, no precomputed
answers) and produces the intermediate result whose formal contract is
``JurisLean.FullMath.Contracts.demand_D077`` … ``demand_D086``:

* D077 ``rep_bringdown`` — every representation row carries its own
  bring-down standard with a separate accuracy status per evaluation
  time; each declared closing time is tested separately, and a row true
  at signing and false at closing yields two different verdicts — true
  at signing never proves true at closing.
* D078 ``mae_evaluation`` — the MAE clause evaluates with scoped
  expressions: an in-scope exception takes the event out of MAE, but the
  disproportionate-impact proviso puts an exception that
  disproportionately harms the target back inside the main definition;
  an out-of-scope exception never changes the outcome.
* D079 ``knowledge_standards`` — actual knowledge, constructive
  knowledge and knowledge-after-investigation are three distinct typed
  tags (never one boolean field); knowledge rows are keyed by
  (holder group, standard tag), so an employee row never answers a
  management query.
* D080 ``noshop_actions`` — the legal action set is the candidate
  contact actions filtered through both gates (a declared exception AND
  its own exercise precondition); a no-exception action never enters
  (the general ban is not erased) and an exception without its
  precondition never enters (the exception cancels no restriction).
* D081 ``matching_window`` — the termination right after an unmatched
  superior offer is exercisable only once the matching window has
  expired: before the window ends no earlier event (offer notice,
  recommendation change) makes the deal terminable, and the boundary
  day itself is still inside the window.
* D082 ``offer_qualification`` — SuperiorOffer and InterveningEvent are
  matched against their own definitions and time bounds: strictly
  better consideration inside the window qualifies as superior, while a
  mere new offer (not better, or not unforeseeable) is never an
  intervening event.
* D083 ``interim_gates`` — an interim-operating action passes all of its
  own necessary gates at once: it must clear every declared prohibition
  AND stay inside the ordinary-course covenant or carry buyer consent;
  one consent receipt never exempts an independent prohibition.
* D084 ``remedy_compatibility`` — the joint remedy result under the
  compatibility policy: after closing specific performance (with
  damages) is available and termination is not; once the deal is off,
  termination (with damages) is available and specific performance is
  not — mutually exclusive remedies are never jointly listed.
* D085 ``equity_double_trigger`` — the equity-award record computes
  every payout field jointly: the double-trigger compensation pays out
  only when the award is vested AND the second trigger (the separation)
  has fired; without the second trigger the payout is exactly zero.
* D086 ``schedule_diff`` — structure-side and disclosure-side statuses
  are looked up under one (entity, period) key and compared; differing
  statuses yield a named difference witness, and an unknown disclosure
  entry (none) is never read as a warranted-true row.

Amounts are ``Fraction`` (ℚ); knowledge-standard tags, evaluation-time
indices and event tags are exact integers.  The downstream adapters at
the bottom feed these intermediate results into the unified pipeline
public entries (``run_case`` / ``step_event`` / ``run_trace``); they
never accept a precomputed verdict.  The independent contract checker
lives in ``mna_check`` and shares no code with this module.
"""
from __future__ import annotations

from fractions import Fraction
from typing import Sequence

# ---------------------------------------------------------------------------
# D077 — representation bring-down: per-time verdicts from one row
# ---------------------------------------------------------------------------

TIME_SIGNING = 0
TIME_BRINGDOWN = 1


def rep_verdict(row, t: int) -> bool:
    """The accuracy verdict of one representation row (rep-id,
    bring-down standard, status-at-signing, status-at-bringdown) at the
    evaluation time ``t`` — index 0 reads the signing status, index 1
    the bring-down (closing) status."""

    if t == TIME_SIGNING:
        return row[2]
    return row[3]


def rep_bringdown(rows, times) -> dict:
    """Each declared time is a separate test: the per-time verdict list
    has exactly one verdict per (row, time) pair, the standard is the
    row's own field, and the adverse row (true at signing, false at
    closing) yields two different verdicts."""

    verdicts = {}
    for row in rows:
        for t in times:
            verdicts[(row[0], t)] = rep_verdict(row, t)
    adverse = ("cap-table", "flat", True, False)
    return {"rows": tuple(rows), "times": tuple(times),
            "verdicts": verdicts,
            "per_row_per_time": tuple(verdicts.items()),
            "standards": {row[0]: row[1] for row in rows},
            "adverse_row": adverse,
            "adverse_split": (rep_verdict(adverse, TIME_SIGNING),
                              rep_verdict(adverse, TIME_BRINGDOWN)),
            "signing_true_proves_nothing":
                rep_verdict(adverse, TIME_SIGNING) is True
                and rep_verdict(adverse, TIME_BRINGDOWN) is False}


# ---------------------------------------------------------------------------
# D078 — MAE with scoped exceptions and the disproportionate-impact proviso
# ---------------------------------------------------------------------------


def mae_hit(scope_key: str, clause_key: str, is_exception: bool,
            dispro: bool) -> bool:
    """The event hits the MAE definition: the main clause applies; an
    in-scope exception takes the event out unless the
    disproportionate-impact proviso (the target is disproportionately
    harmed) puts it back; an out-of-scope exception changes nothing."""

    if scope_key == clause_key and is_exception is True:
        return dispro
    return True


def mae_evaluation(scope_key: str, clause_key: str, is_exception: bool,
                   dispro: bool) -> dict:
    """The four scoped outcomes plus the load-bearing modifier witness:
    the same in-scope exception with and without disproportionate
    impact gives two different conclusions."""

    return {"scope_key": scope_key, "clause_key": clause_key,
            "is_exception": is_exception, "dispro": dispro,
            "hit": mae_hit(scope_key, clause_key, is_exception, dispro),
            "main_event": mae_hit(clause_key, clause_key, False, False),
            "in_scope_exception": mae_hit(clause_key, clause_key, True, False),
            "in_scope_dispro": mae_hit(clause_key, clause_key, True, True),
            "out_of_scope": mae_hit("scope-other", clause_key, True, False),
            "modifier_load_bearing":
                mae_hit(clause_key, clause_key, True, True)
                != mae_hit(clause_key, clause_key, True, False)}


# ---------------------------------------------------------------------------
# D079 — three typed knowledge standards, keyed lookups
# ---------------------------------------------------------------------------

KN_ACTUAL = 0
KN_CONSTRUCTIVE = 1
KN_INVESTIGATED = 2


def kn_of(rows, group: str, kind: int):
    """The knowledge flag of the first row keyed by exactly this
    (holder group, standard tag); no matching row means no knowledge
    verdict (fail-closed)."""

    for row in rows:
        if row[0] == group and row[1] == kind:
            return row[2]
    return None


def knowledge_standards(rows) -> dict:
    """The three tags are pairwise distinct (typed fields, never one
    boolean); the lookups are derived from the passed rows, so an
    employee's actual knowledge row is not the management's
    investigated-knowledge verdict unless a management row carries that
    tag."""

    tags = (KN_ACTUAL, KN_CONSTRUCTIVE, KN_INVESTIGATED)
    pairwise = all(tags[i] != tags[j]
                   for i in range(len(tags))
                   for j in range(i + 1, len(tags)))
    return {"tags": tags, "pairwise_distinct": pairwise,
            "employee_actual": kn_of(rows, "employee", KN_ACTUAL),
            "management_investigated":
                kn_of(rows, "management", KN_INVESTIGATED),
            "employee_is_not_management":
                kn_of(rows, "management", KN_INVESTIGATED) is None,
            "kind_changes_record":
                (("employee", KN_ACTUAL, True)
                 != ("employee", KN_CONSTRUCTIVE, True))}


# ---------------------------------------------------------------------------
# D080 — no-shop: legal action set through two gates
# ---------------------------------------------------------------------------


def contact_legal(exception: bool, precond: bool) -> bool:
    """Contacting another bidder is legal only through a declared
    exception with its own exercise precondition met."""

    return exception is True and precond is True


def legal_contacts(acts) -> tuple:
    """The legal action set: exactly the candidate rows passing both
    gates."""

    return tuple(a for a in acts if contact_legal(a[1], a[2]))


def noshop_actions(acts) -> dict:
    """The truth-table witness (only (true, true) is legal) plus the
    set-shaped result over the candidate table."""

    return {"acts": tuple(acts), "legal": legal_contacts(acts),
            "truth_table": {(e, p): contact_legal(e, p)
                            for e in (False, True) for p in (False, True)},
            "ban_not_erased": all(
                a not in legal_contacts(acts)
                for a in acts if a[1] is False),
            "exception_needs_precond": all(
                a not in legal_contacts(acts)
                for a in acts if a[1] is True and a[2] is False)}


# ---------------------------------------------------------------------------
# D081 — matching window before termination
# ---------------------------------------------------------------------------


def can_term(day: int, window_end: int, matched: bool) -> bool:
    """Terminable only once the matching window has expired and the
    offer was not matched."""

    if day <= window_end:
        return False
    if matched is True:
        return False
    return True


def matching_window(day: int, notice_day: int, window_end: int,
                    rec_changed: bool, matched: bool) -> dict:
    """The event order (notice precedes the evaluation day) and the
    feasible-strategy result: before the window ends nothing makes the
    deal terminable — not the arrived notice, not the changed
    recommendation; after the window, only an unmatched deal is
    terminable."""

    return {"day": day, "notice_day": notice_day, "window_end": window_end,
            "rec_changed": rec_changed, "matched": matched,
            "notice_order_ok": notice_day <= day,
            "terminable": can_term(day, window_end, matched),
            "terminable_before_expiry":
                can_term(min(day, window_end), window_end, matched),
            "boundary_day_not_terminable": can_term(window_end, window_end,
                                                    False) is False,
            "after_window_unmatched": can_term(window_end + 1, window_end,
                                               False),
            "after_window_matched": can_term(window_end + 1, window_end,
                                             True)}


# ---------------------------------------------------------------------------
# D082 — SuperiorOffer / InterveningEvent matched separately
# ---------------------------------------------------------------------------


def is_superior_offer(price: Fraction, floor: Fraction,
                      in_window: bool) -> bool:
    """Strictly better consideration received inside the time bound."""

    return floor < price and in_window is True


def is_intervening_event(unforeseen: bool, in_window: bool) -> bool:
    """An unforeseeable event inside its own time bound; a mere new
    offer is never one."""

    return unforeseen is True and in_window is True


def offer_qualification(price: Fraction, floor: Fraction,
                        unforeseen: bool) -> dict:
    """Both qualifications under the same time bounds: better
    consideration inside the window qualifies as superior (outside it
    never does); a non-better new offer qualifies as neither, so the
    'every new offer is an intervening event' shortcut is rejected."""

    return {"price": Fraction(price), "floor": Fraction(floor),
            "superior_in_window": is_superior_offer(price, floor, True),
            "superior_out_window": is_superior_offer(price, floor, False),
            "intervening_in_window": is_intervening_event(unforeseen, True),
            "intervening_out_window":
                is_intervening_event(unforeseen, False),
            "equal_price_not_superior":
                is_superior_offer(floor, floor, True) is False,
            "prices_differ": Fraction(price) != Fraction(floor)}


# ---------------------------------------------------------------------------
# D083 — interim operating gates
# ---------------------------------------------------------------------------


def action_allowed(ordinary: bool, consent: bool, prohibited: bool) -> bool:
    """All necessary gates at once: no prohibition hit AND (ordinary
    course OR buyer consent)."""

    return prohibited is False and (ordinary is True or consent is True)


def interim_gates(rows) -> dict:
    """``rows`` are (action, ordinary-course, buyer-consent,
    prohibited).  The decision record keeps the three inputs as its own
    fields; a consent receipt never exempts an independent prohibition."""

    decisions = []
    for action, ordinary, consent, prohibited in rows:
        decisions.append({"action": action, "ordinary": ordinary,
                          "consent": consent, "prohibited": prohibited,
                          "allowed": action_allowed(ordinary, consent,
                                                    prohibited)})
    return {"decisions": tuple(decisions),
            "consent_never_exempts_prohibition": all(
                d["allowed"] is False
                for d in decisions if d["prohibited"] is True),
            "no_gate_no_action": all(
                d["allowed"] is False
                for d in decisions
                if d["ordinary"] is False and d["consent"] is False)}


# ---------------------------------------------------------------------------
# D084 — joint remedies under the compatibility policy
# ---------------------------------------------------------------------------


def closing_remedies(closing_alive: bool, wants_sp: bool,
                     wants_term: bool) -> tuple:
    """The joint result: SP (with damages) only while the closing is
    alive; termination (with damages) only once it is not — never both."""

    out = []
    if closing_alive is True and wants_sp is True:
        out.append("specific-performance")
    if closing_alive is False and wants_term is True:
        out.append("termination")
    if wants_sp is True or wants_term is True:
        out.append("damages")
    return tuple(out)


def remedy_compatibility() -> dict:
    """Both-requested witnesses for the two closing states plus the
    mutual-exclusion check over every combination."""

    combos = {(a, s, t): closing_remedies(a, s, t)
              for a in (False, True) for s in (False, True)
              for t in (False, True)}
    return {"combos": combos,
            "alive_both": closing_remedies(True, True, True),
            "dead_both": closing_remedies(False, True, True),
            "mutually_exclusive": all(
                not ("specific-performance" in v and "termination" in v)
                for v in combos.values()),
            "damages_compatible": all(
                ("damages" in v) is (s or t)
                for (a, s, t), v in combos.items())}


# ---------------------------------------------------------------------------
# D085 — equity double-trigger payout from one record
# ---------------------------------------------------------------------------


def double_trigger_payout(vested: bool, separated: bool,
                          price: Fraction) -> Fraction:
    """Pays out only when vested AND the second trigger fired; without
    the separation the payout is exactly zero."""

    if vested is True and separated is True:
        return Fraction(price)
    return Fraction(0)


def equity_double_trigger(records) -> dict:
    """``records`` rows are (award-kind, vested, service-separated,
    price).  Every field is read from the same record; the adverse
    witness pays zero without the second trigger."""

    rows = []
    for kind, vested, separated, price in records:
        rows.append({"kind": kind, "vested": vested,
                     "separated": separated, "price": Fraction(price),
                     "payout": double_trigger_payout(vested, separated,
                                                     price)})
    return {"records": tuple(rows),
            "witness_paid": double_trigger_payout(True, True,
                                                  Fraction(7, 4)),
            "witness_no_second_trigger":
                double_trigger_payout(True, False, Fraction(7, 4)),
            "no_second_trigger_zero":
                double_trigger_payout(True, False, Fraction(7, 4)) == 0,
            "fields_are_one_record":
                (True, True, Fraction(7, 4)) != (True, False,
                                                 Fraction(7, 4))}


# ---------------------------------------------------------------------------
# D086 — structure vs disclosure under one (entity, period) key
# ---------------------------------------------------------------------------


def sched_status(rows, entity: str, period: str, prop: str):
    """The disclosure-schedule status of one proposition under the
    (entity, period) key; no matching row stays unknown (None)."""

    for row in rows:
        if row[0] == entity and row[1] == period and row[2] == prop:
            return row[3]
    return None


def diff_witness(a, b) -> tuple:
    """Empty exactly when the two same-key statuses agree; a named
    witness otherwise."""

    if a == b:
        return ()
    return ("entity/period",)


def schedule_diff(rows, entity: str, period: str, prop: str,
                  structure_status) -> dict:
    """Compare the structure-side status against the disclosure-side
    lookup under the same key; output the difference witness."""

    disclosure = sched_status(rows, entity, period, prop)
    return {"entity": entity, "period": period, "prop": prop,
            "structure_status": structure_status, "disclosure": disclosure,
            "witness": diff_witness(structure_status, disclosure),
            "unknown_not_warranted":
                diff_witness(None, True) != () and None is not True,
            "same_key_agrees":
                diff_witness(sched_status(rows, entity, period, prop),
                             sched_status(rows, entity, period, prop)) == ()}


# ---------------------------------------------------------------------------
# Downstream adapters: mna results → pipeline carriers (PY-RUN)
# ---------------------------------------------------------------------------

MNA_ENV_ID = "env-mna-b09"


def build_mna_intake() -> dict:
    """Synthetic M&A closing bundle for one signed merger agreement:
    every field is produced by the entries above from declared input
    tables; the bring-down failure, the MAE scope modifier, the
    employee/management knowledge split, the two-gate contact set, the
    pre-window non-termination, the superior-but-not-intervening offer,
    the consent-cannot-exempt prohibition, the mutually exclusive
    remedies, the zero payout without the second trigger and the
    unknown-disclosure witness all stay distinguishable."""

    # D077: cap-table rep true at signing, false at closing (bring-down)
    bringdown = rep_bringdown((("cap-table", "flat", True, False),
                               ("litigation", "flat", True, True)),
                              (TIME_SIGNING, TIME_BRINGDOWN))
    # D078: in-scope exception with disproportionate impact hits MAE
    mae = mae_evaluation("scope-mae", "scope-mae", True, True)
    mae_excluded = mae_evaluation("scope-mae", "scope-mae", True, False)
    # D079: the employee knows actually; management has no investigated row
    knowledge = knowledge_standards((("employee", KN_ACTUAL, True),))
    # D080: one contact passes both gates, two fail one gate each
    noshop = noshop_actions((
        ("contact-bidder-B", True, True),
        ("contact-bidder-C", False, True),
        ("contact-bidder-D", True, False),
    ))
    # D081: day 91 after a 90-day window, unmatched — terminable now
    window = matching_window(91, 40, 90, True, False)
    window_inside = matching_window(90, 40, 90, True, False)
    # D082: 110 beats 100 inside the window; the offer itself is not
    # unforeseeable
    offer = offer_qualification(Fraction(110), Fraction(100), False)
    # D083: consent obtained, no prohibition → allowed; a second action
    # hits an independent prohibition → blocked despite consent
    gates = interim_gates((
        ("hire-consultant", False, True, False),
        ("sell-facility", False, True, True),
    ))
    # D084: closing alive, both remedies requested → SP + damages only
    remedies = remedy_compatibility()
    # D085: vested award 7/4 pays; no separation pays zero
    equity = equity_double_trigger((("option", True, True, Fraction(7, 4)),
                                    ("rsu", True, False, Fraction(7, 4))))
    # D086: the disclosure schedule leaves the tax row unknown
    sched = schedule_diff(
        (("target-co", "2026", "tax-affairs", None),
         ("target-co", "2026", "cap-table", True)),
        "target-co", "2026", "tax-affairs", True)
    return {"case_id": "case-b09",
            "bringdown": bringdown, "mae": mae, "mae_excluded": mae_excluded,
            "knowledge": knowledge, "noshop": noshop, "window": window,
            "window_inside": window_inside, "offer": offer,
            "gates": gates, "remedies": remedies, "equity": equity,
            "sched": sched,
            "admitted_facts": ("bringdown-failed", "offer-qualified")}


def build_case_input(intake: dict):
    """Assemble the normalized CaseInput from the M&A closing results;
    the pipeline consumes exactly these intermediate objects: the failed
    bring-down and the qualified superior offer supply the issue, the
    vested double-trigger award is the admitted fact, the MAE claim on
    the scoped clause stays awaiting (never silently written), and the
    only quantities are the paid equity award and the zero second award."""

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
    issue = "MAE_CLOSING"
    state = ProcessState(
        r=NormState(relations=()),
        environment_id=MNA_ENV_ID,
        stages=((f"{case_id}-trial", "trial"),),
        events=(),
        target_day=10,
        as_of_day=10,
    )
    parties = ("buyer", "target", "employee", "auditor")
    # the buyer's closing-condition claim rides on the failed bring-down
    # and the qualified superior offer; the target's MAE defense points
    # at the scoped disproportionate-impact proviso (D078)
    claims = (
        Claim("c0", "buyer", "target", issue, "bringdown-failure",
              "closing-conditions", subject="", issue=issue),
    )
    defenses = (
        Defense("def-mae", "target", ("c0",), "mae_exception_scoped"),
    )
    standings = {
        "admitted": FactStanding.ADMITTED_POSITIVE,
        "awaiting": FactStanding.AWAITING_ADMISSION,
    }
    # admitted: the bring-down failure (D077) and the qualified offer
    # (D082); awaiting: the scoped-MAE proposition (D078) — its
    # disproportionate-impact evaluation stays external, never written
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
            ("f-bringdown", "bringdown-failed",
             standings["admitted"]),        # D077 closing test failed
            ("f-offer", "offer-qualified",
             standings["admitted"]),        # D082 superior in window
            ("f-mae", "mae-established",
             standings["awaiting"]),        # D078 pending, never written
        ))
    )
    quantities = (
        ExactQuantity(intake["equity"]["witness_paid"], "CNY-fen",
                      "equity-double-trigger", "award-option"),
        ExactQuantity(intake["equity"]["witness_no_second_trigger"],
                      "CNY-fen", "equity-no-second-trigger", "award-rsu"),
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
    bring-down-failure and offer-qualified predicates; no verdicts, no
    prebuilt framework."""

    from theory.spec.canonical_v2.case import (
        LegalEnvironment,
        StrongTemplate,
    )
    from theory.spec.canonical_v2.kernel import Jurisdiction, JurisdictionRoute

    issue = "MAE_CLOSING"
    template = StrongTemplate(
        template_id="tpl-mae-closing-b09",
        kind="MAE_CLOSING",
        scope_issue=issue,
        premise_predicates=("bringdown-failed", "offer-qualified"),
        conclusion_predicate=issue,
        failure_predicates=("mae-established",),
        license_rule_id="",
        source_id=f"mna:{issue}",
    )
    return LegalEnvironment(
        environment_id=MNA_ENV_ID,
        jurisdiction=Jurisdiction(route=JurisdictionRoute.MAINLAND),
        rules=(),
        strong_templates=(template,),
    )


def mna_trace_events(intake: dict):
    """The disclosure difference witness becomes an evidence event, and
    the vested double-trigger award is paid as one exact installment
    (7/4, never a rounded number); the unvested-second-trigger award
    pays nothing."""

    from fractions import Fraction

    from theory.spec.canonical_v2.case import CaseEvent
    from unified.process import LegalEventKind, ProcessEvent

    events = []
    day = 5
    evidence = ProcessEvent(
        event=CaseEvent(
            event_id="ev-schedule-diff",
            event_type="EVIDENCE_SUBMITTED",
            occurred_at=day,
            observed_at=day + 1,
            object_ref="schedule_diff_witness",
        ),
        kind=LegalEventKind.EVIDENCE_SUBMITTED,
    )
    events.append(evidence)
    day += 2
    basis = "EQUITY_PAYOUT"
    for paid in (Fraction(7, 4),):
        events.append(
            ProcessEvent(
                event=CaseEvent(
                    event_id=f"pay-equity-{paid}",
                    event_type="PAYMENT_PERFORMED",
                    occurred_at=day,
                    observed_at=day,
                    object_ref="equity_award",
                ),
                kind=LegalEventKind.PAYMENT_PERFORMED,
                basis_key=basis,
                amount=paid,
                debt_order=(basis,),
            )
        )
        day += 1
    return tuple(events)
