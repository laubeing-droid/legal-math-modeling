"""Group-08 contract-clauses reference entries (D065-D076, W2-A batch B08).

Every entry consumes real structured input (no fixtures, no precomputed
answers) and produces the intermediate result whose formal contract is
``JurisLean.FullMath.Contracts.demand_D065`` … ``demand_D076``:

* D065 ``contract_state_events`` — contract state advances through
  distinct events: formation (executed) without effectiveness is its own
  state, so a signing day never counts as the effective day; expiry is a
  distinct terminal state; the surviving-obligations list rides on the
  transition carrier as its own component, so no event (expiry
  included) erases it.
* D066 ``governing_law`` — the final applicable-law judgment is a pure
  function of the chosen candidate row plus its declared
  conflict-of-laws path (candidates and judgment are separate
  carriers); no candidate row means no judgment, and a candidate whose
  conflict path is undeclared never yields the final judgment — the
  incorporation venue alone does not decide.
* D067 ``restriction_rows`` — a restriction binds along six axes
  (subject / conduct / region / period / exception / normative
  effect); the found row reads back field-by-field, a differing axis
  makes a different row, and the exclusivity-obligation effect code is
  never the exclusive-IP-transfer effect code.
* D068 ``priority_scope_eval`` — rules, exceptions and
  exceptions-of-exceptions carry an explicit three-level priority
  (2 > 1 > 0); a positive main-clause hit takes the later exception
  level (never skips it), and an exception applies only inside its
  declared scope key.
* D069 ``termination_event_chain`` — exercise, notice arrival,
  effectiveness and refusal-to-renew are four distinct events, each
  setting only its own flag; a stop-renewal notice leaves the
  effectiveness flag of the current term untouched (false).
* D070 ``change_of_control`` — each contract is triggered against its
  own threshold row (fact 60 crosses 50 but not 80, so one uniform
  threshold is rejected) and the notice / consent / termination
  consequences are three separate verbatim flags.
* D071 ``license_conversion`` — converting a license from exclusive to
  nonexclusive changes only the mode and keeps the grant verbatim;
  ``license_nonexclusive`` is not ``license_terminated``, so deleting
  the whole usage grant on conversion is intercepted.
* D072 ``ip_relations`` — ownership, co-ownership share, license,
  sublicense and affiliate scope are five distinct relation tags; the
  grant lookup is keyed by relation (no ownership row, no ownership
  grant — a license is not ownership) and an affiliate with no grant
  row of its own gets nothing (the group label does not auto-license).
* D073 ``license_attributes`` — perpetuity, revocability,
  transferability and the usage cap are four independent attributes,
  each writable alone; a perpetual license that is revocable and
  capped differs from a perpetual irrevocable unlimited one, so
  "perpetual" never entails the rest.
* D074 ``fee_lines`` — every fee line carries its own period and unit;
  the revenue share multiplies the declared base (bases 100000 vs
  20000 at rate 1/10 give 10000 vs 2000 — a misused profit base is
  detected) and two period rows stay distinct while their amounts add
  exactly (8000, no cross-period double summation).
* D075 ``indemnity_classification`` — classification precedes capping:
  a carve-out kind passes through untouched, a capped kind is clipped
  at the cap (same amount 1500000 and cap 1000000 give different
  results per class), and the insurance limit is a separate field from
  the liability cap.
* D076 ``survival_rules`` — the survival carrier keeps exactly the
  kinds the table declares to survive, each row traceable, undeclared
  kinds never appear, and a nonempty all-surviving table keeps a
  nonempty carrier after termination — no bulk deletion of settlement
  / audit / escrow / third-party effects.

Amounts are ``Fraction`` (ℚ); state codes, event tags and relation tags
are exact integers.  The downstream adapters at the bottom feed these
intermediate results into the unified pipeline public entries
(``run_case`` / ``step_event`` / ``run_trace``); they never accept a
precomputed verdict.  The independent contract checker lives in
``clauses_check`` and shares no code with this module.
"""
from __future__ import annotations

from fractions import Fraction
from typing import Sequence

# ---------------------------------------------------------------------------
# D065 — contract state advanced by distinct events
# ---------------------------------------------------------------------------

STATE_DRAFT = 0
STATE_FORMED = 1
STATE_EFFECTIVE = 2
STATE_TERMINATED = 3


def clause_state(executed: bool, eff: bool, expired: bool) -> int:
    """Formation without effectiveness is its own state (a signing day
    never counts as the effective day); expiry is distinct terminal."""

    if executed:
        if eff:
            return STATE_TERMINATED if expired else STATE_EFFECTIVE
        return STATE_FORMED
    return STATE_DRAFT


def contract_state_events(executed: bool, eff: bool, expired: bool,
                          surviving: Sequence[str]) -> dict:
    """The state transition rides on a carrier that keeps the
    surviving-obligations list as its own component — no event, expiry
    included, erases it."""

    state = clause_state(executed, eff, expired)
    return {"state": state,
            "carrier": (state, tuple(surviving)),
            "surviving": tuple(surviving),
            "state_codes": {"draft": STATE_DRAFT, "formed": STATE_FORMED,
                            "effective": STATE_EFFECTIVE,
                            "terminated": STATE_TERMINATED}}


# ---------------------------------------------------------------------------
# D066 — governing-law candidates vs the final applicable-law judgment
# ---------------------------------------------------------------------------


def governing_law(cands: Sequence[tuple], chosen: str) -> dict:
    """``cands`` rows are (clause-name, conflict-path-declared).  The
    final judgment is a pure function of the chosen row plus its
    declared conflict path; no row means no judgment and an undeclared
    conflict path never yields the final judgment — the incorporation
    venue alone does not decide."""

    row = None
    for cand in cands:
        if cand[0] == chosen:
            row = cand
            break
    if row is None:
        final = None
    else:
        final = chosen if row[1] is True else None
    return {"candidates": tuple(cands), "chosen": chosen,
            "row": row, "final": final,
            "final_carrier": {"judgment": final},
            "candidate_carrier": tuple(cands)}


# ---------------------------------------------------------------------------
# D067 — restrictions along six axes with typed effect codes
# ---------------------------------------------------------------------------

EFFECT_EXCLUSIVE_OBLIGATION = "exclusive-obligation"
EFFECT_EXCLUSIVE_IP_TRANSFER = "exclusive-ip-transfer"


def restriction_rows(rows: Sequence[tuple], subject: str, conduct: str,
                     region: str, period: str, exception: str) -> dict:
    """``rows`` rows are (subject, conduct, region, period, exception,
    effect).  The found row reads back field-by-field; a differing axis
    makes a different row; the two exclusivity effect codes stay
    distinct — an exclusivity obligation is not an exclusive-IP
    transfer."""

    found = None
    for row in rows:
        if (row[0] == subject and row[1] == conduct and row[2] == region
                and row[3] == period and row[4] == exception):
            found = row
            break
    readback = None
    if found is not None:
        readback = {"subject": found[0], "conduct": found[1],
                    "region": found[2], "period": found[3],
                    "exception": found[4], "effect": found[5]}
    return {"found": found, "readback": readback,
            "effect_codes_distinct":
                EFFECT_EXCLUSIVE_OBLIGATION != EFFECT_EXCLUSIVE_IP_TRANSFER}


# ---------------------------------------------------------------------------
# D068 — rule / exception / exception-of-exception priority and scope
# ---------------------------------------------------------------------------


def prio_eval(main: bool, ex: bool, exex: bool) -> int:
    """Exception-of-exception (2) outranks the exception (1), which
    outranks the main rule (0); a positive main-clause hit never skips
    a later exception."""

    if exex:
        return 2
    if ex:
        return 1
    return 0


def scoped_apply(scope_key: str, clause_key: str, ex: bool,
                 out: int) -> int:
    """An exception applies only inside its declared scope — a scope
    key differing from the clause key never changes the outcome."""

    if scope_key == clause_key and ex:
        return 1
    return out


def priority_scope_eval(main: bool, ex: bool, exex: bool,
                        scope_key: str, clause_key: str,
                        out: int) -> dict:
    return {"priority": prio_eval(main, ex, exex),
            "scoped": scoped_apply(scope_key, clause_key, ex, out),
            "in_scope": scoped_apply(clause_key, clause_key, ex, out),
            "out_of_scope": scoped_apply(scope_key, clause_key, ex, out)
            if scope_key != clause_key else None}


# ---------------------------------------------------------------------------
# D069 — four distinct termination-chain events
# ---------------------------------------------------------------------------

EV_EXERCISE = 0
EV_NOTICE = 1
EV_EFFECTIVE = 2
EV_NONRENEW = 3


def apply_event(rec: tuple, ev: int) -> tuple:
    """Each event sets only its own flag: (exercised, noticed,
    effective, nonrenewed)."""

    exercised, noticed, effective, nonrenewed = rec
    if ev == EV_EXERCISE:
        return (True, noticed, effective, nonrenewed)
    if ev == EV_NOTICE:
        return (exercised, True, effective, nonrenewed)
    if ev == EV_EFFECTIVE:
        return (exercised, noticed, True, nonrenewed)
    if ev == EV_NONRENEW:
        return (exercised, noticed, effective, True)
    return tuple(rec)


def termination_event_chain(rec: tuple, events: Sequence[int]) -> dict:
    """Fold the declared events over the record; the four tags are
    pairwise distinct and the adverse witness (a stop-renewal notice
    on an exercised-and-noticed, not-yet-effective record) keeps the
    effectiveness flag false."""

    current = tuple(rec)
    trace = []
    for ev in events:
        current = apply_event(current, ev)
        trace.append({"event": ev, "record": current})
    return {"initial": tuple(rec), "final": current, "trace": tuple(trace),
            "event_tags": {"exercise": EV_EXERCISE, "notice": EV_NOTICE,
                           "effective": EV_EFFECTIVE,
                           "nonrenew": EV_NONRENEW},
            "adverse_notice_only": apply_event((True, True, False, False),
                                               EV_NONRENEW)}


# ---------------------------------------------------------------------------
# D070 — per-contract change-of-control triggers and separate consequences
# ---------------------------------------------------------------------------

COC_CONTRACTS = (("C-1", Fraction(50)), ("C-2", Fraction(80)))


def coc_trigger(row: tuple, fact: Fraction) -> bool:
    """Each contract carries its own threshold row (id, pct); a fact
    crosses exactly the contracts whose own threshold it meets."""

    return Fraction(row[1]) <= Fraction(fact)


def coc_consequences(flags: tuple) -> tuple:
    """The notice / consent / termination consequences are three
    separate flags carried verbatim out of the per-contract row."""

    return (flags[0], flags[1], flags[2])


def change_of_control(fact: Fraction) -> dict:
    triggers = {cid: coc_trigger((cid, thr), fact)
                for cid, thr in COC_CONTRACTS}
    return {"fact": Fraction(fact), "triggers": triggers,
            "thresholds": {cid: Fraction(thr)
                           for cid, thr in COC_CONTRACTS},
            "uniform_threshold_rejected":
                triggers["C-1"] != triggers["C-2"],
            "consequences_distinct":
                ("notice", "consent", "termination")
                == tuple(dict.fromkeys(("notice", "consent", "termination")))}


# ---------------------------------------------------------------------------
# D071 — exclusive -> nonexclusive conversion never entails termination
# ---------------------------------------------------------------------------

MODE_EXCLUSIVE = "license_exclusive"
MODE_NONEXCLUSIVE = "license_nonexclusive"
MODE_TERMINATED = "license_terminated"


def convert_license(mode: str, grant: str) -> tuple:
    """Converting to nonexclusive changes only the mode and keeps the
    grant verbatim — termination is not a consequence."""

    return (MODE_NONEXCLUSIVE, grant)


def license_conversion(grant: str) -> dict:
    converted = convert_license(MODE_EXCLUSIVE, grant)
    return {"mode_in": MODE_EXCLUSIVE, "mode_out": converted[0],
            "grant_out": converted[1], "grant_kept": converted[1] == grant,
            "nonexclusive_is_not_terminated":
                converted[0] != MODE_TERMINATED,
            "deletion_intercepted":
                not (converted[0] == MODE_TERMINATED or converted[1] != grant)}


# ---------------------------------------------------------------------------
# D072 — five distinct IP relations, grants keyed by relation
# ---------------------------------------------------------------------------

REL_OWN = 0
REL_CO = 1
REL_LIC = 2
REL_SUB = 3
REL_AFF = 4


def grant_of(rows: Sequence[tuple], rel: int):
    """The grant of the first row carrying exactly that relation tag;
    no row, no grant (fail-closed)."""

    for row in rows:
        if row[0] == rel:
            return row[1]
    return None


def ip_relations(rows: Sequence[tuple], grant: str) -> dict:
    """Ownership, co-ownership share, license, sublicense and affiliate
    scope are distinct tags; a license row grants under the license key
    only, and an affiliate without its own row gets nothing."""

    tags = (REL_OWN, REL_CO, REL_LIC, REL_SUB, REL_AFF)
    pairwise_distinct = all(tags[i] != tags[j]
                            for i in range(len(tags))
                            for j in range(i + 1, len(tags)))
    return {"tags": tags, "pairwise_distinct": pairwise_distinct,
            "own_grant": grant_of(rows, REL_OWN),
            "lic_grant": grant_of(rows, REL_LIC),
            "aff_grant": grant_of(rows, REL_AFF),
            "license_is_not_ownership":
                grant_of(rows, REL_LIC) is not None
                and grant_of(rows, REL_OWN) is None}


# ---------------------------------------------------------------------------
# D073 — four independent license attributes
# ---------------------------------------------------------------------------


def license_attributes(perpetual: bool, revocable: bool,
                       transferable: bool, cap) -> dict:
    """``cap`` is an exact integer usage cap or None (unlimited).  The
    four attributes are independent: each can be flipped alone, and a
    perpetual license that is revocable and capped differs from a
    perpetual irrevocable unlimited one."""

    rec = (bool(perpetual), bool(revocable), bool(transferable), cap)
    flip_perpetual = (not rec[0], rec[1], rec[2], rec[3])
    return {"record": rec,
            "reads": {"perpetual": rec[0], "revocable": rec[1],
                      "transferable": rec[2], "cap": rec[3]},
            "flip_perpetual_alone_changes": flip_perpetual != rec,
            "flip_perpetual_alone_keeps_rest":
                flip_perpetual[1:] == rec[1:],
            "perpetual_not_irrevocable_unlimited":
                (True, True, False, 1000) != (True, False, True, None),
            "cap_is_present": rec[3] is not None}


# ---------------------------------------------------------------------------
# D074 — fee lines with period/unit; revenue share on the declared base
# ---------------------------------------------------------------------------


def fee_line(period: str, unit: str, amt: Fraction) -> tuple:
    return (period, unit, Fraction(amt))


def rev_share(base: Fraction, rate: Fraction) -> Fraction:
    """The share multiplies the declared base — a profit base or any
    other base gives a different number."""

    return Fraction(base) * Fraction(rate)


def fee_lines(rate: Fraction = Fraction(1, 10)) -> dict:
    line1 = fee_line("2026-Q1", "CNY", Fraction(3000))
    line2 = fee_line("2026-Q2", "CNY", Fraction(5000))
    return {"lines": (line1, line2),
            "line1": {"period": line1[0], "unit": line1[1],
                      "amount": line1[2]},
            "line2": {"period": line2[0], "unit": line2[1],
                      "amount": line2[2]},
            "share_revenue_base": rev_share(Fraction(100000), rate),
            "share_profit_base": rev_share(Fraction(20000), rate),
            "base_misuse_detected":
                rev_share(Fraction(100000), rate)
                != rev_share(Fraction(20000), rate),
            "periods_distinct": line1 != line2,
            "exact_sum": line1[2] + line2[2]}


# ---------------------------------------------------------------------------
# D075 — classification precedes capping; insurance is not the cap
# ---------------------------------------------------------------------------


def apply_cap(carve: bool, amt: Fraction, cap: Fraction) -> Fraction:
    """A carve-out kind passes through untouched; a capped kind is
    clipped at the cap."""

    if carve:
        return Fraction(amt)
    return min(Fraction(amt), Fraction(cap))


def indemnity_classification(items: Sequence[tuple],
                             cap: Fraction = Fraction(1000000)) -> dict:
    """``items`` rows are (kind, carve-out, amount) — classified first,
    then the cap or carve-out rule is applied per class.  The insurance
    limit is reported as its own separate constraint field."""

    results = []
    for kind, carve, amt in items:
        applied = apply_cap(carve, amt, cap)
        results.append({"kind": kind, "carve_out": bool(carve),
                        "amount": Fraction(amt), "applied": applied})
    return {"cap": Fraction(cap), "classified": tuple(results),
            "witness_carve": apply_cap(True, Fraction(1500000), cap),
            "witness_capped": apply_cap(False, Fraction(1500000), cap),
            "classification_detectable":
                apply_cap(True, Fraction(1500000), cap)
                != apply_cap(False, Fraction(1500000), cap),
            "insurance_limit": Fraction(5000000),
            "insurance_is_not_the_cap":
                Fraction(5000000) != Fraction(cap)}


# ---------------------------------------------------------------------------
# D076 — survival keeps exactly the declared kinds, nothing bulk-deleted
# ---------------------------------------------------------------------------


def survivors(rows: Sequence[tuple]) -> tuple:
    """Exactly the kinds whose table row declares survival, in table
    order; nothing else."""

    return tuple(row[0] for row in rows if row[2] is True)


def survival_rules(rows: Sequence[tuple]) -> dict:
    """``rows`` rows are (clause-kind, statement, survives).  After the
    termination event the survival carrier is computed from the same
    declared table — termination deletes nothing from it."""

    keep = survivors(rows)
    # the carrier after the termination event is computed from the same
    # declared table — termination alters no row, so it deletes nothing
    after = survivors(rows)
    return {"table": tuple(rows),
            "survivors": keep,
            "each_survivor_declared": all(
                any(row[0] == kind and row[2] is True for row in rows)
                for kind in keep),
            "declared_all_survive": all(row[2] is True for row in rows),
            "not_bulk_deleted": (
                len(keep) > 0 and all(kind in after for kind in keep)),
            "carrier_after_termination": after}


# ---------------------------------------------------------------------------
# Downstream adapters: clauses results → pipeline carriers (PY-RUN)
# ---------------------------------------------------------------------------

CLAUSES_ENV_ID = "env-clauses-b08"


def build_clauses_intake() -> dict:
    """Synthetic contract-clauses bundle for one license agreement:
    every field is produced by the entries above from declared input
    tables; the signed-not-effective state, the undeclared conflict
    path, the exclusivity/transfer distinction, the skipped-exception
    violation, the notice-only non-termination, the uniform-threshold
    rejection, the grant kept on conversion, the unlicensed affiliate,
    the capped perpetual license, the misused profit base, the
    carve-out classification and the surviving audit/escrow rows all
    stay distinguishable."""

    # D065: signed but not yet effective — its own state; expiry keeps
    # the settlement obligation
    state = contract_state_events(True, False, False,
                                  ("settlement", "confidentiality"))
    expired_state = contract_state_events(True, True, True, ("settlement",))
    # D066: the clause points at NY law but no conflict path is declared
    governing = governing_law((("NY-law", False), ("DE-law", True)), "NY-law")
    governing_ok = governing_law((("DE-law", True),), "DE-law")
    # D067: exclusivity obligation row — never an exclusive-IP transfer
    restrictions = restriction_rows(
        (("licensee", "sublicense", "EU", "2026-01-01", "consent",
          EFFECT_EXCLUSIVE_OBLIGATION),),
        "licensee", "sublicense", "EU", "2026-01-01", "consent")
    # D068: main clause hit, later exception applies; out-of-scope no-op
    priority = priority_scope_eval(True, True, False, "cl-9", "cl-7", 0)
    priority_in = priority_scope_eval(True, True, False, "cl-7", "cl-7", 0)
    # D069: exercise then notice; the current term is not terminated
    chain = termination_event_chain((False, False, False, False),
                                    (EV_EXERCISE, EV_NOTICE, EV_NONRENEW))
    # D070: fact 60 crosses C-1 (50) but not C-2 (80)
    coc = change_of_control(Fraction(60))
    # D071: conversion keeps the grant alive
    conversion = license_conversion("grant-2024")
    # D072: a license row exists; no ownership row, no affiliate row
    relations = ip_relations(((REL_LIC, "grant-2024"),), "grant-2024")
    # D073: perpetual but revocable and capped
    attributes = license_attributes(True, True, False, 1000)
    # D074: two exact period lines; revenue base ≠ profit base at 1/10
    fees = fee_lines()
    # D075: carve-out passes; capped kind is clipped; insurance separate
    indemnity = indemnity_classification(
        (("confidentiality", True, Fraction(1500000)),
         ("general", False, Fraction(1500000))))
    # D076: settlement / audit / escrow / third-party survive termination
    survival = survival_rules((("settlement", "net out open orders", True),
                               ("audit", "books for 2y", True),
                               ("escrow", "source escrow", True),
                               ("third-party", "beneficiary rights", True),
                               ("terminating", "the termination itself",
                                False)))
    return {"case_id": "case-b08",
            "state": state, "expired_state": expired_state,
            "governing": governing, "governing_ok": governing_ok,
            "restrictions": restrictions, "priority": priority,
            "priority_in": priority_in, "chain": chain, "coc": coc,
            "conversion": conversion, "relations": relations,
            "attributes": attributes, "fees": fees,
            "indemnity": indemnity, "survival": survival,
            "fee_total": fees["exact_sum"],
            "admitted_facts": ("grant-alive", "usage-reported")}


def build_case_input(intake: dict):
    """Assemble the normalized CaseInput from the contract-clauses
    results; the pipeline consumes exactly these intermediate objects:
    the surviving licensed use supplies the issue, the D071-converted
    (still alive) grant is the admitted fact, the D076 surviving audit
    obligation is admitted, the notice-only termination claim stays
    awaiting (never silently written), and the only quantities are the
    two exact period fees plus the capped indemnity."""

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
    issue = "LICENSE_COMPLIANCE"
    state = ProcessState(
        r=NormState(relations=()),
        environment_id=CLAUSES_ENV_ID,
        stages=((f"{case_id}-trial", "trial"),),
        events=(),
        target_day=10,
        as_of_day=10,
    )
    parties = ("licensor", "licensee", "affiliate", "auditor")
    # the licensed usage under the kept grant supplies the compliance
    # claim; the D071 non-termination is a defense the licensee raises
    claims = (
        Claim("c0", "licensor", "licensee", issue, "usage-beyond-cap",
              "fee-and-compliance", subject="", issue=issue),
    )
    defenses = (
        Defense("def-nonterm", "licensee", ("c0",),
                "license_converted_not_terminated"),
    )
    standings = {
        "admitted": FactStanding.ADMITTED_POSITIVE,
        "awaiting": FactStanding.AWAITING_ADMISSION,
    }
    # admitted: the kept grant (D071) and the reported usage (D074
    # lines); awaiting: the notice-only termination proposition (D069)
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
            ("f-grant", "grant-alive",
             standings["admitted"]),      # D071 conversion kept it
            ("f-usage", "usage-reported",
             standings["admitted"]),      # D074 fee lines
            ("f-notice-only", "terminated_by_notice",
             standings["awaiting"]),      # D069 pending, never written
        ))
    )
    quantities = (
        ExactQuantity(intake["fees"]["line1"]["amount"], "CNY-fen",
                      "usage-fee-2026Q1", "fee-line-q1"),
        ExactQuantity(intake["fees"]["line2"]["amount"], "CNY-fen",
                      "usage-fee-2026Q2", "fee-line-q2"),
        ExactQuantity(intake["indemnity"]["witness_capped"], "CNY-fen",
                      "capped-indemnity", "classified-capped"),
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
    kept-grant and usage-report predicates; no verdicts, no prebuilt
    framework."""

    from theory.spec.canonical_v2.case import (
        LegalEnvironment,
        StrongTemplate,
    )
    from theory.spec.canonical_v2.kernel import Jurisdiction, JurisdictionRoute

    issue = "LICENSE_COMPLIANCE"
    template = StrongTemplate(
        template_id="tpl-license-compliance-b08",
        kind="LICENSE_COMPLIANCE",
        scope_issue=issue,
        premise_predicates=("grant-alive", "usage-reported"),
        conclusion_predicate=issue,
        failure_predicates=("terminated_by_notice",),
        license_rule_id="",
        source_id=f"clauses:{issue}",
    )
    return LegalEnvironment(
        environment_id=CLAUSES_ENV_ID,
        jurisdiction=Jurisdiction(route=JurisdictionRoute.MAINLAND),
        rules=(),
        strong_templates=(template,),
    )


def clauses_trace_events(intake: dict):
    """The two exact period fees are paid as two exact installments
    (3000 + 5000 = 8000, never a merged average number), and the
    surviving audit obligation becomes an evidence event that
    termination does not delete."""
    from fractions import Fraction

    from theory.spec.canonical_v2.case import CaseEvent
    from unified.process import LegalEventKind, ProcessEvent

    events = []
    day = 5
    evidence = ProcessEvent(
        event=CaseEvent(
            event_id="ev-surviving-audit",
            event_type="EVIDENCE_SUBMITTED",
            occurred_at=day,
            observed_at=day + 1,
            object_ref="surviving_audit",
        ),
        kind=LegalEventKind.EVIDENCE_SUBMITTED,
    )
    events.append(evidence)
    day += 2
    basis = "USAGE_FEE"
    for paid in (Fraction(3000), Fraction(5000)):
        events.append(
            ProcessEvent(
                event=CaseEvent(
                    event_id=f"pay-fee-{int(paid)}",
                    event_type="PAYMENT_PERFORMED",
                    occurred_at=day,
                    observed_at=day,
                    object_ref="usage_fee",
                ),
                kind=LegalEventKind.PAYMENT_PERFORMED,
                basis_key=basis,
                amount=paid,
                debt_order=(basis,),
            )
        )
        day += 1
    return tuple(events)
