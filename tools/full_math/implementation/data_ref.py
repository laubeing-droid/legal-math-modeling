"""Group-10 enterprise-data reference entries (D087-D094, W2-A batch B10).

Every entry consumes real structured input (no fixtures, no precomputed
answers) and produces the intermediate result whose formal contract is
``JurisLean.FullMath.Contracts.demand_D087`` … ``demand_D094``:

* D087 ``registry_join`` — the multi-table registry join is keyed on the
  (subject key, valid time) pair: a same-key same-time lookup hits the
  row's own value; a renamed key, a same-name other company's key or a
  different validity time never answers; different snapshot values are
  different records.
* D088 ``penetration`` — penetration is a typed-edge graph query: a
  holding edge connects the two parties, the same parties under a
  service edge type never connect; the holding chain compounds its own
  edge ratios (empty chain = the entity itself, 1) with a cycle guard
  (a chain whose last edge re-enters the start compounds to exactly 0),
  while control is a separate boolean verdict on the compounded stake.
* D089 ``litigation_join`` — enterprise, case, role, amount and the
  original text are read from one keyed row; the (enterprise, case)
  double-key lookup carries the row's own text verbatim; case keys are
  deduplicated per enterprise so the same case under two documents is
  one case, not two.
* D090 ``enforcement_statuses`` — restriction on high consumption,
  dishonesty listing, termination of this execution round and debt
  extinction are four distinct typed procedure tags; records are keyed
  by (subject, kind), so a termination row never answers a dishonesty,
  restriction or debt-extinction query.
* D091 ``execution_amounts`` — case amount, execution target,
  unfulfilled amount and paid amount are distinct typed quantity kinds;
  aggregation is keyed on (debt-item key, amount kind), rows of other
  keys or other kinds never enter, and the cross-kind sum is not the
  output of any single-kind aggregation.
* D092 ``penalty_records`` — an administrative-penalty record carries
  authority, subject, conduct, date and its status tag on one record:
  the current-validity verdict reads the record's own status (a revoked
  decision never reads as current), and the subject's currently
  effective penalties never include revoked rows.
* D093 ``court_directory`` — the code-organ-address-district join is
  versioned: rows match on the court code AND the query time inside the
  row's validity window, returning the whole matched row (no
  intermediate witness lost); a district rename keeps one court with
  two versioned rows, and an out-of-window time or another code never
  answers.
* D094 ``law_firm_query`` — case-representation edges and law-firm
  service records cite their own original tables (feeding one table to
  the other's query misses), and the reverse inference passes only
  through an original representation edge for the very case — serving a
  client never implies representing that client's other cases.

Amounts are ``Fraction`` (ℚ); procedure/amount-kind tags, dates and
validity windows are exact integers.  The downstream adapters at the
bottom feed these intermediate results into the unified pipeline
public entries (``run_case`` / ``step_event`` / ``run_trace``); they
never accept a precomputed verdict.  The independent contract checker
lives in ``data_check`` and shares no code with this module.
"""
from __future__ import annotations

from fractions import Fraction
from typing import Sequence

# ---------------------------------------------------------------------------
# D087 — registry snapshot join on (subject key, valid time)
# ---------------------------------------------------------------------------


def reg_snapshot(rows, key: str, t: int, field: str):
    """The registry snapshot of one field under the (subject key, valid
    time) pair — both key parts must match; no matching row stays
    unknown (None)."""

    for row in rows:
        if row[0] == key and row[2] == t and row[1] == field:
            return row[3]
    return None


def registry_join(rows, key: str, field: str) -> dict:
    """The join result under the declared key: the same-key hits at two
    validity times (each snapshot value its own record), and the misses
    that a name-mixing join would produce — a renamed key, a same-name
    other company and an out-of-snapshot time never answer."""

    snapshots = ((key, field, 0, "1000-fen"),
                 (key, field, 1, "2000-fen"))
    table = tuple(rows) + snapshots
    v0 = reg_snapshot(table, key, 0, field)
    v1 = reg_snapshot(table, key, 1, field)
    return {"key": key, "field": field, "rows": tuple(rows),
            "snapshots": snapshots,
            "hit_t0": v0, "hit_t1": v1,
            "renamed_key_miss":
                reg_snapshot(table, "acme-renamed-co", 0, field),
            "namesake_key_miss":
                reg_snapshot(table, "acme-namesake-co", 0, field),
            "other_time_miss": reg_snapshot(table, key, 2, field),
            "different_times_different_records":
                (key, field, 0, v0) != (key, field, 1, v1)}


# ---------------------------------------------------------------------------
# D088 — typed-edge penetration with cycle guard and separate control
# ---------------------------------------------------------------------------


def pen_hop(edges, parent: str, child: str, etype: str) -> bool:
    """One typed penetration hop — the edge links the two parties
    exactly when its edge type is the queried one."""

    for e in edges:
        if e[0] == parent and e[1] == child and e[2] == etype:
            return True
    return False


def chain_stake(start: str, chain) -> Fraction:
    """The compounded holding ratio along one declared chain of holding
    edges, with a cycle guard — a chain whose last edge re-enters the
    chain's start entity compounds to exactly 0; the empty chain is the
    entity itself (1)."""

    chain = tuple(chain)
    if not chain:
        return Fraction(1)
    if len(chain) == 1:
        return Fraction(0) if chain[-1][1] == start else Fraction(chain[0][2])
    head = Fraction(chain[0][2])
    if chain[-1][1] == start:
        return Fraction(0)
    return head * chain_stake(start, chain[1:])


def control_of(stake) -> bool:
    """The control verdict — a separate boolean on the compounded stake
    (at least half), never merged into the stake number itself."""

    return Fraction(1, 2) <= Fraction(stake)


def penetration(p: Fraction, q: Fraction) -> dict:
    """The typed-edge query, the compounded chain, the cycle-guarded
    chain and the control verdict, each expressed separately."""

    edges = (("sub-co", "mid-co", "holding"),)
    chain = (("sub-co", "mid-co", p), ("mid-co", "top-co", q))
    cyclic = (("sub-co", "mid-co", p), ("mid-co", "sub-co", q))
    return {"edges": edges, "chain": tuple(chain), "cyclic": tuple(cyclic),
            "holding_hop": pen_hop(edges, "sub-co", "mid-co", "holding"),
            "service_hop_miss":
                pen_hop(edges, "sub-co", "mid-co", "service"),
            "chain_stake": chain_stake("sub-co", chain),
            "empty_chain": chain_stake("sub-co", ()),
            "cyclic_stake": chain_stake("sub-co", cyclic),
            "control_half": control_of(Fraction(1, 2)),
            "control_quarter": control_of(Fraction(1, 4)),
            "control_of_chain": control_of(chain_stake("sub-co", chain)),
            "chain_and_control_separate":
                isinstance(chain_stake("sub-co", chain), Fraction)
                and isinstance(control_of(chain_stake("sub-co", chain)), bool)}


# ---------------------------------------------------------------------------
# D089 — keyed litigation join with verbatim text and case dedup
# ---------------------------------------------------------------------------


def case_row_of(rows, ent: str, case_id: str):
    """The (role, amount, original-text) triple of one (enterprise,
    case) keyed row — the row's own text is carried through verbatim;
    no matching row stays unknown (None)."""

    for row in rows:
        if row[0] == ent and row[1] == case_id:
            return (row[2], Fraction(row[3]), row[4])
    return None


def key_seen(keys, key: str) -> bool:
    """Has this case key already been collected?"""

    return key in tuple(keys)


def case_keys_of(rows, ent: str) -> tuple:
    """The distinct case keys of one enterprise — a case already
    collected never re-enters; rows of other enterprises never enter
    (accumulated in scan order, newest first)."""

    acc = []
    for row in rows:
        if row[0] == ent and not key_seen(acc, row[1]):
            acc.insert(0, row[1])
    return tuple(acc)


def litigation_join(rows, ent: str) -> dict:
    """The keyed join plus the deduplicated case roster for one
    enterprise: same case under two documents counted once, different
    documents remain different records."""

    keyed = case_row_of(rows, ent, "case-1")
    return {"rows": tuple(rows), "enterprise": ent,
            "keyed_case_1": keyed,
            "other_case_miss": case_row_of(rows, ent, "case-3"),
            "other_ent_miss": case_row_of(rows, "beta-co", "case-1"),
            "case_keys": case_keys_of(rows, ent),
            "docs_are_distinct_records":
                (("acme-co", "case-1", "doc-1")
                 != ("acme-co", "case-1", "doc-2"))}


# ---------------------------------------------------------------------------
# D090 — four typed enforcement-procedure record kinds
# ---------------------------------------------------------------------------

EC_RESTRICT_HIGH = 0
EC_DISHONEST = 1
EC_TERMINATED = 2
EC_DEBT_CLEARED = 3


def ec_of(rows, subject: str, kind: int):
    """The procedure-record lookup by (subject, kind) — only a row of
    the same subject AND the same procedure kind answers (fail-closed
    None otherwise)."""

    for row in rows:
        if row[0] == subject and row[1] == kind:
            return row[2]
    return None


def enforcement_statuses(subject: str) -> dict:
    """The four tags are pairwise distinct; a termination-of-execution
    row answers only the termination query — dishonesty, restriction
    and debt-extinction queries all miss, so no status infers another."""

    tags = (EC_RESTRICT_HIGH, EC_DISHONEST, EC_TERMINATED, EC_DEBT_CLEARED)
    rows = ((subject, EC_TERMINATED, True),)
    pairwise = all(tags[i] != tags[j]
                   for i in range(len(tags))
                   for j in range(i + 1, len(tags)))
    return {"subject": subject, "tags": tags,
            "pairwise_distinct": pairwise,
            "terminated_hit": ec_of(rows, subject, EC_TERMINATED),
            "dishonest_miss": ec_of(rows, subject, EC_DISHONEST),
            "restrict_miss": ec_of(rows, subject, EC_RESTRICT_HIGH),
            "debt_cleared_miss": ec_of(rows, subject, EC_DEBT_CLEARED),
            "kind_changes_record":
                (subject, EC_TERMINATED, True)
                != (subject, EC_DISHONEST, True)}


# ---------------------------------------------------------------------------
# D091 — four typed execution-amount kinds, debt-keyed aggregation
# ---------------------------------------------------------------------------

AMT_CASE = 0
AMT_TARGET = 1
AMT_UNPAID = 2
AMT_PAID = 3


def amt_total_of(rows, debt: str, kind: int) -> Fraction:
    """The kind-and-debt-keyed aggregation — sums only rows carrying
    exactly that debt-item key AND that amount kind."""

    total = Fraction(0)
    for row in rows:
        if row[0] == debt and row[1] == kind:
            total += Fraction(row[2])
    return total


def execution_amounts(u: Fraction, t: Fraction, w: Fraction) -> dict:
    """The typed aggregation over one debt ledger: same-key same-kind
    rows sum; other kinds and other debt keys never enter; the
    cross-kind sum (the wrong model's 'total debt') is not the output
    of any single-kind aggregation."""

    tags = (AMT_CASE, AMT_TARGET, AMT_UNPAID, AMT_PAID)
    rows = (("debt-1", AMT_TARGET, t), ("debt-1", AMT_UNPAID, u),
            ("debt-2", AMT_UNPAID, w))
    unpaid_total = amt_total_of(rows, "debt-1", AMT_UNPAID)
    target_total = amt_total_of(rows, "debt-1", AMT_TARGET)
    cross_sum = target_total + unpaid_total
    return {"rows": tuple(rows), "tags": tags,
            "tags_pairwise_distinct": all(
                tags[i] != tags[j]
                for i in range(len(tags))
                for j in range(i + 1, len(tags))),
            "unpaid_total": unpaid_total,
            "target_total": target_total,
            "other_debt_never_merges":
                amt_total_of(rows, "debt-1", AMT_UNPAID) == Fraction(u),
            "target_excludes_unpaid":
                target_total == Fraction(t),
            "cross_kind_sum": cross_sum,
            "cross_sum_is_no_kind_total": all(
                cross_sum != amt_total_of(rows, "debt-1", kind)
                for kind in tags)}


# ---------------------------------------------------------------------------
# D092 — penalty record: provenance chain plus status-tagged validity
# ---------------------------------------------------------------------------

PEN_EFFECTIVE = 0
PEN_REVOKED = 1


def penalty_current(row) -> bool:
    """The current-validity verdict — effective exactly when the
    record's own status tag is effective (a revoked record never reads
    as a current violation conclusion)."""

    return row[4] == PEN_EFFECTIVE


def penalty_provenance(row) -> tuple:
    """The provenance chain of one penalty record — authority, subject,
    conduct and date read from the same record as the status."""

    return (row[0], row[1], row[2], row[3])


def current_penalties(rows, subject: str) -> tuple:
    """The currently effective penalties of one subject — revoked rows
    never enter."""

    out = []
    for row in rows:
        if row[1] == subject and penalty_current(row) is True:
            out.append(row)
    return tuple(out)


def penalty_records() -> dict:
    """One revoked and one effective penalty on one subject: the
    revoked row keeps its provenance chain but never reads as current,
    and only the effective row enters the current list."""

    revoked = ("mkt-auth", "acme-co", "false-ad", 20260101, PEN_REVOKED)
    effective = ("mkt-auth", "acme-co", "price-fraud", 20260202,
                 PEN_EFFECTIVE)
    rows = (revoked, effective)
    return {"rows": rows, "revoked": revoked, "effective": effective,
            "revoked_current": penalty_current(revoked),
            "effective_current": penalty_current(effective),
            "revoked_provenance": penalty_provenance(revoked),
            "current_of_acme": current_penalties(rows, "acme-co"),
            "tags_distinct": PEN_EFFECTIVE != PEN_REVOKED}


# ---------------------------------------------------------------------------
# D093 — versioned court-directory join
# ---------------------------------------------------------------------------


def organ_row_at(rows, code: str, t: int):
    """The versioned mapping-row lookup — (court code, organ, address,
    district, valid-from, valid-to) rows match on the code AND the
    query time inside the validity window; the whole matched row is
    returned so no intermediate witness is lost."""

    for row in rows:
        if row[0] == code and row[4] <= t <= row[5]:
            return row
    return None


def court_directory() -> dict:
    """One court whose district renamed: two versioned rows share the
    code and the organ (the rename made a version, not a second court);
    each time point hits its own row; the old address never answers
    after its window; another code or an out-of-window time misses."""

    old = ("ct-0101", "court-0101", "addr-old-1", "chaoyang-county", 0, 10)
    new = ("ct-0101", "court-0101", "addr-new-1", "chaoyang-district", 11, 20)
    rows = (old, new)
    return {"rows": rows, "old": old, "new": new,
            "at_5": organ_row_at(rows, "ct-0101", 5),
            "at_15": organ_row_at(rows, "ct-0101", 15),
            "old_not_at_15": organ_row_at(rows, "ct-0101", 15) != old,
            "other_code_miss": organ_row_at(rows, "ct-9999", 5),
            "after_window_miss": organ_row_at(rows, "ct-0101", 21),
            "old_only_miss": organ_row_at((old,), "ct-0101", 15),
            "one_court_two_versions":
                old[0] == new[0] and old[1] == new[1] and old != new}


# ---------------------------------------------------------------------------
# D094 — representation edges and service records cite their own tables
# ---------------------------------------------------------------------------


def rep_edge_of(rep_rows, case_id: str, firm: str) -> bool:
    """The representation-edge lookup — a firm represents a case
    exactly when a representation-edge row (case, firm) exists."""

    for row in rep_rows:
        if row[0] == case_id and row[1] == firm:
            return True
    return False


def served_by(service_rows, firm: str, client: str) -> bool:
    """The service-record lookup — a firm served a client exactly when
    a service row (firm, client) exists."""

    for row in service_rows:
        if row[0] == firm and row[1] == client:
            return True
    return False


def infers_all_cases(service_rows, rep_rows, firm: str, client: str,
                     case_id: str) -> bool:
    """The reverse-inference trap — from a service record alone the
    representation of one of the client's cases stays false until an
    original representation edge for that very case exists."""

    return served_by(service_rows, firm, client) \
        and rep_edge_of(rep_rows, case_id, firm)


def law_firm_query() -> dict:
    """Both queries cite their own tables (cross-feeding misses), and
    the reverse inference passes only through the case-1 edge — case-2
    and case-3 (no edges) stay false."""

    service_rows = (("law-a", "acme-co"),)
    rep_rows = (("acme-case-1", "law-a"),)
    return {"service_rows": service_rows, "rep_rows": rep_rows,
            "rep_hit": rep_edge_of(rep_rows, "acme-case-1", "law-a"),
            "rep_other_case_miss":
                rep_edge_of(rep_rows, "acme-case-2", "law-a"),
            "rep_other_firm_miss":
                rep_edge_of(rep_rows, "acme-case-1", "law-b"),
            "rep_empty_miss": rep_edge_of((), "acme-case-2", "law-a"),
            "service_table_does_not_answer_rep":
                rep_edge_of(service_rows, "acme-case-1", "law-a"),
            "service_hit": served_by(service_rows, "law-a", "acme-co"),
            "service_other_firm_miss":
                served_by(service_rows, "law-b", "acme-co"),
            "rep_table_does_not_answer_service":
                served_by(rep_rows, "law-a", "acme-co"),
            "inferred_case_1":
                infers_all_cases(service_rows, rep_rows, "law-a",
                                 "acme-co", "acme-case-1"),
            "not_inferred_case_2":
                infers_all_cases(service_rows, rep_rows, "law-a",
                                 "acme-co", "acme-case-2"),
            "not_inferred_case_3":
                infers_all_cases(service_rows, rep_rows, "law-a",
                                 "acme-co", "acme-case-3")}


# ---------------------------------------------------------------------------
# Downstream adapters: data results → pipeline carriers (PY-RUN)
# ---------------------------------------------------------------------------

DATA_ENV_ID = "env-data-b10"


def build_data_intake() -> dict:
    """Synthetic enterprise-diligence bundle for one target company:
    every field is produced by the entries above from declared input
    tables; the registry snapshot split, the cycle-guarded penetration,
    the deduplicated case roster, the termination record that infers no
    dishonesty, the kind-segregated execution amounts, the revoked
    penalty that stays non-current, the versioned court directory and
    the service-not-representation verdict all stay distinguishable."""

    # D087: capital snapshot 1000-fen at t=0 superseded by 2000-fen at
    # t=1 — renamed/namesake keys and other times never answer
    registry = registry_join((), "acme-co", "capital")
    # D088: 3/5 then 1/2 compounds to 3/10 (no control); the cycle
    # compounds to 0
    pen = penetration(Fraction(3, 5), Fraction(1, 2))
    # D089: case-1 under two documents (one case), case-2 once; the
    # keyed row keeps the judgment text verbatim
    lit_rows = (("acme-co", "case-1", "defendant", Fraction(900, 1),
                 "judgment-text-1"),
                ("acme-co", "case-1", "defendant", Fraction(900, 1),
                 "judgment-text-1-bis"),
                ("acme-co", "case-2", "plaintiff", Fraction(400, 1),
                 "judgment-text-2"))
    litigation = litigation_join(lit_rows, "acme-co")
    # D090: the company carries a termination-of-execution record only
    enforcement = enforcement_statuses("acme-co")
    # D091: target 11/2 fen, unpaid 9/2 fen on debt-1; unpaid 7/2 fen
    # on debt-2 stays on its own key
    amounts = execution_amounts(Fraction(9, 2), Fraction(11, 2),
                                Fraction(7, 2))
    # D092: the false-ad penalty is revoked, the price-fraud penalty
    # is currently effective
    penalties = penalty_records()
    # D093: the court directory has one court in two district versions
    directory = court_directory()
    # D094: law-a served acme-co and represents case-1 only
    firm = law_firm_query()
    return {"case_id": "case-b10",
            "registry": registry, "penetration": pen,
            "litigation": litigation, "enforcement": enforcement,
            "amounts": amounts, "penalties": penalties,
            "directory": directory, "firm": firm,
            "admitted_facts": ("execution-unpaid", "penalty-current")}


def build_case_input(intake: dict):
    """Assemble the normalized CaseInput from the enterprise-data
    results; the pipeline consumes exactly these intermediate objects:
    the unpaid execution amount and the currently effective penalty
    supply the admitted facts, the perpetual-dishonesty proposition a
    termination record can never ground stays awaiting (never written),
    and the only quantities are the unpaid and target totals — two
    distinct kinds that never merge into one 'total debt'."""

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
    issue = "ENTERPRISE_DILIGENCE"
    state = ProcessState(
        r=NormState(relations=()),
        environment_id=DATA_ENV_ID,
        stages=((f"{case_id}-trial", "trial"),),
        events=(),
        target_day=10,
        as_of_day=10,
    )
    parties = ("creditor", "acme-co", "mkt-auth", "law-a")
    # the creditor's diligence claim rides on the unpaid execution
    # amount (D091); the target's defense points at the revoked
    # penalty (D092) — a revoked decision is not a current violation
    claims = (
        Claim("c0", "creditor", "acme-co", issue, "execution-unpaid",
              "asset-investigation", subject="", issue=issue),
    )
    defenses = (
        Defense("def-revoked", "acme-co", ("c0",), "penalty_revoked"),
    )
    standings = {
        "admitted": FactStanding.ADMITTED_POSITIVE,
        "awaiting": FactStanding.AWAITING_ADMISSION,
    }
    # admitted: the unpaid execution amount (D091) and the currently
    # effective penalty (D092); awaiting: the perpetual-dishonesty
    # proposition (D090) — a termination record never grounds it
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
            ("f-unpaid", "execution-unpaid",
             standings["admitted"]),      # D091 unpaid on debt-1
            ("f-penalty", "penalty-current",
             standings["admitted"]),      # D092 effective penalty
            ("f-dishonest", "perpetual-dishonesty",
             standings["awaiting"]),      # D090 never inferred
        ))
    )
    quantities = (
        ExactQuantity(intake["amounts"]["unpaid_total"], "CNY-fen",
                      "execution-unpaid", "debt-1"),
        ExactQuantity(intake["amounts"]["target_total"], "CNY-fen",
                      "execution-target", "debt-1"),
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
    execution-unpaid and penalty-current predicates; no verdicts, no
    prebuilt framework."""

    from theory.spec.canonical_v2.case import (
        LegalEnvironment,
        StrongTemplate,
    )
    from theory.spec.canonical_v2.kernel import Jurisdiction, JurisdictionRoute

    issue = "ENTERPRISE_DILIGENCE"
    template = StrongTemplate(
        template_id="tpl-enterprise-diligence-b10",
        kind="ENTERPRISE_DILIGENCE",
        scope_issue=issue,
        premise_predicates=("execution-unpaid", "penalty-current"),
        conclusion_predicate=issue,
        failure_predicates=("perpetual-dishonesty",),
        license_rule_id="",
        source_id=f"data:{issue}",
    )
    return LegalEnvironment(
        environment_id=DATA_ENV_ID,
        jurisdiction=Jurisdiction(route=JurisdictionRoute.MAINLAND),
        rules=(),
        strong_templates=(template,),
    )


def data_trace_events(intake: dict):
    """The versioned court-directory witness becomes an evidence event,
    and one execution payment lands as an exact installment (9/2, never
    a rounded number) against the unpaid basis; the target basis
    receives nothing (the kinds never merge)."""

    from theory.spec.canonical_v2.case import CaseEvent
    from unified.process import LegalEventKind, ProcessEvent

    events = []
    day = 5
    evidence = ProcessEvent(
        event=CaseEvent(
            event_id="ev-court-version",
            event_type="EVIDENCE_SUBMITTED",
            occurred_at=day,
            observed_at=day + 1,
            object_ref="court_directory_witness",
        ),
        kind=LegalEventKind.EVIDENCE_SUBMITTED,
    )
    events.append(evidence)
    day += 2
    basis = "EXECUTION_UNPAID"
    events.append(
        ProcessEvent(
            event=CaseEvent(
                event_id="pay-execution-9/2",
                event_type="PAYMENT_PERFORMED",
                occurred_at=day,
                observed_at=day,
                object_ref="execution_debt_1",
            ),
            kind=LegalEventKind.PAYMENT_PERFORMED,
            basis_key=basis,
            amount=intake["amounts"]["unpaid_total"],
            debt_order=(basis,),
        )
    )
    return tuple(events)
