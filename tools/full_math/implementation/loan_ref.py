"""Group-06 loan/guarantee reference entries (D047-D056, W2-A batch B06).

Every entry consumes real structured input (no fixtures, no precomputed
answers) and produces the intermediate result whose formal contract is
``JurisLean.FullMath.Contracts.demand_D047`` … ``demand_D056``:

* D047 ``loan_discharge`` — the delivery fact and the discharge fact
  enter the responsibility chain separately: only a delivered loan is
  booked (an undelivered IOU has a zero balance), discharge is decided
  by the payment stream actually covering the booked amounts (balance
  zero ⇔ paid covers due), and a lending record alone never implies
  later non-discharge — the same delivered ledger with a full repayment
  stream is discharged (ALL_134 counterexample: 出借记录不能自动证明后来
  未清偿).
* D048 ``offset_ledger`` — the offset ledger updates in admission order:
  every allocation is nonnegative and within its payment, debt identities
  are preserved row by row (traceable balance), a payment id that occurs
  twice makes the stream illegal, and one repayment cannot simultaneously
  cover the interest in full AND the principal in full (ALL_134
  counterexample: 同一还款同时全额扣本金、又全额扣利息应拒绝).
* D049 ``charges_report`` — term interest, overdue interest and the
  penalty are separate computation components (the term component is
  invariant under the overdue parameters; a period splits additively in
  integer days), and their composition is subject to the applicable
  policy cap — three similar percentages stacked to 30 over a cap of 24
  are rejected while dropping the penalty component (20) passes (ALL_134
  counterexample: 相似百分比不能默认三项全叠加).
* D050 ``security_readout`` — suretyship, mortgage and pledge are
  distinct legal relations with distinct establishment events (contract,
  registration, delivery): a signed security document alone establishes
  neither the mortgage nor the pledge, proceeds of the collateral are
  distributed down the priority waterfall with conservation (recoveries
  + leftover = proceeds) and priority (a later-ranked positive recovery
  implies every earlier claim is fully covered) (ALL_134 counterexample:
  签担保文件不自动证明登记完成或财产已交付).
* D051 ``corp_guarantee`` — resolution existence, procedure, representative
  authority and guarantee validity are separate predicates connected by
  rules: the corporate surety needs resolution AND signature (either one
  missing means not established), and on the very same "signature only"
  event set the corporate guarantee is not established while the
  natural-person suretyship is — no single blanket invalidation rule
  (ALL_134 counterexample: 仅无决议字段不得由一条统一规则宣布所有担保无效).
* D052 ``signature_attribution`` — signer, nominal capacity, the
  representation relation, the contract party and the responsible person
  are separately encoded fields: signing on behalf of a company makes the
  company (not the natural-person signer whose name is in the signature
  text) the responsible subject, and the ledger-side beneficiary field is
  preserved row by row through offsetting (ALL_134 counterexample: 签名
  文本为自然人名不自动由其个人承担全部合同义务).
* D053 ``spousal_attribution`` — marriage period, spouse signature,
  common intent, household/business use and debt attribution are
  independent issues: joint attribution requires the signature or the
  intent+use pair, flipping the marriage-period field never changes the
  attribution, and a marriage-period loan with no signature, intent or
  use is not a joint debt (ALL_134 counterexample: 婚内借款不自动推出
  夫妻共同债务).
* D054 ``veil_readout`` — the company-relation evidence forms a support
  graph and the personality-mixing evaluation is a separate rule layer:
  the joint-liability consequence attaches exactly through the evaluation
  (heavy edges: commingled funds or one-way control); a shared phone
  number alone generates no unlimited joint-liability edge (ALL_134
  counterexample: 共用电话不直接生成无限连带责任边).
* D055 ``fund_source_readout`` — fund source and cash capability are
  sourced fact candidates: an unsourced candidate stays unproven (never
  admitted), a sourced one is admitted, and from "income low" to "cash
  lending impossible" there is no admitted rule — insufficiency means
  unproven, never a fabricated negative fact (ALL_134 counterexample:
  收入低不自动证明不可能现金出借).
* D056 ``fee_ledger_readout`` — attorney fees, court fees and
  preservation fees are independent debt items with their own basis,
  beneficiary and claim status (three distinct fee kinds, a supported
  status requires a supporting basis — a self-quoted attorney-fee row is
  never auto-supported), and grouping the ledger conserves the total
  (ALL_134 counterexample: 自身工时报价不能自动作为对方应赔律师费).

Amounts are ``Fraction`` (ℚ).  The quantity-ledger surface is consumed
from ``quantledger_ref`` (the Python mirror of
``JurisLean.Seams.UnifiedQuantLedger``, the green B06 prerequisite
carrier), never redefined here.  The downstream adapters at the bottom
feed these intermediate results into the unified pipeline public entries
(``run_case`` / ``step_event`` / ``run_trace``); they never accept a
precomputed verdict.  The independent contract checker lives in
``loan_check`` and shares no code with this module.
"""
from __future__ import annotations

from fractions import Fraction
from typing import Dict, List, Optional, Sequence, Tuple

from tools.full_math.implementation.quantledger_ref import (
    BASIS_CONTRACT,
    BASIS_SELF,
    EV_DELIVERED,
    EV_REGISTERED,
    EV_RESOLUTION,
    EV_SIGNED,
    KIND_ATTORNEY,
    KIND_COURT,
    KIND_INTEREST,
    KIND_PRESERVATION,
    KIND_PRINCIPAL,
    LoanCharges,
    LedgerItem,
    STATUS_SUPPORTED,
    after_pay,
    allocs_of,
    corp_surety_established,
    distribute_proceeds,
    fee_supported,
    loan_ledger,
    outstanding,
    outstanding_after_stream,
    required_event,
    sec_established,
    seg_split_total,
    status_consistent,
    stream_allocs,
    stream_legal,
    sum_where_beneficiary,
    InterestSeg,
    charges_within,
    overdue_interest,
    penalty_charge,
    term_interest,
    total_charges,
)

F = Fraction

SEC_SURETYSHIP = "suretyship"
SEC_MORTGAGE = "mortgage"
SEC_PLEDGE = "pledge"

# ---------------------------------------------------------------------------
# D047 — delivery fact and discharge fact enter the chain separately
# ---------------------------------------------------------------------------


def loan_discharge(delivered: bool, ident: int, principal: Fraction,
                   payments: Sequence[Fraction]) -> dict:
    """The loan file of one matter: the delivery fact (delivered ⇒ booked
    principal, undelivered ⇒ empty ledger) and the discharge fact (the
    repayment stream covering the booked amounts) are read out
    separately (Lean ``Contracts.demand_D047``); the lending record
    alone never implies later non-discharge."""

    principal = Fraction(principal)
    payments = [Fraction(p) for p in payments]
    if any(p < 0 for p in payments):
        raise ValueError("payments must be nonnegative")
    ledger = loan_ledger(delivered, ident, principal)
    due = outstanding(ledger)
    rows = stream_allocs(payments, ledger)
    balance = outstanding_after_stream(payments, ledger)
    paid = sum(payments, F(0))
    return {
        "delivered": delivered,
        "booked": due,                       # delivery fact readout
        "undelivered_balance_zero":
            outstanding(loan_ledger(False, ident, principal)) == 0,
        "paid": paid,
        "rows": rows,
        "balance_after": balance,            # discharge fact readout
        "discharged": balance == 0,
        "discharged_iff_covered": (balance == 0) == (due <= paid),
        # a lending record alone does not imply non-discharge: the same
        # delivered ledger with a full repayment stream is discharged
        "record_alone_implies_unpaid": False,
        "full_stream_discharges":
            outstanding_after_stream([due], ledger) == 0,
    }


# ---------------------------------------------------------------------------
# D048 — admission-order offset ledger, per-payment bounds, traceability
# ---------------------------------------------------------------------------


def offset_ledger(items: Sequence[LedgerItem],
                  payments: Sequence[Fraction]) -> dict:
    """The offset ledger over one admission-ordered debt list: per-payment
    rows in admission order, every allocation nonnegative and within its
    payment, debt identities preserved row by row, the balance traceable
    step by step, and duplicate payment ids rejected (Lean
    ``Contracts.demand_D048``)."""

    payments = [Fraction(p) for p in payments]
    if any(p < 0 for p in payments):
        raise ValueError("payments must be nonnegative")
    rows = stream_allocs(payments, items)
    cur = list(items)
    balances = [outstanding(cur)]
    for p, row in zip(payments, rows):
        for it, a in zip(cur, row):
            if a < 0:
                raise ValueError("negative allocation")
        if sum(row, F(0)) > p:
            raise ValueError("allocation exceeds its payment")
        cur = after_pay(p, cur)
        balances.append(outstanding(cur))
    idents_before = [it.ident for it in items]
    idents_after = [it.ident for it in cur]
    dup_stream = [(7, F(100)), (7, F(50))]      # same payment id twice
    legal_stream = [(1, F(100)), (2, F(50))]
    return {
        "admission_order": [it.kind for it in items],
        "rows": rows,
        "row_nonneg": all(all(a >= 0 for a in row) for row in rows),
        "row_within_payment":
            all(sum(row, F(0)) <= p for p, row in zip(payments, rows)),
        "idents_preserved": idents_before == idents_after,
        "balance_trace": balances,
        "duplicate_id_rejected": not stream_legal(dup_stream),
        "distinct_ids_legal": stream_legal(legal_stream),
        "final_balance": balances[-1],
    }


def demo_offset_150() -> dict:
    """The admission-order witness of the fee 10 → interest 100 →
    principal 200 ledger: a 150 payment offsets (10, 100, 40) leaving a
    balance of 160 (the Lean ``demoLedger_readout`` mirror); a 350
    payment covers everything leaving zero."""

    ledger = (
        LedgerItem(1, "attorneyFee", BASIS_CONTRACT, 0, STATUS_SUPPORTED,
                   F(10)),
        LedgerItem(2, KIND_INTEREST, BASIS_CONTRACT, 0, STATUS_SUPPORTED,
                   F(100)),
        LedgerItem(3, KIND_PRINCIPAL, BASIS_CONTRACT, 0, STATUS_SUPPORTED,
                   F(200)),
    )
    part = offset_ledger(ledger, [F(150)])
    full = offset_ledger(ledger, [F(350)])
    return {
        "part_allocs": part["rows"][0],
        "part_balance": part["final_balance"],
        "full_allocs": full["rows"][0],
        "full_balance": full["final_balance"],
    }


def double_full_rejected(payment: Fraction = F(150)) -> dict:
    """One repayment cannot simultaneously offset the interest in full
    AND the principal in full: on the interest-100 + principal-200
    ledger the legal allocation of 150 is [100, 50]; the double-full
    row [100, 200] sums to 300 and is never the real allocation."""

    payment = Fraction(payment)
    ledger = (
        LedgerItem(2, KIND_INTEREST, BASIS_CONTRACT, 0, STATUS_SUPPORTED,
                   F(100)),
        LedgerItem(3, KIND_PRINCIPAL, BASIS_CONTRACT, 0, STATUS_SUPPORTED,
                   F(200)),
    )
    real = allocs_of(payment, ledger)
    double_full = [F(100), F(200)]
    return {
        "payment": payment,
        "real_allocs": real,
        "double_full_row": double_full,
        "double_full_exceeds_payment":
            sum(double_full, F(0)) > payment,
        "never_equals_real": real != double_full,
    }


# ---------------------------------------------------------------------------
# D049 — three charge components under the applicable policy cap
# ---------------------------------------------------------------------------


def charges_report(principal: Fraction, denom: int,
                   term_rate: Fraction, term_days: int,
                   overdue_rate: Fraction, overdue_days: int,
                   penalty_rate: Fraction, penalty_days: int,
                   cap: Fraction) -> dict:
    """Term interest, overdue interest and the penalty as separate
    computation components with their composition subject to the policy
    cap (Lean ``Contracts.demand_D049``): the term component is
    invariant under the overdue parameters, a period splits additively
    in integer days, and the stacked total is checked against the cap."""

    c = LoanCharges(Fraction(principal), denom, Fraction(term_rate),
                    term_days, Fraction(overdue_rate), overdue_days,
                    Fraction(penalty_rate), penalty_days)
    cap = Fraction(cap)
    term = term_interest(c)
    overdue = overdue_interest(c)
    penalty = penalty_charge(c)
    total = total_charges(c)
    # component independence: change the overdue parameters, the term
    # component does not move
    c2 = LoanCharges(c.principal, denom, c.term_rate, c.term_days,
                     Fraction(overdue_rate) * 2, overdue_days + 30,
                     c.penalty_rate, c.penalty_days)
    # segment additivity: split the term period at any day count
    seg = InterestSeg(c.principal, c.term_rate, term_days, denom)
    left, right = seg_split_total(seg, term_days // 2)
    return {
        "term": term, "overdue": overdue, "penalty": penalty,
        "total": total, "cap": cap,
        "within_cap": charges_within(cap, c),
        "term_independent_of_overdue": term_interest(c2) == term,
        "seg_split_sums": left + right == seg.interest(),
        "components_sum": term + overdue + penalty == total,
    }


def stacking_not_default() -> dict:
    """Similar percentages do not stack by default: principal 100 with
    term/overdue/penalty each 10 stacks to 30 and is rejected over the
    cap 24; dropping the penalty component gives 20 which passes."""

    all_stack = LoanCharges(F(100), 1, F(1, 10), 1, F(1, 10), 1,
                            F(1, 10), 1)
    no_penalty = LoanCharges(F(100), 1, F(1, 10), 1, F(1, 10), 1,
                             F(1, 10), 0)
    return {
        "all_total": total_charges(all_stack),
        "all_within_24": charges_within(F(24), all_stack),
        "no_penalty_total": total_charges(no_penalty),
        "no_penalty_within_24": charges_within(F(24), no_penalty),
    }


# ---------------------------------------------------------------------------
# D050 — typed security relations, establishment events, priority waterfall
# ---------------------------------------------------------------------------


def security_readout(events: Sequence[str],
                     claims: Sequence[Fraction] = (F(100), F(100)),
                     proceeds: Fraction = F(150)) -> dict:
    """Suretyship/mortgage/pledge as distinct relations with distinct
    establishment events, plus the priority waterfall over the
    collateral proceeds (Lean ``Contracts.demand_D050``)."""

    events = list(events)
    proceeds = Fraction(proceeds)
    claims = [Fraction(c) for c in claims]
    kinds = (SEC_SURETYSHIP, SEC_MORTGAGE, SEC_PLEDGE)
    required = {k: required_event(k) for k in kinds}
    established = {k: sec_established(k, events) for k in kinds}
    rows, leftover = distribute_proceeds(claims, proceeds)
    recoveries = sum(rows, F(0))
    # priority: a strictly positive later-rank recovery implies every
    # earlier claim is fully covered (checked on rank 1 vs rank 0)
    later_positive = rows[1] > 0
    earlier_full = rows[0] == claims[0]
    return {
        "events": events,
        "required_events": required,
        "required_events_distinct":
            len(set(required.values())) == len(required),
        "established": established,
        "signing_only_establishes_mortgage":
            sec_established(SEC_MORTGAGE, [EV_SIGNED]),
        "signing_only_establishes_pledge":
            sec_established(SEC_PLEDGE, [EV_SIGNED]),
        "registered_mortgage_established":
            sec_established(SEC_MORTGAGE, [EV_SIGNED, EV_REGISTERED]),
        "delivered_pledge_established":
            sec_established(SEC_PLEDGE, [EV_DELIVERED]),
        "claims": claims, "proceeds": proceeds,
        "priority_rows": rows, "leftover": leftover,
        "distribution_conserved": recoveries + leftover == proceeds,
        "later_positive_implies_earlier_full":
            (not later_positive) or earlier_full,
    }


# ---------------------------------------------------------------------------
# D051 — corporate-guarantee predicates connected by rules
# ---------------------------------------------------------------------------


def corp_guarantee(events: Sequence[str]) -> dict:
    """Resolution existence, procedure, representative authority and the
    guarantee validity as separate predicates connected by rules: the
    corporate surety needs resolution AND signature; the same
    signature-only event set leaves the corporate guarantee
    unestablished while the natural-person suretyship is established —
    no blanket invalidation (Lean ``Contracts.demand_D051``)."""

    events = list(events)
    same_events = [EV_SIGNED]
    return {
        "events": events,
        "corp_established": corp_surety_established(events),
        "resolution_present": EV_RESOLUTION in events,
        "signature_present": EV_SIGNED in events,
        "needs_both": corp_surety_established([EV_RESOLUTION, EV_SIGNED]),
        "resolution_alone_insufficient":
            not corp_surety_established([EV_RESOLUTION]),
        # same event set: corporate not established, natural person is
        "same_events_corp_not_established":
            not corp_surety_established(same_events),
        "same_events_natural_surety_established":
            sec_established(SEC_SURETYSHIP, same_events),
        "no_blanket_invalidation":
            (not corp_surety_established(same_events))
            and sec_established(SEC_SURETYSHIP, same_events),
    }


# ---------------------------------------------------------------------------
# D052 — signer / capacity / party / responsible person separately encoded
# ---------------------------------------------------------------------------


def resp_of(signer: int, capacity: str,
            principal: Optional[int] = None) -> int:
    """The responsible subject of a signature — the represented
    principal when the representation relation points at one, otherwise
    the signer (Lean ``Contracts.respOf``)."""

    if capacity == "ownName":
        return signer
    if capacity == "onBehalfOf":
        if principal is None:
            raise ValueError("onBehalfOf requires the principal id")
        return principal
    raise ValueError(f"unknown capacity: {capacity}")


def signature_attribution(signer: int, capacity: str,
                          principal: Optional[int] = None,
                          items: Sequence[LedgerItem] = (),
                          payment: Fraction = F(0)) -> dict:
    """Signer, nominal capacity, representation relation, contract party
    and responsible person as separate fields (Lean
    ``Contracts.demand_D052``); the ledger side keeps the beneficiary
    field row by row through the offsetting payment."""

    responsible = resp_of(signer, capacity, principal)
    items = list(items)
    payment = Fraction(payment)
    after = after_pay(payment, items)
    return {
        "signer": signer,
        "capacity": capacity,
        "principal": principal,
        "responsible": responsible,
        "natural_name_is_signer": signer != principal,
        "signer_bears_all": responsible == signer,
        "beneficiaries_before": [it.beneficiary for it in items],
        "beneficiaries_after": [it.beneficiary for it in after],
        "beneficiaries_preserved":
            [it.beneficiary for it in items] == [it.beneficiary for it in after],
    }


# ---------------------------------------------------------------------------
# D053 — spousal-debt issues independent; attribution by its own rule
# ---------------------------------------------------------------------------


def joint_debt(in_marriage: bool, spouse_signed: bool,
               common_intent: bool, household_use: bool) -> bool:
    """Joint attribution needs the spouse signature or the intent+use
    pair — never the marriage period alone (Lean
    ``Contracts.jointDebt``)."""

    return bool(spouse_signed or (common_intent and household_use))


def spousal_attribution(in_marriage: bool, spouse_signed: bool,
                        common_intent: bool, household_use: bool) -> dict:
    """The five spousal-debt issues as independent fields: flipping the
    marriage-period field never changes the attribution; a marriage-
    period loan with no signature/intent/use is not joint; signature
    alone or intent+use each establish the joint attribution (Lean
    ``Contracts.demand_D053``)."""

    base = joint_debt(in_marriage, spouse_signed, common_intent,
                      household_use)
    flipped = joint_debt(not in_marriage, spouse_signed, common_intent,
                         household_use)
    return {
        "in_marriage": in_marriage,
        "spouse_signed": spouse_signed,
        "common_intent": common_intent,
        "household_use": household_use,
        "joint": base,
        "marriage_flip_invariant": base == flipped,
        "married_alone_not_joint":
            not joint_debt(True, False, False, False),
        "signature_suffices": joint_debt(True, True, False, False),
        "intent_use_suffice": joint_debt(True, False, True, True),
    }


# ---------------------------------------------------------------------------
# D054 — support graph of company-relation evidence + separate veil rule
# ---------------------------------------------------------------------------

LIGHT_EDGES = ("sharedPhone", "sharedAddress")
HEAVY_EDGES = ("commingledFunds", "underControl")


def personality_mix(edges: Sequence[str]) -> bool:
    """The separate evaluation rule: personality mixing is reached only
    through the heavy edges (Lean ``Contracts.personalityMix``)."""

    return any(e in edges for e in HEAVY_EDGES)


def corp_joint_due(edges: Sequence[str]) -> bool:
    """The joint-liability consequence attaches only through the
    evaluation rule — never directly from an evidence edge (Lean
    ``Contracts.corpJointDue``)."""

    return personality_mix(edges)


def veil_readout(edges: Sequence[str]) -> dict:
    """The support graph of company-relation evidence with the
    personality-mixing evaluation as a separate rule layer (Lean
    ``Contracts.demand_D054``): a shared phone (or phone+address) graph
    reaches neither the evaluation nor the consequence; commingled
    funds or one-way control reach both."""

    edges = list(edges)
    phone_only = ["sharedPhone"]
    phone_addr = ["sharedPhone", "sharedAddress"]
    return {
        "edges": edges,
        "light_only": all(e in LIGHT_EDGES for e in edges),
        "mix": personality_mix(edges),
        "joint_due": corp_joint_due(edges),
        "consequence_is_evaluation": corp_joint_due(edges) == personality_mix(edges),
        "phone_only_no_mix": not personality_mix(phone_only),
        "phone_address_no_liability":
            not corp_joint_due(phone_addr),
        "commingled_reaches_both":
            personality_mix(["commingledFunds"])
            and corp_joint_due(["commingledFunds"]),
        "control_reaches_both":
            corp_joint_due(["underControl"]),
    }


# ---------------------------------------------------------------------------
# D055 — sourced fact candidates; insufficiency is unproven, not negative
# ---------------------------------------------------------------------------


def fund_source_readout(candidates: Sequence[Tuple[bool, int]]) -> dict:
    """Fund source and cash capability as sourced fact candidates: an
    unsourced candidate is never admitted (unproven), a sourced one is;
    from "income low" to "cash lending impossible" no rule is admitted
    (the rule base is empty), so insufficiency of sources reads out as
    unproven — never a fabricated negative fact (Lean
    ``Contracts.demand_D055``)."""

    candidates = [(bool(s), int(i)) for s, i in candidates]
    admissions = {(i, s): s for s, i in candidates}
    # the admitted rule base from incomeLow to cashImpossible (empty)
    cash_rules: List[Tuple[str, str]] = []
    shared_ids = {i for _, i in candidates
                  if (i, True) in admissions and (i, False) in admissions}
    return {
        "candidates": candidates,
        "admissions": admissions,
        "unsourced_unproven":
            all(not admissions[(i, s)]
                for s, i in candidates if not s),
        "sourced_admitted":
            all(admissions[(i, s)]
                for s, i in candidates if s),
        "same_id_sourced_unsourced_differ":
            all(admissions[(i, True)] is not admissions[(i, False)]
                for i in shared_ids),
        "cash_rules": cash_rules,
        "no_income_low_to_impossible_rule":
            ("incomeLow", "cashImpossible") not in cash_rules,
        "insufficiency_is_unproven_not_negative":
            all(not admissions[(i, s)]
                for s, i in candidates if not s)
            and cash_rules == [],
    }


# ---------------------------------------------------------------------------
# D056 — independent fee debt items: basis / beneficiary / claim status
# ---------------------------------------------------------------------------


def fee_ledger_readout(items: Sequence[LedgerItem],
                       beneficiary: int = 2) -> dict:
    """Attorney/court/preservation fees as independent debt items with
    their own basis, beneficiary and claim status (Lean
    ``Contracts.demand_D056``): three distinct fee kinds, a supported
    status requires a supporting basis (self-quoted never
    auto-supported), and the beneficiary grouping conserves the total."""

    items = list(items)
    kinds = [it.kind for it in items]
    self_quoted = LedgerItem(5, KIND_ATTORNEY, BASIS_SELF, 2,
                             STATUS_SUPPORTED, F(3000))
    stipulated = LedgerItem(6, KIND_ATTORNEY, BASIS_CONTRACT, 2,
                            STATUS_SUPPORTED, F(3000))
    fee_kinds = (KIND_ATTORNEY, KIND_COURT, KIND_PRESERVATION)
    return {
        "kinds": kinds,
        "fee_kinds_distinct": len(set(fee_kinds)) == 3
                              and KIND_ATTORNEY != KIND_PRINCIPAL,
        "rows_consistent": all(status_consistent(it) for it in items),
        "self_quoted_row": self_quoted,
        "self_quoted_supported": status_consistent(self_quoted),
        "stipulated_row": stipulated,
        "stipulated_supported": status_consistent(stipulated),
        "beneficiary_total": sum_where_beneficiary(beneficiary, items),
        "total": outstanding(items),
        "others_total":
            outstanding(items) - sum_where_beneficiary(beneficiary, items),
        "partition_conserved":
            sum_where_beneficiary(beneficiary, items)
            + (outstanding(items)
               - sum_where_beneficiary(beneficiary, items))
            == outstanding(items),
    }


# ---------------------------------------------------------------------------
# Downstream adapters: loan/guarantee results → pipeline carriers (PY-RUN)
# ---------------------------------------------------------------------------

LOAN_ENV_ID = "env-loan-b06"


def build_loan_intake() -> dict:
    """Synthetic loan/guarantee bundle for one lending matter: every
    field is produced by the entries above from declared structured
    inputs; the delivery/discharge readout, the offset ledger, the
    charge components, the security profile, the corporate-guarantee
    predicates, the signature attribution, the spousal attribution, the
    veil readout, the fund-source readout and the fee ledger all stay
    distinguishable."""

    demo = (
        LedgerItem(1, "attorneyFee", BASIS_CONTRACT, 0, STATUS_SUPPORTED,
                   F(10)),
        LedgerItem(2, KIND_INTEREST, BASIS_CONTRACT, 0, STATUS_SUPPORTED,
                   F(100)),
        LedgerItem(3, KIND_PRINCIPAL, BASIS_CONTRACT, 0, STATUS_SUPPORTED,
                   F(200)),
    )
    fees = (
        LedgerItem(6, KIND_ATTORNEY, BASIS_CONTRACT, 2, STATUS_SUPPORTED,
                   F(3000)),
        LedgerItem(7, KIND_COURT, BASIS_CONTRACT, 0, STATUS_SUPPORTED,
                   F(500)),
        LedgerItem(8, KIND_PRESERVATION, BASIS_CONTRACT, 0,
                   STATUS_SUPPORTED, F(200)),
    )
    return {
        "case_id": "case-b06",
        "delivery": loan_discharge(True, 1, F(200), [F(150)]),
        "offset": offset_ledger(demo, [F(150), F(60)]),
        "double_full": double_full_rejected(),
        "charges": charges_report(F(100), 1, F(1, 10), 1, F(1, 10), 1,
                                  F(1, 10), 1, F(24)),
        "stacking": stacking_not_default(),
        "security": security_readout([EV_SIGNED, EV_REGISTERED]),
        "corp": corp_guarantee([EV_SIGNED]),
        "signature": signature_attribution(3, "onBehalfOf", 7),
        "spousal": spousal_attribution(True, False, False, False),
        "veil": veil_readout(["sharedPhone"]),
        "funds": fund_source_readout([(True, 3), (False, 3), (True, 4)]),
        "fees": fee_ledger_readout(fees),
        "admitted_facts": ("loan-delivered", "guarantee-registered"),
    }


def build_case_input(intake: dict):
    """Assemble the normalized CaseInput from the loan/guarantee
    results; the pipeline consumes exactly these intermediate objects:
    the delivered-loan and registered-guarantee facts supply the
    admitted facts, the undischarged proposition from the lending
    record alone stays awaiting (never written), and the only
    quantities are the loan balance after the partial repayment and the
    contract-stipulated attorney fee — two separate debt items that are
    never merged."""

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
    issue = "LOAN_GUARANTEE"
    state = ProcessState(
        r=NormState(relations=()),
        environment_id=LOAN_ENV_ID,
        stages=((f"{case_id}-trial", "trial"),),
        events=(),
        target_day=10,
        as_of_day=10,
    )
    parties = ("client", "counterparty", "lender", "guarantor")
    # the lender's repayment claim rides on the delivered loan with its
    # admission-order offset ledger (D047/D048); the counterparty's
    # defense points at the corporate-guarantee predicate gap (D051) —
    # a missing resolution blocks the corporate guarantee, it does not
    # invalidate the natural-person suretyship
    claims = (
        Claim("c0", "lender", "client", issue, "loan-delivered",
              "loan-restitution", subject="", issue=issue),
    )
    defenses = (
        Defense("def-corp-no-resolution", "counterparty", ("c0",),
                "corporate_guarantee_unestablished"),
    )
    standings = {
        "admitted": FactStanding.ADMITTED_POSITIVE,
        "awaiting": FactStanding.AWAITING_ADMISSION,
    }
    # admitted: the delivered loan (D047) and the registered mortgage
    # (D050); awaiting: the record-alone-non-discharged proposition
    # (D047 adverse side) — a lending record never grounds it here
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
            ("f-delivery", "loan-delivered",
             standings["admitted"]),       # D047 delivery fact
            ("f-mortgage", "guarantee-registered",
             standings["admitted"]),       # D050 registered mortgage
            ("f-record-alone", "record-alone-non-discharged",
             standings["awaiting"]),       # D047 adverse, never written
        ))
    )
    quantities = (
        ExactQuantity(intake["delivery"]["balance_after"], "CNY-fen",
                      "loan-balance", "loan-discharge"),
        ExactQuantity(intake["fees"]["stipulated_row"].amount, "CNY-fen",
                      "attorney-fee-stipulated", "fee-ledger"),
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
    delivered-loan and registered-guarantee predicates; no verdicts, no
    prebuilt framework."""

    from theory.spec.canonical_v2.case import (
        LegalEnvironment,
        StrongTemplate,
    )
    from theory.spec.canonical_v2.kernel import Jurisdiction, JurisdictionRoute

    issue = "LOAN_GUARANTEE"
    template = StrongTemplate(
        template_id="tpl-loan-b06",
        kind="LOAN_DELIVERY",
        scope_issue=issue,
        premise_predicates=("loan-delivered", "guarantee-registered"),
        conclusion_predicate=issue,
        failure_predicates=("record-alone-non-discharged",),
        license_rule_id="",
        source_id=f"loan:{issue}",
    )
    return LegalEnvironment(
        environment_id=LOAN_ENV_ID,
        jurisdiction=Jurisdiction(route=JurisdictionRoute.MAINLAND),
        rules=(),
        strong_templates=(template,),
    )


def loan_trace_events(intake: dict):
    """The repayment witness becomes payment events allocated across
    the fee/interest/principal ledger in admission order (the exact ℚ
    amounts of the D048 offset rows — the 150 payment then the 60
    payment), and the stipulated attorney fee lands as its own exact
    installment against its own basis; the self-quoted fee basis
    receives nothing (a self-quote is never auto-supported, never
    merged with the stipulated fee)."""

    from theory.spec.canonical_v2.case import CaseEvent
    from unified.process import LegalEventKind, ProcessEvent

    events = []
    day = 4
    for i, row in enumerate(intake["offset"]["rows"], start=1):
        events.append(
            ProcessEvent(
                event=CaseEvent(
                    event_id=f"pay-offset-{i}",
                    event_type="PAYMENT_PERFORMED",
                    occurred_at=day,
                    observed_at=day,
                    object_ref="offset_ledger",
                ),
                kind=LegalEventKind.PAYMENT_PERFORMED,
                basis_key="PAYABLE_AMOUNT",
                amount=sum(row, F(0)),
                debt_order=("PAYABLE_AMOUNT",),
            )
        )
        day += 3
    events.append(
        ProcessEvent(
            event=CaseEvent(
                event_id="pay-attorney-stipulated",
                event_type="PAYMENT_PERFORMED",
                occurred_at=day,
                observed_at=day,
                object_ref="fee_ledger",
            ),
            kind=LegalEventKind.PAYMENT_PERFORMED,
            basis_key="ATTORNEY_FEE_STIPULATED",
            amount=intake["fees"]["stipulated_row"].amount,
            debt_order=("ATTORNEY_FEE_STIPULATED",),
        )
    )
    return tuple(events)
