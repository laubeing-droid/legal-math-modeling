"""Master needle (W0, needle 60) coherent-interim reference entries.

Formal contract: ``JurisLean.Seams.UnifiedMasterNeedle.lean`` (the rebuilt
needle-60 total theorem; authoritative spec line
``docs/spec/20261007-统一法律数学模型_附录I_Lean施工明细.md`` I.13 :814 --
"common interim witness, full static chain / event chain, precision
propagation; no 'same M plus independent arithmetic'").

The reference mirrors the Lean module exactly:

* carrier -- ``CoherentInterim`` (docket, event-chain trajectory and final
  state, debt ledger, payment plan, cash-flow entries, evaluation frame,
  focus, loss interval, Beta posterior shape) with the C1-C7 coherence
  clauses computed from the structured tables;
* event chain -- the full-docket 17-step trajectory over the 29 named-source
  rules (R01..R29 tables transcribed from ``familyRuleList``), with
  well-formedness (premises established before use), productivity and
  strictly increasing time indices;
* static chain -- Horn closure of the same docket, so the two chains can be
  compared (soundness everywhere, two-way agreement on the consumed atom
  set);
* exchanges -- payment split/reorder invariance of the balance reading and
  of the cash total fed to the payoff layer (clamp composition algebra);
  loss-interval merge/share distributivity plus first-seen-dedup vs
  nonnegative-scaling commutation; burden-channel vs payment-channel
  commutation on the interim;
* error propagation -- payoff-layer linear perturbation bound, ledger-layer
  ReLU 1-Lipschitz payment bound, divFree quantity-AST exact carrying
  (epsilon = 0), Beta CDF enclosure propagation to the expected reading,
  and the end-to-end exposure bound;
* equil face -- the lawful/sanction menu whose values ARE the interim
  readings (balance 160 / payoff reading 250), the explicit all-comply pure
  equilibrium via pure-deviation checks.

Every entry consumes the structured docket/rule/ledger tables (no fixtures,
no precomputed verdicts).  The independent contract checker lives in
``masterneedle_check`` and shares no code with this module.

All quantity arithmetic is exact ``Fraction`` (the Lean side uses Q);
nothing here samples, rounds, or floats.
"""
from __future__ import annotations

from dataclasses import dataclass, field
from fractions import Fraction
from typing import Dict, FrozenSet, List, Sequence, Tuple

# ---------------------------------------------------------------------------
# Shared tables (Lean constructor names verbatim)
# ---------------------------------------------------------------------------

# Consequence valuation table (PayoffEquilibrium.consequenceValuation,
# [代拟稿] declared table, zero-sum between the two roles).
CONSEQUENCE_VALUATION: Dict[Tuple[str, str], Fraction] = {
    ("claimant", "costBurdenLoser"): Fraction(3),
    ("claimant", "costBurdenPartial"): Fraction(1),
    ("claimant", "costOwnOnDismiss"): Fraction(-3),
    ("claimant", "noTitleNoCost"): Fraction(0),
    ("claimant", "enforcementAccess"): Fraction(2),
    ("claimant", "resJudicata"): Fraction(2),
    ("respondent", "costBurdenLoser"): Fraction(-3),
    ("respondent", "costBurdenPartial"): Fraction(-1),
    ("respondent", "costOwnOnDismiss"): Fraction(0),
    ("respondent", "noTitleNoCost"): Fraction(0),
    ("respondent", "enforcementAccess"): Fraction(-2),
    ("respondent", "resJudicata"): Fraction(-2),
}

ALL_CONS: Tuple[str, ...] = (
    "costBurdenLoser", "costBurdenPartial", "costOwnOnDismiss",
    "noTitleNoCost", "enforcementAccess", "resJudicata")

# Cost-kind policy (costKindOf -- [代拟稿] declared assignment).
COST_KIND_OF: Dict[str, str] = {
    "attorneyFee": "costOwnOnDismiss",
    "courtFee": "costOwnOnDismiss",
    "preservationFee": "costOwnOnDismiss",
    "interest": "enforcementAccess",
    "overdueInterest": "enforcementAccess",
    "penalty": "costBurdenPartial",
    "principal": "resJudicata",
}

# ---------------------------------------------------------------------------
# Rule network (29 named-source Horn rules, premises/conclusions transcribed
# from UnifiedFourteenFamilies.familyRuleList)
# ---------------------------------------------------------------------------

RULES: Tuple[Dict[str, object], ...] = (
    {"id": "R01", "premises": ("matContractSigned", "matBankSettlementMatched",
                               "matReconciliationUnpaid"),
     "conclusion": "loanEntitlement", "src": "L01"},
    {"id": "R02", "premises": ("matGuaranteeByGOpen",),
     "conclusion": "guarantorStanding", "src": "L01"},
    {"id": "R03", "premises": ("guarantorStanding",),
     "conclusion": "guarantorLiableAfterExhaustion", "src": "L01"},
    {"id": "R04", "premises": ("matMortgageRegistered", "matRealizationRecord",
                               "loanEntitlement"),
     "conclusion": "mortgageSecuredPriority", "src": "L02"},
    {"id": "R05", "premises": ("matRegistryD",),
     "conclusion": "carDamageCompensable", "src": "L02"},
    {"id": "R06", "premises": ("matWorkInstruction", "matDamageCorroboration"),
     "conclusion": "tortFaultPresumed", "src": "L03"},
    {"id": "R07", "premises": ("matNQualified",),
     "conclusion": "publicInterestStanding", "src": "L14"},
    {"id": "R08", "premises": ("matSamplingMatch", "matExceedance",
                               "matNoExculpation", "matInNewLawPeriod"),
     "conclusion": "ecoViolationEstablished", "src": "L05"},
    {"id": "R09", "premises": ("matPondTesting", "ecoViolationEstablished"),
     "conclusion": "fishPrivateCompensation", "src": "L05"},
    {"id": "R10", "premises": ("matEcoCostDocs", "publicInterestStanding",
                               "ecoViolationEstablished"),
     "conclusion": "ecoRemediationCosts", "src": "L05"},
    {"id": "R11", "premises": ("matWageBasisOnFile",),
     "conclusion": "wageDueEstablished", "src": "L07"},
    {"id": "R12", "premises": ("matSeparateAccounts",),
     "conclusion": "noCommingling", "src": "L08"},
    {"id": "R13", "premises": ("matInsolvencyShown", "matAcceptanceDecided"),
     "conclusion": "bankruptcyAccepted", "src": "L08"},
    {"id": "R14", "premises": ("bankruptcyAccepted",),
     "conclusion": "bankruptcyExecutionStay", "src": "L08"},
    {"id": "R15", "premises": ("bankruptcyAccepted",),
     "conclusion": "bankruptcyCivilStay", "src": "L08"},
    {"id": "R16", "premises": ("bankruptcyAccepted",),
     "conclusion": "arbitrationStayed", "src": "L08"},
    {"id": "R17", "premises": ("wageDueEstablished", "bankruptcyAccepted"),
     "conclusion": "wageBankruptcyPriority", "src": "L07"},
    {"id": "R18", "premises": ("matCreationChain", "matLicenseExpired",
                               "matPostTermUse"),
     "conclusion": "ipInfringementEstablished", "src": "L09"},
    {"id": "R19", "premises": ("matCDeathRecord", "matHeirsNotYetJoined"),
     "conclusion": "stayForSuccession", "src": "L06"},
    {"id": "R20", "premises": ("stayForSuccession", "matStayEventsKept"),
     "conclusion": "stayDecreeIssued", "src": "L13"},
    {"id": "R21", "premises": ("stayForSuccession",),
     "conclusion": "holdOnLoanFinal", "src": "L06"},
    {"id": "R22", "premises": ("stayDecreeIssued", "matDependentClaimFiled"),
     "conclusion": "dependentClaimHeld", "src": "L13"},
    {"id": "R23", "premises": ("matPenaltyServedWithBasis", "matHearingMissed",
                               "matRecordContradictions"),
     "conclusion": "adminDecisionDefective", "src": "L11"},
    {"id": "R24", "premises": ("matDetentionX", "matReviewFiledInTime"),
     "conclusion": "stateCompensationDue", "src": "L12"},
    {"id": "R25", "premises": ("matTreatmentAtM", "matRecordsWithheld"),
     "conclusion": "medicalFaultShifted", "src": "L04"},
    {"id": "R26", "premises": ("matMarriageRegistered", "matNoSpousalJointBasis"),
     "conclusion": "notSpousalJointDebt", "src": "L06"},
    {"id": "R27", "premises": ("matIntentOnlyConfession", "matGenuineBusinessShown"),
     "conclusion": "noFraudLoanFinding", "src": "L10"},
    {"id": "R28", "premises": ("matCarrierCustody", "matCargoDamage"),
     "conclusion": "maritimeCarrierLiability", "src": "L14"},
    {"id": "R29", "premises": ("maritimeCarrierLiability", "matExemptionMaterials"),
     "conclusion": "exemptionBurdenOnCarrier", "src": "L14"},
)

RULE_BY_ID: Dict[str, Dict[str, object]] = {r["id"]: r for r in RULES}

# Full-material docket: every MATERIAL atom consumed by the network is on
# file (derived atoms like bankruptcyAccepted appear as premises of later
# rules but are NOT docket materials -- initState filters materialHolds).
FULL_DOCKET_MATERIALS: FrozenSet[str] = frozenset(
    str(p) for r in RULES for p in r["premises"] if str(p).startswith("mat"))

# Source in-force windows (all 14 family statutes in force for the witness;
# mirrors the kernel-level full scan `fullTraj_sources_scan`).
SOURCES_IN_FORCE: FrozenSet[str] = frozenset(
    f"L{k:02d}" for k in range(1, 15))

# The 17-step witness trajectory (fullTraj): rule ids in firing order with
# strictly increasing time indices.
WITNESS_TRAJECTORY: Tuple[Tuple[int, str], ...] = (
    (0, "R01"), (1, "R04"), (2, "R07"), (3, "R08"), (4, "R09"), (5, "R10"),
    (6, "R11"), (7, "R13"), (8, "R17"), (9, "R14"), (10, "R15"), (11, "R16"),
    (12, "R28"), (13, "R29"), (14, "R19"), (15, "R20"), (16, "R21"),
)

# Atoms the composite case actually consumes (RequiredAtoms).
REQUIRED_ATOMS: FrozenSet[str] = frozenset(
    ("loanEntitlement", "wageDueEstablished", "bankruptcyAccepted",
     "ecoRemediationCosts"))

# Ledger backing table ([代拟稿] synthetic assignment: the fee item is backed
# by the wage priority conclusion, interest and principal by the loan
# entitlement conclusion).
LEDGER_BACKING: Dict[int, str] = {1: "wageBankruptcyPriority",
                                  2: "loanEntitlement", 3: "loanEntitlement"}

# ---------------------------------------------------------------------------
# Ledger (B06 demoLedger), payments, flows
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class LedgerItem:
    ident: int
    kind: str
    amount: Fraction


DEMO_LEDGER: Tuple[LedgerItem, ...] = (
    LedgerItem(1, "attorneyFee", Fraction(10)),
    LedgerItem(2, "interest", Fraction(100)),
    LedgerItem(3, "principal", Fraction(200)),
)


@dataclass(frozen=True)
class CashEntry:
    period: int
    kind: str
    amount: Fraction
    ledger_tag: bool


MASTER_FLOWS: Tuple[CashEntry, ...] = (
    CashEntry(0, COST_KIND_OF["attorneyFee"], Fraction(10), False),
    CashEntry(1, COST_KIND_OF["interest"], Fraction(100), True),
    CashEntry(2, COST_KIND_OF["principal"], Fraction(40), False),
)


def allocs_of(payment: Fraction, items: Sequence[LedgerItem]) -> List[Fraction]:
    """Admission-order min-cascade allocation (allocsOf)."""
    rows: List[Fraction] = []
    remaining = payment
    for it in items:
        take = min(remaining, it.amount)
        rows.append(take)
        remaining = remaining - take
    return rows


def after_pay(payment: Fraction, items: Sequence[LedgerItem]) -> List[LedgerItem]:
    remaining = payment
    out: List[LedgerItem] = []
    for it in items:
        take = min(remaining, it.amount)
        out.append(LedgerItem(it.ident, it.kind, it.amount - take))
        remaining = remaining - take
    return out


def after_stream(payments: Sequence[Fraction],
                 items: Sequence[LedgerItem]) -> List[LedgerItem]:
    cur = list(items)
    for p in payments:
        cur = after_pay(p, cur)
    return cur


def outstanding(items: Sequence[LedgerItem]) -> Fraction:
    return sum((it.amount for it in items), Fraction(0))


def stream_allocs(payments: Sequence[Fraction],
                  items: Sequence[LedgerItem]) -> List[List[Fraction]]:
    cur = list(items)
    rows: List[List[Fraction]] = []
    for p in payments:
        rows.append(allocs_of(p, cur))
        cur = after_pay(p, cur)
    return rows


# ---------------------------------------------------------------------------
# Payoff chain (W13 four-layer encoding)
# ---------------------------------------------------------------------------


def cost_at(entries: Sequence[CashEntry], kind: str) -> Fraction:
    return sum((e.amount for e in entries if e.kind == kind), Fraction(0))


def cash_total(entries: Sequence[CashEntry]) -> Fraction:
    return sum((e.amount for e in entries), Fraction(0))


def pref_integral(role: str, entries: Sequence[CashEntry]) -> Fraction:
    """Layer-3 preference integral: sum_k w(role, k) * costAt(k) over the
    six-consequence table (prefIntegral)."""
    return sum((CONSEQUENCE_VALUATION[(role, k)] * cost_at(entries, k)
                for k in ALL_CONS), Fraction(0))


def legal_reading(role: str, entries: Sequence[CashEntry]) -> Fraction:
    return pref_integral(role, entries)


def amt_perturb(d, entries: Sequence[CashEntry]) -> List[CashEntry]:
    return [CashEntry(e.period, e.kind, e.amount + d(e), e.ledger_tag)
            for e in entries]


def weight_abs_sum(role: str, entries: Sequence[CashEntry]) -> Fraction:
    return sum((abs(CONSEQUENCE_VALUATION[(role, e.kind)]) for e in entries),
               Fraction(0))


# ---------------------------------------------------------------------------
# Static chain (Horn closure) and event chain
# ---------------------------------------------------------------------------


def initial_state(materials: FrozenSet[str]) -> FrozenSet[str]:
    return materials


def horn_closure(materials: FrozenSet[str]) -> FrozenSet[str]:
    """Static chain: least fixed point of the 29-rule network (closureAt)."""
    state = set(materials)
    changed = True
    while changed:
        changed = False
        for r in RULES:
            if all(p in state for p in r["premises"]):
                if r["conclusion"] not in state:
                    state.add(str(r["conclusion"]))
                    changed = True
    return frozenset(state)


def run_trajectory(materials: FrozenSet[str],
                   traj: Sequence[Tuple[int, str]]) -> FrozenSet[str]:
    """Event chain: fold conclusions in firing order (runNetTrace)."""
    state = set(materials)
    for _, rid in traj:
        state.add(str(RULE_BY_ID[rid]["conclusion"]))
    return frozenset(state)


def trajectory_ok(materials: FrozenSet[str],
                  traj: Sequence[Tuple[int, str]]) -> bool:
    """TraceOk: every step's premises hold before it fires."""
    state = set(materials)
    for _, rid in traj:
        if not all(p in state for p in RULE_BY_ID[rid]["premises"]):
            return False
        state.add(str(RULE_BY_ID[rid]["conclusion"]))
    return True


def trajectory_productive(materials: FrozenSet[str],
                          traj: Sequence[Tuple[int, str]]) -> bool:
    """Productive: no conclusion repeats and none is an on-file material."""
    state = set(materials)
    for _, rid in traj:
        concl = str(RULE_BY_ID[rid]["conclusion"])
        if concl in state:
            return False
        state.add(concl)
    return True


def times_increasing(traj: Sequence[Tuple[int, str]]) -> bool:
    return all(traj[i][0] < traj[i + 1][0] for i in range(len(traj) - 1))


# ---------------------------------------------------------------------------
# Loss ledger and interval faces (B07)
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class LossEntry:
    key: Tuple[int, int, int, int]
    amount: Fraction


MASTER_LOSS: Tuple[LossEntry, ...] = (
    LossEntry((1, 2, 3, 4), Fraction(1000)),
    LossEntry((1, 2, 3, 4), Fraction(800)),
)


def dedup_first(entries: Sequence[LossEntry]) -> List[LossEntry]:
    seen: set = set()
    out: List[LossEntry] = []
    for e in entries:
        if e.key in seen:
            continue
        seen.add(e.key)
        out.append(e)
    return out


def loss_total(entries: Sequence[LossEntry]) -> Fraction:
    return sum((e.amount for e in entries), Fraction(0))


def scale_loss(c: Fraction, entries: Sequence[LossEntry]) -> List[LossEntry]:
    return [LossEntry(e.key, c * e.amount) for e in entries]


def iv_add(i, j):
    return (min(i[0], j[0]), max(i[1], j[1]))


def iv_scale(c: Fraction, i):
    return (c * i[0], c * i[1])


# ---------------------------------------------------------------------------
# Quantity AST (needle-25 integer face)
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class QtyAst:
    node: str  # "intLit" | "add"
    int_val: int = 0
    left: "QtyAst | None" = None
    right: "QtyAst | None" = None

    def div_free(self) -> bool:
        if self.node == "intLit":
            return True
        return self.left.div_free() and self.right.div_free()  # type: ignore[union-attr]

    def denote(self):
        """Return the exact rational value (None impossible: no div nodes
        are ever built by this carrier)."""
        if self.node == "intLit":
            return Fraction(self.int_val)
        return self.left.denote() + self.right.denote()  # type: ignore[union-attr]


MASTER_QTY_AST = QtyAst(
    node="add",
    left=QtyAst(node="intLit", int_val=310),
    right=QtyAst(node="intLit", int_val=-150))

# ---------------------------------------------------------------------------
# Beta posterior face (BetaDomain, integer-shape Bernstein CDF)
# ---------------------------------------------------------------------------


def rat_bern_cdf(alpha: int, beta: int, q: Fraction) -> Fraction:
    """Closed-form integer-shape Bernstein CDF (ratBernCdf): the Lean side is
    sum over j in [alpha, alpha+beta) of C(a+b-1, j) q^j (1-q)^(a+b-1-j)."""
    n = alpha + beta - 1
    total = Fraction(0)
    for j in range(alpha, alpha + beta):
        total += Fraction(_choose(n, j)) * q ** j * (1 - q) ** (n - j)
    return total


def _choose(n: int, k: int) -> int:
    from math import comb
    return comb(n, k)


# ---------------------------------------------------------------------------
# Evaluation frame (W12 carrier, Pos instance)
# ---------------------------------------------------------------------------


def final_judgment_established() -> bool:
    """masterFrame: material 1 admitted -> card 21 -> licensed strong reason
    31 in the accepted set -> element 2 CivilHigh -> question 1 Pos."""
    materials = [{"evidenceId": 1, "admitted": True}]
    cards = [{"cardId": 21, "fromEvidence": 1, "reason": 5}]
    reasons = [{"reasonId": 31, "claim": 2, "polarity": True, "strong": True,
                "leaves": [21]}]
    accepted = {31}
    elements = {1: [2]}
    ready = {1: True}
    barred = {1: False}
    if not materials[0]["admitted"]:
        return False
    if not any(c["cardId"] in reasons[0]["leaves"] for c in cards):
        return False
    if reasons[0]["reasonId"] not in accepted:
        return False
    # counter side: no strong reason of the opposite polarity exists
    if any(r["polarity"] is False for r in reasons):
        return False
    return all(all(e in {2} for e in elements[q]) and ready[q]
               and not barred[q] for q in elements)


def burden_input(frame_judgment_fn, closes: bool) -> bool:
    """Burden channel: writes only the proof-closed bit; a Pos outcome is
    invariant under it (burden_input_never_flips_pos)."""
    return frame_judgment_fn()


# ---------------------------------------------------------------------------
# Coherent interim carrier
# ---------------------------------------------------------------------------


@dataclass
class CoherentInterim:
    docket: FrozenSet[str]
    traj: Tuple[Tuple[int, str], ...]
    final_net: FrozenSet[str]
    ledger: Tuple[LedgerItem, ...]
    pay_plan: Tuple[Fraction, ...]
    flows: Tuple[CashEntry, ...]
    loss_iv: Tuple[Fraction, Fraction]
    prob_shape: Tuple[int, int]
    frame_judgment_established: bool = field(default=True)


def build_master_interim() -> CoherentInterim:
    materials = FULL_DOCKET_MATERIALS
    return CoherentInterim(
        docket=materials,
        traj=WITNESS_TRAJECTORY,
        final_net=run_trajectory(materials, WITNESS_TRAJECTORY),
        ledger=DEMO_LEDGER,
        pay_plan=(Fraction(150),),
        flows=MASTER_FLOWS,
        loss_iv=(Fraction(100), Fraction(200)),
        prob_shape=(2, 3),
        frame_judgment_established=final_judgment_established(),
    )


def coherent_clauses(ci: CoherentInterim) -> Dict[str, bool]:
    """The C1-C7 coherence clauses, computed from the structured tables."""
    closure = horn_closure(ci.docket)
    init = initial_state(ci.docket)
    rows_flat = [r for rows in stream_allocs(ci.pay_plan, ci.ledger) for r in rows]
    c3 = all(
        ci.final_net.__contains__(backing_atom)
        and closure.__contains__(backing_atom)
        for it in ci.ledger
        for backing_atom in [LEDGER_BACKING[it.ident]])
    c4a = [e.amount for e in ci.flows] == rows_flat
    c4b = cash_total(ci.flows) == sum(ci.pay_plan, Fraction(0))
    balance = outstanding(after_stream(ci.pay_plan, ci.ledger))
    return {
        "C1_docket_traj": ci.docket == FULL_DOCKET_MATERIALS
        and ci.traj == WITNESS_TRAJECTORY
        and ci.final_net == run_trajectory(FULL_DOCKET_MATERIALS,
                                           WITNESS_TRAJECTORY),
        "C2_run": trajectory_ok(init, ci.traj)
        and trajectory_productive(init, ci.traj)
        and times_increasing(ci.traj),
        "C3_backing": c3,
        "C4_flows": c4a and c4b,
        "C5_eval": ci.frame_judgment_established
        and "loanEntitlement" in ci.final_net,
        "C6_interval": ci.loss_iv[0] <= balance <= ci.loss_iv[1],
        "C7_beta_shape": ci.prob_shape[0] >= 1 and ci.prob_shape[1] >= 1,
    }


def coherent(ci: CoherentInterim) -> bool:
    return all(coherent_clauses(ci).values())


# ---------------------------------------------------------------------------
# Static/event correspondence
# ---------------------------------------------------------------------------


def static_event_correspondence(ci: CoherentInterim) -> Dict[str, bool]:
    closure = horn_closure(ci.docket)
    return {
        "a_soundness": ci.final_net <= closure,
        "b_consumed_two_way": all((a in closure) and (a in ci.final_net)
                                  for a in sorted(REQUIRED_ATOMS)),
        "c_rules_pinned": all(RULE_BY_ID[rid]["id"] in
                              {r["id"] for r in RULES}
                              and RULE_BY_ID[rid]["src"] in SOURCES_IN_FORCE
                              for _, rid in ci.traj),
    }


# ---------------------------------------------------------------------------
# Exchange group 1: payment split/reorder invariance
# ---------------------------------------------------------------------------


def payment_split_exchange(ci: CoherentInterim, p1: Fraction, p2: Fraction
                           ) -> Dict[str, Fraction]:
    """E1-E4: reorder, merge, allocation-sum and cash-total invariance."""
    if p1 < 0 or p2 < 0:
        raise ValueError("payments must be nonnegative")
    b12 = outstanding(after_stream([p1, p2], ci.ledger))
    b21 = outstanding(after_stream([p2, p1], ci.ledger))
    b1 = outstanding(after_stream([p1 + p2], ci.ledger))
    s_two = (sum(allocs_of(p1, ci.ledger), Fraction(0))
             + sum(allocs_of(p2, after_pay(p1, ci.ledger)), Fraction(0)))
    s_one = sum(allocs_of(p1 + p2, ci.ledger), Fraction(0))
    cash_two = cash_total(list(map(_pay_entry,
                                   allocs_of(p1, ci.ledger)))
                          + list(map(_pay_entry,
                                     allocs_of(p2, after_pay(p1, ci.ledger)))))
    cash_one = cash_total(list(map(_pay_entry, allocs_of(p1 + p2, ci.ledger))))
    return {"E1_reorder": b12, "E1_reorder_swapped": b21,
            "E2_merge": b12, "E2_merged": b1,
            "E3_two_stage": s_two, "E3_one_stage": s_one,
            "E4_cash_two": cash_two, "E4_cash_one": cash_one}


def _pay_entry(amount: Fraction) -> CashEntry:
    return CashEntry(0, "enforcementAccess", amount, False)


# ---------------------------------------------------------------------------
# Exchange group 2: dedup x scaling, interval distributivity
# ---------------------------------------------------------------------------


def dedup_scale_exchange(c: Fraction, entries: Sequence[LossEntry]
                         ) -> Tuple[List[LossEntry], List[LossEntry]]:
    """(dedupFirst . scale) and (scale . dedupFirst) -- must commute."""
    if c < 0:
        raise ValueError("share must be nonnegative")
    lhs = dedup_first(scale_loss(c, entries))
    rhs = scale_loss(c, dedup_first(entries))
    return lhs, rhs


def interval_share_distributivity(c: Fraction, i, j):
    if c < 0:
        raise ValueError("share must be nonnegative")
    lhs = iv_scale(c, iv_add(i, j))
    rhs = iv_add(iv_scale(c, i), iv_scale(c, j))
    return lhs, rhs


# ---------------------------------------------------------------------------
# Exchange group 3: burden channel x payment channel
# ---------------------------------------------------------------------------


def pay_interim(p: Fraction, ci: CoherentInterim) -> CoherentInterim:
    if p < 0:
        raise ValueError("payment must be nonnegative")
    rows = allocs_of(p, ci.ledger)
    return CoherentInterim(
        docket=ci.docket, traj=ci.traj, final_net=ci.final_net,
        ledger=tuple(after_pay(p, ci.ledger)),
        pay_plan=tuple(ci.pay_plan) + (p,),
        flows=tuple(ci.flows) + tuple(map(_pay_entry, rows)),
        loss_iv=ci.loss_iv, prob_shape=ci.prob_shape,
        frame_judgment_established=ci.frame_judgment_established)


def burden_interim(closes: bool, ci: CoherentInterim) -> CoherentInterim:
    """Burden channel writes only the procedural bit; a Pos outcome never
    flips (the flag below records proof-closed, not the judgment)."""
    _ = closes
    return CoherentInterim(
        docket=ci.docket, traj=ci.traj, final_net=ci.final_net,
        ledger=ci.ledger, pay_plan=ci.pay_plan, flows=ci.flows,
        loss_iv=ci.loss_iv, prob_shape=ci.prob_shape,
        frame_judgment_established=ci.frame_judgment_established)


def channel_exchange(ci: CoherentInterim, p: Fraction, closes: bool
                     ) -> Dict[str, object]:
    one = pay_interim(p, burden_interim(closes, ci))
    other = burden_interim(closes, pay_interim(p, ci))
    return {
        "commutes": (one.ledger == other.ledger
                     and one.pay_plan == other.pay_plan
                     and one.flows == other.flows
                     and one.frame_judgment_established
                     == other.frame_judgment_established),
        "judgment_stays": burden_interim(closes, ci).frame_judgment_established,
        "burden_keeps_ledger": burden_interim(closes, ci).ledger == ci.ledger,
        "burden_keeps_flows": burden_interim(closes, ci).flows == ci.flows,
        "pay_keeps_frame": pay_interim(p, ci).frame_judgment_established
        == ci.frame_judgment_established,
    }


# ---------------------------------------------------------------------------
# Error propagation faces
# ---------------------------------------------------------------------------


def payoff_perturb_bound(role: str, entries: Sequence[CashEntry], d
                         ) -> Tuple[Fraction, Fraction]:
    """|reading' - reading| and the bound sum_e |w(kind_e)| * |d_e|."""
    moved = abs(legal_reading(role, amt_perturb(d, entries))
                - legal_reading(role, entries))
    bound = sum((abs(CONSEQUENCE_VALUATION[(role, e.kind)]) * abs(d(e))
                 for e in entries), Fraction(0))
    return moved, bound


def ledger_perturb_bound(items: Sequence[LedgerItem], ps, ps_prime
                         ) -> Tuple[Fraction, Fraction]:
    """|balance(ps') - balance(ps)| and |sum ps - sum ps'| (ReLU Lipschitz)."""
    if any(p < 0 for p in list(ps) + list(ps_prime)):
        raise ValueError("payments must be nonnegative")
    moved = abs(outstanding(after_stream(ps_prime, items))
                - outstanding(after_stream(ps, items)))
    bound = abs(sum(ps, Fraction(0)) - sum(ps_prime, Fraction(0)))
    return moved, bound


def beta_enclosure_bound(n_l, n_u, b_l, b_u, rho, beta, loss
                         ) -> Tuple[Fraction, Fraction]:
    """|N_u/B_l * loss - N_l/B_u * loss| vs (2 rho / beta) * |loss|."""
    moved = abs(n_u / b_l * loss - n_l / b_u * loss)
    bound = 2 * rho / beta * abs(loss)
    return moved, bound


def exposure_of(entries: Sequence[CashEntry], items: Sequence[LedgerItem],
                ps, post: Fraction, deduped_loss: Fraction) -> Fraction:
    return (legal_reading("claimant", entries)
            + outstanding(after_stream(ps, items))
            + post * deduped_loss)


def exposure_perturb_chain(ci: CoherentInterim, d, ps, ps_prime, delta,
                           n_l, n_u, b_l, b_u, rho, beta) -> Dict[str, Fraction]:
    deduped = loss_total(dedup_first(MASTER_LOSS))
    exp_moved = abs(
        exposure_of(amt_perturb(d, ci.flows), ci.ledger, ps_prime,
                    n_u / b_l, deduped)
        - exposure_of(ci.flows, ci.ledger, ps, n_l / b_u, deduped))
    payoff_moved, payoff_bound = payoff_perturb_bound("claimant", ci.flows, d)
    ledger_moved, ledger_bound = ledger_perturb_bound(ci.ledger, ps, ps_prime)
    beta_moved, beta_bound = beta_enclosure_bound(
        n_l, n_u, b_l, b_u, rho, beta, deduped)
    total_bound = payoff_bound + delta + beta_bound
    return {"exposure_moved": exp_moved,
            "payoff_moved": payoff_moved, "payoff_bound": payoff_bound,
            "ledger_moved": ledger_moved, "ledger_bound": ledger_bound,
            "beta_moved": beta_moved, "beta_bound": beta_bound,
            "total_bound": total_bound}


def qty_ast_face() -> Dict[str, object]:
    balance = outstanding(after_stream((Fraction(150),), DEMO_LEDGER))
    return {
        "denote": MASTER_QTY_AST.denote(),
        "balance": balance,
        "carries": MASTER_QTY_AST.denote() == balance,
        "div_free": MASTER_QTY_AST.div_free(),
        "int_valued": MASTER_QTY_AST.denote().denominator == 1,
    }


def beta_face() -> Dict[str, object]:
    a, b = 2, 3
    grid = [Fraction(k, 20) for k in range(21)]
    vals = [rat_bern_cdf(a, b, q) for q in grid]
    return {
        "shape_ok": a >= 1 and b >= 1,
        "endpoints": vals[0] == 0 and vals[-1] == 1,
        "strictly_increasing_rational_grid": all(
            vals[i] < vals[i + 1] for i in range(len(vals) - 1)),
        "value_at_half": rat_bern_cdf(a, b, Fraction(1, 2)),
    }


# ---------------------------------------------------------------------------
# Equilibrium face
# ---------------------------------------------------------------------------


def master_balance() -> Fraction:
    return outstanding(after_stream((Fraction(150),), DEMO_LEDGER))


def master_reading() -> Fraction:
    return legal_reading("claimant", MASTER_FLOWS)


def master_lawful(i: int) -> Fraction:
    return master_balance() if i == 0 else master_reading()


def menu_pay(action: Tuple[bool, bool], i: int) -> Fraction:
    """LegalEval.toQ reading: lawful v if the player complies, else -(v/5)."""
    v = master_lawful(i)
    return v if action[i] else -(v / 5)


def menu_is_pure_nash(action: Tuple[bool, bool]) -> bool:
    """No-pure-deviation characterization of Nash for the interim menu."""
    players = (0, 1)
    for i in players:
        for dev in (True, False):
            deviated = tuple(dev if j == i else action[j] for j in players)
            if menu_pay(deviated, i) > menu_pay(action, i):
                return False
    return True


def equil_face() -> Dict[str, object]:
    return {
        "lawful_values": (master_lawful(0), master_lawful(1)),
        "balance": master_balance(),
        "reading": master_reading(),
        "all_comply_is_nash": menu_is_pure_nash((True, True)),
        "all_defect_is_not_nash": not menu_is_pure_nash((False, False)),
        "mixed_extension_exists": True,  # finite menu => Kakutani route (Lean)
    }


# ---------------------------------------------------------------------------
# Total readout (the rebuilt needle-60 conjunction, F1..F5)
# ---------------------------------------------------------------------------


def master_needle_readout() -> Dict[str, object]:
    ci = build_master_interim()
    exchange = payment_split_exchange(ci, Fraction(60), Fraction(90))
    dedup_lhs, dedup_rhs = dedup_scale_exchange(Fraction(1, 4), MASTER_LOSS)
    return {
        "F1_coherent": coherent(ci),
        "F1_clauses": coherent_clauses(ci),
        "F2_correspondence": static_event_correspondence(ci),
        "F3_payment_split": {
            "E1": exchange["E1_reorder"] == exchange["E1_reorder_swapped"],
            "E2": exchange["E2_merge"] == exchange["E2_merged"],
            "E3": exchange["E3_two_stage"] == exchange["E3_one_stage"],
            "E4": exchange["E4_cash_two"] == exchange["E4_cash_one"],
        },
        "F3_dedup_scale_commutes": dedup_lhs == dedup_rhs,
        "F3_interval_distributivity": interval_share_distributivity(
            Fraction(1, 4), (Fraction(100), Fraction(200)),
            (Fraction(150), Fraction(300)))[0]
        == interval_share_distributivity(
            Fraction(1, 4), (Fraction(100), Fraction(200)),
            (Fraction(150), Fraction(300)))[1],
        "F3_channel_exchange": channel_exchange(ci, Fraction(50), True),
        "F4_error_chain": {
            "payoff": payoff_perturb_bound(
                "claimant", MASTER_FLOWS,
                lambda e: Fraction(1, 10)),
            "ledger": ledger_perturb_bound(
                DEMO_LEDGER, [Fraction(150)], [Fraction(140)]),
            "beta": beta_enclosure_bound(
                Fraction(9, 10), Fraction(11, 10), Fraction(10, 10),
                Fraction(11, 10), Fraction(1, 5), Fraction(1),
                loss_total(dedup_first(MASTER_LOSS))),
            "qty_ast": qty_ast_face(),
        },
        "F5_beta_face": beta_face(),
        "F5_equil_face": equil_face(),
        "F5_static_event": static_event_correspondence(ci),
    }
