"""Unified quantity-ledger reference (W2-A batch B06/B07 shared substrate).

Mirror of the Lean module ``JurisLean.Seams.UnifiedQuantLedger`` — the shared
quantity-ledger + legal-interval construction consumed by demand batches B06
(组06 D047–D056 借贷/担保) and B07 (组07 D057–D064 侵权), same-source with
W2-B N01/N02.  Every amount is a :class:`fractions.Fraction`, every day/id is
an ``int``; no float ever enters an amount (repo LegalTech rule 2).

Sections (one-to-one with the Lean file):

1.  units and tagged quantities (value-level unit discipline);
2.  itemized debt ledger: admission-order allocation, per-payment bounds,
    trackable balances, stream legality (distinct payment ids);
3.  loan charges: term interest / overdue interest / penalty as separate
    components, exact segmented accrual, policy cap, compounding;
4.  collateral: creation-event gating per security kind, priority
    distribution of liquidation proceeds;
5.  intervals: endpoint algebra over ℚ (nonnegative scale, negation,
    subtraction, intersection, containment) plus legal tags
    (loss / cause / fault) enforced at the type level;
6.  establishment gates and shares; several / joint / supplementary modes
    with the external total constraint and the internal recourse pool;
7.  loss ledger: first-seen dedup by (event, beneficiary, item, time);
8.  remedies (non-monetary carry no amount) and same-scenario witnesses;
9.  lightweight fact admission / tort-candidate partition / imputation gate.

The allocation core reuses ``tools/unified_math_v2/unified/quantities.py``
(``allocate_payment``, the §6.5 waterfall) exactly as the Lean side reuses
``JurisLean.Seams.UnifiedQuantities.waterfall``; everything else is local.
"""
from __future__ import annotations

from dataclasses import dataclass, field
from fractions import Fraction
from typing import Dict, List, Optional, Sequence, Tuple

from tools.unified_math_v2.unified.quantities import allocate_payment

F = Fraction

# ---------------------------------------------------------------------------
# 1. Units and tagged quantities (value-level discipline; Lean: TIv tags)
# ---------------------------------------------------------------------------

DIMS = ("money", "share", "days")


class UnitError(ValueError):
    """Incompatible-unit arithmetic refused (100元 + 3米 is an error, not a
    silent coercion)."""


@dataclass(frozen=True)
class Unit:
    dim: str                 # money | share | days
    item: int = 0            # debt item id
    subj: int = 0            # subject / beneficiary
    period: int = 0          # period id
    canon: int = 0           # computation canon

    def __post_init__(self) -> None:
        if self.dim not in DIMS:
            raise ValueError(f"unknown dimension: {self.dim}")


@dataclass(frozen=True)
class Qty:
    val: Fraction
    unit: Unit

    def __post_init__(self) -> None:
        if type(self.val) is not Fraction:
            raise TypeError("amounts must be Fractions")

    def plus(self, other: "Qty") -> "Qty":
        if self.unit != other.unit:
            raise UnitError(
                f"unit mismatch: {self.unit} + {other.unit}")
        return Qty(self.val + other.val, self.unit)

    def scaled(self, c: Fraction) -> "Qty":
        if type(c) is not Fraction or c < 0:
            raise ValueError("scale factor must be a nonnegative Fraction")
        return Qty(self.val * c, self.unit)


# ---------------------------------------------------------------------------
# 2. Itemized debt ledger (D047/D048/D056)
# ---------------------------------------------------------------------------

KIND_PRINCIPAL = "principal"
KIND_INTEREST = "interest"
KIND_OVERDUE = "overdueInterest"
KIND_PENALTY = "penalty"
KIND_ATTORNEY = "attorneyFee"
KIND_COURT = "courtFee"
KIND_PRESERVATION = "preservationFee"
DEBT_KINDS = (
    KIND_PRINCIPAL, KIND_INTEREST, KIND_OVERDUE, KIND_PENALTY,
    KIND_ATTORNEY, KIND_COURT, KIND_PRESERVATION,
)

BASIS_CONTRACT = "contractStip"
BASIS_STATUTORY = "statutory"
BASIS_COURT = "courtOrder"
BASIS_SELF = "selfQuoted"
FEE_BASES = (BASIS_CONTRACT, BASIS_STATUTORY, BASIS_COURT, BASIS_SELF)

STATUS_CLAIMED = "claimed"
STATUS_SUPPORTED = "supported"
STATUS_UNSUPPORTED = "unsupported"
CLAIM_STATUSES = (STATUS_CLAIMED, STATUS_SUPPORTED, STATUS_UNSUPPORTED)


@dataclass(frozen=True)
class LedgerItem:
    ident: int
    kind: str
    basis: str
    beneficiary: int
    status: str
    amount: Fraction

    def __post_init__(self) -> None:
        if self.kind not in DEBT_KINDS:
            raise ValueError(f"unknown debt kind: {self.kind}")
        if self.basis not in FEE_BASES:
            raise ValueError(f"unknown fee basis: {self.basis}")
        if self.status not in CLAIM_STATUSES:
            raise ValueError(f"unknown claim status: {self.status}")
        if type(self.amount) is not Fraction or self.amount < 0:
            raise ValueError("amount must be a nonnegative Fraction")


def li_amounts(items: Sequence[LedgerItem]) -> List[Fraction]:
    return [it.amount for it in items]


def outstanding(items: Sequence[LedgerItem]) -> Fraction:
    return sum(li_amounts(items), F(0))


def _waterfall(payment: Fraction, amounts: Sequence[Fraction]) -> List[Fraction]:
    """Admission-order allocation — the §6.5 waterfall reused from the
    unified v2 quantities module (groups of one), exactly as the Lean side
    reuses ``UnifiedQuantities.waterfall``."""

    alloc = allocate_payment(payment, [[a] for a in amounts])
    return [row[0] for row in alloc.allocations]


def allocs_of(payment: Fraction, items: Sequence[LedgerItem]) -> List[Fraction]:
    if type(payment) is not Fraction or payment < 0:
        raise ValueError("payment must be a nonnegative Fraction")
    return _waterfall(payment, li_amounts(items))


def after_pay(payment: Fraction, items: Sequence[LedgerItem]) -> List[LedgerItem]:
    """Identity-preserving ledger after one payment (balance tracking)."""

    allocs = allocs_of(payment, items)
    return [
        LedgerItem(it.ident, it.kind, it.basis, it.beneficiary, it.status,
                   it.amount - a)
        for it, a in zip(items, allocs)
    ]


def after_stream(payments: Sequence[Fraction],
                 items: Sequence[LedgerItem]) -> List[LedgerItem]:
    cur = list(items)
    for p in payments:
        cur = after_pay(p, cur)
    return cur


def stream_allocs(payments: Sequence[Fraction],
                  items: Sequence[LedgerItem]) -> List[List[Fraction]]:
    rows: List[List[Fraction]] = []
    cur = list(items)
    for p in payments:
        rows.append(allocs_of(p, cur))
        cur = after_pay(p, cur)
    return rows


def outstanding_after_stream(payments: Sequence[Fraction],
                             items: Sequence[LedgerItem]) -> Fraction:
    """max(due − paid, 0) — the clamped end-to-end balance (Lean
    ``outstanding_afterStream``)."""

    paid = sum(payments, F(0))
    due = outstanding(items)
    return max(due - paid, F(0))


def stream_legal(payments: Sequence[Tuple[int, Fraction]]) -> bool:
    """Distinct payment ids (no double-counted payment) and nonnegative
    amounts."""

    ids = [pid for pid, _ in payments]
    return len(ids) == len(set(ids)) and all(
        type(a) is Fraction and a >= 0 for _, a in payments)


def fee_supported(basis: str) -> bool:
    return basis != BASIS_SELF


def status_consistent(it: LedgerItem) -> bool:
    """A `supported` claim status requires a supporting basis; a self-quoted
    attorney-fee basis cannot be auto-supported (D056 counterexample)."""

    return it.status != STATUS_SUPPORTED or fee_supported(it.basis)


def sum_where_beneficiary(b: int, items: Sequence[LedgerItem]) -> Fraction:
    return sum((it.amount for it in items if it.beneficiary == b), F(0))


def sum_filter_partition(f, items: Sequence[LedgerItem]) -> bool:
    """Two-way Bool partition conserves the total (D053/D056 grouping)."""

    yes = sum((it.amount for it in items if f(it)), F(0))
    no = sum((it.amount for it in items if not f(it)), F(0))
    return yes + no == outstanding(items)


def loan_ledger(delivered: bool, ident: int, principal: Fraction) -> List[LedgerItem]:
    """Only a delivered loan enters the ledger (D047)."""

    if not delivered:
        return []
    return [LedgerItem(ident, KIND_PRINCIPAL, BASIS_STATUTORY, 0,
                       STATUS_SUPPORTED, principal)]


# ---------------------------------------------------------------------------
# 3. Loan charges: segments, components, policy cap, compounding (D049)
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class InterestSeg:
    base: Fraction
    rate: Fraction
    days: int
    denom: int

    def __post_init__(self) -> None:
        if type(self.base) is not Fraction or type(self.rate) is not Fraction:
            raise TypeError("base/rate must be Fractions")
        if type(self.days) is not int or self.days < 0:
            raise ValueError("days must be a nonnegative int")
        if type(self.denom) is not int or self.denom <= 0:
            raise ValueError("denom must be a positive int (day-count "
                             "convention, e.g. 365/360)")

    def interest(self) -> Fraction:
        """base × rate × days / denom — exact; no rounding inside a segment."""

        return self.base * self.rate * F(self.days, self.denom)


def seg_split_total(seg: InterestSeg, d1: int) -> Tuple[Fraction, Fraction]:
    """Split the segment at day d1: the two parts sum to the whole
    (Lean ``seg_split``)."""

    d2 = seg.days - d1
    if d1 < 0 or d2 < 0:
        raise ValueError("split point out of segment")
    left = InterestSeg(seg.base, seg.rate, d1, seg.denom)
    right = InterestSeg(seg.base, seg.rate, d2, seg.denom)
    return left.interest(), right.interest()


@dataclass(frozen=True)
class LoanCharges:
    principal: Fraction
    denom: int
    term_rate: Fraction
    term_days: int
    overdue_rate: Fraction
    overdue_days: int
    penalty_rate: Fraction
    penalty_days: int


def term_interest(c: LoanCharges) -> Fraction:
    return InterestSeg(c.principal, c.term_rate, c.term_days, c.denom).interest()


def overdue_interest(c: LoanCharges) -> Fraction:
    return InterestSeg(c.principal, c.overdue_rate, c.overdue_days,
                       c.denom).interest()


def penalty_charge(c: LoanCharges) -> Fraction:
    return InterestSeg(c.principal, c.penalty_rate, c.penalty_days,
                       c.denom).interest()


def total_charges(c: LoanCharges) -> Fraction:
    return term_interest(c) + overdue_interest(c) + penalty_charge(c)


def charges_within(cap: Fraction, c: LoanCharges) -> bool:
    """Composition subject to the applicable policy cap (the cap value is
    policy data)."""

    return total_charges(c) <= cap


def capitalize(b: Fraction, r: Fraction, days: int, denom: int) -> Fraction:
    return b + InterestSeg(b, r, days, denom).interest()


def compound_two_periods(b: Fraction, r: Fraction, d1: int, d2: int,
                         denom: int) -> Tuple[Fraction, Fraction]:
    """(compound over both periods, simple parts + interest-on-interest) —
    the two are equal (Lean ``compound_two_periods``)."""

    inner = InterestSeg(b, r, d1, denom).interest()
    compound = capitalize(capitalize(b, r, d1, denom), r, d2, denom)
    parts = (capitalize(b, r, d1, denom)
             + InterestSeg(b, r, d2, denom).interest()
             + InterestSeg(inner, r, d2, denom).interest())
    return compound, parts


# ---------------------------------------------------------------------------
# 4. Collateral: creation events and priority (D050/D051)
# ---------------------------------------------------------------------------

SEC_SURETYSHIP = "suretyship"
SEC_MORTGAGE = "mortgage"
SEC_PLEDGE = "pledge"
SEC_KINDS = (SEC_SURETYSHIP, SEC_MORTGAGE, SEC_PLEDGE)

EV_SIGNED = "signed"
EV_REGISTERED = "registered"
EV_DELIVERED = "delivered"
EV_RESOLUTION = "boardResolution"
SEC_EVENTS = (EV_SIGNED, EV_REGISTERED, EV_DELIVERED, EV_RESOLUTION)


def required_event(kind: str) -> str:
    """[代拟稿] creation-event baseline: suretyship—contract; mortgage—
    registration; pledge—delivery."""

    return {
        SEC_SURETYSHIP: EV_SIGNED,
        SEC_MORTGAGE: EV_REGISTERED,
        SEC_PLEDGE: EV_DELIVERED,
    }[kind]


def sec_established(kind: str, events: Sequence[str]) -> bool:
    return required_event(kind) in events


def corp_surety_established(events: Sequence[str]) -> bool:
    return EV_RESOLUTION in events and EV_SIGNED in events


def distribute_proceeds(claims: Sequence[Fraction],
                        proceeds: Fraction) -> Tuple[List[Fraction], Fraction]:
    """Priority distribution of liquidation proceeds down the claim list
    (waterfall); returns (per-claim recoveries, leftover proceeds)."""

    if type(proceeds) is not Fraction or proceeds < 0:
        raise ValueError("proceeds must be a nonnegative Fraction")
    alloc = allocate_payment(proceeds, [[c] for c in claims])
    return [row[0] for row in alloc.allocations], alloc.remaining


# ---------------------------------------------------------------------------
# 5. Intervals: endpoint algebra + legal tags (B07 / N02 same-source)
# ---------------------------------------------------------------------------


class IvQ:
    """Closed interval with ordered ℚ endpoints (Lean ``Iv``)."""

    __slots__ = ("lo", "hi")

    def __init__(self, lo: Fraction, hi: Fraction) -> None:
        if type(lo) is not Fraction or type(hi) is not Fraction:
            raise TypeError("endpoints must be Fractions")
        if lo > hi:
            raise ValueError("interval endpoints out of order")
        self.lo, self.hi = lo, hi

    def mem(self, x: Fraction) -> bool:
        return self.lo <= x <= self.hi

    def __eq__(self, other: object) -> bool:
        return (isinstance(other, IvQ) and self.lo == other.lo
                and self.hi == other.hi)

    def __repr__(self) -> str:
        return f"IvQ({self.lo}, {self.hi})"


def v_add(a: IvQ, b: IvQ) -> IvQ:
    return IvQ(a.lo + b.lo, a.hi + b.hi)


def v_neg(a: IvQ) -> IvQ:
    return IvQ(-a.hi, -a.lo)


def v_sub(a: IvQ, b: IvQ) -> IvQ:
    return v_add(a, v_neg(b))


def v_scale(c: Fraction, a: IvQ) -> IvQ:
    if type(c) is not Fraction or c < 0:
        raise ValueError("scale factor must be a nonnegative Fraction")
    return IvQ(c * a.lo, c * a.hi)


def v_inter(a: IvQ, b: IvQ) -> Optional[IvQ]:
    """Fail-closed intersection: None when the intervals are disjoint."""

    lo, hi = max(a.lo, b.lo), min(a.hi, b.hi)
    if lo > hi:
        return None
    return IvQ(lo, hi)


def v_contained(a: IvQ, b: IvQ) -> bool:
    """a ⊆ b."""

    return b.lo <= a.lo and a.hi <= b.hi


TAG_LOSS = "loss"
TAG_CAUSE = "cause"
TAG_FAULT = "fault"
IV_TAGS = (TAG_LOSS, TAG_CAUSE, TAG_FAULT)


class TagIv:
    """Legal-tagged interval — cross-tag operations raise (the type-level
    discipline of Lean ``TIv`` at value level)."""

    __slots__ = ("tag", "iv")

    def __init__(self, tag: str, iv: IvQ) -> None:
        if tag not in IV_TAGS:
            raise ValueError(f"unknown interval tag: {tag}")
        self.tag, self.iv = tag, iv

    @staticmethod
    def _same(a: "TagIv", b: "TagIv") -> None:
        if a.tag != b.tag:
            raise TypeError(f"cross-tag interval operation: {a.tag} vs {b.tag}")

    def plus(self, other: "TagIv") -> "TagIv":
        TagIv._same(self, other)
        return TagIv(self.tag, v_add(self.iv, other.iv))

    def scaled(self, c: Fraction) -> "TagIv":
        return TagIv(self.tag, v_scale(c, self.iv))

    def fault_ok(self) -> bool:
        """Fault-share well-formedness: endpoints within [0, 1]."""

        return (self.tag == TAG_FAULT and self.iv.lo >= 0
                and self.iv.hi <= 1)


def cause_times_loss(ci: TagIv, li: TagIv) -> TagIv:
    """cause × loss → loss (four-endpoint product; the sharing interval)."""

    if ci.tag != TAG_CAUSE or li.tag != TAG_LOSS:
        raise TypeError("cause_times_loss needs (cause, loss) tags")
    products = [x * y for x in (ci.iv.lo, ci.iv.hi)
                for y in (li.iv.lo, li.iv.hi)]
    return TagIv(TAG_LOSS, IvQ(min(products), max(products)))


# ---------------------------------------------------------------------------
# 6. Gates, shares and liability modes (D059/D060/D062)
# ---------------------------------------------------------------------------


def legal_shares(gates: Sequence[bool], shares: Sequence[Fraction]) -> bool:
    """Gate closed ⇒ zero share; shares nonnegative; all gates open ⇒
    shares sum to one (D059)."""

    if len(gates) != len(shares):
        return False
    for g, s in zip(gates, shares):
        if type(s) is not Fraction or s < 0:
            return False
        if (not g) and s != 0:
            return False
    if all(gates) and sum(shares, F(0)) != 1:
        return False
    return True


MODE_SEVERAL = "several"
MODE_JOINT = "joint"
MODE_SUPP = "supplementary"
RESP_MODES = (MODE_SEVERAL, MODE_JOINT, MODE_SUPP)


def external_due(mode: str, loss: Fraction, internal_share: Fraction,
                 primary_due: Fraction, secondary_due: Fraction) -> Fraction:
    if mode == MODE_SEVERAL:
        return internal_share
    if mode == MODE_JOINT:
        return loss
    if mode == MODE_SUPP:
        return min(max(loss - primary_due, F(0)), secondary_due)
    raise ValueError(f"unknown mode: {mode}")


def pays_sum_base(base: Fraction, shares: Sequence[Fraction]) -> Fraction:
    return sum((s * base for s in shares), F(0))


def joint_recovery_ok(loss: Fraction, recoveries: Sequence[Fraction]) -> bool:
    """External total constraint: total recoveries never exceed the loss."""

    return sum(recoveries, F(0)) <= loss


def recourse_of(paid: Fraction, internal_share: Fraction) -> Fraction:
    return max(paid - internal_share, F(0))


def deficit_of(paid: Fraction, internal_share: Fraction) -> Fraction:
    return max(internal_share - paid, F(0))


def recourse_pool_balanced(paid: Sequence[Fraction],
                           internal_shares: Sequence[Fraction]) -> bool:
    """Σ paid = Σ shares ⇒ Σ recourse = Σ deficit (the internal recourse
    pool is exactly the deficit pool — no fabricated recourse)."""

    if sum(paid, F(0)) != sum(internal_shares, F(0)):
        return False
    left = sum((recourse_of(p, s) for p, s in zip(paid, internal_shares)), F(0))
    right = sum((deficit_of(p, s) for p, s in zip(paid, internal_shares)), F(0))
    return left == right


def supp_distribution(primary_due: Fraction, secondary_due: Fraction,
                      loss: Fraction) -> Tuple[Fraction, Fraction]:
    """Supplementary liability: the secondary party pays only the unpaid
    remainder, capped by its own due."""

    rows, _ = distribute_proceeds([primary_due, secondary_due], loss)
    return rows[0], rows[1]


# ---------------------------------------------------------------------------
# 7. Loss ledger: first-seen dedup + aggregation (D061)
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class LossEntry:
    event: int
    beneficiary: int
    item: int
    time: int
    amount: Fraction

    def __post_init__(self) -> None:
        if type(self.amount) is not Fraction or self.amount < 0:
            raise ValueError("loss amount must be a nonnegative Fraction")

    @property
    def key(self) -> Tuple[int, int, int, int]:
        return (self.event, self.beneficiary, self.item, self.time)


def loss_total(entries: Sequence[LossEntry]) -> Fraction:
    return sum((e.amount for e in entries), F(0))


def dedup_first(entries: Sequence[LossEntry]) -> List[LossEntry]:
    """Keep the first occurrence per key — an invoice amount and an
    appraisal of the same loss are counted once."""

    seen = set()
    out: List[LossEntry] = []
    for e in entries:
        if e.key not in seen:
            seen.add(e.key)
            out.append(e)
    return out


# ---------------------------------------------------------------------------
# 8. Remedies and scenario witnesses (D063/D064)
# ---------------------------------------------------------------------------

REMEDY_RESTITUTION = "restitution"
REMEDY_CESSATION = "cessation"
REMEDY_APOLOGY = "apology"


def amount_of(remedy) -> Optional[Fraction]:
    """Non-monetary remedies carry no amount (None, never a fake 0)."""

    if isinstance(remedy, Fraction):
        return remedy
    return None


def monetary_total(remedies: Sequence) -> Fraction:
    return sum((r for r in remedies if isinstance(r, Fraction)), F(0))


@dataclass(frozen=True)
class ScenarioWitness:
    scen_id: int
    ratios: Tuple[Fraction, ...]
    values: Tuple[Fraction, ...]


@dataclass(frozen=True)
class SummaryRecord:
    scen_id: int
    ratios: Tuple[Fraction, ...]
    values: Tuple[Fraction, ...]
    limit: Fraction

    def from_same_witness(self, w: ScenarioWitness) -> bool:
        return (self.scen_id == w.scen_id and self.ratios == w.ratios
                and self.values == w.values)


# ---------------------------------------------------------------------------
# 9. Lightweight admission / tort partition / imputation (D055/D057/D058)
# ---------------------------------------------------------------------------


def admitted_fact(cand: Tuple[bool, int]) -> bool:
    """(sourced?, id) — fail-closed: unsourced candidates never admit."""

    return cand[0]


def tort_partition(cands: Sequence[Tuple[str, bool]]):
    """Element-based selection with an open residual bucket (D057)."""

    selected = [c for c in cands if c[1]]
    residual = [c for c in cands if not c[1]]
    return selected, residual


def imputed(legal_gate: bool, cause_lo: Fraction) -> bool:
    """Legal imputation needs an open gate AND a strictly positive causal
    measure — statistical strength alone never imputes (D058)."""

    return legal_gate and cause_lo > 0


# ---------------------------------------------------------------------------
# The B06 consumption witness (mirrors the Lean demoLedger readout)
# ---------------------------------------------------------------------------

STAT_RANK = {
    KIND_ATTORNEY: 0, KIND_COURT: 0, KIND_PRESERVATION: 0,
    KIND_INTEREST: 1, KIND_OVERDUE: 2, KIND_PENALTY: 3, KIND_PRINCIPAL: 4,
}


def rank_ordered(items: Sequence[LedgerItem]) -> bool:
    ranks = [STAT_RANK[it.kind] for it in items]
    return all(a <= b for a, b in zip(ranks, ranks[1:]))


DEMO_LEDGER: Tuple[LedgerItem, ...] = (
    LedgerItem(1, KIND_ATTORNEY, BASIS_STATUTORY, 0, STATUS_SUPPORTED, F(10)),
    LedgerItem(2, KIND_INTEREST, BASIS_CONTRACT, 0, STATUS_SUPPORTED, F(100)),
    LedgerItem(3, KIND_PRINCIPAL, BASIS_CONTRACT, 0, STATUS_SUPPORTED, F(200)),
)
