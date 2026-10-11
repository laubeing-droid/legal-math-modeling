"""Payoff-chain and lawView use-point reference for needles 28 and 48 (W1-13).

Needle 28 (appendix I:782, S4 ``legal_payoff_preserved``): Z1 audit
(docs/full-math/NEEDLE_STRENGTH_AUDIT.md, needle-28 row) judged the old
delivery a "fixed legal status congruence" — cash preservation and payoff
preservation were two INDEPENDENT conjuncts and the preference-integral
structure was missing entirely.  This module is the four-layer encoding
chain:

    cash-flow entries -> cost aggregation (per consequence kind)
                      -> preference integral (weighted sum over the finite
                          discrete preference vector, exact Fraction)
                      -> legal payoff reading (anchor payoff_of on status
                          vectors; legal_reading = the integral itself for
                          general flows).

Needle 48 (appendix I:802, XT ``legal_time_nonanticipation``): the old
delivery carried the view discipline as an EXTERNAL premise ``hview`` plus
one definition-level sample.  This module evaluates the REAL 29-rule body
network (mirrored from UnifiedFourteenFamilies) on docket states read
through the truncated view ``law_view`` (= Temporal.trunc), and the
per-rule use points are computed facts:

- every premise material read of R01/R23/R19 equals its view read;
- each rule body's evaluation is future-blind (appending events dated
  after the as-of point changes nothing);
- the three rules fire on the witness ledger through the view and are
  blocked when the needed material is out of window.

Lean contract: proofs/lean/juris_lean/JurisLean/Seams/UnifiedPayoffChain.lean
(namespace JurisLean.Seams.UnifiedPayoffChain).  Independent checker:
tools/full_math/implementation/payoffchain_check.py (shares only the
frozen carriers below; every predicate is re-implemented inline).
"""
from __future__ import annotations

from dataclasses import dataclass, replace
from enum import Enum
from fractions import Fraction
from typing import Dict, FrozenSet, Iterable, List, Tuple

# ===========================================================================
# Frozen carriers — needle 28 (mirror of PayoffEquilibrium.lean carriers;
# valuation numbers are the anchor's [代拟稿] declared table)
# ===========================================================================


class LegalStatus(Enum):
    UPHELD = "upheld"
    PARTIALLY_UPHELD = "partiallyUpheld"
    DISMISSED = "dismissed"
    UNENFORCEABLE = "unenforceable"


class Role(Enum):
    CLAIMANT = "claimant"
    RESPONDENT = "respondent"


class Consequence(Enum):
    COST_BURDEN_LOSER = "costBurdenLoser"
    COST_BURDEN_PARTIAL = "costBurdenPartial"
    COST_OWN_ON_DISMISS = "costOwnOnDismiss"
    NO_TITLE_NO_COST = "noTitleNoCost"
    ENFORCEMENT_ACCESS = "enforcementAccess"
    RES_JUDICATA = "resJudicata"


#: Finite discrete preference vector: the anchor's per-role valuation of the
#: six monetized consequence kinds (PayoffEquilibrium.consequenceValuation).
CONSEQUENCE_VALUATION: Dict[Tuple[Role, Consequence], Fraction] = {
    (Role.CLAIMANT, Consequence.COST_BURDEN_LOSER): Fraction(3),
    (Role.CLAIMANT, Consequence.COST_BURDEN_PARTIAL): Fraction(1),
    (Role.CLAIMANT, Consequence.COST_OWN_ON_DISMISS): Fraction(-3),
    (Role.CLAIMANT, Consequence.NO_TITLE_NO_COST): Fraction(0),
    (Role.CLAIMANT, Consequence.ENFORCEMENT_ACCESS): Fraction(2),
    (Role.CLAIMANT, Consequence.RES_JUDICATA): Fraction(2),
    (Role.RESPONDENT, Consequence.COST_BURDEN_LOSER): Fraction(-3),
    (Role.RESPONDENT, Consequence.COST_BURDEN_PARTIAL): Fraction(-1),
    (Role.RESPONDENT, Consequence.COST_OWN_ON_DISMISS): Fraction(0),
    (Role.RESPONDENT, Consequence.NO_TITLE_NO_COST): Fraction(0),
    (Role.RESPONDENT, Consequence.ENFORCEMENT_ACCESS): Fraction(-2),
    (Role.RESPONDENT, Consequence.RES_JUDICATA): Fraction(-2),
}

#: Consequence kinds hung on each declared status (declaredConsequences).
DECLARED_CONSEQUENCES: Dict[LegalStatus, Tuple[Consequence, ...]] = {
    LegalStatus.UPHELD: (Consequence.COST_BURDEN_LOSER,
                         Consequence.ENFORCEMENT_ACCESS,
                         Consequence.RES_JUDICATA),
    LegalStatus.PARTIALLY_UPHELD: (Consequence.COST_BURDEN_PARTIAL,
                                   Consequence.ENFORCEMENT_ACCESS),
    LegalStatus.DISMISSED: (Consequence.COST_OWN_ON_DISMISS,),
    LegalStatus.UNENFORCEABLE: (Consequence.NO_TITLE_NO_COST,),
}

#: The full six-kind index (allCons).
ALL_CONS: Tuple[Consequence, ...] = (
    Consequence.COST_BURDEN_LOSER,
    Consequence.COST_BURDEN_PARTIAL,
    Consequence.COST_OWN_ON_DISMISS,
    Consequence.NO_TITLE_NO_COST,
    Consequence.ENFORCEMENT_ACCESS,
    Consequence.RES_JUDICATA,
)


@dataclass(frozen=True)
class CashEntry:
    """Layer-1 cash-flow entry: period + consequence kind + amount (exact
    Fraction, sign gives direction) + a bookkeeping bit no downstream layer
    reads (ledger_tag)."""

    period: int
    kind: Consequence
    amount: Fraction
    ledger_tag: bool


@dataclass(frozen=True)
class PayFlow:
    """Actual consequence cash-flow record: entries + declared status +
    docket bit (shape follows UnifiedNeedlesS4.CashFlow)."""

    entries: Tuple[CashEntry, ...]
    declared_status: LegalStatus
    docket: bool


# ---------------------------------------------------------------------------
# Layer maps: cash -> costs -> preference integral -> legal payoff reading
# ---------------------------------------------------------------------------


def cost_at(entries: Iterable[CashEntry], k: Consequence) -> Fraction:
    """Layer-2 encoding map: per-kind aggregation (finite discrete cost
    vector component)."""

    total = Fraction(0)
    for e in entries:
        if e.kind == k:
            total += e.amount
    return total


def cost_total(entries: Tuple[CashEntry, ...]) -> Fraction:
    """Cost-vector direct sum (unweighted total)."""

    return sum((cost_at(entries, k) for k in ALL_CONS), Fraction(0))


def cash_total(entries: Tuple[CashEntry, ...]) -> Fraction:
    """Layer-1 actual folding: entry sum (unweighted)."""

    return sum((e.amount for e in entries), Fraction(0))


def pref_integral(role: Role, entries: Tuple[CashEntry, ...]) -> Fraction:
    """Layer-3 encoding map: weighted sum over the finite discrete preference
    vector — sum_k valuation(role, k) * cost_at(k)."""

    return sum((CONSEQUENCE_VALUATION[(role, k)] * cost_at(entries, k)
                for k in ALL_CONS), Fraction(0))


def legal_payoff(role: Role, status: LegalStatus) -> Fraction:
    """Layer-4 anchor reading: the declared table's fold (PayoffEquilibrium.
    legal_payoff), computed from the frozen carriers — not a hardcoded grid."""

    return sum((CONSEQUENCE_VALUATION[(role, c)]
                for c in DECLARED_CONSEQUENCES[status]), Fraction(0))


def payoff_of(role: Role, status: LegalStatus, docket: bool) -> Fraction:
    """Anchor docket reading: depends on the status projection only."""

    return legal_payoff(role, status)


def legal_reading(role: Role, flow: PayFlow) -> Fraction:
    """Layer-4 reading of a general flow = its preference integral (the
    modelling choice declared in the Lean header)."""

    return pref_integral(role, flow.entries)


def status_flow(status: LegalStatus) -> PayFlow:
    """Status vector: one unit entry per declared consequence of the status
    (the standard pre-image of the anchor reading)."""

    return PayFlow(
        entries=tuple(CashEntry(0, c, Fraction(1), False)
                      for c in DECLARED_CONSEQUENCES[status]),
        declared_status=status,
        docket=False,
    )


def doubled_status_flow(status: LegalStatus) -> PayFlow:
    """Same declared status, every unit entry's amount doubled."""

    base = status_flow(status)
    return replace(base, entries=tuple(
        replace(e, amount=2 * e.amount) for e in base.entries))


def flip_tags(entries: Tuple[CashEntry, ...]) -> Tuple[CashEntry, ...]:
    """Layer-1 bookkeeping rewrite: flip every ledger bit."""

    return tuple(replace(e, ledger_tag=not e.ledger_tag) for e in entries)


def status_projection(flow: PayFlow) -> Tuple[LegalStatus, bool]:
    """The OLD encoding: project a flow onto (declared status, docket) —
    exactly what the old anchor's status congruence can see."""

    return (flow.declared_status, flow.docket)


def cost_at_dropped(entries: Tuple[CashEntry, ...], k: Consequence) -> Fraction:
    """A BROKEN cost encoding: res-judicata dropped from the vector."""

    if k == Consequence.RES_JUDICATA:
        return Fraction(0)
    return cost_at(entries, k)


#: Witness cash flow ([代拟稿] amounts): cost-burden 10, enforcement 2,
#: res-judicata 5.
WITNESS_ENTRIES: Tuple[CashEntry, ...] = (
    CashEntry(0, Consequence.COST_BURDEN_LOSER, Fraction(10), False),
    CashEntry(1, Consequence.ENFORCEMENT_ACCESS, Fraction(2), True),
    CashEntry(2, Consequence.RES_JUDICATA, Fraction(5), False),
)


# ===========================================================================
# Frozen carriers — needle 48 (mirror of UnifiedFourteenFamilies rule table
# and the 57 material atoms)
# ===========================================================================

#: The 57 material atoms (input materials) of the fourteen-family network.
MAT_ATOMS: Tuple[str, ...] = (
    # L01 contract
    "matContractSigned", "matBankSettlementMatched", "matReconciliationUnpaid",
    "matGuaranteeByGOpen",
    # L02 property
    "matRegistryD", "matMortgageRegistered", "matOtherTitles",
    "matRealizationRecord",
    # L03 tort
    "matWorkInstruction", "matDamageCorroboration", "matNotWorkInjury",
    # L04 medical
    "matTreatmentAtM", "matRecordsWithheld", "matPreExistingChecks",
    # L05 environment
    "matSamplingMatch", "matExceedance", "matPondTesting", "matEcoCostDocs",
    "matNoExculpation", "matInNewLawPeriod",
    # L06 family/succession
    "matMarriageRegistered", "matNoSpousalJointBasis", "matCDeathRecord",
    "matHeirIdentityOnFile", "matHeirsNotYetJoined",
    # L07 labor
    "matWageBasisOnFile", "matOvertimeUnsupported",
    # L08 corporate bankruptcy
    "matSeparateAccounts", "matInsolvencyShown", "matAcceptanceDecided",
    # L09 IP
    "matCreationChain", "matLicenseExpired", "matPostTermUse",
    "matNoWillfulnessGravity",
    # L10 criminal
    "matLoanAcquisitionProven", "matIntentOnlyConfession",
    "matGenuineBusinessShown", "matCriminalTrialDone",
    # L11 admin
    "matPenaltyServedWithBasis", "matFactualDisputes", "matHearingMissed",
    "matRecordContradictions",
    # L12 review compensation
    "matDetentionX", "matReviewFiledInTime", "matReturnDamageRecords",
    "matRemoteProfitUnsupported", "matDifferentAct",
    # L13 procedure/execution remedy
    "matStayEventsKept", "matPriorCarJudgment", "matNamedErrorAlleged",
    "matDependentClaimFiled", "matPriorCaseUnconcluded",
    # L14 arbitration/maritime/public
    "matMaritimeContractWithClause", "matCarrierCustody", "matCargoDamage",
    "matExemptionMaterials", "matNQualified",
)

MAT_ATOM_SET: FrozenSet[str] = frozenset(MAT_ATOMS)


@dataclass(frozen=True)
class LawRule:
    """A named-source rule: premise atom set -> conclusion atom."""

    rid: int
    premises: FrozenSet[str]
    conclusion: str


#: The 29-rule body network (UnifiedFourteenFamilies.familyRuleList).
FAMILY_RULES: Tuple[LawRule, ...] = (
    LawRule(1, frozenset({"matContractSigned", "matBankSettlementMatched",
                          "matReconciliationUnpaid"}), "loanEntitlement"),
    LawRule(2, frozenset({"matGuaranteeByGOpen"}), "guarantorStanding"),
    LawRule(3, frozenset({"guarantorStanding"}), "gEnforcementAfterExhaustion"),
    LawRule(4, frozenset({"matMortgageRegistered", "matRealizationRecord",
                          "loanEntitlement"}), "mortgageSecuredPriority"),
    LawRule(5, frozenset({"matWorkInstruction",
                          "matDamageCorroboration"}), "carDamageLiability"),
    LawRule(6, frozenset({"matTreatmentAtM",
                          "matRecordsWithheld"}), "medicalFaultPresumed"),
    LawRule(7, frozenset({"matNQualified"}), "publicInterestStanding"),
    LawRule(8, frozenset({"matSamplingMatch", "matExceedance",
                          "matNoExculpation",
                          "matInNewLawPeriod"}), "ecoViolationEstablished"),
    LawRule(9, frozenset({"matPondTesting",
                          "ecoViolationEstablished"}), "fishPrivateCompensation"),
    LawRule(10, frozenset({"matEcoCostDocs", "publicInterestStanding",
                           "ecoViolationEstablished"}), "ecoRemediationCosts"),
    LawRule(11, frozenset({"matWageBasisOnFile"}), "wageDueEstablished"),
    LawRule(12, frozenset({"matSeparateAccounts"}), "noComminglingProven"),
    LawRule(13, frozenset({"matInsolvencyShown",
                           "matAcceptanceDecided"}), "bankruptcyAccepted"),
    LawRule(14, frozenset({"bankruptcyAccepted"}), "bankruptcyExecutionStay"),
    LawRule(15, frozenset({"bankruptcyAccepted"}), "bankruptcyCivilStay"),
    LawRule(16, frozenset({"bankruptcyAccepted"}), "arbitrationStayed"),
    LawRule(17, frozenset({"wageDueEstablished",
                           "bankruptcyAccepted"}), "wageBankruptcyPriority"),
    LawRule(18, frozenset({"matCreationChain", "matLicenseExpired",
                           "matPostTermUse"}), "ipOrdinaryInfringement"),
    LawRule(19, frozenset({"matCDeathRecord",
                           "matHeirsNotYetJoined"}), "stayForSuccession"),
    LawRule(20, frozenset({"stayForSuccession",
                           "matStayEventsKept"}), "stayDecreeIssued"),
    LawRule(21, frozenset({"stayForSuccession"}), "holdOnLoanFinal"),
    LawRule(22, frozenset({"matDependentClaimFiled",
                           "matPriorCaseUnconcluded"}), "holdOnDependentClaim"),
    LawRule(23, frozenset({"matPenaltyServedWithBasis", "matHearingMissed",
                           "matRecordContradictions"}), "adminDefectsEstablished"),
    LawRule(24, frozenset({"matDetentionX", "matReturnDamageRecords",
                           "matReviewFiledInTime"}), "xReturnDue"),
    LawRule(25, frozenset({"matDetentionX",
                           "matReturnDamageRecords"}), "xDamageCompensation"),
    LawRule(26, frozenset({"matPriorCarJudgment", "matNamedErrorAlleged",
                           "matStayEventsKept"}), "retrialAdmitted"),
    LawRule(27, frozenset({"retrialAdmitted"}), "executoryEffectKept"),
    LawRule(28, frozenset({"matCarrierCustody",
                           "matCargoDamage"}), "maritimeCarrierLiability"),
    LawRule(29, frozenset({"maritimeCarrierLiability",
                           "matExemptionMaterials"}), "exemptionBurdenOnCarrier"),
)

#: The three real rule bodies whose use points are proven per-rule.
R01 = FAMILY_RULES[0]
R23 = FAMILY_RULES[22]
R19 = FAMILY_RULES[18]

# ---------------------------------------------------------------------------
# Timed ledger, view, docket read, and the actual eval
# ---------------------------------------------------------------------------

#: A dated material event: (epoch day, atom).
Event = Tuple[int, str]
EvLedger = Tuple[Event, ...]


def law_view(as_of: int, ledger: EvLedger) -> EvLedger:
    """lawView = Temporal.trunc: keep exactly the events dated <= as_of."""

    return tuple(e for e in ledger if e[0] <= as_of)


def occurs_by(as_of: int, ledger: EvLedger, atom: str) -> bool:
    """View read: is the atom declared inside the truncated view?"""

    return any(e[1] == atom for e in law_view(as_of, ledger))


def is_material_atom(atom: str) -> bool:
    return atom in MAT_ATOM_SET


def law_docket(as_of: int, ledger: EvLedger) -> FrozenSet[str]:
    """The as-of docket read: the set of material atoms on file through the
    view (non-material event atoms are inert — no material field reads
    them)."""

    return frozenset(a for a in MAT_ATOMS if occurs_by(as_of, ledger, a))


def material_holds(atom: str, docket: FrozenSet[str]) -> bool:
    """The material bridge: material atoms read the docket, derived atoms
    never hold as inputs."""

    return atom in docket if is_material_atom(atom) else False


def closure(docket: FrozenSet[str]) -> FrozenSet[str]:
    """Forward-chaining closure of the 29-rule network over the docket
    (initial facts = material atoms on file)."""

    derived = set(docket)
    changed = True
    while changed:
        changed = False
        for r in FAMILY_RULES:
            if r.conclusion not in derived and r.premises <= derived:
                derived.add(r.conclusion)
                changed = True
    return frozenset(derived)


def eval_at(atom: str, ledger: EvLedger, as_of: int) -> bool:
    """The actual eval: derivability of the atom in the real rule network of
    the as-of docket state."""

    return atom in closure(law_docket(as_of, ledger))


def rule_fires_at(rule: LawRule, ledger: EvLedger, as_of: int) -> bool:
    return eval_at(rule.conclusion, ledger, as_of)


# ---------------------------------------------------------------------------
# Witness ledgers
# ---------------------------------------------------------------------------

#: Adjudication time (epoch day, [代拟稿] demo value).
T_CUT = 100

#: Witness ledger: every premise material of R01/R23/R19 arrives before the
#: cut (days 10-80).
WIT_LEDGER: EvLedger = (
    (10, "matContractSigned"),
    (20, "matBankSettlementMatched"),
    (30, "matReconciliationUnpaid"),
    (40, "matPenaltyServedWithBasis"),
    (50, "matHearingMissed"),
    (60, "matRecordContradictions"),
    (70, "matCDeathRecord"),
    (80, "matHeirsNotYetJoined"),
)

#: Late ledger: the contract material arrives only on day 150.
LATE_LEDGER: EvLedger = (
    (10, "matBankSettlementMatched"),
    (30, "matReconciliationUnpaid"),
    (150, "matContractSigned"),
)
