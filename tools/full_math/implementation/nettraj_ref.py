"""Joint fourteen-family network trajectory reference entries (W15, needle 42).

Formal contract: ``JurisLean.Seams.UnifiedNetTrajectory.lean``
(needle 42 gap closure; authoritative spec line
``docs/spec/20261007-统一法律数学模型_附录I_Lean施工明细.md`` I.13 :796 --
"actual non-empty trajectory on the joint fourteen-family network").

The carrier mirrors the Lean module exactly:

* atoms -- 57 material atoms + 29 derived atoms + 10 failure atoms, named
  verbatim after the Lean constructors of ``UnifiedFourteenFamilies.Atom``;
* rules -- the 29 named-source Horn rules R01..R29 with premise sets and
  conclusions transcribed from ``familyRuleList``;
* dockets -- the full-material witness docket plus two partial dockets
  (L05 exceedance measurement missing; L08 acceptance decision missing);
* trajectories -- finite chains of rule firings, each step recording its
  time index, fired rule (premises consumed, conclusion produced, named
  statute source), exactly the "trajectory record" the Lean ``Step``
  structure carries.

Every entry consumes the structured docket/rule tables (no fixtures, no
precomputed verdicts) and produces the intermediate readings whose Lean
counterparts are ``traceOk_*``/``productive_card_bound``/``prodStep_wf``/
``nontrivial_net_trajectory_exists``/``full_net_trajectory_end_to_end``/
``partial_net_trajectory_difference``.  The independent contract checker
lives in ``nettraj_check`` and shares no code with this module.

All quantity arithmetic is exact ``Fraction`` (the Lean side uses Q);
nothing here samples, rounds, or floats.
"""
from __future__ import annotations

from fractions import Fraction
from typing import Dict, FrozenSet, List, Sequence, Set, Tuple

# ---------------------------------------------------------------------------
# Atom tables (Lean constructor names verbatim)
# ---------------------------------------------------------------------------

FAMILY_MATERIALS: Dict[str, Tuple[str, ...]] = {
    "L01Contract": (
        "matContractSigned", "matBankSettlementMatched",
        "matReconciliationUnpaid", "matGuaranteeByGOpen"),
    "L02Property": (
        "matRegistryD", "matMortgageRegistered", "matOtherTitles",
        "matRealizationRecord"),
    "L03Tort": ("matWorkInstruction", "matDamageCorroboration", "matNotWorkInjury"),
    "L04Medical": ("matTreatmentAtM", "matRecordsWithheld", "matPreExistingChecks"),
    "L05Environment": (
        "matSamplingMatch", "matExceedance", "matPondTesting",
        "matEcoCostDocs", "matNoExculpation", "matInNewLawPeriod"),
    "L06FamilySuccession": (
        "matMarriageRegistered", "matNoSpousalJointBasis", "matCDeathRecord",
        "matHeirIdentityOnFile", "matHeirsNotYetJoined"),
    "L07Labor": ("matWageBasisOnFile", "matOvertimeUnsupported"),
    "L08CorporateBankruptcy": (
        "matSeparateAccounts", "matInsolvencyShown", "matAcceptanceDecided"),
    "L09Ip": (
        "matCreationChain", "matLicenseExpired", "matPostTermUse",
        "matNoWillfulnessGravity"),
    "L10Criminal": (
        "matLoanAcquisitionProven", "matIntentOnlyConfession",
        "matGenuineBusinessShown", "matCriminalTrialDone"),
    "L11Admin": (
        "matPenaltyServedWithBasis", "matFactualDisputes", "matHearingMissed",
        "matRecordContradictions"),
    "L12ReviewCompensation": (
        "matDetentionX", "matReviewFiledInTime", "matReturnDamageRecords",
        "matRemoteProfitUnsupported", "matDifferentAct"),
    "L13ProcedureExecutionRemedy": (
        "matStayEventsKept", "matPriorCarJudgment", "matNamedErrorAlleged",
        "matDependentClaimFiled", "matPriorCaseUnconcluded"),
    "L14ArbitrationMaritimePublic": (
        "matMaritimeContractWithClause", "matCarrierCustody", "matCargoDamage",
        "matExemptionMaterials", "matNQualified"),
}

MATERIAL_ATOMS: Tuple[str, ...] = tuple(
    a for fam in FAMILY_MATERIALS.values() for a in fam)

DERIVED_ATOMS: Tuple[str, ...] = (
    "loanEntitlement", "guarantorStanding", "gEnforcementAfterExhaustion",
    "mortgageSecuredPriority", "carDamageLiability", "medicalFaultPresumed",
    "publicInterestStanding", "ecoViolationEstablished", "fishPrivateCompensation",
    "ecoRemediationCosts", "wageDueEstablished", "noComminglingProven",
    "bankruptcyAccepted", "bankruptcyExecutionStay", "bankruptcyCivilStay",
    "arbitrationStayed", "wageBankruptcyPriority", "ipOrdinaryInfringement",
    "stayForSuccession", "stayDecreeIssued", "holdOnLoanFinal",
    "holdOnDependentClaim", "adminDefectsEstablished", "xReturnDue",
    "xDamageCompensation", "retrialAdmitted", "executoryEffectKept",
    "maritimeCarrierLiability", "exemptionBurdenOnCarrier")

FAILURE_ATOMS: Tuple[str, ...] = (
    "overtimeClaimEstablished", "medicalAddedDamageAward", "spousalJointDebt",
    "ipPunitiveDamages", "fraudConviction", "remoteProfitAward",
    "corporateVeilPierced", "loanFinalDecree", "dependentClaimFinalDecree",
    "adminFinalDisposition")

ALL_ATOMS: FrozenSet[str] = frozenset(MATERIAL_ATOMS + DERIVED_ATOMS + FAILURE_ATOMS)

# ---------------------------------------------------------------------------
# Named statute sources (Lean ``srcTag`` windows; base day 20260815)
# ---------------------------------------------------------------------------

BASE_DAY = 20260815

SOURCE_WINDOWS: Dict[str, Tuple[int, int]] = {
    "civilCode490_626": (20210101, 99991231),
    "civilCode681_687": (20210101, 99991231),
    "civilCode1165_1191": (20210101, 99991231),
    "civilCode1222": (20210101, 99991231),
    "ecoCode147": (20260101, 99991231),
    "ecoCode1075_1081": (20260101, 99991231),
    "ecoCode1080": (20260101, 99991231),
    "laborContractLaw30": (20080101, 99991231),
    "companyLaw23": (20240701, 99991231),
    "bankruptcyLaw2_13": (20070601, 99991231),
    "bankruptcyLaw19": (20070601, 99991231),
    "bankruptcyLaw20": (20070601, 99991231),
    "bankruptcyLaw109_110": (20070601, 99991231),
    "bankruptcyLaw113": (20070601, 99991231),
    "copyrightLaw52_54": (20210601, 99991231),
    "civProcLaw153_1": (20240101, 99991231),
    "civProcLaw153_5": (20240101, 99991231),
    "civProcLaw210_217": (20240101, 99991231),
    "adminPunishLaw63_64": (20210715, 99991231),
    "stateCompensationLaw36": (20130101, 99991231),
    "maritimeLaw43_57": (20260101, 99991231),
    "maritimeLaw51": (20260101, 99991231),
}


def src_in_force(src: str) -> bool:
    eff_from, eff_to = SOURCE_WINDOWS[src]
    return eff_from <= BASE_DAY < eff_to


# ---------------------------------------------------------------------------
# Rule network (29 Horn rules; premises/conclusions verbatim from familyRuleList)
# ---------------------------------------------------------------------------

Rule = Dict[str, object]


def _r(rid: int, premises: Sequence[str], conclusion: str, src: str) -> Rule:
    return {
        "rid": rid,
        "name": "R%02d" % rid,
        "premises": frozenset(premises),
        "conclusion": conclusion,
        "src": src,
    }


RULES: Tuple[Rule, ...] = (
    _r(1, ("matContractSigned", "matBankSettlementMatched",
           "matReconciliationUnpaid"), "loanEntitlement", "civilCode490_626"),
    _r(2, ("matGuaranteeByGOpen",), "guarantorStanding", "civilCode681_687"),
    _r(3, ("guarantorStanding",), "gEnforcementAfterExhaustion", "civilCode681_687"),
    _r(4, ("matMortgageRegistered", "matRealizationRecord", "loanEntitlement"),
       "mortgageSecuredPriority", "bankruptcyLaw109_110"),
    _r(5, ("matWorkInstruction", "matDamageCorroboration"),
       "carDamageLiability", "civilCode1165_1191"),
    _r(6, ("matTreatmentAtM", "matRecordsWithheld"),
       "medicalFaultPresumed", "civilCode1222"),
    _r(7, ("matNQualified",), "publicInterestStanding", "ecoCode147"),
    _r(8, ("matSamplingMatch", "matExceedance", "matNoExculpation",
           "matInNewLawPeriod"), "ecoViolationEstablished", "ecoCode1075_1081"),
    _r(9, ("matPondTesting", "ecoViolationEstablished"),
       "fishPrivateCompensation", "ecoCode1080"),
    _r(10, ("matEcoCostDocs", "publicInterestStanding", "ecoViolationEstablished"),
        "ecoRemediationCosts", "ecoCode1080"),
    _r(11, ("matWageBasisOnFile",), "wageDueEstablished", "laborContractLaw30"),
    _r(12, ("matSeparateAccounts",), "noComminglingProven", "companyLaw23"),
    _r(13, ("matInsolvencyShown", "matAcceptanceDecided"),
        "bankruptcyAccepted", "bankruptcyLaw2_13"),
    _r(14, ("bankruptcyAccepted",), "bankruptcyExecutionStay", "bankruptcyLaw19"),
    _r(15, ("bankruptcyAccepted",), "bankruptcyCivilStay", "bankruptcyLaw20"),
    _r(16, ("bankruptcyAccepted",), "arbitrationStayed", "bankruptcyLaw20"),
    _r(17, ("wageDueEstablished", "bankruptcyAccepted"),
        "wageBankruptcyPriority", "bankruptcyLaw113"),
    _r(18, ("matCreationChain", "matLicenseExpired", "matPostTermUse"),
        "ipOrdinaryInfringement", "copyrightLaw52_54"),
    _r(19, ("matCDeathRecord", "matHeirsNotYetJoined"),
        "stayForSuccession", "civProcLaw153_1"),
    _r(20, ("stayForSuccession", "matStayEventsKept"),
        "stayDecreeIssued", "civProcLaw153_1"),
    _r(21, ("stayForSuccession",), "holdOnLoanFinal", "civProcLaw153_1"),
    _r(22, ("matDependentClaimFiled", "matPriorCaseUnconcluded"),
        "holdOnDependentClaim", "civProcLaw153_5"),
    _r(23, ("matPenaltyServedWithBasis", "matHearingMissed",
            "matRecordContradictions"), "adminDefectsEstablished", "adminPunishLaw63_64"),
    _r(24, ("matDetentionX", "matReturnDamageRecords", "matReviewFiledInTime"),
        "xReturnDue", "stateCompensationLaw36"),
    _r(25, ("matDetentionX", "matReturnDamageRecords"),
        "xDamageCompensation", "stateCompensationLaw36"),
    _r(26, ("matPriorCarJudgment", "matNamedErrorAlleged", "matStayEventsKept"),
        "retrialAdmitted", "civProcLaw210_217"),
    _r(27, ("retrialAdmitted",), "executoryEffectKept", "civProcLaw210_217"),
    _r(28, ("matCarrierCustody", "matCargoDamage"),
        "maritimeCarrierLiability", "maritimeLaw43_57"),
    _r(29, ("maritimeCarrierLiability", "matExemptionMaterials"),
        "exemptionBurdenOnCarrier", "maritimeLaw51"),
)

RULES_BY_RID: Dict[int, Rule] = {r["rid"]: r for r in RULES}  # type: ignore[index]

# ---------------------------------------------------------------------------
# Dockets (shared quantities as exact Fractions; witness point P0=100,w=10,b=20,a=10)
# ---------------------------------------------------------------------------

WITNESS_QTY: Dict[str, Fraction] = {
    "loanPrincipal": Fraction(100),
    "provenDueWage": Fraction(10),
    "collateralNet": Fraction(20),
    "otherNetAssets": Fraction(10),
}


def _material_table(missing: Sequence[str]) -> FrozenSet[str]:
    """Full-material docket minus the named materials (the two partial dockets)."""
    bad = frozenset(missing)
    return frozenset(a for a in MATERIAL_ATOMS if a not in bad)


DOCKETS: Dict[str, FrozenSet[str]] = {
    "full": frozenset(MATERIAL_ATOMS),
    "partialEco": _material_table(("matExceedance",)),
    "partialBank": _material_table(("matAcceptanceDecided",)),
}


def shortfall(qty: Dict[str, Fraction]) -> Fraction:
    """Net unmet balance P0 + w - (b + a), exact rational (shortfall_positive)."""
    return (qty["loanPrincipal"] + qty["provenDueWage"]
            - (qty["collateralNet"] + qty["otherNetAssets"]))


def no_double_debt(qty: Dict[str, Fraction]) -> Tuple[Fraction, Fraction, Fraction]:
    """Secured part + unsecured part = principal (no_double_debt), exact."""
    secured = qty["collateralNet"]
    unsecured = qty["loanPrincipal"] - qty["collateralNet"]
    return secured, unsecured, secured + unsecured


# ---------------------------------------------------------------------------
# Trajectory machinery (mirror of Step / initState / runNetTrace / TraceOk)
# ---------------------------------------------------------------------------

def init_state(docket: str) -> FrozenSet[str]:
    """initState: all materials on file in the docket (= Horn initial facts)."""
    return DOCKETS[docket]


def rule_of(rid: int) -> Rule:
    if rid not in RULES_BY_RID:
        raise ValueError("unknown rule id %r (trajectory cannot invent rules)" % (rid,))
    return RULES_BY_RID[rid]


def make_step(idx: int, rid: int) -> Dict[str, object]:
    """A trajectory step record: time index + fired rule (premises/conclusion/src)."""
    r = rule_of(rid)
    return {
        "idx": idx,
        "rid": rid,
        "name": r["name"],
        "premises": frozenset(r["premises"]),  # type: ignore[arg-type]
        "conclusion": r["conclusion"],
        "src": r["src"],
    }


def run_trace(docket: str, steps: Sequence[Dict[str, object]]) -> Dict[str, object]:
    """runNetTrace + TraceOk check + trajectory record log.

    Folds the state left-to-right inserting each step's conclusion; a step is
    enabled when all of its consumed premises are already established (on-file
    material or an earlier step's conclusion).  Returns the final state, the
    per-step log (with consumed/produced/time/source) and the ok verdict.
    """
    state: Set[str] = set(init_state(docket))
    log: List[Dict[str, object]] = []
    reasons: List[str] = []
    for pos, st in enumerate(steps):
        r = rule_of(st["rid"])  # type: ignore[index]
        prem = frozenset(r["premises"])  # type: ignore[arg-type]
        missing = prem - state
        if missing:
            reasons.append(
                "step %d (t=%s, %s) consumes unavailable premises: %s"
                % (pos, st["idx"], r["name"], sorted(missing)))
        state.add(r["conclusion"])  # type: ignore[index]
        log.append({
            "pos": pos,
            "idx": st["idx"],
            "rid": st["rid"],
            "name": r["name"],
            "consumed": sorted(prem),
            "produced": r["conclusion"],
            "src": r["src"],
            "enabled": not missing,
        })
    return {
        "docket": docket,
        "init": frozenset(init_state(docket)),
        "final": frozenset(state),
        "log": log,
        "ok": not reasons,
        "reasons": tuple(reasons),
        "length": len(steps),
    }


def closure(docket: str) -> FrozenSet[str]:
    """closureAt: iterate the Horn step operator to a fixed point."""
    current = set(init_state(docket))
    while True:
        new = set(current)
        for r in RULES:
            if r["premises"] <= current:  # type: ignore[operator]
                new.add(r["conclusion"])  # type: ignore[index]
        if new == current:
            return frozenset(current)
        current = new


def is_productive(out: Dict[str, object]) -> bool:
    """Productive: every step's conclusion was new when fired (no re-firing)."""
    if not out["ok"]:
        return False
    state: Set[str] = set(out["init"])  # type: ignore[arg-type]
    for entry in out["log"]:  # type: ignore[union-attr]
        if entry["produced"] in state:  # type: ignore[index]
            return False
        state.add(entry["produced"])  # type: ignore[index]
    return True


def times_increasing(steps: Sequence[Dict[str, object]]) -> bool:
    idxs = [st["idx"] for st in steps]
    return all(a < b for a, b in zip(idxs, idxs[1:]))


def remain_card(state: FrozenSet[str], universe: FrozenSet[str] = ALL_ATOMS) -> int:
    """remainCard measure: atoms still addable (universe minus the state)."""
    return len(universe - state)


def traj_outcome(docket: str, steps: Sequence[Dict[str, object]]) -> Dict[str, object]:
    """Full trajectory reading (contract observable for the checker)."""
    out = run_trace(docket, steps)
    clo = closure(docket)
    finals = out["final"]
    return {
        "docket": docket,
        "ok": out["ok"],
        "reasons": out["reasons"],
        "length": out["length"],
        "nonempty": out["length"] > 0,
        "times_increasing": times_increasing(steps),
        "productive": is_productive(out),
        "init": out["init"],
        "final": finals,
        "conclusions": tuple(e["produced"] for e in out["log"]),  # type: ignore[union-attr]
        "closure_consistent": finals <= clo,
        "closure": clo,
        "sources_in_force": tuple(
            (e["src"], src_in_force(e["src"]))  # type: ignore[index]
            for e in out["log"]),  # type: ignore[union-attr]
        "bound": (out["length"] + len(out["init"]) <= len(ALL_ATOMS)),  # type: ignore[arg-type]
        "remain_final": remain_card(finals),
    }


# ---------------------------------------------------------------------------
# Witness trajectories (mirror of ecoChain / fullTraj / partialEco/BankTraj)
# ---------------------------------------------------------------------------

ECO_CHAIN: Tuple[Dict[str, object], ...] = (
    make_step(0, 7), make_step(1, 8), make_step(2, 10))

FULL_TRAJ: Tuple[Dict[str, object], ...] = tuple(
    make_step(i, rid) for i, rid in enumerate(
        (1, 4, 7, 8, 9, 10, 11, 13, 17, 14, 15, 16, 28, 29, 19, 20, 21)))

PARTIAL_ECO_TRAJ: Tuple[Dict[str, object], ...] = (make_step(0, 7),)

PARTIAL_BANK_TRAJ: Tuple[Dict[str, object], ...] = tuple(
    make_step(i, rid) for i, rid in enumerate((11, 19, 20, 21)))


def needle42_witness() -> Dict[str, object]:
    """nontrivial_net_trajectory_exists: existence form on ecoChain/fullDocket."""
    return traj_outcome("full", ECO_CHAIN)


def full_net_trajectory() -> Dict[str, object]:
    """full_net_trajectory_end_to_end: 17-step full docket reading."""
    return traj_outcome("full", FULL_TRAJ)


def partial_eco_reading() -> Dict[str, object]:
    """Partial docket 1: 1-step trajectory runs; eco chain unreachable."""
    run = traj_outcome("partialEco", PARTIAL_ECO_TRAJ)
    run["blocked"] = {
        "ecoViolationEstablished":
            "ecoViolationEstablished" not in run["closure"],
        "fishPrivateCompensation":
            "fishPrivateCompensation" not in run["closure"],
        "ecoRemediationCosts":
            "ecoRemediationCosts" not in run["closure"],
    }
    run["in_full_closure"] = {
        a: a in closure("full")
        for a in ("ecoViolationEstablished", "fishPrivateCompensation",
                  "ecoRemediationCosts")}
    return run


def partial_bank_reading() -> Dict[str, object]:
    """Partial docket 2: 4-step trajectory runs; bankruptcy cluster unreachable."""
    run = traj_outcome("partialBank", PARTIAL_BANK_TRAJ)
    run["blocked"] = {
        a: a not in run["closure"]
        for a in ("bankruptcyAccepted", "bankruptcyExecutionStay",
                  "bankruptcyCivilStay", "arbitrationStayed",
                  "wageBankruptcyPriority")}
    run["in_full_closure"] = {
        a: a in closure("full")
        for a in ("bankruptcyAccepted", "wageBankruptcyPriority")}
    return run


def quantities_reading() -> Dict[str, Fraction]:
    """Shared-quantity readouts (Fraction exact; Lean Q side is UFF's job)."""
    secured, unsecured, total = no_double_debt(WITNESS_QTY)
    return {
        "shortfall": shortfall(WITNESS_QTY),
        "secured": secured,
        "unsecured": unsecured,
        "secured_plus_unsecured": total,
        "loanPrincipal": WITNESS_QTY["loanPrincipal"],
        "collateralNet": WITNESS_QTY["collateralNet"],
    }
