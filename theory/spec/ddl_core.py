#!/usr/bin/env python3
"""Minimal DDL core for specification-first legal reasoning.

This module fixes only the smallest deontic semantics needed before a runtime
may safely implement them. It is intentionally narrow: it defines what the core
modalities mean, how violation consequences are attached, how reparations are
structured, and how exception or burden-gated defenses are represented.
"""

from __future__ import annotations

from dataclasses import dataclass
from enum import Enum
from typing import Iterable, Optional, Sequence, Tuple

from .canonical_semantics import (
    CanonicalNorm,
    CanonicalPriority,
    CanonicalReparation,
    CanonicalViolation,
    Modality,
    ReparationMode,
)


class ExceptionKind(str, Enum):
    """Structured exception semantics for the minimal DDL layer."""

    DEFEATER = "DEFEATER"
    JUSTIFICATION = "JUSTIFICATION"
    EXCUSE = "EXCUSE"


class BurdenOfProof(str, Enum):
    """Who must establish a condition for the defense to activate."""

    CLAIMANT = "CLAIMANT"
    RESPONDENT = "RESPONDENT"
    COURT = "COURT"
    PRESUMED_UNLESS_REBUTTED = "PRESUMED_UNLESS_REBUTTED"


@dataclass(frozen=True)
class CanonicalDefense:
    """A defense that can defeat or suspend a norm-violation consequence."""

    defense_id: str
    label: str
    exception_kind: ExceptionKind
    trigger_facts: Tuple[str, ...]
    defeats_conclusion: str
    burden_of_proof: BurdenOfProof
    notes: str = ""


@dataclass(frozen=True)
class DDLNormBundle:
    """A minimal closed semantic unit for downstream shadow implementation."""

    norm: CanonicalNorm
    defenses: Tuple[CanonicalDefense, ...] = ()
    priorities: Tuple[CanonicalPriority, ...] = ()


def validate_minimal_ddl_bundle(bundle: DDLNormBundle) -> None:
    """Validate semantic invariants that the runtime is not allowed to invent."""

    norm = bundle.norm
    if norm.modality == Modality.PERMISSION and norm.violation is not None:
        raise ValueError("PERMISSION must not directly carry a violation consequence.")

    if norm.modality == Modality.CONSTITUTIVE and norm.violation is not None:
        raise ValueError("CONSTITUTIVE norms define status, not breach liability.")

    if norm.modality in (Modality.OBLIGATION, Modality.PROHIBITION) and norm.violation is None:
        raise ValueError("OBLIGATION/PROHIBITION norms must define their violation consequence.")

    if norm.violation is not None and not norm.violation.reparations:
        raise ValueError("Violation consequences must declare at least one reparation structure.")

    if norm.modality in (Modality.PERMISSION, Modality.CONSTITUTIVE) and norm.conclusion_fact is None:
        raise ValueError("PERMISSION/CONSTITUTIVE norms must declare a positive conclusion_fact.")

    for defense in bundle.defenses:
        if norm.violation is None:
            raise ValueError("Defense-bearing bundles must define a violation consequence.")
        if defense.defeats_conclusion != norm.violation.consequence_fact:
            raise ValueError(
                f"Defense {defense.defense_id} defeats {defense.defeats_conclusion}, "
                f"not the bundle consequence {norm.violation.consequence_fact}."
            )


def make_contract_breach_bundle() -> DDLNormBundle:
    """Build the first reusable DDL slice for contract breach."""

    repair_chain = CanonicalReparation(
        reparation_id="rep::contract_breach",
        mode=ReparationMode.ORDERED_CHAIN,
        options=(
            "remedy_continue_performance",
            "remedy_cure",
            "remedy_damages",
        ),
        notes=(
            "Minimal ordered repair baseline for the first slice. "
            "Downstream law-specific material may refine availability or order."
        ),
    )
    violation = CanonicalViolation(
        violation_id="vio::contract_breach",
        norm_id="norm::delivery",
        trigger_fact="goods_not_delivered",
        consequence_fact="delivery_breach",
        reparations=(repair_chain,),
    )
    norm = CanonicalNorm(
        norm_id="norm::delivery",
        modality=Modality.OBLIGATION,
        actor="seller",
        action="deliver_goods",
        condition_facts=("contract_exists", "delivery_due"),
        conclusion_fact="norm::delivery::active",
        exception_facts=("force_majeure",),
        violation=violation,
    )
    defense = CanonicalDefense(
        defense_id="defense::force_majeure",
        label="force_majeure",
        exception_kind=ExceptionKind.EXCUSE,
        trigger_facts=("force_majeure",),
        defeats_conclusion="delivery_breach",
        burden_of_proof=BurdenOfProof.RESPONDENT,
        notes="The excuse defeats the breach conclusion, not the underlying contract fact.",
    )
    bundle = DDLNormBundle(norm=norm, defenses=(defense,))
    validate_minimal_ddl_bundle(bundle)
    return bundle


def make_license_permission_priority_bundles() -> Tuple[DDLNormBundle, ...]:
    """Build a second slice covering constitutive, permission, and priority defeat."""

    constitutive_norm = CanonicalNorm(
        norm_id="norm::license_status",
        modality=Modality.CONSTITUTIVE,
        actor="licensor",
        action="activate_license",
        condition_facts=("license_signed", "rights_holder_authorized"),
        conclusion_fact="license_status_active",
    )
    permission_norm = CanonicalNorm(
        norm_id="norm::licensed_use_permission",
        modality=Modality.PERMISSION,
        actor="licensee",
        action="use_work_within_scope",
        condition_facts=("license_status_active", "use_within_scope"),
        conclusion_fact="use_permitted",
    )
    violation = CanonicalViolation(
        violation_id="vio::unauthorized_use",
        norm_id="norm::unauthorized_use_prohibition",
        trigger_fact="used_work",
        consequence_fact="unauthorized_use",
        reparations=(
            CanonicalReparation(
                reparation_id="rep::unauthorized_use",
                mode=ReparationMode.ALTERNATIVE,
                options=("remedy_stop_use", "remedy_damages"),
                notes="Minimal alternative remedies for prohibited unlicensed use.",
            ),
        ),
    )
    prohibition_norm = CanonicalNorm(
        norm_id="norm::unauthorized_use_prohibition",
        modality=Modality.PROHIBITION,
        actor="user",
        action="use_work_without_authorization",
        condition_facts=("used_work",),
        conclusion_fact="norm::unauthorized_use_prohibition::active",
        violation=violation,
    )
    priority = CanonicalPriority(
        priority_id="priority::license_over_prohibition",
        winner="norm::licensed_use_permission",
        loser="norm::unauthorized_use_prohibition",
        reason="A valid in-scope license defeats the general unauthorized-use prohibition.",
    )
    bundles = (
        DDLNormBundle(norm=constitutive_norm),
        DDLNormBundle(norm=permission_norm, priorities=(priority,)),
        DDLNormBundle(norm=prohibition_norm, priorities=(priority,)),
    )
    for bundle in bundles:
        validate_minimal_ddl_bundle(bundle)
    return bundles


def make_permission_conflict_bundles() -> Tuple[DDLNormBundle, ...]:
    """构造独立 permission slice：许可不会自动推出义务，冲突必须经 AAF/priority 处理。"""

    permission_norm = CanonicalNorm(
        norm_id="norm::permission_source",
        modality=Modality.PERMISSION,
        actor="requester",
        action="perform_conditioned_act",
        condition_facts=("permission_source", "condition_satisfied"),
        conclusion_fact="permission_granted",
    )
    violation = CanonicalViolation(
        violation_id="vio::prohibition_candidate",
        norm_id="norm::general_prohibition",
        trigger_fact="prohibition_candidate",
        consequence_fact="not_permitted",
        reparations=(
            CanonicalReparation(
                reparation_id="rep::permission_conflict",
                mode=ReparationMode.COURT_SELECTED,
                options=("remedy_block_act", "remedy_manual_review"),
                notes="Conflict remains unresolved unless explicit override evidence exists.",
            ),
        ),
    )
    prohibition_norm = CanonicalNorm(
        norm_id="norm::general_prohibition",
        modality=Modality.PROHIBITION,
        actor="requester",
        action="perform_conditioned_act_without_override",
        condition_facts=("prohibition_candidate",),
        conclusion_fact="norm::general_prohibition::active",
        violation=violation,
    )
    priority = CanonicalPriority(
        priority_id="priority::permission_over_prohibition",
        winner="norm::permission_source",
        loser="norm::general_prohibition",
        reason="Verified override evidence is required before permission defeats prohibition.",
    )
    bundles = (
        DDLNormBundle(norm=permission_norm, priorities=(priority,)),
        DDLNormBundle(norm=prohibition_norm, priorities=(priority,)),
    )
    for bundle in bundles:
        validate_minimal_ddl_bundle(bundle)
    return bundles


def make_priority_decision_bundles() -> Tuple[DDLNormBundle, ...]:
    """构造独立 priority slice：priority 证据缺失或循环时不能默认任一方获胜。"""

    rule_a_norm = CanonicalNorm(
        norm_id="norm::rule_a_supports_claim",
        modality=Modality.PERMISSION,
        actor="party_a",
        action="support_claim",
        condition_facts=("rule_a_supports_claim",),
        conclusion_fact="claim_supported_by_rule_a",
    )
    violation = CanonicalViolation(
        violation_id="vio::rule_b_attacks_claim",
        norm_id="norm::rule_b_attacks_claim",
        trigger_fact="rule_b_attacks_claim",
        consequence_fact="claim_attacked_by_rule_b",
        reparations=(
            CanonicalReparation(
                reparation_id="rep::priority_review",
                mode=ReparationMode.COURT_SELECTED,
                options=("remedy_manual_priority_review",),
                notes="Priority disputes without verified ordering remain fail-closed.",
            ),
        ),
    )
    rule_b_norm = CanonicalNorm(
        norm_id="norm::rule_b_attacks_claim",
        modality=Modality.PROHIBITION,
        actor="party_b",
        action="attack_claim",
        condition_facts=("rule_b_attacks_claim",),
        conclusion_fact="norm::rule_b_attack::active",
        violation=violation,
    )
    priority = CanonicalPriority(
        priority_id="priority::rule_a_over_rule_b",
        winner="norm::rule_a_supports_claim",
        loser="norm::rule_b_attacks_claim",
        reason="Verified priority evidence lets rule A defeat rule B.",
    )
    bundles = (
        DDLNormBundle(norm=rule_a_norm, priorities=(priority,)),
        DDLNormBundle(norm=rule_b_norm, priorities=(priority,)),
    )
    for bundle in bundles:
        validate_minimal_ddl_bundle(bundle)
    return bundles

def make_tort_bundle() -> DDLNormBundle:
    """Build the third DDL slice for tort liability."""
    violation = CanonicalViolation(
        violation_id="vio::tort_liability",
        norm_id="norm::tort_liability",
        trigger_fact="tort_breach_candidate",
        consequence_fact="tort_liability",
        reparations=(
            CanonicalReparation(
                reparation_id="rep::tort",
                mode=ReparationMode.ORDERED_CHAIN,
                options=("remedy_compensation", "remedy_restoration"),
                notes="Compensation first, then restoration if applicable.",
            ),
        ),
    )
    norm = CanonicalNorm(
        norm_id="norm::tort_liability",
        modality=Modality.OBLIGATION,
        actor="actor",
        action="refrain_from_tort",
        condition_facts=("duty_of_care", "breach_of_duty", "causation", "damage"),
        conclusion_fact="norm::tort::active",
        violation=violation,
        exception_facts=("contributory_negligence",),
    )
    defense = CanonicalDefense(
        defense_id="defense::contributory_negligence",
        label="contributory_negligence",
        exception_kind=ExceptionKind.DEFEATER,
        trigger_facts=("contributory_negligence",),
        defeats_conclusion="tort_liability",
        burden_of_proof=BurdenOfProof.RESPONDENT,
        notes="Contributory negligence defeats tort liability.",
    )
    bundle = DDLNormBundle(norm=norm, defenses=(defense,))
    validate_minimal_ddl_bundle(bundle)
    return bundle


def make_criminal_bundle() -> DDLNormBundle:
    """Build the fourth DDL slice for criminal liability."""
    violation = CanonicalViolation(
        violation_id="vio::criminal_liability",
        norm_id="norm::criminal_liability",
        trigger_fact="criminal_breach_candidate",
        consequence_fact="criminal_liability",
        reparations=(
            CanonicalReparation(
                reparation_id="rep::criminal",
                mode=ReparationMode.ORDERED_CHAIN,
                options=("remedy_penalty",),
                notes="Penalty determination follows liability.",
            ),
        ),
    )
    norm = CanonicalNorm(
        norm_id="norm::criminal_liability",
        modality=Modality.PROHIBITION,
        actor="actor",
        action="commit_offense",
        condition_facts=("actus_reus", "mens_rea", "absence_of_defense"),
        conclusion_fact="norm::criminal::active",
        exception_facts=("self_defense",),
        violation=violation,
    )
    defense = CanonicalDefense(
        defense_id="defense::self_defense",
        label="self_defense",
        exception_kind=ExceptionKind.JUSTIFICATION,
        trigger_facts=("self_defense",),
        defeats_conclusion="criminal_liability",
        burden_of_proof=BurdenOfProof.RESPONDENT,
        notes="Self-defense justifies the act and defeats criminal liability.",
    )
    bundle = DDLNormBundle(norm=norm, defenses=(defense,))
    validate_minimal_ddl_bundle(bundle)
    return bundle


def make_admin_bundle() -> tuple[DDLNormBundle, ...]:
    """Build the fifth DDL slice for administrative illegality with priority override."""
    violation = CanonicalViolation(
        violation_id="vio::admin_illegality",
        norm_id="norm::admin_illegality",
        trigger_fact="admin_breach_candidate",
        consequence_fact="admin_illegality",
        reparations=(
            CanonicalReparation(
                reparation_id="rep::admin",
                mode=ReparationMode.ORDERED_CHAIN,
                options=("remedy_revocation", "remedy_compensation"),
                notes="Revocation of illegal act first, then compensation.",
            ),
        ),
    )
    admin_norm = CanonicalNorm(
        norm_id="norm::admin_illegality",
        modality=Modality.OBLIGATION,
        actor="administrative_body",
        action="act_within_authority",
        condition_facts=("admin_action", "exceeds_authority", "no_legal_basis"),
        conclusion_fact="norm::admin::active",
        violation=violation,
    )
    priority = CanonicalPriority(
        priority_id="priority::higher_law_over_admin",
        winner="norm::higher_law",
        loser="norm::admin_illegality",
        reason="A higher law norm defeats an administrative act that lacks legal basis.",
    )
    higher_law_norm = CanonicalNorm(
        norm_id="norm::higher_law",
        modality=Modality.CONSTITUTIVE,
        actor="legislature",
        action="establish_legal_basis",
        condition_facts=("legal_basis_exists",),
        conclusion_fact="admin_action_valid",
    )
    bundles = (
        DDLNormBundle(norm=admin_norm, priorities=(priority,)),
        DDLNormBundle(norm=higher_law_norm, priorities=(priority,)),
    )
    for bundle in bundles:
        validate_minimal_ddl_bundle(bundle)
    return bundles



def summarize_reparation_modes(bundles: Sequence[DDLNormBundle]) -> Tuple[str, ...]:
    """Expose the reparation semantics used by the current specification slices."""

    modes = []
    for bundle in bundles:
        if bundle.norm.violation is None:
            continue
        for reparation in bundle.norm.violation.reparations:
            modes.append(reparation.mode.value)
    return tuple(modes)


def list_defense_targets(bundles: Iterable[DDLNormBundle]) -> Tuple[str, ...]:
    """List every conclusion explicitly defeasible under the current DDL core."""

    targets = []
    for bundle in bundles:
        for defense in bundle.defenses:
            targets.append(defense.defeats_conclusion)
    return tuple(targets)
