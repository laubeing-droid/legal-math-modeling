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

    for defense in bundle.defenses:
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
