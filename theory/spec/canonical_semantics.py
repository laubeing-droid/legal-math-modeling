#!/usr/bin/env python3
"""Canonical semantic schema for the specification side of legal reasoning.

This module is intentionally small, transparent, and conservative. It is not a
production runtime. Its job is to fix a single semantic vocabulary that Lean
specifications, reference evaluators, and downstream runtimes can share without
quietly changing meanings.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from enum import Enum
from typing import Any, Dict, Optional, Tuple


class Modality(str, Enum):
    """Minimal deontic modality set for the shared semantic model."""

    OBLIGATION = "OBLIGATION"
    PROHIBITION = "PROHIBITION"
    PERMISSION = "PERMISSION"
    CONSTITUTIVE = "CONSTITUTIVE"


class RuleKind(str, Enum):
    """Kinds of rules that may appear in the shared model."""

    HORN = "HORN"
    EXCEPTION = "EXCEPTION"
    PRIORITY = "PRIORITY"
    CONSTITUTIVE = "CONSTITUTIVE"


class AttackKind(str, Enum):
    """Distinguishes generic conflict from legally structured defeat."""

    REBUTTAL = "REBUTTAL"
    EXCEPTION = "EXCEPTION"
    PRIORITY_DEFEAT = "PRIORITY_DEFEAT"


class ReparationMode(str, Enum):
    """How remedies compose once liability is established."""

    ALTERNATIVE = "ALTERNATIVE"
    ORDERED_CHAIN = "ORDERED_CHAIN"
    CONCURRENT = "CONCURRENT"
    COURT_SELECTED = "COURT_SELECTED"


class DecisionStatus(str, Enum):
    """Minimal decision-status space for spec-side certificates."""

    PROVED = "PROVED"
    REFUTED = "REFUTED"
    UNDECIDED = "UNDECIDED"
    TAINTED = "TAINTED"


@dataclass(frozen=True)
class CanonicalFact:
    """A canonical atomic fact used by the formal and reference layers."""

    fact_id: str
    predicate: str
    arguments: Tuple[str, ...] = ()
    source_ref: Optional[str] = None
    attributes: Dict[str, Any] = field(default_factory=dict)

    @property
    def key(self) -> str:
        """Stable key used by the reference interpreter."""

        if not self.arguments:
            return self.predicate
        return f"{self.predicate}({','.join(self.arguments)})"


@dataclass(frozen=True)
class CanonicalPriority:
    """A priority relation between two rules or arguments."""

    priority_id: str
    winner: str
    loser: str
    reason: str


@dataclass(frozen=True)
class CanonicalReparation:
    """A structured remedy payload tied to a violation or liability finding."""

    reparation_id: str
    mode: ReparationMode
    options: Tuple[str, ...]
    notes: str = ""


@dataclass(frozen=True)
class CanonicalViolation:
    """Represents the legal consequence of an unexcused norm breach."""

    violation_id: str
    norm_id: str
    trigger_fact: str
    consequence_fact: str
    reparations: Tuple["CanonicalReparation", ...] = ()


@dataclass(frozen=True)
class CanonicalNorm:
    """Minimal norm representation for the specification layer."""

    norm_id: str
    modality: Modality
    actor: str
    action: str
    condition_facts: Tuple[str, ...]
    exception_facts: Tuple[str, ...] = ()
    violation: Optional[CanonicalViolation] = None


@dataclass(frozen=True)
class CanonicalRule:
    """Canonical rule form shared by formal specs and the reference evaluator."""

    rule_id: str
    kind: RuleKind
    premises: Tuple[str, ...]
    conclusions: Tuple[str, ...]
    exceptions: Tuple[str, ...] = ()
    priority_over: Tuple[str, ...] = ()
    notes: str = ""


@dataclass(frozen=True)
class CanonicalClaim:
    """A claim submitted to the argumentation layer."""

    claim_id: str
    conclusion: str
    basis_rules: Tuple[str, ...] = ()


@dataclass(frozen=True)
class CanonicalArgument:
    """A structured argument produced from a rule firing and supporting facts."""

    argument_id: str
    claim_id: str
    rule_id: str
    conclusion: str
    support_facts: Tuple[str, ...]
    exception_facts: Tuple[str, ...] = ()


@dataclass(frozen=True)
class CanonicalAttack:
    """A directed attack or defeat between two arguments."""

    attack_id: str
    attacker_id: str
    target_id: str
    kind: AttackKind
    reason: str


@dataclass(frozen=True)
class CanonicalProofStep:
    """A single trace step emitted by the reference layer."""

    step_index: int
    phase: str
    event: str
    payload: Dict[str, Any]


@dataclass(frozen=True)
class CanonicalProofTrace:
    """Canonical trace container used for shadow validation downstream."""

    trace_id: str
    status: DecisionStatus
    steps: Tuple[CanonicalProofStep, ...]
    fail_closed_reason: Optional[str] = None
