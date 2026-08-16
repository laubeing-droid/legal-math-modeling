#!/usr/bin/env python3
"""Typed identity, canonical serialization, and digest helpers for v2.

Typed IDs carry their kind in the value domain; parsing enforces the kind,
so a fact id can never be substituted for a rule id. Canonicalization is
deterministic (sorted, duplicate-free) and digests bind canonical content
only; a digest never proves authority.
"""

from __future__ import annotations

import hashlib
import json
from dataclasses import dataclass
from enum import Enum
from typing import Any, Iterable, List


class IdKind(str, Enum):
    """Typed ID kinds; aligned with Lean `IdKind`."""

    FACT = "fact"
    RULE = "rule"
    NORM = "norm"
    CLAIM = "claim"
    ARGUMENT = "argument"
    ATTACK = "attack"
    OBLIGATION = "obligation"
    SNAPSHOT = "snapshot"
    RECEIPT = "receipt"
    CERTIFICATE = "certificate"
    SCOPE = "scope"


class Modality(str, Enum):
    OBLIGATION = "OBLIGATION"
    PROHIBITION = "PROHIBITION"
    PERMISSION = "PERMISSION"
    CONSTITUTIVE = "CONSTITUTIVE"


class RuleKind(str, Enum):
    HORN = "HORN"
    EXCEPTION = "EXCEPTION"
    PRIORITY = "PRIORITY"
    CONSTITUTIVE = "CONSTITUTIVE"


class AttackKind(str, Enum):
    REBUTTAL = "REBUTTAL"
    EXCEPTION = "EXCEPTION"
    PRIORITY_DEFEAT = "PRIORITY_DEFEAT"
    UNDERCUT = "UNDERCUT"
    PREMISE_CHALLENGE = "PREMISE_CHALLENGE"


class DecisionStatus(str, Enum):
    PROVED = "PROVED"
    REFUTED = "REFUTED"
    UNDECIDED = "UNDECIDED"
    TAINTED = "TAINTED"


class FailureStatus(str, Enum):
    """Execution/evidence statuses; everything except SUCCESS fails closed."""

    SUCCESS = "SUCCESS"
    UNKNOWN = "UNKNOWN"
    TIMEOUT = "TIMEOUT"
    SKIP = "SKIP"
    NOT_RUN = "NOT_RUN"
    BACKEND_UNAVAILABLE = "BACKEND_UNAVAILABLE"
    ERROR = "ERROR"
    CI_NOT_RUN = "CI_NOT_RUN"

    @property
    def fail_closed(self) -> bool:
        return self is not FailureStatus.SUCCESS


class GateStatus(str, Enum):
    PASS = "PASS"
    FAIL = "FAIL"
    BLOCKED = "BLOCKED"
    DISPUTED = "DISPUTED"


class AuthorityLevel(str, Enum):
    """Proposal authority lattice; levels never auto-escalate."""

    UNTRUSTED_PROPOSAL = "UNTRUSTED_PROPOSAL"
    SOURCE_BOUND_CANDIDATE = "SOURCE_BOUND_CANDIDATE"
    HUMAN_REVIEWED_CANDIDATE = "HUMAN_REVIEWED_CANDIDATE"
    ADMITTED_FORMAL_INPUT = "ADMITTED_FORMAL_INPUT"


class BackendKind(str, Enum):
    DIRECT_REFERENCE = "DIRECT_REFERENCE"
    HORN = "HORN"
    ARGUMENTATION = "ARGUMENTATION"
    CLOSED_FORM = "CLOSED_FORM"
    ASP = "ASP"
    SMT = "SMT"


AUTHORITY_ORDER = (
    AuthorityLevel.UNTRUSTED_PROPOSAL,
    AuthorityLevel.SOURCE_BOUND_CANDIDATE,
    AuthorityLevel.HUMAN_REVIEWED_CANDIDATE,
    AuthorityLevel.ADMITTED_FORMAL_INPUT,
)


def authority_rank(level: AuthorityLevel) -> int:
    return AUTHORITY_ORDER.index(level)


@dataclass(frozen=True)
class TypedId:
    """An identifier whose kind is part of its identity."""

    kind: IdKind
    payload: str

    def __post_init__(self) -> None:
        if not self.payload:
            raise ValueError("TypedId payload must be non-empty")

    @property
    def canonical(self) -> str:
        return f"{self.kind.value}::{self.payload}"

    @classmethod
    def parse(cls, raw: str, expected_kind: IdKind) -> "TypedId":
        prefix, sep, payload = raw.partition("::")
        if not sep or not payload:
            raise ValueError(f"Malformed typed id: {raw!r}")
        try:
            kind = IdKind(prefix)
        except ValueError as exc:
            raise ValueError(f"Unknown id kind in {raw!r}") from exc
        if kind is not expected_kind:
            raise ValueError(
                f"Id kind mismatch: expected {expected_kind.value}, got {kind.value}"
            )
        return cls(kind=kind, payload=payload)


def canonical_json(value: Any) -> str:
    """Deterministic JSON form: sorted keys, tight separators, UTF-8."""

    return json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=False)


def canonical_digest(value: Any) -> str:
    """SHA-256 over the canonical JSON form; content binding only."""

    return hashlib.sha256(canonical_json(value).encode("utf-8")).hexdigest()


def canonical_collection(ids: Iterable[TypedId]) -> List[str]:
    """Deterministic duplicate-free canonical ordering of typed ids."""

    rendered = [typed_id.canonical for typed_id in ids]
    return sorted(set(rendered))
