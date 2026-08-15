#!/usr/bin/env python3
"""Canonical semantics v2 reference package.

This package is the decisive v2 semantic universe on the Python side.
`theory/spec/canonical_semantics.py` remains the v1 compatibility entry;
v1 never gains v2 decisive status. Names, field semantics, and enums are
aligned with the Lean registry through the machine-readable manifest in
`manifest.py`; Python serializable contracts do not take Lean-definition
authority.
"""

from .manifest import (
    ENUM_REGISTRY,
    MANIFEST_SCHEMA,
    TYPE_LAYERS,
    V1_CANONICAL_TYPES,
    build_manifest,
    canonical_v2_type_names,
)
from .migration import migrate_v1_payload
from .types import (
    AttackKind,
    AuthorityLevel,
    BackendKind,
    DecisionStatus,
    FailureStatus,
    GateStatus,
    IdKind,
    Modality,
    RuleKind,
    TypedId,
    canonical_collection,
    canonical_digest,
    canonical_json,
)

__all__ = [
    "AttackKind",
    "AuthorityLevel",
    "BackendKind",
    "DecisionStatus",
    "ENUM_REGISTRY",
    "FailureStatus",
    "GateStatus",
    "IdKind",
    "MANIFEST_SCHEMA",
    "Modality",
    "RuleKind",
    "TYPE_LAYERS",
    "TypedId",
    "V1_CANONICAL_TYPES",
    "build_manifest",
    "canonical_collection",
    "canonical_digest",
    "canonical_json",
    "canonical_v2_type_names",
    "migrate_v1_payload",
]
