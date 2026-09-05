#!/usr/bin/env python3
"""Machine-readable canonical v2 manifest.

The manifest lists every v2 type by layer and every shared enum, so Lean
and Python stay aligned by comparison rather than by convention. This file
mirrors the Lean registry in `JurisLean/LegalModelV2.lean`; when the two
disagree, the drift gate fails closed. Python serializable contracts do
not take Lean-definition authority.
"""

from __future__ import annotations

from typing import Any, Dict, List

MANIFEST_SCHEMA = "spec-canonical-manifest-v2"

V1_CANONICAL_TYPES = (
    "LegalFact",
    "LegalRule",
    "LegalNorm",
    "LegalClaim",
    "Argument",
    "Attack",
    "Priority",
    "Violation",
    "Reparation",
    "DecisionStatus",
    "ProofTrace",
)

TYPE_LAYERS: Dict[str, List[str]] = {
    "identity": [
        "LegalId",
        "ContentDigest",
        "SchemaVersion",
        "SemanticsVersion",
        "CommitId",
        "TreeId",
        "BuildId",
        "CaseScope",
        "RunScope",
        "SourceLocator",
        "TimePoint",
        "TimeInterval",
        "ExactAmount",
        "ExactRate",
        "RoundingPolicy",
    ],
    "source": [
        "SourceSnapshotRef",
        "SourceVersionEdge",
        "SourcePath",
        "EvidenceRef",
        "InterpretationRef",
        "FactCandidate",
        "FactAdmissionAttestation",
        "ProposalEnvelope",
        "HumanResearchReceipt",
    ],
    "reasoning": list(V1_CANONICAL_TYPES) + ["Permission", "Exception"],
    "compilation": [
        "LegalSpec",
        "LegalIVL",
        "ProofObligation",
        "BackendKind",
        "BackendProblem",
        "BackendWitness",
        "TranslationWitness",
        "CheckerReceipt",
        "SolverReceipt",
        "ProofReceipt",
        "RuntimeRefinementReceipt",
    ],
}

ENUM_REGISTRY: Dict[str, List[str]] = {
    "IdKind": [
        "fact",
        "rule",
        "norm",
        "claim",
        "argument",
        "attack",
        "obligation",
        "snapshot",
        "receipt",
        "certificate",
        "scope",
    ],
    "Modality": ["OBLIGATION", "PROHIBITION", "PERMISSION", "CONSTITUTIVE"],
    "RuleKind": ["HORN", "EXCEPTION", "PRIORITY", "CONSTITUTIVE"],
    "AttackKind": [
        "REBUTTAL",
        "EXCEPTION",
        "PRIORITY_DEFEAT",
        "UNDERCUT",
        "PREMISE_CHALLENGE",
    ],
    "DecisionStatus": ["PROVED", "REFUTED", "UNDECIDED", "TAINTED"],
    "FailureStatus": [
        "SUCCESS",
        "UNKNOWN",
        "TIMEOUT",
        "SKIP",
        "NOT_RUN",
        "BACKEND_UNAVAILABLE",
        "ERROR",
        "CI_NOT_RUN",
    ],
    "GateStatus": ["PASS", "FAIL", "BLOCKED", "DISPUTED"],
    "AuthorityLevel": [
        "UNTRUSTED_PROPOSAL",
        "SOURCE_BOUND_CANDIDATE",
        "HUMAN_REVIEWED_CANDIDATE",
        "ADMITTED_FORMAL_INPUT",
    ],
    "BackendKind": [
        "DIRECT_REFERENCE",
        "HORN",
        "ARGUMENTATION",
        "CLOSED_FORM",
        "ASP",
        "SMT",
    ],
}


def canonical_v2_type_names() -> List[str]:
    """Full v2 universe in layer order (identity, source, reasoning, compilation)."""

    names: List[str] = []
    for layer in ("identity", "source", "reasoning", "compilation"):
        names.extend(TYPE_LAYERS[layer])
    return names


def build_manifest() -> Dict[str, Any]:
    """Emit the machine-readable manifest with derived counts and invariants."""

    names = canonical_v2_type_names()
    return {
        "schema_version": MANIFEST_SCHEMA,
        "type_layers": TYPE_LAYERS,
        "enum_registry": ENUM_REGISTRY,
        "type_count": len(names),
        "type_names": names,
        "invariants": {
            "no_duplicate_type_names": len(names) == len(set(names)),
            "v1_types_preserved_in_reasoning": all(
                name in TYPE_LAYERS["reasoning"] for name in V1_CANONICAL_TYPES
            ),
        },
    }
