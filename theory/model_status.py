#!/usr/bin/env python3
"""
2026-06-11 evidence-calibrated model status ledger.

This module is the bridge between the early Claude mathematical-modeling
drafts and the later Codex/Kimi proof and legal-data validation packages.
It intentionally separates:

1. proved finite artifacts,
2. toy/synthetic proofs,
3. refuted claims,
4. data-insufficient claims,
5. engineering design directions.

Downstream code should import this ledger before turning a mathematical
claim into a production invariant.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from enum import Enum
from typing import Dict, List


class EvidenceStatus(str, Enum):
    PROVED_BY_EXHAUSTIVE_ENUMERATION = "PROVED_BY_EXHAUSTIVE_ENUMERATION"
    REFUTED_BY_COUNTEREXAMPLE = "REFUTED_BY_COUNTEREXAMPLE"
    DATA_INSUFFICIENT_FOR_PROOF = "DATA_INSUFFICIENT_FOR_PROOF"
    TOY_SYNTHETIC_PROOF_ONLY = "TOY_SYNTHETIC_PROOF_ONLY"
    PARTIAL_PROVED = "PARTIAL_PROVED"
    PENDING_TOOLCHAIN = "PENDING_TOOLCHAIN"
    ENGINEERING_BASELINE = "ENGINEERING_BASELINE"


class DataQuality(str, Enum):
    REAL = "real"              # Real legal data (court records, case law)
    SYNTHETIC = "synthetic"    # AI-generated or toy data
    PROXY = "proxy"            # Proxy data (fee schedules, not real timesheets)
    ANNOTATED = "annotated"    # Expert-annotated data
    UNKNOWN = "unknown"


@dataclass(frozen=True)
class ModelClaim:
    claim_id: str
    title: str
    status: EvidenceStatus
    data_quality: DataQuality = DataQuality.UNKNOWN
    allowed_claim: str = ""
    forbidden_claim: str = ""
    engineering_action: str = ""
    evidence_paths: List[str] = field(default_factory=list)


CLAIMS: Dict[str, ModelClaim] = {
    "A1_REAL_ROSETTA": ModelClaim(
        claim_id="A1_REAL_ROSETTA",
        title="Cross-jurisdiction Rosetta/category mapping on real data",
        status=EvidenceStatus.DATA_INSUFFICIENT_FOR_PROOF,
        data_quality=DataQuality.ANNOTATED,
        allowed_claim=(
            "Real CN/US/HK data contains source-backed collision and "
            "asymmetry witnesses, but does not prove a universal no-functor theorem."
        ),
        forbidden_claim="No total natural transformation has been formally proved for all real legal facts.",
        engineering_action="Use obstruction guards and jurisdiction-specific routing; do not auto-merge CN/US/HK claims.",
        evidence_paths=[
            "proofs/strict_proof_baseline/p0a_category",
            "data/cn_legal/",
        ],
    ),
    "A1_TOY_ROSETTA": ModelClaim(
        claim_id="A1_TOY_ROSETTA",
        title="Toy finite no-total-mapping checker",
        status=EvidenceStatus.TOY_SYNTHETIC_PROOF_ONLY,
        data_quality=DataQuality.SYNTHETIC,
        allowed_claim="The constructed 5-pattern toy model has no collision-free assignment.",
        forbidden_claim="The toy model does not prove the real legal inventory theorem.",
        engineering_action="Keep as a circuit-breaker test for synthetic/toy data promotion.",
        evidence_paths=[
            "proofs/strict_proof_baseline/p0a_category",
        ],
    ),
    "C_REAL_BANACH": ModelClaim(
        claim_id="C_REAL_BANACH",
        title="Real full-dimensional Banach pricing contraction",
        status=EvidenceStatus.DATA_INSUFFICIENT_FOR_PROOF,
        data_quality=DataQuality.PROXY,
        allowed_claim="Current pricing data is proxy-only and can validate schemas/gates, not real contraction.",
        forbidden_claim="Real LegalOS pricing is not empirically or formally proved as a full-dimensional Banach contraction.",
        engineering_action="Use pricing data-insufficiency gate; require real timesheets before calibration claims.",
        evidence_paths=[
            "data/legal_validation_results.json",
        ],
    ),
    "C_TOY_BANACH": ModelClaim(
        claim_id="C_TOY_BANACH",
        title="Toy scalar/effective-node contraction",
        status=EvidenceStatus.TOY_SYNTHETIC_PROOF_ONLY,
        data_quality=DataQuality.SYNTHETIC,
        allowed_claim="A scalar/toy smoothing map can be a contraction under explicit beta and metric assumptions.",
        forbidden_claim="This does not validate production pricing across all dimensions.",
        engineering_action="Implement only behind an experimental calibration interface with data-quality labels.",
        evidence_paths=[
            "proofs/strict_proof_baseline/p0c_banach",
        ],
    ),
    "D_PRIVILEGE_EPSILON": ModelClaim(
        claim_id="D_PRIVILEGE_EPSILON",
        title="Legal privilege determines DP epsilon",
        status=EvidenceStatus.REFUTED_BY_COUNTEREXAMPLE,
        data_quality=DataQuality.ANNOTATED,
        allowed_claim="Law can classify release modes; epsilon is a policy parameter with audit labels.",
        forbidden_claim="A legal privilege level does not determine a unique numerical epsilon.",
        engineering_action="Expose epsilon as policy config; require approval and provenance for each data class.",
        evidence_paths=[
            "proofs/strict_proof_baseline/p0d_privilege_epsilon",
            "data/dp_privilege/",
        ],
    ),
    "E_AAF_GROUNDED": ModelClaim(
        claim_id="E_AAF_GROUNDED",
        title="Dung AAF grounded extension",
        status=EvidenceStatus.PROVED_BY_EXHAUSTIVE_ENUMERATION,
        data_quality=DataQuality.SYNTHETIC,
        allowed_claim="Grounded extension is executable and exhaustively verified for directed attack graphs with n <= 4.",
        forbidden_claim="This does not prove equivalence with the original nonmonotone evaluator for all production rules.",
        engineering_action="Use a stratified two-stage evaluator: monotone Horn closure first, Dung AAF second.",
        evidence_paths=[
            "proofs/strict_proof_baseline/p1e_aaf",
            "data/aaf_legal/",
        ],
    ),
    "E_ORIGINAL_EVALUATOR_MONOTONE": ModelClaim(
        claim_id="E_ORIGINAL_EVALUATOR_MONOTONE",
        title="Original rebuttal/confidence evaluator is monotone",
        status=EvidenceStatus.REFUTED_BY_COUNTEREXAMPLE,
        data_quality=DataQuality.SYNTHETIC,
        allowed_claim="Original evaluator has a nonmonotonic counterexample; bounded operational termination is separate.",
        forbidden_claim="Do not apply Tarski/Kleene monotone fixpoint proof directly to the full original evaluator.",
        engineering_action="Separate monotone Horn inference from rebuttal/exception argumentation.",
        evidence_paths=[
            "proofs/strict_proof_baseline/evaluator_nonmonotone_counterexample.json",
        ],
    ),
}


def get_claim(claim_id: str) -> ModelClaim:
    return CLAIMS[claim_id]


def print_model_status_summary() -> None:
    print("=" * 72)
    print("juris-calculus evidence-calibrated model status")
    print("=" * 72)
    for claim in CLAIMS.values():
        print(f"{claim.claim_id}: {claim.status.value}")
        print(f"  data_quality: {claim.data_quality.value}")
        print(f"  allowed:   {claim.allowed_claim}")
        print(f"  forbidden: {claim.forbidden_claim}")
        print(f"  action:    {claim.engineering_action}")
        print()


def validate_status_ledger() -> bool:
    """Basic internal consistency check for CI and handoff packages."""
    assert CLAIMS, "CLAIMS must not be empty"
    ids = [claim.claim_id for claim in CLAIMS.values()]
    assert len(ids) == len(set(ids)), "duplicate claim_id"
    for claim in CLAIMS.values():
        assert claim.allowed_claim
        assert claim.forbidden_claim
        assert claim.engineering_action
        assert claim.evidence_paths
    return True


if __name__ == "__main__":
    validate_status_ledger()
    print_model_status_summary()
