#!/usr/bin/env python3
"""
juris-calculus evidence-calibrated theory module.

This package no longer presents every early mathematical draft as a
completed proof. It is a model-design workspace calibrated by the
2026-06-11 strict proof baseline and legal-data validation baseline.

Usage:
    python -m theory --summary
    python -m theory --status

The status ledger is in model_status.py.
"""

from __future__ import annotations

import sys
from typing import Dict

try:
    from .model_status import CLAIMS, print_model_status_summary, validate_status_ledger
except ImportError:  # direct execution from this directory
    from model_status import CLAIMS, print_model_status_summary, validate_status_ledger


THEOREMS: Dict[str, str] = {
    claim_id: f"{claim.title} -- {claim.status.value}"
    for claim_id, claim in CLAIMS.items()
}


def print_summary() -> None:
    print("=" * 72)
    print("JURIS-CALCULUS THEORY -- Evidence-Calibrated Index")
    print("=" * 72)
    for i, (claim_id, desc) in enumerate(THEOREMS.items(), 1):
        print(f"  [{i}] {claim_id:28s} {desc}")
    print()
    print("Accepted package labels:")
    print("  - ACCEPTED_AS_STRICT_PROOF_BASELINE_WITH_LIMITATIONS")
    print("  - ACCEPTED_AS_LEGAL_DATA_VALIDATION_BASELINE_WITH_LIMITATIONS")
    print()
    print("Forbidden labels:")
    print("  - FINAL_ALL_THEOREMS_PROVED")
    print("  - REAL_PRICING_VALIDATED")
    print("  - DP_EPSILON_LEGALLY_DETERMINED")
    print("=" * 72)


def run_all(quick: bool = False) -> bool:
    """Validate the status ledger.

    The old runner executed early proof scripts with over-strong theorem
    wording. The calibrated runner checks that every production-relevant
    mathematical claim has an explicit evidence status and engineering
    action. Detailed runnable proofs live in the strict proof package.
    """
    del quick
    validate_status_ledger()
    print_summary()
    return True


if __name__ == "__main__":
    if "--status" in sys.argv:
        validate_status_ledger()
        print_model_status_summary()
    else:
        run_all(quick="--quick" in sys.argv)
