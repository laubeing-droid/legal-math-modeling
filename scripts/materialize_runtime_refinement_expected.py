#!/usr/bin/env python3
"""Materialize LMM-side expected refinement fixtures (M9, party 1).

Writes content-addressed expected fixtures for the runtime refinement
pipeline. The actual receipts must come from the external runtime through
its formal public entry (party 2); comparison happens in the independent
verifier (party 3). Local output is never evidence until CI binds it to
the subject commit.
"""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from theory.spec.runtime_differential import build_expected_fixture

PLACEHOLDER_COMMIT = "0" * 40


def contract_breach_fixture(lmm_commit: str) -> dict:
    return build_expected_fixture(
        lmm_commit=lmm_commit,
        fixture_cases=(
            {"case_id": "contract::plain", "expected_status": "PROVED"},
            {"case_id": "contract::force-majeure", "expected_status": "REFUTED"},
            {"case_id": "contract::malformed-certificate", "expected_status": "TAINTED"},
        ),
        source_snapshot_digests=("a" * 64,),
        rule_pack_digest="b" * 64,
    )


def fact_admission_fixture(lmm_commit: str) -> dict:
    return build_expected_fixture(
        lmm_commit=lmm_commit,
        fixture_cases=(
            {"case_id": "admission::three-gates-pass", "expected_status": "PROVED"},
            {"case_id": "admission::interpretation-gate-fail", "expected_status": "UNDECIDED"},
            {"case_id": "admission::revoked-attestation", "expected_status": "UNDECIDED"},
        ),
        source_snapshot_digests=("c" * 64,),
        rule_pack_digest="d" * 64,
    )


def unknown_timeout_fixture(lmm_commit: str) -> dict:
    return build_expected_fixture(
        lmm_commit=lmm_commit,
        fixture_cases=(
            {"case_id": "backend::unknown-outcome", "expected_status": "UNDECIDED"},
            {"case_id": "backend::timeout-outcome", "expected_status": "UNDECIDED"},
        ),
        source_snapshot_digests=("e" * 64,),
        rule_pack_digest="f" * 64,
    )


FIXTURE_BUILDERS = {
    "contract_breach.expected.json": contract_breach_fixture,
    "fact_admission.expected.json": fact_admission_fixture,
    "unknown_timeout.expected.json": unknown_timeout_fixture,
}


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--output-dir", type=Path, required=True)
    parser.add_argument(
        "--lmm-commit",
        default=PLACEHOLDER_COMMIT,
        help="Subject LMM commit; CI must bind CI_SUBJECT_SHA, not a placeholder.",
    )
    args = parser.parse_args()

    args.output_dir.mkdir(parents=True, exist_ok=True)
    for name, builder in FIXTURE_BUILDERS.items():
        fixture = builder(args.lmm_commit)
        fixture["subject_commit_binding"] = (
            "CI_SUBJECT_SHA" if args.lmm_commit == PLACEHOLDER_COMMIT else args.lmm_commit
        )
        target = args.output_dir / name
        target.write_text(
            json.dumps(fixture, ensure_ascii=False, indent=2) + "\n", encoding="utf-8"
        )
        print(f"wrote {target}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
