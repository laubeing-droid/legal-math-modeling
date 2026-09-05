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
import hashlib
import json
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from theory.spec.runtime_differential import build_expected_fixture

PLACEHOLDER_COMMIT = "0" * 40


def _canonical_digest(payload: object) -> str:
    encoded = json.dumps(
        payload, sort_keys=True, separators=(",", ":"), ensure_ascii=False
    ).encode("utf-8")
    return hashlib.sha256(encoded).hexdigest()


def _bindings(
    fixture_dir: Path | None,
    group: str,
    case_ids: tuple[str, ...],
    *,
    placeholder_source: str,
    placeholder_rules: str,
) -> tuple[tuple[str, ...], str]:
    if fixture_dir is None:
        return (placeholder_source,), placeholder_rules
    path = fixture_dir / f"{group}.fixture.json"
    fixture = json.loads(path.read_text(encoding="utf-8"))
    if (
        fixture.get("schema_version") != "jc/runtime-refinement-fixture/1.0"
        or fixture.get("group") != group
        or set(fixture) != {"schema_version", "group", "source_snapshot", "rule_pack"}
    ):
        raise ValueError(f"invalid Juris Calculus refinement fixture: {path}")
    actual_case_ids = tuple(
        case["case_id"] for case in fixture["source_snapshot"]["cases"]
    )
    if actual_case_ids != case_ids:
        raise ValueError(f"Juris Calculus case identities differ for {group}")
    return (
        (_canonical_digest(fixture["source_snapshot"]),),
        _canonical_digest(fixture["rule_pack"]),
    )


def contract_breach_fixture(
    lmm_commit: str, fixture_dir: Path | None = None
) -> dict:
    case_ids = (
        "contract::plain",
        "contract::force-majeure",
        "contract::malformed-certificate",
    )
    source_digests, rule_pack_digest = _bindings(
        fixture_dir,
        "contract_breach",
        case_ids,
        placeholder_source="a" * 64,
        placeholder_rules="b" * 64,
    )
    return build_expected_fixture(
        lmm_commit=lmm_commit,
        fixture_cases=(
            {"case_id": "contract::plain", "expected_status": "PROVED"},
            {"case_id": "contract::force-majeure", "expected_status": "REFUTED"},
            {"case_id": "contract::malformed-certificate", "expected_status": "TAINTED"},
        ),
        source_snapshot_digests=source_digests,
        rule_pack_digest=rule_pack_digest,
    )


def fact_admission_fixture(
    lmm_commit: str, fixture_dir: Path | None = None
) -> dict:
    case_ids = (
        "admission::three-gates-pass",
        "admission::disputed-fact",
        "admission::revoked-attestation",
    )
    source_digests, rule_pack_digest = _bindings(
        fixture_dir,
        "fact_admission",
        case_ids,
        placeholder_source="c" * 64,
        placeholder_rules="d" * 64,
    )
    return build_expected_fixture(
        lmm_commit=lmm_commit,
        fixture_cases=(
            {"case_id": "admission::three-gates-pass", "expected_status": "PROVED"},
            {"case_id": "admission::disputed-fact", "expected_status": "UNDECIDED"},
            {"case_id": "admission::revoked-attestation", "expected_status": "UNDECIDED"},
        ),
        source_snapshot_digests=source_digests,
        rule_pack_digest=rule_pack_digest,
    )


def unknown_timeout_fixture(
    lmm_commit: str, fixture_dir: Path | None = None
) -> dict:
    case_ids = ("backend::unknown-outcome", "backend::timeout-outcome")
    source_digests, rule_pack_digest = _bindings(
        fixture_dir,
        "unknown_timeout",
        case_ids,
        placeholder_source="e" * 64,
        placeholder_rules="f" * 64,
    )
    return build_expected_fixture(
        lmm_commit=lmm_commit,
        fixture_cases=(
            {"case_id": "backend::unknown-outcome", "expected_status": "UNDECIDED"},
            {"case_id": "backend::timeout-outcome", "expected_status": "UNDECIDED"},
        ),
        source_snapshot_digests=source_digests,
        rule_pack_digest=rule_pack_digest,
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
    parser.add_argument(
        "--runtime-fixture-dir",
        type=Path,
        default=None,
        help="Juris Calculus executable fixtures whose content must bind CI evidence.",
    )
    args = parser.parse_args()

    args.output_dir.mkdir(parents=True, exist_ok=True)
    for name, builder in FIXTURE_BUILDERS.items():
        fixture = builder(args.lmm_commit, args.runtime_fixture_dir)
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
