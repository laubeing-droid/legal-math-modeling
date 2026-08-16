from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

from theory.spec.runtime_differential import (
    build_runtime_receipt_for_test,
    verify_runtime_refinement_receipt,
)

REPO_ROOT = Path(__file__).resolve().parents[1]
FIXTURE_DIR = REPO_ROOT / "runtime" / "refinement_cases"


def _load_expected(name: str) -> dict:
    return json.loads((FIXTURE_DIR / name).read_text(encoding="utf-8"))


def test_expected_fixtures_are_materialized_and_well_formed() -> None:
    for name in (
        "contract_breach.expected.json",
        "fact_admission.expected.json",
        "unknown_timeout.expected.json",
    ):
        fixture = _load_expected(name)

        assert fixture["schema_version"] == "spec-runtime-refinement-v2"
        assert fixture["role"] == "expected"
        assert len(fixture["fixture_digest"]) == 64
        assert fixture["cases"]
        assert fixture["subject_commit_binding"] == "CI_SUBJECT_SHA"


def test_expected_fixture_accepts_matching_external_receipt() -> None:
    expected = _load_expected("contract_breach.expected.json")
    actual = build_runtime_receipt_for_test(
        expected,
        runtime_commit="9" * 40,
        actual_cases=(
            {"case_id": case["case_id"], "actual_status": case["expected_status"]}
            for case in expected["cases"]
        ),
    )

    report = verify_runtime_refinement_receipt(
        expected, actual, expected_lmm_commit=expected["lmm_commit"]
    )

    assert report.passed is True
    assert report.blocked is False


def test_expected_fixture_rejects_status_mismatch() -> None:
    expected = _load_expected("unknown_timeout.expected.json")
    actual = build_runtime_receipt_for_test(
        expected,
        runtime_commit="9" * 40,
        actual_cases=(
            {"case_id": "backend::unknown-outcome", "actual_status": "PROVED"},
            {"case_id": "backend::timeout-outcome", "actual_status": "UNDECIDED"},
        ),
    )

    report = verify_runtime_refinement_receipt(expected, actual)

    assert report.passed is False
    assert "STATUS_MISMATCH" in report.error_codes


def test_verifier_cli_is_fail_closed_without_actual_receipt(tmp_path: Path) -> None:
    expected_path = tmp_path / "expected.json"
    expected_path.write_text(
        json.dumps(_load_expected("fact_admission.expected.json")), encoding="utf-8"
    )

    result = subprocess.run(
        [
            sys.executable,
            str(REPO_ROOT / "scripts" / "verify_runtime_refinement_receipt.py"),
            "--expected",
            str(expected_path),
        ],
        capture_output=True,
        text=True,
        cwd=REPO_ROOT,
    )

    assert result.returncode == 1
    assert "MISSING_ACTUAL_RECEIPT" in result.stdout
