from __future__ import annotations

from copy import deepcopy
import hashlib
import json
from pathlib import Path
import subprocess
import sys

import pytest

from scripts.materialize_runtime_refinement_expected import materialize_expected_fixture
from scripts.verify_runtime_refinement_receipt import verification_payload
from theory.spec.runtime_differential import (
    build_expected_fixture,
    build_runtime_receipt_for_test,
    verify_runtime_refinement_receipt,
)


LMM_COMMIT = "1" * 40
RUNTIME_COMMIT = "2" * 40
SOURCE_DIGEST = "a" * 64
RULE_PACK_DIGEST = "b" * 64
ROOT = Path(__file__).resolve().parents[2]


def _canonical_sha256(value: object) -> str:
    return hashlib.sha256(
        json.dumps(
            value,
            ensure_ascii=False,
            sort_keys=True,
            separators=(",", ":"),
        ).encode("utf-8")
    ).hexdigest()


def _semantic_result(*, claims: tuple[str, ...] = ("claim::plain",)) -> dict:
    payload = {
        "schema_version": "3.0",
        "run_id": "run::fixture",
        "execution_status": "completed",
        "result_status": "accepted_formal_result",
        "formal_kernel_used": True,
        "review_required": False,
        "checker_accepted": True,
        "certificate_kind": "formal",
        "engine_version": "3.0.2",
        "pack_id": "lmm-refinement-fixture",
        "pack_version": "1.0.0",
        "pack_digest": RULE_PACK_DIGEST,
        "claims": list(claims),
        "branches": [],
        "used_fact_ids": ["fact::plain"],
        "used_rule_ids": ["rule::plain"],
        "source_ids": [f"fixture-source@{SOURCE_DIGEST}"],
        "missing_fact_ids": [],
        "missing_fact_review": [],
        "taint": [],
        "risk_labels": [],
        "checker_receipt": {
            "receipt_kind": "independent_grounded_checker",
            "valid": True,
            "violations": [],
            "claim_projection": {
                "accepted_argument_ids": ["arg::plain"],
                "accepted_claim_ids": list(claims),
            },
        },
    }
    payload["result_digest"] = _canonical_sha256(payload)
    return payload


def _expected() -> dict:
    return build_expected_fixture(
        lmm_commit=LMM_COMMIT,
        fixture_cases=(
            {
                "case_id": "contract::plain",
                "expected_status": "PROVED",
                "projection": {
                    "focus_claim_id": "claim::plain",
                    "refuting_claim_ids": ["claim::plain-refuter"],
                },
            },
        ),
        source_snapshot_digests=(SOURCE_DIGEST,),
        rule_pack_digest=RULE_PACK_DIGEST,
    )


def _actual(expected: dict) -> dict:
    return build_runtime_receipt_for_test(
        expected,
        runtime_commit=RUNTIME_COMMIT,
        actual_cases=(
            {
                "case_id": "contract::plain",
                "audit_bundle_digest": "c" * 64,
                "semantic_result": _semantic_result(),
            },
        ),
    )


def _rehash_case_and_receipt(receipt: dict, case_index: int = 0) -> None:
    case = receipt["cases"][case_index]
    case_payload = dict(case)
    case_payload.pop("output_digest", None)
    case["output_digest"] = _canonical_sha256(case_payload)
    receipt_payload = dict(receipt)
    receipt_payload.pop("receipt_digest", None)
    receipt["receipt_digest"] = _canonical_sha256(receipt_payload)


def test_external_runtime_receipt_is_verified_independently() -> None:
    expected = _expected()
    report = verify_runtime_refinement_receipt(
        expected,
        _actual(expected),
        expected_lmm_commit=LMM_COMMIT,
        expected_runtime_commit=RUNTIME_COMMIT,
    )

    assert report.passed is True
    assert report.receipt_valid is True
    assert report.aligned is True
    assert report.blocked is False
    assert report.compared_case_ids == ("contract::plain",)


def test_missing_actual_receipt_is_fail_closed() -> None:
    report = verify_runtime_refinement_receipt(_expected(), None)

    assert report.passed is False
    assert report.receipt_valid is False
    assert report.aligned is False
    assert report.blocked is True
    assert "MISSING_ACTUAL_RECEIPT" in report.error_codes


def test_v1_runtime_receipt_is_never_v2_decisive() -> None:
    actual = _actual(_expected())
    actual["schema_version"] = "runtime-refinement-receipt-v1"
    _rehash_case_and_receipt(actual)

    report = verify_runtime_refinement_receipt(_expected(), actual)

    assert report.passed is False
    assert "LEGACY_RECEIPT_NOT_DECISIVE" in report.error_codes


@pytest.mark.parametrize(
    ("mutator", "code"),
    (
        (lambda r: r.update(runtime_commit="3" * 40), "RUNTIME_COMMIT_MISMATCH"),
        (lambda r: r.update(fixture_digest="d" * 64), "FIXTURE_DIGEST_MISMATCH"),
        (lambda r: r.update(execution_status="ERROR"), "RUNTIME_EXECUTION_FAILED"),
        (lambda r: r["cases"][0].update(actual_status="UNKNOWN"), "UNKNOWN_STATUS_MAPPING"),
        (lambda r: r["cases"][0].update(audit_bundle_digest="e" * 64), "OUTPUT_DIGEST_MISMATCH"),
    ),
)
def test_runtime_receipt_rejects_binding_and_status_mutations(mutator, code: str) -> None:
    expected = _expected()
    actual = deepcopy(_actual(expected))
    mutator(actual)

    report = verify_runtime_refinement_receipt(
        expected,
        actual,
        expected_lmm_commit=LMM_COMMIT,
        expected_runtime_commit=RUNTIME_COMMIT,
    )

    assert report.passed is False
    assert code in report.error_codes


def test_actual_status_cannot_be_self_reported_even_with_fresh_digests() -> None:
    expected = _expected()
    actual = deepcopy(_actual(expected))
    actual["cases"][0]["actual_status"] = "REFUTED"
    _rehash_case_and_receipt(actual)

    report = verify_runtime_refinement_receipt(expected, actual)

    assert report.receipt_valid is False
    assert report.aligned is False
    assert "STATUS_DERIVATION_MISMATCH" in report.error_codes


def test_embedded_runtime_semantic_result_is_recomputed() -> None:
    expected = _expected()
    actual = deepcopy(_actual(expected))
    actual["cases"][0]["semantic_result"]["claims"] = ["claim::forged"]
    _rehash_case_and_receipt(actual)

    report = verify_runtime_refinement_receipt(expected, actual)

    assert report.receipt_valid is False
    assert "RUNTIME_RESULT_DIGEST_MISMATCH" in report.error_codes


def test_valid_receipt_can_report_a_real_cross_runtime_divergence() -> None:
    expected = _expected()
    actual = build_runtime_receipt_for_test(
        expected,
        runtime_commit=RUNTIME_COMMIT,
        actual_cases=(
            {
                "case_id": "contract::plain",
                "audit_bundle_digest": "c" * 64,
                "semantic_result": _semantic_result(claims=("claim::plain-refuter",)),
            },
        ),
    )

    report = verify_runtime_refinement_receipt(expected, actual)

    assert report.receipt_valid is True
    assert report.aligned is False
    assert report.passed is False
    assert report.error_codes == ("RESULT_MISMATCH",)


def test_tracked_schema_requires_embedded_runtime_evidence() -> None:
    schema = json.loads(
        (ROOT / "runtime" / "runtime_refinement_receipt.schema.json").read_text(
            encoding="utf-8"
        )
    )
    case_schema = schema["properties"]["cases"]["items"]

    assert schema["properties"]["schema_version"]["const"] == (
        "runtime-refinement-receipt-v2"
    )
    assert {"audit_bundle_digest", "semantic_result"} <= set(case_schema["required"])
    assert "actual_status" not in case_schema["properties"]["semantic_result"].get(
        "properties", {}
    )


def test_tracked_template_is_projection_complete_and_expected_only() -> None:
    template = json.loads(
        (
            ROOT
            / "runtime"
            / "refinement_cases"
            / "four_slice_expected.template.json"
        ).read_text(encoding="utf-8")
    )

    assert template["schema_version"] == "runtime-refinement-expected-template-v2"
    assert template["status"] == "expected_only_not_runtime_receipt"
    assert len(template["cases"]) == 10
    assert all(
        case["projection"]["focus_claim_id"]
        and case["projection"]["refuting_claim_ids"] == sorted(
            case["projection"]["refuting_claim_ids"]
        )
        for case in template["cases"]
    )


def test_materializer_turns_template_into_commit_bound_expected_fixture() -> None:
    template = json.loads(
        (
            ROOT
            / "runtime"
            / "refinement_cases"
            / "four_slice_expected.template.json"
        ).read_text(encoding="utf-8")
    )

    expected = materialize_expected_fixture(
        template,
        lmm_commit=LMM_COMMIT,
        source_snapshot_digests=(SOURCE_DIGEST,),
        rule_pack_digest=RULE_PACK_DIGEST,
    )

    assert expected["schema_version"] == "runtime-refinement-expected-v2"
    assert expected["lmm_commit"] == LMM_COMMIT
    assert len(expected["cases"]) == 10
    payload = dict(expected)
    assert payload.pop("fixture_digest") == _canonical_sha256(payload)


def test_verifier_cli_payload_distinguishes_invalid_from_divergent() -> None:
    expected = _expected()
    divergent = build_runtime_receipt_for_test(
        expected,
        runtime_commit=RUNTIME_COMMIT,
        actual_cases=(
            {
                "case_id": "contract::plain",
                "audit_bundle_digest": "c" * 64,
                "semantic_result": _semantic_result(
                    claims=("claim::plain-refuter",)
                ),
            },
        ),
    )
    divergent_report = verify_runtime_refinement_receipt(expected, divergent)
    invalid = deepcopy(divergent)
    invalid["receipt_digest"] = "d" * 64
    invalid_report = verify_runtime_refinement_receipt(expected, invalid)

    assert verification_payload(divergent_report)["status"] == "INCONCLUSIVE"
    assert verification_payload(invalid_report)["status"] == "BLOCKED"


@pytest.mark.parametrize(
    "script_name",
    (
        "materialize_runtime_refinement_expected.py",
        "verify_runtime_refinement_receipt.py",
    ),
)
def test_runtime_refinement_scripts_support_direct_execution(script_name: str) -> None:
    completed = subprocess.run(
        [sys.executable, str(ROOT / "scripts" / script_name), "--help"],
        cwd=ROOT.parent,
        capture_output=True,
        text=True,
        check=False,
    )

    assert completed.returncode == 0, completed.stderr
    assert "usage:" in completed.stdout


def test_tracked_external_receipt_remains_valid_but_inconclusive() -> None:
    evidence_root = ROOT / "docs" / "remediation" / "runtime-refinement"
    expected = json.loads(
        (evidence_root / "expected-b9925428.json").read_text(encoding="utf-8")
    )
    bindings = json.loads(
        (evidence_root / "run-bindings-be60fc2f.json").read_text(encoding="utf-8")
    )
    actual = json.loads(
        (evidence_root / "runtime-receipt-b9925428-be60fc2f.json").read_text(
            encoding="utf-8"
        )
    )

    report = verify_runtime_refinement_receipt(
        expected,
        actual,
        expected_lmm_commit="b9925428ca1c8663c8dbca236c1d5d2f231097af",
        expected_runtime_commit="be60fc2f5aebf76c909d8ff81e269c969664435a",
    )

    assert all(set(case) == {"case_id", "run_id"} for case in bindings["cases"])
    assert report.receipt_valid is True
    assert report.aligned is False
    assert report.passed is False
    assert report.error_codes == ("RESULT_MISMATCH",)
    assert len(report.compared_case_ids) == 10
