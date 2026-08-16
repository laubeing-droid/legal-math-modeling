from __future__ import annotations

from copy import deepcopy

import pytest

from theory.spec.runtime_differential import (
    build_expected_fixture,
    build_runtime_receipt_for_test,
    verify_runtime_refinement_receipt,
)


def _expected() -> dict:
    return build_expected_fixture(
        lmm_commit="1" * 40,
        fixture_cases=(
            {"case_id": "contract::plain", "expected_status": "PROVED"},
            {"case_id": "contract::force-majeure", "expected_status": "REFUTED"},
        ),
        source_snapshot_digests=("a" * 64,),
        rule_pack_digest="b" * 64,
    )


def _actual(expected: dict) -> dict:
    return build_runtime_receipt_for_test(
        expected,
        runtime_commit="2" * 40,
        actual_cases=(
            {"case_id": "contract::plain", "actual_status": "PROVED"},
            {"case_id": "contract::force-majeure", "actual_status": "REFUTED"},
        ),
    )


def test_external_runtime_receipt_is_verified_independently() -> None:
    expected = _expected()
    report = verify_runtime_refinement_receipt(
        expected,
        _actual(expected),
        expected_lmm_commit="1" * 40,
        expected_runtime_commit="2" * 40,
    )

    assert report.passed is True
    assert report.blocked is False


def test_missing_actual_receipt_is_fail_closed() -> None:
    report = verify_runtime_refinement_receipt(_expected(), None)

    assert report.passed is False
    assert report.blocked is True
    assert "MISSING_ACTUAL_RECEIPT" in report.error_codes


@pytest.mark.parametrize(
    ("mutator", "code"),
    (
        (lambda r: r.update(runtime_commit="3" * 40), "RUNTIME_COMMIT_MISMATCH"),
        (lambda r: r.update(fixture_digest="c" * 64), "FIXTURE_DIGEST_MISMATCH"),
        (lambda r: r.update(execution_status="ERROR"), "RUNTIME_EXECUTION_FAILED"),
        (lambda r: r["cases"][0].update(actual_status="UNKNOWN"), "UNKNOWN_STATUS_MAPPING"),
    ),
)
def test_runtime_receipt_rejects_binding_and_status_mutations(mutator, code: str) -> None:
    expected = _expected()
    actual = deepcopy(_actual(expected))
    mutator(actual)

    report = verify_runtime_refinement_receipt(
        expected,
        actual,
        expected_lmm_commit="1" * 40,
        expected_runtime_commit="2" * 40,
    )

    assert report.passed is False
    assert code in report.error_codes

