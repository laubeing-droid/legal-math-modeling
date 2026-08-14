#!/usr/bin/env python3
"""Verify externally supplied runtime refinement receipts."""

from __future__ import annotations

from dataclasses import dataclass
import hashlib
import json
import re
from typing import Any, Iterable, Mapping, Tuple


COMMIT_PATTERN = re.compile(r"^[0-9a-f]{40}$")
DIGEST_PATTERN = re.compile(r"^[0-9a-f]{64}$")
KNOWN_STATUSES = {"PROVED", "REFUTED", "UNDECIDED", "TAINTED"}
KNOWN_SEMANTICS = {("grounded", "1")}


def _canonical_sha256(value: Any) -> str:
    content = json.dumps(
        value,
        ensure_ascii=False,
        sort_keys=True,
        separators=(",", ":"),
    ).encode("utf-8")
    return hashlib.sha256(content).hexdigest()


@dataclass(frozen=True)
class RuntimeRefinementReport:
    passed: bool
    blocked: bool
    error_codes: Tuple[str, ...]
    compared_case_ids: Tuple[str, ...] = ()


def build_expected_fixture(
    *,
    lmm_commit: str,
    fixture_cases: Iterable[Mapping[str, str]],
    source_snapshot_digests: Iterable[str],
    rule_pack_digest: str,
    semantics_id: str = "grounded",
    semantics_version: str = "1",
) -> dict[str, Any]:
    """Build content-addressed reference expectations without runtime output."""

    cases = sorted(
        (dict(case) for case in fixture_cases),
        key=lambda case: str(case.get("case_id", "")),
    )
    payload: dict[str, Any] = {
        "schema_version": "runtime-refinement-expected-v1",
        "lmm_commit": lmm_commit,
        "source_snapshot_digests": sorted(source_snapshot_digests),
        "rule_pack_digest": rule_pack_digest,
        "semantics": {"id": semantics_id, "version": semantics_version},
        "cases": cases,
    }
    payload["fixture_digest"] = _canonical_sha256(payload)
    return payload


def build_runtime_receipt_for_test(
    expected: Mapping[str, Any],
    *,
    runtime_commit: str,
    actual_cases: Iterable[Mapping[str, str]],
) -> dict[str, Any]:
    """Create unit-test input; production receipts must come from an external runtime."""

    cases: list[dict[str, Any]] = []
    for case in sorted(
        (dict(item) for item in actual_cases),
        key=lambda item: str(item.get("case_id", "")),
    ):
        case["output_digest"] = _canonical_sha256(case)
        cases.append(case)
    payload: dict[str, Any] = {
        "schema_version": "runtime-refinement-receipt-v1",
        "producer": "test-only-external-runtime",
        "execution_status": "PASS",
        "lmm_commit": expected.get("lmm_commit"),
        "runtime_commit": runtime_commit,
        "fixture_digest": expected.get("fixture_digest"),
        "source_snapshot_digests": list(expected.get("source_snapshot_digests", [])),
        "rule_pack_digest": expected.get("rule_pack_digest"),
        "semantics": dict(expected.get("semantics", {})),
        "cases": cases,
    }
    payload["receipt_digest"] = _canonical_sha256(payload)
    return payload


def _case_map(
    cases: Any, status_field: str
) -> tuple[dict[str, Mapping[str, Any]], set[str]]:
    errors: set[str] = set()
    if not isinstance(cases, list):
        return {}, {"MALFORMED_CASES"}
    result: dict[str, Mapping[str, Any]] = {}
    ids: list[str] = []
    for case in cases:
        if not isinstance(case, Mapping):
            errors.add("MALFORMED_CASE")
            continue
        case_id = str(case.get("case_id", ""))
        if not case_id or case_id in result:
            errors.add("DUPLICATE_CASE_ID")
        result[case_id] = case
        ids.append(case_id)
        if case.get(status_field) not in KNOWN_STATUSES:
            errors.add("UNKNOWN_STATUS_MAPPING")
    if ids != sorted(ids):
        errors.add("UNSTABLE_CASE_ORDER")
    return result, errors


def verify_runtime_refinement_receipt(
    expected: Mapping[str, Any],
    actual: Mapping[str, Any] | None,
    *,
    expected_lmm_commit: str | None = None,
    expected_runtime_commit: str | None = None,
) -> RuntimeRefinementReport:
    """Compare reference expectations with an actual receipt supplied by another process."""

    if actual is None:
        return RuntimeRefinementReport(
            False, True, ("MISSING_ACTUAL_RECEIPT",), ()
        )

    errors: set[str] = set()
    expected_payload = dict(expected)
    expected_digest = expected_payload.pop("fixture_digest", None)
    if expected.get("schema_version") != "runtime-refinement-expected-v1":
        errors.add("UNKNOWN_EXPECTED_SCHEMA")
    if expected_digest != _canonical_sha256(expected_payload):
        errors.add("EXPECTED_FIXTURE_DIGEST_MISMATCH")

    receipt_payload = dict(actual)
    receipt_digest = receipt_payload.pop("receipt_digest", None)
    if actual.get("schema_version") != "runtime-refinement-receipt-v1":
        errors.add("UNKNOWN_RECEIPT_SCHEMA")
    if receipt_digest != _canonical_sha256(receipt_payload):
        errors.add("RECEIPT_DIGEST_MISMATCH")
    if actual.get("execution_status") != "PASS":
        errors.add("RUNTIME_EXECUTION_FAILED")

    lmm_commit = expected.get("lmm_commit")
    if not isinstance(lmm_commit, str) or not COMMIT_PATTERN.fullmatch(lmm_commit):
        errors.add("INVALID_LMM_COMMIT")
    if actual.get("lmm_commit") != lmm_commit:
        errors.add("LMM_COMMIT_MISMATCH")
    if expected_lmm_commit is not None and (
        lmm_commit != expected_lmm_commit
        or actual.get("lmm_commit") != expected_lmm_commit
    ):
        errors.add("LMM_COMMIT_MISMATCH")

    runtime_commit = actual.get("runtime_commit")
    if not isinstance(runtime_commit, str) or not COMMIT_PATTERN.fullmatch(runtime_commit):
        errors.add("INVALID_RUNTIME_COMMIT")
    if expected_runtime_commit is not None and runtime_commit != expected_runtime_commit:
        errors.add("RUNTIME_COMMIT_MISMATCH")

    if actual.get("fixture_digest") != expected.get("fixture_digest"):
        errors.add("FIXTURE_DIGEST_MISMATCH")
    if actual.get("rule_pack_digest") != expected.get("rule_pack_digest"):
        errors.add("RULE_PACK_DIGEST_MISMATCH")
    if actual.get("source_snapshot_digests") != expected.get("source_snapshot_digests"):
        errors.add("SOURCE_SNAPSHOT_DIGEST_MISMATCH")
    if actual.get("semantics") != expected.get("semantics"):
        errors.add("SEMANTICS_MISMATCH")
    semantics = expected.get("semantics", {})
    if not isinstance(semantics, Mapping) or (
        semantics.get("id"), semantics.get("version")
    ) not in KNOWN_SEMANTICS:
        errors.add("UNKNOWN_SEMANTICS")

    expected_cases, expected_case_errors = _case_map(
        expected.get("cases"), "expected_status"
    )
    actual_cases, actual_case_errors = _case_map(actual.get("cases"), "actual_status")
    errors.update(expected_case_errors)
    errors.update(actual_case_errors)
    if set(expected_cases) != set(actual_cases):
        errors.add("CASE_SET_MISMATCH")
    for case_id in set(expected_cases).intersection(actual_cases):
        expected_case = expected_cases[case_id]
        actual_case = actual_cases[case_id]
        if expected_case.get("expected_status") != actual_case.get("actual_status"):
            errors.add("RESULT_MISMATCH")
        digest_case = dict(actual_case)
        claimed_output_digest = digest_case.pop("output_digest", None)
        if claimed_output_digest != _canonical_sha256(digest_case):
            errors.add("OUTPUT_DIGEST_MISMATCH")

    compared = tuple(sorted(set(expected_cases).intersection(actual_cases)))
    return RuntimeRefinementReport(
        passed=not errors,
        blocked=bool(errors),
        error_codes=tuple(sorted(errors)),
        compared_case_ids=compared,
    )
