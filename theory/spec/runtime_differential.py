#!/usr/bin/env python3
"""Independently verify externally produced runtime refinement receipts."""

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
EXPECTED_SCHEMA = "runtime-refinement-expected-v2"
RECEIPT_SCHEMA = "runtime-refinement-receipt-v2"
NON_SEMANTIC_RUNTIME_FIELDS = frozenset(
    {
        "created_at",
        "generated_at",
        "output_path",
        "pid",
        "result_digest",
        "semantic_digest",
        "temp_dir",
        "timestamp",
    }
)
RUNTIME_RESULT_FIELDS = frozenset(
    {
        "schema_version",
        "run_id",
        "result_digest",
        "execution_status",
        "result_status",
        "formal_kernel_used",
        "review_required",
        "checker_accepted",
        "certificate_kind",
        "engine_version",
        "pack_id",
        "pack_version",
        "pack_digest",
        "claims",
        "branches",
        "used_fact_ids",
        "used_rule_ids",
        "source_ids",
        "missing_fact_ids",
        "missing_fact_review",
        "taint",
        "risk_labels",
        "checker_receipt",
    }
)
FAIL_CLOSED_RISK_LABELS = frozenset(
    {
        "GROUNDED_TRUNCATED",
        "RELEVANT_FACT_NOT_ADMITTED",
        "RELEVANT_RULE_NOT_ADMITTED",
        "USED_RULE_SOURCE_UNVERIFIED",
    }
)


def _canonical_sha256(value: Any) -> str:
    content = json.dumps(
        value,
        ensure_ascii=False,
        sort_keys=True,
        separators=(",", ":"),
    ).encode("utf-8")
    return hashlib.sha256(content).hexdigest()


def _semantic_projection(value: Any) -> Any:
    """Mirror JC's documented canonical semantic projection without importing JC."""

    if isinstance(value, Mapping):
        return {
            str(key): _semantic_projection(nested)
            for key, nested in sorted(value.items(), key=lambda item: str(item[0]))
            if str(key) not in NON_SEMANTIC_RUNTIME_FIELDS
        }
    if isinstance(value, (set, frozenset)):
        projected = [_semantic_projection(item) for item in value]
        return sorted(
            projected,
            key=lambda item: json.dumps(
                item,
                ensure_ascii=False,
                sort_keys=True,
                separators=(",", ":"),
            ),
        )
    if isinstance(value, (list, tuple)):
        return [_semantic_projection(item) for item in value]
    return value


def _semantic_runtime_digest(value: Mapping[str, Any]) -> str:
    return _canonical_sha256(_semantic_projection(value))


def _json_copy(value: Any) -> Any:
    return json.loads(json.dumps(value, ensure_ascii=False))


@dataclass(frozen=True)
class RuntimeRefinementReport:
    passed: bool
    receipt_valid: bool
    aligned: bool
    blocked: bool
    error_codes: Tuple[str, ...]
    compared_case_ids: Tuple[str, ...] = ()


def _normalize_expected_case(case: Mapping[str, Any]) -> dict[str, Any]:
    case_id = str(case.get("case_id", ""))
    expected_status = str(case.get("expected_status", ""))
    projection = case.get("projection")
    if not case_id or expected_status not in KNOWN_STATUSES:
        raise ValueError("expected cases require a case_id and known expected_status")
    if not isinstance(projection, Mapping):
        raise ValueError(f"{case_id}: projection is required")
    focus_claim_id = str(projection.get("focus_claim_id", ""))
    refuting_value = projection.get("refuting_claim_ids")
    if not focus_claim_id or not isinstance(refuting_value, (list, tuple)):
        raise ValueError(f"{case_id}: projection fields are invalid")
    refuting_claim_ids = sorted(str(item) for item in refuting_value)
    if (
        any(not item for item in refuting_claim_ids)
        or len(refuting_claim_ids) != len(set(refuting_claim_ids))
        or focus_claim_id in refuting_claim_ids
    ):
        raise ValueError(f"{case_id}: projection claims must be nonempty and unique")
    return {
        "case_id": case_id,
        "expected_status": expected_status,
        "projection": {
            "focus_claim_id": focus_claim_id,
            "refuting_claim_ids": refuting_claim_ids,
        },
    }


def build_expected_fixture(
    *,
    lmm_commit: str,
    fixture_cases: Iterable[Mapping[str, Any]],
    source_snapshot_digests: Iterable[str],
    rule_pack_digest: str,
    semantics_id: str = "grounded",
    semantics_version: str = "1",
) -> dict[str, Any]:
    """Build a content-addressed reference fixture without runtime output."""

    cases = sorted(
        (_normalize_expected_case(case) for case in fixture_cases),
        key=lambda case: case["case_id"],
    )
    if len({case["case_id"] for case in cases}) != len(cases):
        raise ValueError("expected case IDs must be unique")
    sources = sorted(str(item) for item in source_snapshot_digests)
    if (
        not COMMIT_PATTERN.fullmatch(lmm_commit)
        or not DIGEST_PATTERN.fullmatch(rule_pack_digest)
        or any(not DIGEST_PATTERN.fullmatch(item) for item in sources)
        or len(sources) != len(set(sources))
    ):
        raise ValueError("fixture commit and digests must be canonical")
    if (semantics_id, semantics_version) not in KNOWN_SEMANTICS:
        raise ValueError("unsupported refinement semantics")
    payload: dict[str, Any] = {
        "schema_version": EXPECTED_SCHEMA,
        "lmm_commit": lmm_commit,
        "source_snapshot_digests": sources,
        "rule_pack_digest": rule_pack_digest,
        "semantics": {"id": semantics_id, "version": semantics_version},
        "cases": cases,
    }
    payload["fixture_digest"] = _canonical_sha256(payload)
    return payload


def _derive_runtime_status(
    expected_case: Mapping[str, Any],
    semantic_result: Mapping[str, Any],
) -> str:
    if semantic_result.get("execution_status") != "completed":
        return "TAINTED"
    if semantic_result.get("result_status") == "engine_error":
        return "TAINTED"
    taint = semantic_result.get("taint")
    risk_labels = semantic_result.get("risk_labels")
    if not isinstance(taint, list) or not isinstance(risk_labels, list):
        return "TAINTED"
    if taint or FAIL_CLOSED_RISK_LABELS.intersection(str(item) for item in risk_labels):
        return "TAINTED"
    if semantic_result.get("result_status") == "missing_required_fact":
        return "UNDECIDED"

    claims_value = semantic_result.get("claims")
    if not isinstance(claims_value, list):
        return "TAINTED"
    claims = {str(item) for item in claims_value}
    projection = expected_case.get("projection")
    if not isinstance(projection, Mapping):
        return "TAINTED"
    focus_claim_id = str(projection.get("focus_claim_id", ""))
    refuting_value = projection.get("refuting_claim_ids")
    if not focus_claim_id or not isinstance(refuting_value, list):
        return "TAINTED"
    refuting_claim_ids = {str(item) for item in refuting_value}

    checker_receipt = semantic_result.get("checker_receipt")
    if claims:
        if not isinstance(checker_receipt, Mapping) or checker_receipt.get("valid") is not True:
            return "TAINTED"
    focus_accepted = focus_claim_id in claims
    refuter_accepted = bool(refuting_claim_ids.intersection(claims))
    if focus_accepted and refuter_accepted:
        return "UNDECIDED"
    if focus_accepted:
        return "PROVED"
    if refuter_accepted:
        return "REFUTED"
    return "UNDECIDED"


def build_runtime_receipt_for_test(
    expected: Mapping[str, Any],
    *,
    runtime_commit: str,
    actual_cases: Iterable[Mapping[str, Any]],
) -> dict[str, Any]:
    """Create test input; production receipts must come from an external runtime."""

    expected_by_id = {
        str(case.get("case_id", "")): case
        for case in expected.get("cases", [])
        if isinstance(case, Mapping)
    }
    cases: list[dict[str, Any]] = []
    for supplied in sorted(
        (_json_copy(item) for item in actual_cases),
        key=lambda item: str(item.get("case_id", "")),
    ):
        case_id = str(supplied.get("case_id", ""))
        semantic_result = supplied.get("semantic_result")
        if case_id not in expected_by_id or not isinstance(semantic_result, Mapping):
            raise ValueError("actual test cases must match an expected case and embed semantics")
        case: dict[str, Any] = {
            "case_id": case_id,
            "actual_status": _derive_runtime_status(
                expected_by_id[case_id], semantic_result
            ),
            "audit_bundle_digest": supplied.get("audit_bundle_digest"),
            "semantic_result": semantic_result,
        }
        case["output_digest"] = _canonical_sha256(case)
        cases.append(case)
    payload: dict[str, Any] = {
        "schema_version": RECEIPT_SCHEMA,
        "producer": "test-only-external-runtime",
        "execution_status": "PASS",
        "lmm_commit": expected.get("lmm_commit"),
        "runtime_commit": runtime_commit,
        "fixture_digest": expected.get("fixture_digest"),
        "source_snapshot_digests": list(
            expected.get("source_snapshot_digests", [])
        ),
        "rule_pack_digest": expected.get("rule_pack_digest"),
        "semantics": dict(expected.get("semantics", {})),
        "cases": cases,
    }
    payload["receipt_digest"] = _canonical_sha256(payload)
    return payload


def _case_map(
    cases: Any,
    status_field: str,
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


def _validate_expected_case(case: Mapping[str, Any]) -> set[str]:
    errors: set[str] = set()
    if set(case) != {"case_id", "expected_status", "projection"}:
        errors.add("MALFORMED_EXPECTED_CASE")
    projection = case.get("projection")
    if not isinstance(projection, Mapping) or set(projection) != {
        "focus_claim_id",
        "refuting_claim_ids",
    }:
        return errors | {"MALFORMED_PROJECTION"}
    focus = projection.get("focus_claim_id")
    refuting = projection.get("refuting_claim_ids")
    if not isinstance(focus, str) or not focus or not isinstance(refuting, list):
        errors.add("MALFORMED_PROJECTION")
        return errors
    if (
        any(not isinstance(item, str) or not item for item in refuting)
        or refuting != sorted(refuting)
        or len(refuting) != len(set(refuting))
        or focus in refuting
    ):
        errors.add("MALFORMED_PROJECTION")
    return errors


def _validate_semantic_result(
    semantic: Any,
    *,
    expected_rule_pack_digest: Any,
) -> tuple[set[str], set[str]]:
    errors: set[str] = set()
    source_digests: set[str] = set()
    if not isinstance(semantic, Mapping):
        return {"MALFORMED_RUNTIME_RESULT"}, source_digests
    if set(semantic) != RUNTIME_RESULT_FIELDS:
        errors.add("MALFORMED_RUNTIME_RESULT")
    claimed_digest = semantic.get("result_digest")
    if not isinstance(claimed_digest, str) or not DIGEST_PATTERN.fullmatch(claimed_digest):
        errors.add("INVALID_RUNTIME_RESULT_DIGEST")
    elif claimed_digest != _semantic_runtime_digest(semantic):
        errors.add("RUNTIME_RESULT_DIGEST_MISMATCH")
    if semantic.get("pack_digest") != expected_rule_pack_digest:
        errors.add("RUNTIME_PACK_DIGEST_MISMATCH")

    sorted_fields = (
        "claims",
        "used_fact_ids",
        "used_rule_ids",
        "source_ids",
        "missing_fact_ids",
        "taint",
        "risk_labels",
    )
    for field in sorted_fields:
        value = semantic.get(field)
        if (
            not isinstance(value, list)
            or any(not isinstance(item, str) for item in value)
            or value != sorted(value)
            or len(value) != len(set(value))
        ):
            errors.add("UNSTABLE_RUNTIME_RESULT")
    source_ids = semantic.get("source_ids")
    if isinstance(source_ids, list):
        for source_id in source_ids:
            if not isinstance(source_id, str) or "@" not in source_id:
                errors.add("INVALID_RUNTIME_SOURCE_ID")
                continue
            digest = source_id.rsplit("@", 1)[1]
            if not DIGEST_PATTERN.fullmatch(digest):
                errors.add("INVALID_RUNTIME_SOURCE_ID")
            else:
                source_digests.add(digest)

    claims = semantic.get("claims")
    checker_receipt = semantic.get("checker_receipt")
    if isinstance(claims, list) and isinstance(checker_receipt, Mapping):
        projection = checker_receipt.get("claim_projection")
        accepted = projection.get("accepted_claim_ids") if isinstance(projection, Mapping) else None
        if accepted is not None and accepted != claims:
            errors.add("CHECKER_CLAIM_PROJECTION_MISMATCH")
    return errors, source_digests


def verify_runtime_refinement_receipt(
    expected: Mapping[str, Any],
    actual: Mapping[str, Any] | None,
    *,
    expected_lmm_commit: str | None = None,
    expected_runtime_commit: str | None = None,
) -> RuntimeRefinementReport:
    """Compare LMM expectations with a self-contained external runtime receipt."""

    if actual is None:
        return RuntimeRefinementReport(
            False,
            False,
            False,
            True,
            ("MISSING_ACTUAL_RECEIPT",),
            (),
        )

    structural_errors: set[str] = set()
    alignment_errors: set[str] = set()
    expected_payload = dict(expected)
    expected_digest = expected_payload.pop("fixture_digest", None)
    expected_schema = expected.get("schema_version")
    if expected_schema != EXPECTED_SCHEMA:
        structural_errors.add(
            "LEGACY_EXPECTED_NOT_DECISIVE"
            if expected_schema == "runtime-refinement-expected-v1"
            else "UNKNOWN_EXPECTED_SCHEMA"
        )
    if expected_digest != _canonical_sha256(expected_payload):
        structural_errors.add("EXPECTED_FIXTURE_DIGEST_MISMATCH")

    expected_cases, expected_case_errors = _case_map(
        expected.get("cases"), "expected_status"
    )
    structural_errors.update(expected_case_errors)
    for case in expected_cases.values():
        structural_errors.update(_validate_expected_case(case))

    receipt_payload = dict(actual)
    receipt_digest = receipt_payload.pop("receipt_digest", None)
    receipt_schema = actual.get("schema_version")
    if receipt_schema != RECEIPT_SCHEMA:
        structural_errors.add(
            "LEGACY_RECEIPT_NOT_DECISIVE"
            if receipt_schema == "runtime-refinement-receipt-v1"
            else "UNKNOWN_RECEIPT_SCHEMA"
        )
    if receipt_digest != _canonical_sha256(receipt_payload):
        structural_errors.add("RECEIPT_DIGEST_MISMATCH")
    if actual.get("execution_status") != "PASS":
        structural_errors.add("RUNTIME_EXECUTION_FAILED")
    if not isinstance(actual.get("producer"), str) or not actual.get("producer"):
        structural_errors.add("INVALID_RUNTIME_PRODUCER")

    lmm_commit = expected.get("lmm_commit")
    if not isinstance(lmm_commit, str) or not COMMIT_PATTERN.fullmatch(lmm_commit):
        structural_errors.add("INVALID_LMM_COMMIT")
    if actual.get("lmm_commit") != lmm_commit:
        structural_errors.add("LMM_COMMIT_MISMATCH")
    if expected_lmm_commit is not None and (
        lmm_commit != expected_lmm_commit
        or actual.get("lmm_commit") != expected_lmm_commit
    ):
        structural_errors.add("LMM_COMMIT_MISMATCH")

    runtime_commit = actual.get("runtime_commit")
    if not isinstance(runtime_commit, str) or not COMMIT_PATTERN.fullmatch(runtime_commit):
        structural_errors.add("INVALID_RUNTIME_COMMIT")
    if expected_runtime_commit is not None and runtime_commit != expected_runtime_commit:
        structural_errors.add("RUNTIME_COMMIT_MISMATCH")

    if actual.get("fixture_digest") != expected.get("fixture_digest"):
        structural_errors.add("FIXTURE_DIGEST_MISMATCH")
    if actual.get("rule_pack_digest") != expected.get("rule_pack_digest"):
        structural_errors.add("RULE_PACK_DIGEST_MISMATCH")
    if actual.get("source_snapshot_digests") != expected.get("source_snapshot_digests"):
        structural_errors.add("SOURCE_SNAPSHOT_DIGEST_MISMATCH")
    if actual.get("semantics") != expected.get("semantics"):
        structural_errors.add("SEMANTICS_MISMATCH")
    semantics = expected.get("semantics", {})
    if not isinstance(semantics, Mapping) or (
        semantics.get("id"), semantics.get("version")
    ) not in KNOWN_SEMANTICS:
        structural_errors.add("UNKNOWN_SEMANTICS")

    actual_cases, actual_case_errors = _case_map(
        actual.get("cases"), "actual_status"
    )
    structural_errors.update(actual_case_errors)
    if set(expected_cases) != set(actual_cases):
        structural_errors.add("CASE_SET_MISMATCH")

    observed_source_digests: set[str] = set()
    for case_id in set(expected_cases).intersection(actual_cases):
        expected_case = expected_cases[case_id]
        actual_case = actual_cases[case_id]
        if set(actual_case) != {
            "case_id",
            "actual_status",
            "audit_bundle_digest",
            "semantic_result",
            "output_digest",
        }:
            structural_errors.add("MALFORMED_RUNTIME_CASE")
        bundle_digest = actual_case.get("audit_bundle_digest")
        if not isinstance(bundle_digest, str) or not DIGEST_PATTERN.fullmatch(bundle_digest):
            structural_errors.add("INVALID_AUDIT_BUNDLE_DIGEST")
        digest_case = dict(actual_case)
        claimed_output_digest = digest_case.pop("output_digest", None)
        if claimed_output_digest != _canonical_sha256(digest_case):
            structural_errors.add("OUTPUT_DIGEST_MISMATCH")
        semantic_errors, case_source_digests = _validate_semantic_result(
            actual_case.get("semantic_result"),
            expected_rule_pack_digest=expected.get("rule_pack_digest"),
        )
        structural_errors.update(semantic_errors)
        observed_source_digests.update(case_source_digests)
        semantic = actual_case.get("semantic_result")
        if isinstance(semantic, Mapping):
            derived_status = _derive_runtime_status(expected_case, semantic)
            if actual_case.get("actual_status") != derived_status:
                structural_errors.add("STATUS_DERIVATION_MISMATCH")
        if expected_case.get("expected_status") != actual_case.get("actual_status"):
            alignment_errors.add("RESULT_MISMATCH")

    expected_sources = expected.get("source_snapshot_digests")
    if isinstance(expected_sources, list) and observed_source_digests != set(expected_sources):
        structural_errors.add("RUNTIME_SOURCE_COVERAGE_MISMATCH")

    compared = tuple(sorted(set(expected_cases).intersection(actual_cases)))
    receipt_valid = not structural_errors
    aligned = receipt_valid and not alignment_errors
    errors = tuple(sorted(structural_errors | alignment_errors))
    return RuntimeRefinementReport(
        passed=receipt_valid and aligned,
        receipt_valid=receipt_valid,
        aligned=aligned,
        blocked=bool(errors),
        error_codes=errors,
        compared_case_ids=compared,
    )
