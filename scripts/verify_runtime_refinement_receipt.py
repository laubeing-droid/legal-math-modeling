#!/usr/bin/env python3
"""Independent verifier for external runtime refinement receipts (M9, party 3).

Compares an externally supplied actual receipt against an LMM expected
fixture. The actual receipt must come from the external runtime through
its formal public entry; same-process shadow statuses are never accepted.
Missing receipts, commit/digest mismatches, execution failures, and
unknown status mappings are fail-closed.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from theory.spec.runtime_differential import verify_runtime_refinement_receipt


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--expected", type=Path, required=True)
    parser.add_argument("--actual", type=Path, required=False, default=None)
    parser.add_argument("--expected-lmm-commit", default=None)
    parser.add_argument("--expected-runtime-commit", default=None)
    parser.add_argument("--output", type=Path, default=None)
    args = parser.parse_args()

    expected = json.loads(args.expected.read_text(encoding="utf-8"))
    actual = None
    actual_bytes = None
    if args.actual is not None and args.actual.is_file():
        actual_bytes = args.actual.read_bytes()
        actual = json.loads(actual_bytes)

    report = verify_runtime_refinement_receipt(
        expected,
        actual,
        expected_lmm_commit=args.expected_lmm_commit,
        expected_runtime_commit=args.expected_runtime_commit,
    )
    payload = {
        "passed": report.passed,
        "blocked": report.blocked,
        "error_codes": list(report.error_codes),
        "checks": list(report.checks),
        "lmm_commit": None if actual is None else actual.get("lmm_commit"),
        "runtime_commit": None if actual is None else actual.get("runtime_commit"),
        "runtime_build_id": None if actual is None else actual.get("runtime_build_id"),
        "fixture_digest": expected.get("fixture_digest"),
        "actual_receipt_file": None if args.actual is None else args.actual.name,
        "actual_receipt_sha256": (
            None if actual_bytes is None else hashlib.sha256(actual_bytes).hexdigest()
        ),
    }
    rendered = json.dumps(payload, ensure_ascii=False, indent=2)
    if args.output is not None:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(rendered + "\n", encoding="utf-8")
    print(rendered)
    return 0 if report.passed else 1


if __name__ == "__main__":
    sys.exit(main())
