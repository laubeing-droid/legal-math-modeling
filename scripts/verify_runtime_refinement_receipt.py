#!/usr/bin/env python3
"""Verify an external runtime refinement receipt without importing its producer."""

from __future__ import annotations

import argparse
from dataclasses import asdict
import json
from pathlib import Path
import subprocess
from typing import Any, Mapping, Sequence

from theory.spec.runtime_differential import (
    RuntimeRefinementReport,
    verify_runtime_refinement_receipt,
)


def verification_payload(report: RuntimeRefinementReport) -> dict[str, Any]:
    """Expose validity and agreement as separate fail-closed decisions."""

    if report.passed:
        status = "PASS"
    elif report.receipt_valid and not report.aligned:
        status = "INCONCLUSIVE"
    else:
        status = "BLOCKED"
    payload = asdict(report)
    payload["status"] = status
    payload["error_codes"] = list(report.error_codes)
    payload["compared_case_ids"] = list(report.compared_case_ids)
    return payload


def _json_mapping(path: Path) -> Mapping[str, Any]:
    value = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(value, Mapping):
        raise ValueError(f"{path}: top-level JSON value must be an object")
    return value


def _git_head(repo_root: Path) -> str:
    completed = subprocess.run(
        ["git", "-C", str(repo_root), "rev-parse", "HEAD"],
        check=True,
        capture_output=True,
        text=True,
        encoding="utf-8",
    )
    return completed.stdout.strip()


def _parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--expected", required=True)
    parser.add_argument("--actual", required=True)
    parser.add_argument("--expected-lmm-commit")
    parser.add_argument("--expected-runtime-commit")
    parser.add_argument("--runtime-repo")
    return parser


def main(argv: Sequence[str] | None = None) -> int:
    args = _parser().parse_args(argv)
    runtime_commit = args.expected_runtime_commit
    if args.runtime_repo:
        resolved_runtime_commit = _git_head(Path(args.runtime_repo).resolve())
        if runtime_commit is not None and runtime_commit != resolved_runtime_commit:
            raise ValueError("explicit runtime commit differs from runtime repository HEAD")
        runtime_commit = resolved_runtime_commit

    report = verify_runtime_refinement_receipt(
        _json_mapping(Path(args.expected).resolve()),
        _json_mapping(Path(args.actual).resolve()),
        expected_lmm_commit=args.expected_lmm_commit,
        expected_runtime_commit=runtime_commit,
    )
    payload = verification_payload(report)
    print(json.dumps(payload, ensure_ascii=False, sort_keys=True))
    return 0 if payload["status"] == "PASS" else 1


if __name__ == "__main__":
    raise SystemExit(main())
