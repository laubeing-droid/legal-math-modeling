#!/usr/bin/env python3
"""Run the controlled checker-input mutation gate and emit auditable JSON."""

from __future__ import annotations

import argparse
import json
import os
import subprocess
import sys
import tempfile
import xml.etree.ElementTree as ET
from datetime import datetime, timezone
from pathlib import Path


MUTATION_TESTS = (
    "tests/spec/test_certificate_v2.py::test_v2_checker_rejects_required_mutations",
    "tests/spec/test_fact_admission.py::test_receipt_mutations_are_fail_closed",
    "tests/spec/test_proposal_envelope.py::test_proposal_mutations_are_fail_closed",
    "tests/spec/test_runtime_refinement_receipt.py::test_runtime_receipt_rejects_binding_and_status_mutations",
    "tests/spec/test_source_contracts.py::test_bundle_rejects_mutations",
    "tests/spec/test_source_contracts.py::test_source_path_rejects_mutations",
    "tests/spec/test_source_contracts.py::test_temporal_applicability_rejects_mutations",
    "tests/spec/test_translation_witness.py::test_translation_witness_rejects_edge_mutations",
    "tests/spec/test_dual_ir.py::test_pipeline_witness_detects_omitted_and_spurious_mutations",
)


def _cases_from_junit(path: Path) -> list[dict[str, str]]:
    cases = []
    for case in ET.parse(path).getroot().iter("testcase"):
        outcome = "KILLED"
        for tag, value in (("failure", "SURVIVED"), ("error", "ERROR"), ("skipped", "SKIPPED")):
            if case.find(tag) is not None:
                outcome = value
                break
        cases.append(
            {
                "id": f"{case.get('classname', '')}::{case.get('name', '')}",
                "outcome": outcome,
            }
        )
    return cases


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--repo-root", type=Path, default=Path.cwd())
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()

    repo_root = args.repo_root.resolve()
    report: dict = {
        "schema_version": "controlled-input-mutation-report-v1",
        "generated_at": datetime.now(timezone.utc).isoformat(),
        "mutation_kind": "controlled_checker_input",
        "in_ci": bool(os.environ.get("GITHUB_RUN_ID")),
        "subject": {"sha": os.environ.get("GITHUB_SHA", "")},
        "test_nodes": list(MUTATION_TESTS),
        "limitations": [
            "Mutates controlled checker inputs, not Lean source or Python implementation source."
        ],
    }

    with tempfile.TemporaryDirectory() as temp_dir:
        junit = Path(temp_dir) / "mutation-junit.xml"
        command = [
            sys.executable,
            "-m",
            "pytest",
            *MUTATION_TESTS,
            "-q",
            f"--junitxml={junit}",
        ]
        try:
            completed = subprocess.run(
                command,
                cwd=repo_root,
                capture_output=True,
                text=True,
                encoding="utf-8",
                errors="replace",
                timeout=300,
            )
            cases = _cases_from_junit(junit) if junit.is_file() else []
            report["pytest_returncode"] = completed.returncode
            report["output_tail"] = (completed.stdout + completed.stderr)[-2000:]
        except subprocess.TimeoutExpired as exc:
            cases = []
            report["pytest_returncode"] = None
            report["output_tail"] = f"TIMEOUT after {exc.timeout} seconds"

    counts = {name: sum(case["outcome"] == name for case in cases) for name in ("KILLED", "SURVIVED", "ERROR", "SKIPPED")}
    report["cases"] = cases
    report["summary"] = {
        "total": len(cases),
        "killed": counts["KILLED"],
        "survived": counts["SURVIVED"],
        "errors": counts["ERROR"],
        "skipped": counts["SKIPPED"],
        "mutation_score": counts["KILLED"] / len(cases) if cases else 0.0,
    }
    report["status"] = (
        "PASS"
        if report["pytest_returncode"] == 0 and cases and counts["KILLED"] == len(cases)
        else "FAIL"
    )

    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({"status": report["status"], **report["summary"]}))
    return 0 if report["status"] == "PASS" else 1


if __name__ == "__main__":
    raise SystemExit(main())
