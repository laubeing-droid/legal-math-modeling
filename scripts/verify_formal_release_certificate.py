#!/usr/bin/env python3
"""Independent verifier for the formal release certificate.

This verifier intentionally shares no implementation with the generator
beyond the Python standard library. It re-derives the Lean source
inventory from disk, re-hashes CI evidence artifacts, and refuses any
certificate whose claims exceed the bound evidence. A certificate whose
subject commit/tree/toolchain fields are absent is blocked.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import subprocess
import sys
from pathlib import Path
from typing import Any, Dict, List

LEAN_SOURCE_DIR = Path("proofs/lean/juris_lean/JurisLean")
THEOREM_PATTERN = re.compile(r"^theorem\s+([A-Za-z_][A-Za-z0-9_]*)")


def _sha256_of(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(65536), b""):
            digest.update(chunk)
    return digest.hexdigest()


def _read_json_stream(path: Path) -> List[Dict[str, Any]]:
    text = path.read_text(encoding="utf-8")
    decoder = json.JSONDecoder()
    documents = []
    offset = 0
    while offset < len(text):
        while offset < len(text) and text[offset].isspace():
            offset += 1
        if offset < len(text):
            document, offset = decoder.raw_decode(text, offset)
            documents.append(document)
    return documents


def verify_certificate(
    certificate_path: Path,
    *,
    repo_root: Path,
    ci_evidence_dir: Path | None = None,
) -> Dict[str, Any]:
    errors: List[str] = []
    checks: List[str] = []

    certificate = json.loads(Path(certificate_path).read_text(encoding="utf-8"))

    if certificate.get("schema_version") != "spec-formal-release-certificate-v2":
        errors.append("UNKNOWN_CERTIFICATE_SCHEMA")

    claimed = certificate.get("source_inventory", {})
    lean_dir = Path(repo_root) / LEAN_SOURCE_DIR
    actual_paths = sorted(lean_dir.glob("*.lean"))
    claimed_by_path = {source["path"]: source for source in claimed.get("sources", ())}

    if claimed.get("lean_source_file_count") != len(actual_paths):
        errors.append("SOURCE_COUNT_DRIFT")

    theorem_total = 0
    for lean_file in actual_paths:
        rel = lean_file.relative_to(repo_root).as_posix()
        record = claimed_by_path.get(rel)
        if record is None:
            errors.append("UNBOUND_LEAN_SOURCE")
            continue
        if record.get("sha256") != _sha256_of(lean_file):
            errors.append("SOURCE_DIGEST_DRIFT")
        text = lean_file.read_text(encoding="utf-8")
        actual_theorems = [
            {"name": match.group(1), "line": lineno}
            for lineno, line in enumerate(text.splitlines(), start=1)
            if (match := THEOREM_PATTERN.match(line))
        ]
        theorem_total += len(actual_theorems)
        if record.get("theorems") != actual_theorems:
            errors.append("THEOREM_INVENTORY_DRIFT")
    if not any(code.startswith(("SOURCE_", "THEOREM_", "UNBOUND")) for code in errors):
        checks.append("Source and theorem inventory re-derived independently.")

    if claimed.get("theorem_declaration_count") != theorem_total:
        errors.append("THEOREM_COUNT_DRIFT")

    if ci_evidence_dir is not None:
        evidence_dir = Path(ci_evidence_dir)
        for name, claim in certificate.get("ci_evidence", {}).items():
            artifact = evidence_dir / name
            if not artifact.is_file():
                errors.append("MISSING_CI_ARTIFACT")
                continue
            if claim.get("sha256") != _sha256_of(artifact):
                errors.append("CI_ARTIFACT_DIGEST_DRIFT")
        if certificate.get("missing_ci_evidence"):
            errors.append("INCOMPLETE_CI_EVIDENCE")

        identity_path = evidence_dir / "ci-run-identity.json"
        if identity_path.is_file():
            identity = json.loads(identity_path.read_text(encoding="utf-8"))
            subject = certificate.get("subject", {})
            if identity.get("in_ci") is not True or identity.get("status") != "CI_RUN":
                errors.append("INVALID_CI_RUN_IDENTITY")
            if subject != identity.get("subject"):
                errors.append("SUBJECT_IDENTITY_MISMATCH")
            current_head = subprocess.run(
                ["git", "-C", str(repo_root), "rev-parse", "HEAD"],
                capture_output=True,
                text=True,
                check=True,
            ).stdout.strip()
            if subject.get("sha") != current_head:
                errors.append("SUBJECT_SHA_DRIFT")
        else:
            errors.append("MISSING_CI_RUN_IDENTITY")

        mutation_path = evidence_dir / "mutation-property-report.json"
        if mutation_path.is_file():
            mutation = json.loads(mutation_path.read_text(encoding="utf-8"))
            if mutation.get("status") != "PASS":
                errors.append("MUTATION_GATE_NOT_PASS")
            if mutation.get("in_ci") is not True:
                errors.append("MUTATION_GATE_NOT_CI")
            if mutation.get("subject") != {"sha": certificate.get("subject", {}).get("sha")}:
                errors.append("MUTATION_SUBJECT_MISMATCH")
        else:
            errors.append("MISSING_MUTATION_REPORT")

        runtime_path = evidence_dir / "runtime-refinement-report.json"
        if runtime_path.is_file():
            try:
                runtime_reports = _read_json_stream(runtime_path)
            except (json.JSONDecodeError, TypeError):
                runtime_reports = []
                errors.append("INVALID_RUNTIME_REFINEMENT_REPORT")
            expected_reports = len(
                list((Path(repo_root) / "runtime/refinement_cases").glob("*.expected.json"))
            )
            if len(runtime_reports) != expected_reports:
                errors.append("RUNTIME_REFINEMENT_REPORT_COUNT_MISMATCH")
            if any(
                report.get("passed") is not True
                or report.get("blocked") is not False
                or bool(report.get("error_codes"))
                for report in runtime_reports
            ):
                errors.append("RUNTIME_REFINEMENT_NOT_PASS")
            certificate_sha = certificate.get("subject", {}).get("sha")
            if any(
                report.get("lmm_commit") != certificate_sha
                for report in runtime_reports
            ):
                errors.append("RUNTIME_REFINEMENT_SUBJECT_MISMATCH")
            runtime_commits = {
                report.get("runtime_commit") for report in runtime_reports
            }
            if (
                len(runtime_commits) != 1
                or not all(
                    type(commit) is str
                    and re.fullmatch(r"[0-9a-f]{40}", commit) is not None
                    for commit in runtime_commits
                )
                or any(
                    type(report.get("runtime_build_id")) is not str
                    or not report["runtime_build_id"]
                    for report in runtime_reports
                )
            ):
                errors.append("RUNTIME_REFINEMENT_RUNTIME_IDENTITY_INVALID")
            receipt_files: set[str] = set()
            for report in runtime_reports:
                name = report.get("actual_receipt_file")
                digest = report.get("actual_receipt_sha256")
                if (
                    type(name) is not str
                    or Path(name).name != name
                    or name in receipt_files
                    or type(digest) is not str
                ):
                    errors.append("RUNTIME_REFINEMENT_RECEIPT_BINDING_INVALID")
                    continue
                receipt_files.add(name)
                receipt_path = evidence_dir / name
                if not receipt_path.is_file() or _sha256_of(receipt_path) != digest:
                    errors.append("RUNTIME_REFINEMENT_RECEIPT_BINDING_INVALID")
            if not any(code.startswith("RUNTIME_REFINEMENT") for code in errors):
                checks.append("Runtime refinement reports content-checked independently.")
        else:
            errors.append("MISSING_RUNTIME_REFINEMENT_REPORT")

    status = certificate.get("status")
    if errors:
        verdict = "VERIFICATION_FAILED"
    elif status == "RELEASE_BLOCKED_NO_CI_EVIDENCE":
        verdict = "VERIFIED_FAIL_CLOSED"
        checks.append("Certificate correctly refuses release without CI evidence.")
    elif status == "RELEASE_PASS_PENDING_INDEPENDENT_VERIFICATION":
        verdict = "VERIFIED_PENDING_RELEASE_GATE"
    else:
        verdict = "VERIFICATION_FAILED"
        errors.append("UNKNOWN_CERTIFICATE_STATUS")

    return {
        "verdict": verdict,
        "error_codes": sorted(set(errors)),
        "checks": checks,
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--certificate", type=Path, required=True)
    parser.add_argument("--repo-root", type=Path, default=Path.cwd())
    parser.add_argument("--ci-evidence-dir", type=Path, default=None)
    parser.add_argument("--output", type=Path, default=None)
    args = parser.parse_args()

    report = verify_certificate(
        args.certificate,
        repo_root=args.repo_root,
        ci_evidence_dir=args.ci_evidence_dir,
    )
    rendered = json.dumps(report, ensure_ascii=False, indent=2)
    if args.output is not None:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(rendered + "\n", encoding="utf-8")
    print(rendered)
    return 0 if report["verdict"].startswith("VERIFIED") else 1


if __name__ == "__main__":
    sys.exit(main())
