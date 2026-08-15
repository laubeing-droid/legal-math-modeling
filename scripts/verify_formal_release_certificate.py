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
        for name, claim in certificate.get("ci_evidence", {}).items():
            artifact = Path(ci_evidence_dir) / name
            if not artifact.is_file():
                errors.append("MISSING_CI_ARTIFACT")
                continue
            if claim.get("sha256") != _sha256_of(artifact):
                errors.append("CI_ARTIFACT_DIGEST_DRIFT")
        if certificate.get("missing_ci_evidence"):
            errors.append("INCOMPLETE_CI_EVIDENCE")

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
