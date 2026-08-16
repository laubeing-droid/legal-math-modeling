#!/usr/bin/env python3
"""Lean source/theorem inventory generator and release certificate assembler.

`collect_source_inventory` rebuilds the Lean source and theorem inventory
from current source files only; counts are never copied from reports or
memory. The full formal release certificate additionally requires CI
evidence (clean build, axiom audit, guard scan, Python tests, mutation and
refinement reports) bound to the exact subject commit/tree. Without that
evidence the certificate stays fail-closed with status
`RELEASE_BLOCKED_NO_CI_EVIDENCE`.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Dict, List

LEAN_SOURCE_DIR = Path("proofs/lean/juris_lean/JurisLean")

THEOREM_PATTERN = re.compile(r"^theorem\s+([A-Za-z_][A-Za-z0-9_]*)")

INVENTORY_STATUS = "source_inventory_not_release_certificate"
RELEASE_BLOCKED_STATUS = "RELEASE_BLOCKED_NO_CI_EVIDENCE"
RELEASE_SCHEMA = "spec-formal-release-certificate-v2"


def _sha256_of(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def collect_source_inventory(repo_root: Path) -> Dict[str, Any]:
    """Bind every Lean source file and theorem declaration to a digest."""

    root = Path(repo_root)
    lean_dir = root / LEAN_SOURCE_DIR
    sources: List[Dict[str, Any]] = []
    for lean_file in sorted(lean_dir.glob("*.lean")):
        theorems: List[Dict[str, Any]] = []
        text = lean_file.read_text(encoding="utf-8")
        for lineno, line in enumerate(text.splitlines(), start=1):
            match = THEOREM_PATTERN.match(line)
            if match:
                theorems.append({"name": match.group(1), "line": lineno})
        sources.append(
            {
                "path": lean_file.relative_to(root).as_posix(),
                "sha256": _sha256_of(lean_file),
                "theorems": theorems,
            }
        )

    theorem_count = sum(len(source["theorems"]) for source in sources)
    return {
        "status": INVENTORY_STATUS,
        "generated_at": datetime.now(timezone.utc).isoformat(),
        "lean_source_dir": LEAN_SOURCE_DIR.as_posix(),
        "lean_source_file_count": len(sources),
        "theorem_declaration_count": theorem_count,
        "sources": sources,
    }


def assemble_release_certificate(
    repo_root: Path,
    *,
    ci_evidence_dir: Path | None = None,
) -> Dict[str, Any]:
    """Assemble a release certificate; fail-closed without CI evidence."""

    inventory = collect_source_inventory(repo_root)
    certificate: Dict[str, Any] = {
        "schema_version": RELEASE_SCHEMA,
        "status": RELEASE_BLOCKED_STATUS,
        "generated_at": datetime.now(timezone.utc).isoformat(),
        "source_inventory": {
            "lean_source_file_count": inventory["lean_source_file_count"],
            "theorem_declaration_count": inventory["theorem_declaration_count"],
            "sources": inventory["sources"],
        },
        "ci_evidence": {},
        "limitations": [
            "Static inventory is not a Lean build, axiom audit, or release certificate.",
            "Lean build evidence must come from GitHub Actions bound to the subject commit/tree.",
            "Local static results are provisional and never a Lean PASS.",
        ],
    }

    required_evidence = (
        "ci-run-identity.json",
        "lake-clean-build.log",
        "axiom-audit.raw.txt",
        "lean-guard-report.json",
        "pytest-collection.txt",
        "pytest-full.log",
        "mutation-property-report.json",
        "runtime-refinement-report.json",
        "independent-verifier-report.json",
    )
    if ci_evidence_dir is not None:
        evidence_dir = Path(ci_evidence_dir)
        evidence: Dict[str, Any] = {}
        missing = []
        for name in required_evidence:
            artifact = evidence_dir / name
            if artifact.is_file():
                evidence[name] = {
                    "sha256": _sha256_of(artifact),
                    "bytes": artifact.stat().st_size,
                }
            else:
                missing.append(name)
        certificate["ci_evidence"] = evidence
        if not missing:
            certificate["status"] = "RELEASE_PASS_PENDING_INDEPENDENT_VERIFICATION"
        else:
            certificate["missing_ci_evidence"] = missing
    else:
        certificate["missing_ci_evidence"] = list(required_evidence)

    return certificate


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--repo-root", type=Path, default=Path.cwd())
    parser.add_argument("--ci-evidence-dir", type=Path, default=None)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()

    certificate = assemble_release_certificate(
        args.repo_root, ci_evidence_dir=args.ci_evidence_dir
    )
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(
        json.dumps(certificate, ensure_ascii=False, indent=2) + "\n",
        encoding="utf-8",
    )
    print(json.dumps({"status": certificate["status"]}, ensure_ascii=False))
    # Fail-closed: only a pending-independent-verification status exits zero.
    return 0 if certificate["status"] == "RELEASE_PASS_PENDING_INDEPENDENT_VERIFICATION" else 1


if __name__ == "__main__":
    raise SystemExit(main())
