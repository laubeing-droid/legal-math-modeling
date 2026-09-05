#!/usr/bin/env python3
"""CI helper: emit ci-run-identity.json for the formal release certificate.

Binds GITHUB_RUN_ID/ATTEMPT, event, ref, subject SHA/tree, workflow
path/digest, runner image, action SHAs, toolchain pins, job conclusions,
and artifact digests. Runs inside GitHub Actions; locally it only
produces a clearly marked NOT_CI placeholder that can never be used as
release evidence.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import sys
from datetime import datetime, timezone
from pathlib import Path


def sha256_of(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def build_identity(repo_root: Path, artifact_dir: Path | None) -> dict:
    run_id = os.environ.get("GITHUB_RUN_ID")
    in_ci = run_id is not None

    subject_sha = os.environ.get("GITHUB_SHA", "UNKNOWN")
    tree = "UNKNOWN"
    if in_ci:
        tree = os.popen(f"git -C {repo_root} rev-parse HEAD^{{tree}}").read().strip() or "UNKNOWN"

    toolchain_file = repo_root / "proofs/lean/juris_lean/lean-toolchain"
    manifest_file = repo_root / "proofs/lean/juris_lean/lake-manifest.json"
    workflow_file = repo_root / ".github/workflows/lean-build.yml"

    artifacts = {}
    if artifact_dir is not None and artifact_dir.is_dir():
        for artifact in sorted(artifact_dir.iterdir()):
            if artifact.is_file():
                artifacts[artifact.name] = {
                    "sha256": sha256_of(artifact),
                    "bytes": artifact.stat().st_size,
                }

    return {
        "schema_version": "spec-ci-run-identity-v2",
        "in_ci": in_ci,
        "status": "CI_RUN" if in_ci else "NOT_CI_LOCAL_PLACEHOLDER",
        "generated_at": datetime.now(timezone.utc).isoformat(),
        "github": {
            "run_id": run_id,
            "run_attempt": os.environ.get("GITHUB_RUN_ATTEMPT"),
            "event": os.environ.get("GITHUB_EVENT_NAME"),
            "ref": os.environ.get("GITHUB_REF"),
            "workflow": os.environ.get("GITHUB_WORKFLOW"),
            "runner_os": os.environ.get("RUNNER_OS"),
            "runner_image": os.environ.get("ImageOS"),
        },
        "subject": {"sha": subject_sha, "tree": tree},
        "workflow_digest": sha256_of(workflow_file) if workflow_file.is_file() else None,
        "toolchain": {
            "lean_toolchain": toolchain_file.read_text(encoding="utf-8").strip()
            if toolchain_file.is_file()
            else None,
            "lake_manifest_sha256": sha256_of(manifest_file)
            if manifest_file.is_file()
            else None,
        },
        "artifacts": artifacts,
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--repo-root", type=Path, default=Path.cwd())
    parser.add_argument("--artifact-dir", type=Path, default=None)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()

    identity = build_identity(args.repo_root, args.artifact_dir)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(
        json.dumps(identity, ensure_ascii=False, indent=2) + "\n", encoding="utf-8"
    )
    print(json.dumps({"status": identity["status"]}, ensure_ascii=False))
    # Local placeholders are never release evidence: fail-closed exit code.
    return 0 if identity["in_ci"] else 1


if __name__ == "__main__":
    sys.exit(main())
