#!/usr/bin/env python3
"""Independently verify a FormalReleaseCertificate and its raw artifacts."""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import subprocess
from pathlib import Path
from typing import Any, Mapping, Sequence


CERTIFICATE_VERSION = "formal-release-certificate-v1"
SOURCE_HASH_CONTRACT = "utf-8-lf-v1"
REQUIRED_GATES = {
    "pytest_collection",
    "pytest_full",
    "source_inventory",
    "lake_clean",
    "lake_build",
    "axiom_audit",
    "lean_guard",
}
FAIL_CLOSED_MARKERS = {
    "UNKNOWN",
    "TIMEOUT",
    "SKIP",
    "NOT_RUN",
    "BACKEND_UNAVAILABLE",
    "ERROR",
}
THEOREM_PATTERN = re.compile(r"^theorem\s+([^\s(:]+)")


def _canonical_bytes(value: Any) -> bytes:
    return json.dumps(
        value,
        ensure_ascii=False,
        sort_keys=True,
        separators=(",", ":"),
    ).encode("utf-8")


def _sha256(content: bytes) -> str:
    return hashlib.sha256(content).hexdigest()


def _normalized_text_bytes(content: bytes) -> bytes:
    text = content.decode("utf-8")
    return text.replace("\r\n", "\n").replace("\r", "\n").encode("utf-8")


def _git(repo_root: Path, *args: str) -> tuple[int, bytes]:
    completed = subprocess.run(
        ["git", "-C", str(repo_root), *args],
        capture_output=True,
    )
    return completed.returncode, completed.stdout


def _blob(repo_root: Path, commit: str, path: str) -> bytes | None:
    code, content = _git(repo_root, "show", f"{commit}:{path}")
    return content if code == 0 else None


def _source_inventory_from_commit(repo_root: Path, commit: str) -> dict[str, Any]:
    lean_root = "proofs/lean/juris_lean/JurisLean"
    code, output = _git(repo_root, "ls-tree", "-r", "--name-only", commit, "--", lean_root)
    if code != 0:
        return {}
    sources: list[dict[str, Any]] = []
    paths = sorted(
        path
        for path in output.decode("utf-8").splitlines()
        if path.endswith(".lean")
    )
    for path in paths:
        content = _blob(repo_root, commit, path)
        if content is None:
            return {}
        normalized_content = _normalized_text_bytes(content)
        text = normalized_content.decode("utf-8")
        theorems = [
            {"name": match.group(1), "line": line_number}
            for line_number, line in enumerate(text.splitlines(), start=1)
            if (match := THEOREM_PATTERN.match(line))
        ]
        sources.append(
            {
                "path": path,
                "sha256": _sha256(normalized_content),
                "size_bytes": len(normalized_content),
                "theorems": theorems,
            }
        )
    theorem_count = sum(len(source["theorems"]) for source in sources)
    payload = {"sources": sources, "theorem_declaration_count": theorem_count}
    return {
        "manifest_version": "source-inventory-v2",
        "source_hash_contract": SOURCE_HASH_CONTRACT,
        "status": "source_inventory_not_release_certificate",
        "lean_workspace": lean_root,
        "lean_source_file_count": len(sources),
        "theorem_declaration_count": theorem_count,
        "source_inventory_digest": _sha256(_canonical_bytes(payload)),
        "sources": sources,
    }


def verify_certificate(
    certificate: Mapping[str, Any],
    repo_root: Path,
    artifact_dir: Path,
    *,
    require_current_head: bool = True,
) -> dict[str, Any]:
    """Recompute every binding without trusting producer PASS labels."""

    errors: list[str] = []
    if certificate.get("schema_version") != CERTIFICATE_VERSION:
        errors.append("UNKNOWN_SCHEMA_VERSION")

    claimed_digest = certificate.get("certificate_digest")
    digest_payload = dict(certificate)
    digest_payload.pop("certificate_digest", None)
    if claimed_digest != _sha256(_canonical_bytes(digest_payload)):
        errors.append("CERTIFICATE_DIGEST_MISMATCH")

    subject = certificate.get("subject", {})
    commit = str(subject.get("commit", ""))
    code, tree = _git(repo_root, "show", "-s", "--format=%T", commit)
    if code != 0 or tree.decode("utf-8").strip() != subject.get("tree"):
        errors.append("SUBJECT_TREE_MISMATCH")
    if subject.get("dirty") is not False:
        errors.append("SUBJECT_RECORDED_DIRTY")
    if require_current_head:
        _, head = _git(repo_root, "rev-parse", "HEAD")
        if head.decode("utf-8").strip() != commit:
            errors.append("SUBJECT_NOT_CURRENT_HEAD")

    for bound_input in certificate.get("inputs", []):
        path = str(bound_input.get("path", ""))
        content = _blob(repo_root, commit, path)
        if content is None:
            errors.append(f"BOUND_INPUT_MISSING:{path}")
        elif _sha256(content) != bound_input.get("sha256"):
            errors.append(f"BOUND_INPUT_DIGEST_MISMATCH:{path}")

    actual_inventory = _source_inventory_from_commit(repo_root, commit)
    if certificate.get("source_inventory") != actual_inventory:
        errors.append("SOURCE_INVENTORY_MISMATCH")

    environment = certificate.get("environment", {})
    if not isinstance(environment, Mapping):
        errors.append("MALFORMED_ENVIRONMENT")
    elif any(value in FAIL_CLOSED_MARKERS for value in environment.values()):
        errors.append("ENVIRONMENT_NOT_CAPTURED")

    gates = certificate.get("gates", [])
    gate_ids = {gate.get("gate_id") for gate in gates if isinstance(gate, dict)}
    if gate_ids != REQUIRED_GATES:
        errors.append("GATE_SET_MISMATCH")
    for gate in gates:
        gate_id = str(gate.get("gate_id", "UNKNOWN"))
        if gate.get("exit_code") != 0 or gate.get("status") != "PASS":
            errors.append(f"GATE_FAILED:{gate_id}")
        log_name = str(gate.get("raw_log", ""))
        if not log_name or Path(log_name).name != log_name:
            errors.append(f"INVALID_LOG_PATH:{gate_id}")
            continue
        log_path = artifact_dir / log_name
        if not log_path.is_file():
            errors.append(f"RAW_LOG_MISSING:{gate_id}")
            continue
        content = log_path.read_bytes()
        if _sha256(content) != gate.get("raw_log_sha256"):
            errors.append(f"RAW_LOG_DIGEST_MISMATCH:{gate_id}")
        if len(content) != gate.get("raw_log_size_bytes"):
            errors.append(f"RAW_LOG_SIZE_MISMATCH:{gate_id}")
        text = content.decode("utf-8", errors="replace")
        marker_pattern = re.compile(
            r"\b(?:" + "|".join(re.escape(marker) for marker in FAIL_CLOSED_MARKERS) + r")\b"
        )
        if marker_pattern.search(text):
            errors.append(f"FAIL_CLOSED_MARKER:{gate_id}")

    axiom_log = artifact_dir / "axiom_audit.log"
    if axiom_log.is_file():
        axiom_text = axiom_log.read_text(encoding="utf-8", errors="replace")
        if "sorryAx" in axiom_text or "declaration uses 'sorry'" in axiom_text:
            errors.append("UNTRUSTED_AXIOM_FOUND")

    if certificate.get("status") != "FORMAL_RELEASE_VERIFIED":
        errors.append("CERTIFICATE_STATUS_NOT_VERIFIED")
    return {
        "status": "PASS" if not errors else "FAIL",
        "subject_commit": commit,
        "errors": sorted(set(errors)),
    }


def _parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("certificate")
    parser.add_argument("--repo-root", default=None)
    parser.add_argument("--artifact-dir", default=None)
    parser.add_argument("--allow-non-head", action="store_true")
    return parser


def main(argv: Sequence[str] | None = None) -> int:
    args = _parser().parse_args(argv)
    certificate_path = Path(args.certificate).resolve()
    repo_root = (
        Path(args.repo_root).resolve()
        if args.repo_root
        else Path(__file__).resolve().parents[1]
    )
    artifact_dir = (
        Path(args.artifact_dir).resolve()
        if args.artifact_dir
        else certificate_path.parent
    )
    certificate = json.loads(certificate_path.read_text(encoding="utf-8"))
    report = verify_certificate(
        certificate,
        repo_root,
        artifact_dir,
        require_current_head=not args.allow_non_head,
    )
    print(json.dumps(report, ensure_ascii=False, indent=2))
    return 0 if report["status"] == "PASS" else 1


if __name__ == "__main__":
    raise SystemExit(main())
