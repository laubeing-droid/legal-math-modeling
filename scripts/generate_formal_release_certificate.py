#!/usr/bin/env python3
"""Generate source inventories and current-head formal release evidence."""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import platform
import re
import subprocess
import sys
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Iterable, Mapping, Sequence


CERTIFICATE_VERSION = "formal-release-certificate-v1"
INVENTORY_VERSION = "source-inventory-v2"
SOURCE_HASH_CONTRACT = "utf-8-lf-v1"
REQUIRED_GATE_IDS = (
    "pytest_collection",
    "pytest_full",
    "source_inventory",
    "lake_clean",
    "lake_build",
    "axiom_audit",
    "lean_guard",
)
FAIL_CLOSED_MARKERS = {
    "UNKNOWN",
    "TIMEOUT",
    "SKIP",
    "NOT_RUN",
    "BACKEND_UNAVAILABLE",
    "ERROR",
}
THEOREM_PATTERN = re.compile(r"^theorem\s+([^\s(:]+)")


def canonical_json_bytes(value: Any) -> bytes:
    """Serialize JSON deterministically for content addressing."""

    return json.dumps(
        value,
        ensure_ascii=False,
        sort_keys=True,
        separators=(",", ":"),
    ).encode("utf-8")


def sha256_bytes(content: bytes) -> str:
    return hashlib.sha256(content).hexdigest()


def sha256_file(path: Path) -> str:
    return sha256_bytes(path.read_bytes())


def normalized_text_bytes(path: Path) -> bytes:
    """Return strict UTF-8 text with platform-independent LF line endings."""

    text = path.read_bytes().decode("utf-8")
    return text.replace("\r\n", "\n").replace("\r", "\n").encode("utf-8")


def _repo_root(path: str | Path | None = None) -> Path:
    if path is not None:
        return Path(path).resolve()
    return Path(__file__).resolve().parents[1]


def _relative(repo_root: Path, path: Path) -> str:
    return path.resolve().relative_to(repo_root).as_posix()


def _git(repo_root: Path, *args: str) -> str:
    completed = subprocess.run(
        ["git", "-C", str(repo_root), *args],
        check=True,
        capture_output=True,
        text=True,
        encoding="utf-8",
    )
    return completed.stdout.strip()


def _extract_theorems(path: Path) -> list[dict[str, Any]]:
    records: list[dict[str, Any]] = []
    for line_number, line in enumerate(
        path.read_text(encoding="utf-8").splitlines(), start=1
    ):
        match = THEOREM_PATTERN.match(line)
        if match:
            records.append({"name": match.group(1), "line": line_number})
    return records


def collect_source_inventory(repo_root: str | Path) -> dict[str, Any]:
    """Collect source hashes and theorem declarations from the Lean authority tree."""

    root = _repo_root(repo_root)
    lean_root = root / "proofs" / "lean" / "juris_lean" / "JurisLean"
    sources: list[dict[str, Any]] = []
    for path in sorted(lean_root.rglob("*.lean"), key=lambda item: item.as_posix()):
        normalized_content = normalized_text_bytes(path)
        sources.append(
            {
                "path": _relative(root, path),
                "sha256": sha256_bytes(normalized_content),
                "size_bytes": len(normalized_content),
                "theorems": _extract_theorems(path),
            }
        )

    theorem_count = sum(len(source["theorems"]) for source in sources)
    source_payload = {
        "sources": sources,
        "theorem_declaration_count": theorem_count,
    }
    return {
        "manifest_version": INVENTORY_VERSION,
        "source_hash_contract": SOURCE_HASH_CONTRACT,
        "status": "source_inventory_not_release_certificate",
        "lean_workspace": "proofs/lean/juris_lean/JurisLean",
        "lean_source_file_count": len(sources),
        "theorem_declaration_count": theorem_count,
        "source_inventory_digest": sha256_bytes(canonical_json_bytes(source_payload)),
        "sources": sources,
    }


def _module_theorem_counts(inventory: Mapping[str, Any]) -> dict[str, int]:
    return {
        Path(source["path"]).name: len(source["theorems"])
        for source in inventory["sources"]
    }


def _lean_build_targets(inventory: Mapping[str, Any]) -> tuple[str, ...]:
    """Return the root module plus every module bound by the source inventory."""

    source_prefix = "proofs/lean/juris_lean/"
    modules = [
        source["path"]
        .removeprefix(source_prefix)
        .removesuffix(".lean")
        .replace("/", ".")
        for source in inventory["sources"]
    ]
    return ("JurisLean", *modules)


def _theorem_manifest(inventory: Mapping[str, Any]) -> dict[str, Any]:
    return {
        **inventory,
        "release_gate": "fail_closed_until_formal_release_certificate_verifies",
        "module_theorem_counts": _module_theorem_counts(inventory),
        "canonical_types": [
            "LegalFact",
            "LegalRule",
            "LegalNorm",
            "LegalClaim",
            "Argument",
            "Attack",
            "Priority",
            "Violation",
            "Reparation",
            "DecisionStatus",
            "ProofTrace",
        ],
        "ddl_modalities": [
            "OBLIGATION",
            "PROHIBITION",
            "PERMISSION",
            "CONSTITUTIVE",
        ],
        "slices": ["contract breach", "license", "permission", "priority"],
        "allowed_claims": [
            "Lean sources define task-bounded formal statements.",
            "A verified FormalReleaseCertificate binds one commit, tree, toolchain, source inventory, and gate run.",
            "Runtime refinement requires a separate RuntimeRefinementReceipt.",
        ],
        "forbidden_claims": [
            "Do not claim the full runtime is formally proved by Lean.",
            "Do not treat source hashes as proof of source authority or legal correctness.",
            "Do not treat Python tests or runtime receipts as Lean proofs.",
            "Do not present a source inventory as a release certificate.",
        ],
    }


def _lean_manifest(inventory: Mapping[str, Any]) -> dict[str, Any]:
    return {
        "manifest_version": INVENTORY_VERSION,
        "purpose": "Generated Lean source inventory; not a build certificate.",
        "status": inventory["status"],
        "source_hash_contract": inventory["source_hash_contract"],
        "lean_workspace": "proofs/lean/juris_lean",
        "source_inventory_digest": inventory["source_inventory_digest"],
        "lean_source_file_count": inventory["lean_source_file_count"],
        "theorem_declaration_count": inventory["theorem_declaration_count"],
        "source_files": [source["path"] for source in inventory["sources"]],
        "module_theorem_counts": _module_theorem_counts(inventory),
        "required_release_checks": list(REQUIRED_GATE_IDS),
        "fail_closed_values": sorted(FAIL_CLOSED_MARKERS),
    }


def _proof_ledger(inventory: Mapping[str, Any]) -> dict[str, Any]:
    return {
        "ledger_version": INVENTORY_VERSION,
        "authority_order": [
            "Lean source",
            "verified current-head FormalReleaseCertificate",
            "Python regression evidence",
            "source inventories",
            "narrative documents",
        ],
        "source_inventory": {
            "lean_files": inventory["lean_source_file_count"],
            "theorem_declarations": inventory["theorem_declaration_count"],
            "digest": inventory["source_inventory_digest"],
            "hash_contract": inventory["source_hash_contract"],
        },
        "release_gate": "fail_closed_until_formal_release_certificate_verifies",
        "prohibited_substitutions": [
            "Python tests for Lean proof",
            "runtime receipt for Lean proof",
            "source inventory for release certificate",
            "old report for current-head evidence",
        ],
    }


def _write_json(path: Path, value: Mapping[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(
        json.dumps(value, ensure_ascii=False, indent=2) + "\n",
        encoding="utf-8",
    )


def write_source_inventories(repo_root: str | Path) -> dict[str, Any]:
    """Refresh all tracked inventory views from one source scan."""

    root = _repo_root(repo_root)
    inventory = collect_source_inventory(root)
    _write_json(
        root / "docs" / "formal-release" / "theorem_manifest.json",
        _theorem_manifest(inventory),
    )
    _write_json(
        root / "docs" / "remediation" / "lean_manifest.json",
        _lean_manifest(inventory),
    )
    _write_json(
        root / "docs" / "audit" / "proof_ledger.json",
        _proof_ledger(inventory),
    )
    return inventory


def _command_display(command: Sequence[str]) -> str:
    return subprocess.list2cmdline(list(command))


def _run_command_gate(
    gate_id: str,
    command: Sequence[str],
    cwd: Path,
    output_dir: Path,
    repo_root: Path,
) -> dict[str, Any]:
    started = datetime.now(timezone.utc)
    try:
        completed = subprocess.run(
            list(command),
            cwd=cwd,
            capture_output=True,
            text=True,
            encoding="utf-8",
            errors="backslashreplace",
            timeout=10_800,
        )
        exit_code = completed.returncode
        output = completed.stdout + completed.stderr
    except FileNotFoundError as exc:
        exit_code = 127
        output = f"BACKEND_UNAVAILABLE: {exc}\n"
    except subprocess.TimeoutExpired as exc:
        exit_code = 124
        output = f"TIMEOUT: {exc}\n"
    finished = datetime.now(timezone.utc)
    log_name = f"{gate_id}.log"
    log_path = output_dir / log_name
    log_path.write_text(output, encoding="utf-8")
    return {
        "gate_id": gate_id,
        "commands": [_command_display(command)],
        "working_directory": cwd.resolve().relative_to(repo_root).as_posix() or ".",
        "exit_code": exit_code,
        "started_at": started.isoformat(),
        "finished_at": finished.isoformat(),
        "status": "PASS" if exit_code == 0 else "FAIL",
        "raw_log": log_name,
        "raw_log_sha256": sha256_file(log_path),
        "raw_log_size_bytes": log_path.stat().st_size,
    }


def _run_inventory_gate(repo_root: Path, output_dir: Path) -> dict[str, Any]:
    started = datetime.now(timezone.utc)
    current = collect_source_inventory(repo_root)
    manifest_path = repo_root / "docs" / "formal-release" / "theorem_manifest.json"
    recorded = json.loads(manifest_path.read_text(encoding="utf-8"))
    keys = (
        "status",
        "source_hash_contract",
        "lean_source_file_count",
        "theorem_declaration_count",
        "source_inventory_digest",
        "sources",
    )
    mismatches = [key for key in keys if recorded.get(key) != current.get(key)]
    ledger_issues = _sorry_ledger_issues(repo_root, current)
    exit_code = 0 if not mismatches and not ledger_issues else 1
    output = json.dumps(
        {
            "mismatches": mismatches,
            "sorry_ledger_issues": ledger_issues,
            "source_inventory_digest": current["source_inventory_digest"],
            "theorem_declaration_count": current["theorem_declaration_count"],
        },
        ensure_ascii=False,
        indent=2,
    ) + "\n"
    log_path = output_dir / "source_inventory.log"
    log_path.write_text(output, encoding="utf-8")
    finished = datetime.now(timezone.utc)
    return {
        "gate_id": "source_inventory",
        "commands": [
            f"{Path(sys.executable).name} scripts/generate_formal_release_certificate.py --check-inventories"
        ],
        "working_directory": ".",
        "exit_code": exit_code,
        "started_at": started.isoformat(),
        "finished_at": finished.isoformat(),
        "status": "PASS" if exit_code == 0 else "FAIL",
        "raw_log": log_path.name,
        "raw_log_sha256": sha256_file(log_path),
        "raw_log_size_bytes": log_path.stat().st_size,
    }


def _sorry_ledger_issues(
    repo_root: Path, inventory: Mapping[str, Any]
) -> list[str]:
    ledger = (repo_root / "SORRY_LEDGER.md").read_text(encoding="utf-8")
    existing = {
        theorem["name"]
        for source in inventory["sources"]
        for theorem in source["theorems"]
    }
    issues: list[str] = []
    in_current_table = False
    for line in ledger.splitlines():
        if line.strip() == "## Current Theorem Entries":
            in_current_table = True
            continue
        if in_current_table and line.startswith("## "):
            break
        if not in_current_table or not line.startswith("|"):
            continue
        cells = [cell.strip().strip("`") for cell in line.strip("|").split("|")]
        if not cells or cells[0] in {"theorem_name", "---", "_none_"}:
            continue
        if cells[0] not in existing:
            issues.append(f"nonexistent current theorem: {cells[0]}")
    return issues


def _version(command: Sequence[str], cwd: Path) -> str:
    try:
        completed = subprocess.run(
            list(command),
            cwd=cwd,
            capture_output=True,
            text=True,
            encoding="utf-8",
            errors="backslashreplace",
            timeout=30,
        )
    except (FileNotFoundError, subprocess.TimeoutExpired):
        return "BACKEND_UNAVAILABLE"
    output = (completed.stdout or completed.stderr).strip()
    return output if completed.returncode == 0 and output else "ERROR"


def _bound_inputs(repo_root: Path) -> list[dict[str, Any]]:
    paths = (
        "proofs/lean/juris_lean/lean-toolchain",
        "proofs/lean/juris_lean/lakefile.lean",
        "proofs/lean/juris_lean/lake-manifest.json",
        "proofs/lean/juris_lean/JurisLean/AxiomAudit.lean",
        "docs/formal-release/theorem_manifest.json",
        "docs/formal-release/formal_release_certificate.schema.json",
        "scripts/generate_formal_release_certificate.py",
        "scripts/verify_formal_release_certificate.py",
        "scripts/scan_lean_guards.py",
        "SORRY_LEDGER.md",
    )
    return [
        {"path": path, "sha256": sha256_file(repo_root / path)} for path in paths
    ]


def _gate_has_fail_closed_marker(gate: Mapping[str, Any], output_dir: Path) -> bool:
    if gate["status"] != "PASS":
        return True
    content = (output_dir / gate["raw_log"]).read_text(
        encoding="utf-8", errors="replace"
    )
    marker_pattern = re.compile(
        r"\b(?:" + "|".join(re.escape(marker) for marker in FAIL_CLOSED_MARKERS) + r")\b"
    )
    return marker_pattern.search(content) is not None


def generate_formal_release_certificate(
    repo_root: str | Path,
    output_dir: str | Path,
    *,
    lake_command: str = "lake",
) -> Path:
    """Run all current-head gates and write a provisional local certificate artifact."""

    root = _repo_root(repo_root)
    out = Path(output_dir).resolve()
    out.mkdir(parents=True, exist_ok=True)
    lean_root = root / "proofs" / "lean" / "juris_lean"
    inventory = collect_source_inventory(root)
    python = sys.executable
    lake_path = Path(lake_command)
    if lake_path.parent != Path("."):
        lean_command = str(lake_path.with_name("lean.exe"))
        elan_command = str(lake_path.with_name("elan.exe"))
    else:
        lean_command = "lean"
        elan_command = "elan"

    gates = [
        _run_command_gate(
            "pytest_collection",
            (python, "-m", "pytest", "--collect-only", "-q"),
            root,
            out,
            root,
        ),
        _run_command_gate(
            "pytest_full",
            (python, "-m", "pytest", "-q", "-ra"),
            root,
            out,
            root,
        ),
        _run_inventory_gate(root, out),
        _run_command_gate("lake_clean", (lake_command, "clean"), lean_root, out, root),
        _run_command_gate(
            "lake_build",
            (lake_command, "build", *_lean_build_targets(inventory)),
            lean_root,
            out,
            root,
        ),
        _run_command_gate(
            "axiom_audit",
            (lake_command, "env", "lean", "JurisLean/AxiomAudit.lean"),
            lean_root,
            out,
            root,
        ),
        _run_command_gate(
            "lean_guard",
            (
                python,
                "scripts/scan_lean_guards.py",
                "proofs/lean/juris_lean/JurisLean",
            ),
            root,
            out,
            root,
        ),
    ]

    subject_commit = _git(root, "rev-parse", "HEAD")
    tree_hash = _git(root, "show", "-s", "--format=%T", subject_commit)
    dirty_output = _git(root, "status", "--porcelain", "--untracked-files=normal")
    environment = {
        "os": platform.system(),
        "os_release": platform.release(),
        "architecture": platform.machine(),
        "python": sys.version.replace("\n", " "),
        "python_executable": Path(sys.executable).name,
        "elan": _version((elan_command, "--version"), root),
        "lean": _version((lean_command, "--version"), lean_root),
        "lake": _version((lake_command, "--version"), lean_root),
    }
    all_gates_pass = all(
        not _gate_has_fail_closed_marker(gate, out) for gate in gates
    )
    environment_complete = not any(
        value in FAIL_CLOSED_MARKERS for value in environment.values()
    )
    status = (
        "FORMAL_RELEASE_VERIFIED"
        if all_gates_pass and environment_complete and not dirty_output
        else "SOURCE_INVENTORY_NOT_RELEASE_CERTIFICATE"
    )
    certificate: dict[str, Any] = {
        "schema_version": CERTIFICATE_VERSION,
        "status": status,
        "subject": {
            "commit": subject_commit,
            "tree": tree_hash,
            "dirty": bool(dirty_output),
        },
        "environment": environment,
        "inputs": _bound_inputs(root),
        "source_inventory": inventory,
        "gates": gates,
        "trusted_axiom_basis": ["propext", "Quot.sound", "Classical.choice"],
        "limitations": [
            "This certificate binds one commit, tree, toolchain, source inventory, and recorded gate run.",
            "Source digests do not prove source authority, translation fidelity, runtime correctness, or legal correctness.",
            "Python and runtime checks do not substitute for Lean theorems.",
            "Runtime refinement requires a separate RuntimeRefinementReceipt.",
        ],
    }
    certificate["certificate_digest"] = sha256_bytes(
        canonical_json_bytes(certificate)
    )
    certificate_path = out / f"formal-release-certificate-{subject_commit}.json"
    _write_json(certificate_path, certificate)
    return certificate_path


def check_source_inventories(repo_root: str | Path) -> list[str]:
    root = _repo_root(repo_root)
    inventory = collect_source_inventory(root)
    recorded = json.loads(
        (root / "docs" / "formal-release" / "theorem_manifest.json").read_text(
            encoding="utf-8"
        )
    )
    keys = (
        "status",
        "source_hash_contract",
        "lean_source_file_count",
        "theorem_declaration_count",
        "source_inventory_digest",
        "sources",
    )
    issues = [key for key in keys if recorded.get(key) != inventory.get(key)]
    return issues + _sorry_ledger_issues(root, inventory)


def _parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo-root", default=None)
    parser.add_argument("--write-inventories", action="store_true")
    parser.add_argument("--check-inventories", action="store_true")
    parser.add_argument("--run-gates", action="store_true")
    parser.add_argument("--output-dir", default="build-logs/formal-release")
    parser.add_argument("--lake-command", default="lake")
    return parser


def main(argv: Sequence[str] | None = None) -> int:
    args = _parser().parse_args(argv)
    root = _repo_root(args.repo_root)
    if args.write_inventories:
        inventory = write_source_inventories(root)
        print(json.dumps(inventory, ensure_ascii=False, indent=2))
    if args.check_inventories:
        issues = check_source_inventories(root)
        print(json.dumps({"status": "PASS" if not issues else "FAIL", "issues": issues}))
        if issues:
            return 1
    if args.run_gates:
        certificate = generate_formal_release_certificate(
            root,
            root / args.output_dir,
            lake_command=args.lake_command,
        )
        document = json.loads(certificate.read_text(encoding="utf-8"))
        print(certificate)
        return 0 if document["status"] == "FORMAL_RELEASE_VERIFIED" else 1
    if not (args.write_inventories or args.check_inventories or args.run_gates):
        print(json.dumps(collect_source_inventory(root), ensure_ascii=False, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
