from __future__ import annotations

from pathlib import Path
import hashlib
import json
import subprocess

from scripts.generate_formal_release_certificate import (
    assemble_release_certificate,
    collect_source_inventory,
)
from scripts.verify_formal_release_certificate import verify_certificate


REPO_ROOT = Path(__file__).resolve().parents[1]


def test_generated_inventory_binds_every_lean_source_and_theorem() -> None:
    inventory = collect_source_inventory(REPO_ROOT)

    source_paths = {source["path"] for source in inventory["sources"]}
    theorem_records = [
        theorem
        for source in inventory["sources"]
        for theorem in source["theorems"]
    ]

    assert inventory["status"] == "source_inventory_not_release_certificate"
    assert inventory["lean_source_file_count"] == len(source_paths)
    assert inventory["theorem_declaration_count"] == len(theorem_records)
    assert all(len(source["sha256"]) == 64 for source in inventory["sources"])
    assert all(theorem["line"] > 0 for theorem in theorem_records)
    assert not source_paths.intersection(
        {
            "proofs/lean/juris_lean/JurisLean/argmin_polytime.lean",
            "proofs/lean/juris_lean/JurisLean/HornCanonical.lean",
            "proofs/lean/juris_lean/JurisLean/ArgumentCompiler.lean",
        }
    )


def test_release_certificate_binds_ci_subject_without_verifier_self_reference(tmp_path) -> None:
    head = subprocess.run(
        ["git", "-C", str(REPO_ROOT), "rev-parse", "HEAD"],
        capture_output=True,
        text=True,
        check=True,
    ).stdout.strip()
    tree = subprocess.run(
        ["git", "-C", str(REPO_ROOT), "rev-parse", "HEAD^{tree}"],
        capture_output=True,
        text=True,
        check=True,
    ).stdout.strip()
    identity = {
        "in_ci": True,
        "status": "CI_RUN",
        "subject": {"sha": head, "tree": tree},
    }
    (tmp_path / "ci-run-identity.json").write_text(json.dumps(identity), encoding="utf-8")
    (tmp_path / "mutation-property-report.json").write_text(
        json.dumps({"status": "PASS", "in_ci": True, "subject": {"sha": head}}),
        encoding="utf-8",
    )
    for name in (
        "lake-clean-build.log",
        "axiom-audit.raw.txt",
        "lean-guard-report.json",
        "pytest-collection.txt",
        "pytest-full.log",
    ):
        (tmp_path / name).write_text("bound evidence\n", encoding="utf-8")
    runtime_reports = []
    for index in range(3):
        name = f"runtime-{index}.actual.json"
        content = f"receipt {index}\n".encode()
        (tmp_path / name).write_bytes(content)
        runtime_reports.append({
            "passed": True,
            "blocked": False,
            "error_codes": [],
            "checks": [],
            "lmm_commit": head,
            "runtime_commit": "2" * 40,
            "runtime_build_id": "test-build",
            "actual_receipt_file": name,
            "actual_receipt_sha256": hashlib.sha256(content).hexdigest(),
        })
    (tmp_path / "runtime-refinement-report.json").write_text(
        "\n".join(json.dumps(report) for report in runtime_reports), encoding="utf-8"
    )

    certificate = assemble_release_certificate(REPO_ROOT, ci_evidence_dir=tmp_path)
    certificate_path = tmp_path / "formal-release-certificate.json"
    certificate_path.write_text(json.dumps(certificate), encoding="utf-8")
    report = verify_certificate(certificate_path, repo_root=REPO_ROOT, ci_evidence_dir=tmp_path)

    assert certificate["status"] == "RELEASE_PASS_PENDING_INDEPENDENT_VERIFICATION"
    assert certificate["subject"] == identity["subject"]
    assert "independent-verifier-report.json" not in certificate["ci_evidence"]
    assert "missing_ci_evidence" not in certificate
    assert report["verdict"] == "VERIFIED_PENDING_RELEASE_GATE"
    assert report["error_codes"] == []

    blocked_runtime = [
        {
            **report,
            "passed": False,
            "blocked": True,
            "error_codes": ["MISSING_ACTUAL_RECEIPT"],
        }
        for report in runtime_reports
    ]
    (tmp_path / "runtime-refinement-report.json").write_text(
        "\n".join(json.dumps(report) for report in blocked_runtime), encoding="utf-8"
    )
    certificate = assemble_release_certificate(REPO_ROOT, ci_evidence_dir=tmp_path)
    certificate_path.write_text(json.dumps(certificate), encoding="utf-8")
    blocked_report = verify_certificate(
        certificate_path, repo_root=REPO_ROOT, ci_evidence_dir=tmp_path
    )

    assert blocked_report["verdict"] == "VERIFICATION_FAILED"
    assert "RUNTIME_REFINEMENT_NOT_PASS" in blocked_report["error_codes"]
