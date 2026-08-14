from __future__ import annotations

from pathlib import Path

from scripts.generate_formal_release_certificate import (
    _gate_has_fail_closed_marker,
    _lean_build_targets,
    collect_source_inventory,
)


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


def test_fail_closed_marker_scan_ignores_mutation_test_identifiers(tmp_path: Path) -> None:
    log_path = tmp_path / "pytest_collection.log"
    gate = {"status": "PASS", "raw_log": log_path.name}

    log_path.write_text("mutation[UNKNOWN_ACCEPTED_ARGUMENT]\n", encoding="utf-8")
    assert not _gate_has_fail_closed_marker(gate, tmp_path)

    log_path.write_text("result: UNKNOWN\n", encoding="utf-8")
    assert _gate_has_fail_closed_marker(gate, tmp_path)


def test_lake_build_targets_cover_every_inventory_module() -> None:
    inventory = collect_source_inventory(REPO_ROOT)
    targets = _lean_build_targets(inventory)
    expected_modules = {
        source["path"]
        .removeprefix("proofs/lean/juris_lean/")
        .removesuffix(".lean")
        .replace("/", ".")
        for source in inventory["sources"]
    }

    assert targets[0] == "JurisLean"
    assert set(targets[1:]) == expected_modules
    assert len(targets) == inventory["lean_source_file_count"] + 1
    assert "JurisLean.HornFixedPoint" in targets
    assert "JurisLean.AxiomAudit" in targets
