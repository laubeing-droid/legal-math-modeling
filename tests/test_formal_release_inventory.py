from __future__ import annotations

from pathlib import Path

from scripts.generate_formal_release_certificate import collect_source_inventory


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
