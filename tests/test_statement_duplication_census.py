"""The verbatim-duplication census is the measurement behind R-04.

R-04 was booked as "migrate Genealogy's three hundred declarations onto the shared
kernel", premised on restatement. This census is what tests that premise: it counts
statements written identically in two places, and it publishes its own blind spot (the
headers it cannot read) rather than reporting a clean zero.
"""

from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
TOOL = ROOT / "scripts" / "ci" / "build_statement_duplication_census.py"
CENSUS = ROOT / "docs" / "formal-release" / "statement_duplication_census.json"


def test_check_mode_passes_offline() -> None:
    proc = subprocess.run([sys.executable, str(TOOL), "--check"], cwd=ROOT,
                          capture_output=True, text=True, encoding="utf-8",
                          errors="replace")
    assert proc.returncode == 0, proc.stdout + proc.stderr


def test_census_records_its_own_coverage_gap() -> None:
    doc = json.loads(CENSUS.read_text(encoding="utf-8"))
    assert doc["inventory_package_theorems"] > 0
    # A scanner that silently reads less than the account it is checking is the failure
    # mode this whole repository was audited for, so the gap is a published number.
    assert doc["headers_missed_by_scanner"] >= 0
    assert doc["statements_read"] + doc["headers_missed_by_scanner"] == \
        doc["inventory_package_theorems"]


def test_verbatim_duplication_is_small_and_named() -> None:
    doc = json.loads(CENSUS.read_text(encoding="utf-8"))
    # 2 pre-port pairs (FullMath GenericKernels / Representation) plus 6 that arrived
    # verbatim with the byte-faithful external port (upstream's own cross-file helper
    # lemmas: three in the Kuhn cone, append_singleton_inj in Math/TraceRun, and
    # friends). Those 6 live inside JurisLean/External and are upstream's business;
    # what this gate must keep impossible is a *cross-family* match -- a repo module
    # restating an external carrier by hand is exactly the proof island the port
    # exists to avoid.
    assert doc["duplicated_statement_types"] == 8, (
        "R-04's premise was restatement across modules; the census says eight "
        "statements are written verbatim twice (two native, six ported verbatim "
        "from upstream's own duplication). If this number moved, either a real "
        "duplicate appeared or the scanner changed what it can read -- regenerate "
        "and look.")
    assert doc["cross_family_statement_types"] == 0, (
        "no statement is duplicated across Genealogy / Mandate / FullMath / "
        "External families; a cross-family match is new evidence and belongs in "
        "the ledger, not in a merge")
    for stmt, hits in doc["duplicates"].items():
        assert len(hits) >= 2
        for hit in hits:
            assert (ROOT / "proofs" / "lean" / "juris_lean" / "JurisLean" / hit["path"]).exists()
