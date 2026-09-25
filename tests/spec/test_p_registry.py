"""Proof-campaign registry gate: every master-genealogy concept P-001..P-132
is bound to verification anchors that actually exist in the repository,
and the registry roster matches the frozen genealogy tables."""

from __future__ import annotations

import json
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
REGISTRY = ROOT / "theory" / "spec" / "p_registry.json"
GENEALOGY = ROOT / "docs" / "master-plan" / "基线" / "法律概念总谱.md"


def _load() -> dict:
    return json.loads(REGISTRY.read_text(encoding="utf-8"))


def test_registry_covers_all_132_in_order() -> None:
    doc = _load()
    ids = [e["id"] for e in doc["entries"]]
    assert ids == [f"P-{i:03d}" for i in range(1, 133)]
    assert len({e["roster"] for e in doc["entries"] if e["roster"] != "—"} | {"—"}) >= 1


def test_registry_roster_matches_genealogy() -> None:
    text = GENEALOGY.read_text(encoding="utf-8")
    rows = {}
    for line in text.splitlines():
        if line.startswith("| P-"):
            cells = [c.strip() for c in line.strip().strip("|").split("|")]
            rows[cells[0]] = cells[1]
    assert len(rows) == 132
    for e in _load()["entries"]:
        assert rows[e["id"]] == e["roster"], e["id"]


def test_every_anchor_exists_with_symbol() -> None:
    for e in _load()["entries"]:
        assert e["anchors"], e["id"]
        for anchor in e["anchors"]:
            f = ROOT / anchor["file"]
            assert f.exists(), f"{e['id']} -> {anchor['file']}"
            if anchor["symbol"]:
                text = f.read_text(encoding="utf-8", errors="replace")
                assert anchor["symbol"] in text, (
                    f"{e['id']} -> {anchor['symbol']} not in {anchor['file']}"
                )


def test_tiers_and_kinds_are_sound() -> None:
    doc = _load()
    tiers = {e["tier"] for e in doc["entries"]}
    assert tiers == {"PREEXISTING", "SHIPPED_THIS_CAMPAIGN"}
    shipped = [e for e in doc["entries"] if e["tier"] == "SHIPPED_THIS_CAMPAIGN"]
    assert len(shipped) == 75
    for e in shipped:
        # Every campaign-shipped concept anchors both a contract module and a test.
        files = {a["file"] for a in e["anchors"]}
        assert any(f.startswith("tests/") for f in files), e["id"]
        assert any(f.startswith("theory/") for f in files), e["id"]
