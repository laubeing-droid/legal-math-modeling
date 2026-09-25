#!/usr/bin/env python3
"""RC-02 machine-readable claims registry: loader and drift checker.

`docs/formal-release/claims_registry.json` mirrors the two human-readable
lists (ALLOWED_CLAIMS.md / FORBIDDEN_CLAIMS.md) claim by claim. The drift
checker re-parses the markdown sources and compares exact claim text, so a
one-sided edit of either surface fails closed instead of silently becoming
the ninth drift source. The registry grants nothing by itself: an allowed
claim still requires its named evidence bound to the cited subject commit.
"""

from __future__ import annotations

import json
from pathlib import Path
from typing import Dict, List

ROOT = Path(__file__).resolve().parents[2]
REGISTRY_PATH = ROOT / "docs" / "formal-release" / "claims_registry.json"
ALLOWED_MD = ROOT / "docs" / "formal-release" / "ALLOWED_CLAIMS.md"
FORBIDDEN_MD = ROOT / "docs" / "formal-release" / "FORBIDDEN_CLAIMS.md"


class ClaimsRegistryDefect(ValueError):
    """Raised when the registry or its sources violate their contract."""


def load_registry() -> Dict[str, object]:
    doc = json.loads(REGISTRY_PATH.read_text(encoding="utf-8"))
    if doc.get("schema_version") != "claims-registry-v1":
        raise ClaimsRegistryDefect("unexpected schema_version")
    for section in ("allowed", "forbidden"):
        rows = doc.get(section)
        if not isinstance(rows, list) or not rows:
            raise ClaimsRegistryDefect(f"empty or missing section: {section}")
        ids = [row["id"] for row in rows]
        if len(ids) != len(set(ids)):
            raise ClaimsRegistryDefect(f"duplicate ids in section: {section}")
        for row in rows:
            if not row.get("claim", "").strip():
                raise ClaimsRegistryDefect(f"empty claim in {row.get('id')}")
    if not doc.get("fallback_rule"):
        raise ClaimsRegistryDefect("missing fallback_rule")
    return doc


def parse_allowed_md() -> List[str]:
    lines = ALLOWED_MD.read_text(encoding="utf-8").splitlines()
    claims = []
    for line in lines:
        if not line.startswith("|") or line.startswith("|---") or line.startswith("| Claim"):
            continue
        parts = [p.strip() for p in line.strip().strip("|").split("|")]
        if len(parts) == 2:
            claims.append(parts[0])
    return claims


def parse_forbidden_md() -> List[str]:
    claims = []
    in_list = False
    for line in FORBIDDEN_MD.read_text(encoding="utf-8").splitlines():
        if line.startswith("- "):
            in_list = True
            claims.append(line[2:].strip())
        elif in_list and line.strip():
            break
    return claims


def drift_problems() -> List[str]:
    """One-sided edits of md or json surface here; empty list = in lockstep."""

    doc = load_registry()
    problems: List[str] = []

    md_allowed = parse_allowed_md()
    json_allowed = [row["claim"] for row in doc["allowed"]]
    if md_allowed != json_allowed:
        problems.append(
            f"allowed drift: md has {len(md_allowed)} claims, json has {len(json_allowed)}"
        )

    md_forbidden = parse_forbidden_md()
    json_forbidden = [row["claim"] for row in doc["forbidden"]]
    if md_forbidden != json_forbidden:
        problems.append(
            f"forbidden drift: md has {len(md_forbidden)} claims, json has {len(json_forbidden)}"
        )
    return problems
