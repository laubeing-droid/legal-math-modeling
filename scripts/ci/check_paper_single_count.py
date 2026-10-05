#!/usr/bin/env python3
"""Fail-closed gate (round-2 F6): one paper, one artifact, one set of counts.

Origin: round-1 review item B6 -- the same Chinese draft cited 3240/3252 in two
places and 3617/3629 in a third, all allegedly bound to the same inventory
artifact, and 3240 existed only inside a sha256 string. This gate makes that
shape of drift red: in each paper draft, every 4-digit figure (>=3000, years
excluded) appearing in a sentence that talks about theorems/declarations must
be one of the counts the CURRENT artifact itself reports (either scope's
theorem count or counted-declaration count). Nothing is hard-coded: the
allowed set is recomputed from docs/formal-release/theorem_inventory_v3.json
on every run, so a legitimate recount never needs a gate edit.

Scope: the two paper drafts under docs/paper-rewrite/ (the ledger 17_ keeps
run-bound historical figures by design and is out of scope). The allowed set
is the union of the inventory's scope counts and the closure-class counts of
trivial_proof_census.json (a sibling artifact the drafts cite in the same
sentences); both are re-read on every run, never hard-coded.

Exit codes: 0 clean, 1 violations, 2 usage error.
"""

from __future__ import annotations

import json
import re
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[2]
ARTIFACT = REPO_ROOT / "docs" / "formal-release" / "theorem_inventory_v3.json"
PAPERS = (
    REPO_ROOT / "docs" / "paper-rewrite" / "paper_cn.md",
    REPO_ROOT / "docs" / "paper-rewrite" / "paper_en.md",
)

SENTENCE_SPLIT = re.compile(r"[。！？；!?;]+|\n+")
NUM_RE = re.compile(r"\b(\d{4})\b")
THEOREM_CONTEXT = ("定理", "theorem", "Theorem")
YEAR_RE = re.compile(r"^(19|20)\d\d$")


def allowed_counts(artifact: Path = ARTIFACT) -> set[int]:
    doc = json.loads(artifact.read_text(encoding="utf-8"))
    out: set[int] = set()
    for scope in doc["scope_summary"].values():
        out.add(scope["theorem_count"])
        out.add(scope["counted_declaration_count"])
    census = artifact.parent / "trivial_proof_census.json"
    if census.is_file():
        cdoc = json.loads(census.read_text(encoding="utf-8"))
        out.update(int(v) for v in cdoc.get("closure_counts", {}).values())
    return out


def find_violations_in_text(text: str, allowed: set[int]) -> list[tuple[int, str, int]]:
    """(line_no, segment, bad_number) for theorem-sentences citing foreign counts."""
    hits: list[tuple[int, str, int]] = []
    for line_no, line in enumerate(text.splitlines(), 1):
        for segment in SENTENCE_SPLIT.split(line):
            if not any(tok in segment for tok in THEOREM_CONTEXT):
                continue
            for raw in NUM_RE.findall(segment):
                if int(raw) < 3000 or YEAR_RE.match(raw):
                    continue
                if int(raw) not in allowed:
                    hits.append((line_no, segment.strip(), int(raw)))
    return hits


def find_violations(papers= PAPERS, artifact: Path = ARTIFACT) -> list[tuple[Path, int, str, int]]:
    allowed = allowed_counts(artifact)
    hits: list[tuple[Path, int, str, int]] = []
    for paper in papers:
        text = paper.read_text(encoding="utf-8", errors="replace")
        for line_no, segment, number in find_violations_in_text(text, allowed):
            hits.append((paper, line_no, segment, number))
    return hits


def main(argv: list[str]) -> int:
    papers = PAPERS
    artifact = ARTIFACT
    if len(argv) > 1:
        papers = tuple(Path(p) for p in argv[1:-1]) or PAPERS
        artifact = Path(argv[-1])
    if not artifact.is_file():
        print("usage: check_paper_single_count.py [paper...] [artifact.json]", file=sys.stderr)
        return 2
    allowed = allowed_counts(artifact)
    hits = find_violations(papers, artifact)
    for paper, line_no, segment, number in hits:
        print(f"{paper.name}:{line_no}: count {number} not in artifact values {sorted(allowed)}: {segment[:100]}")
    if hits:
        print(f"FAIL: {len(hits)} foreign theorem-count(s) against {artifact.name}")
        return 1
    print(f"PASS: all theorem-count sentences match the artifact ({sorted(allowed)})")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
