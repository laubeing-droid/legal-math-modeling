#!/usr/bin/env python3
"""Fail-closed gate (round-2 F3): no markdown/ledger sentence may couple
``statuteChain_on`` with ``CaseInput`` or ``案卷`` in the same sentence.

Origin: round-2 review item B3 confirmed that the claim "a desensitised sample
runs statuteChain_on end to end" was false -- the chain predicate consumes a
handwritten ``UnifiedModel`` and the case-input layer has no downstream
consumer. This gate makes the corrected wording enforceable: any md file under
the scanned root that again couples the two in one sentence goes red.

Scope note (per the mandate): the red surface is derived by scanning the md
files themselves, never from the theorem inventory or any artifact this gate
also audits. Sentence splitting is punctuation-based (。！？；!?; and newlines);
a line without sentence punctuation counts as one sentence.

Exit codes: 0 clean, 1 violations found, 2 usage error.
"""

from __future__ import annotations

import re
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[2]

CHAIN_TOKEN = "statuteChain_on"
CASE_TOKENS = ("CaseInput", "案卷")
SENTENCE_SPLIT = re.compile(r"[。！？；!?;]+")


def find_violations_in_text(text: str) -> list[tuple[int, str]]:
    """Return (line_number, offending_segment) pairs for one document."""
    hits: list[tuple[int, str]] = []
    for line_no, line in enumerate(text.splitlines(), 1):
        for segment in SENTENCE_SPLIT.split(line):
            if CHAIN_TOKEN in segment and any(tok in segment for tok in CASE_TOKENS):
                hits.append((line_no, segment.strip()))
    return hits


def find_violations(root: Path) -> list[tuple[Path, int, str]]:
    """Scan every *.md under root; return (path, line_number, segment)."""
    hits: list[tuple[Path, int, str]] = []
    for path in sorted(root.rglob("*.md")):
        if any(part in {".git", "node_modules", ".lake"} for part in path.parts):
            continue
        text = path.read_text(encoding="utf-8", errors="replace")
        for line_no, segment in find_violations_in_text(text):
            hits.append((path, line_no, segment))
    return hits


def main(argv: list[str]) -> int:
    root = Path(argv[1]) if len(argv) > 1 else REPO_ROOT / "docs"
    if not root.is_dir():
        print(f"usage: check_statute_chain_caseinput_claim.py [md-root]", file=sys.stderr)
        return 2
    hits = find_violations(root)
    for path, line_no, segment in hits:
        print(f"{path}:{line_no}: couples {CHAIN_TOKEN} with case-input token: {segment[:120]}")
    if hits:
        print(f"FAIL: {len(hits)} sentence(s) couple the chain predicate with the case-input layer")
        return 1
    print(f"PASS: no md sentence couples {CHAIN_TOKEN} with CaseInput/案卷 under {root}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
