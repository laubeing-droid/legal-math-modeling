#!/usr/bin/env python3
"""Fail-closed gate (round-2 F3): no markdown/ledger sentence may couple the
statute-chain predicate with ``CaseInput`` or ``案卷`` as a live claim.

Origin: round-2 review item B3 confirmed that the claim "a desensitised sample
runs statuteChain_on end to end" was false -- the chain predicate consumes a
handwritten ``UnifiedModel`` and the case-input layer has no downstream
consumer. This gate makes the corrected wording enforceable: a sentence that
couples the two as a *positive* claim goes red, while a sentence that *draws
the boundary between them* (e.g. "the two have no consumption edge") stays
green -- otherwise the WBS-8 spec, which must name both to delimit them, could
not exist.

Two prior fail-open edges are closed here: (1) the gate only matched the
snake_case spelling, so a re-coupling under the Lean spelling ``StatuteChainOn``
sailed through; (2) sentences were split per line, so a sentence folded across
two Markdown lines escaped. Both are now caught.

Scope note (per the mandate): the red surface is derived by scanning the md
files themselves, never from the theorem inventory or any artifact this gate
also audits. Sentence splitting is punctuation-based; a line break does not end
a sentence.

Exit codes: 0 clean, 1 violations found, 2 usage error.
"""

from __future__ import annotations

import bisect
import re
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[2]

# The chain predicate is named ``StatuteChainOn`` in Lean (camelCase) and is
# referred to as ``statuteChain_on`` / ``statuteChain_on_instanceM`` in the
# ledgers. Matching only the snake_case form let a document re-couple the two
# under the Lean spelling and sail through; match all spellings, case-blind.
CHAIN_RE = re.compile(r"(?i)statute_?chain_?on")
CASE_TOKENS = ("CaseInput", "案卷")
SENTENCE_SPLIT = re.compile(r"[。！？；!?;]")
# A sentence that NAMES both to draw the boundary between them is the corrected
# wording, not the re-coupling B3 refuted. Do not fire on it.
NEGATION_RE = re.compile(
    r"(无消费边|没有消费|无下游|不消费|未接|不接|两者之间|没有一条|零下游|无下游消费者)"
)


def _line_starts(text: str) -> list[int]:
    starts = [0]
    for line in text.splitlines(keepends=True):
        starts.append(starts[-1] + len(line))
    return starts


def _line_of(offset: int, starts: list[int]) -> int:
    """0-based char offset -> 1-based line number."""
    return bisect.bisect_right(starts, offset)


def find_violations_in_text(text: str) -> list[tuple[int, str]]:
    """Return (line_number, offending_segment) pairs for one document.

    Sentences are split on sentence punctuation only; a line break does NOT end
    a sentence, so a sentence folded across two Markdown lines is still caught.
    A sentence that couples the chain predicate with a case-input token is a
    violation UNLESS it also carries a boundary-drawing negation.
    """
    hits: list[tuple[int, str]] = []
    starts = _line_starts(text)
    seg_start = 0
    i = 0
    n = len(text)
    while i < n:
        if SENTENCE_SPLIT.fullmatch(text[i]):
            seg = text[seg_start:i]
            if (CHAIN_RE.search(seg) and any(tok in seg for tok in CASE_TOKENS)
                    and not NEGATION_RE.search(seg)):
                hits.append((_line_of(seg_start, starts), seg.strip()))
            while i < n and SENTENCE_SPLIT.fullmatch(text[i]):
                i += 1
            seg_start = i
        else:
            i += 1
    seg = text[seg_start:]
    if (CHAIN_RE.search(seg) and any(tok in seg for tok in CASE_TOKENS)
            and not NEGATION_RE.search(seg)):
        hits.append((_line_of(seg_start, starts), seg.strip()))
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
        print(f"{path}:{line_no}: couples the chain predicate with a case-input token: {segment[:120]}")
    if hits:
        print(f"FAIL: {len(hits)} sentence(s) couple the chain predicate with the case-input layer")
        return 1
    print(f"PASS: no md sentence couples the chain predicate with CaseInput/案卷 under {root}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
