"""Every `name:LINE` anchor in the construction docs must point at a real line.

Docs that quote theorem locations by hand go stale the moment a proof file grows in
the middle: on 2026-10-01 a single 14-theorem insertion into `Seams/BoundaryClosure.lean`
shifted 36 anchors in the delivery notes, each of which had been verified when written.
The carrier-surface gate checks that names are *audited*; nothing checked that they are
*still where the doc says*, so a doc can be perfectly honest and still send a reader to
the wrong line.

Rule: for each backticked `identifier:LINE` in the covered docs, LINE must be the line of
some declaration named `identifier` somewhere in the Lean tree. When exactly one file
declares it, that is an exact check; when several do, the anchor passes if any of them
agrees.

`--fix` rewrites an anchor only when the name is declared by exactly one file and that
declaration is unique in the file, so a repair can never invent a location.
"""

from __future__ import annotations

import argparse
import re
import sys
from collections import defaultdict
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
SOURCE_ROOT = ROOT / "proofs" / "lean" / "juris_lean" / "JurisLean"
DOCS = sorted((ROOT / "docs" / "master-plan").glob("0[6-9]_*.md")) + sorted(
    (ROOT / "docs" / "master-plan").glob("1[01]_*.md")
)

DECL = re.compile(
    r"^(?:@\[[^\]]*\][ \t]*)*"
    r"(?:theorem|lemma|def|abbrev|structure|inductive|class)\s+([^\s(:{=\[]+)"
)
ANCHOR = re.compile(r"`([A-Za-z_][A-Za-z0-9_]*(?:\.[A-Za-z0-9_]+)*)\s*:\s*(\d+)`")


def build_index() -> dict[str, list[tuple[str, int]]]:
    """short name -> [(file, line)] over the whole Lean source tree."""

    index: dict[str, list[tuple[str, int]]] = defaultdict(list)
    for lean in sorted(SOURCE_ROOT.rglob("*.lean")):
        rel = lean.relative_to(ROOT).as_posix()
        for lineno, line in enumerate(lean.read_text(encoding="utf-8").splitlines(), 1):
            match = DECL.match(line)
            if match:
                index[match.group(1)].append((rel, lineno))
    return index


def check(doc: Path, index: dict[str, list[tuple[str, int]]]) -> list[str]:
    problems: list[str] = []
    text = doc.read_text(encoding="utf-8")
    for name, line in ANCHOR.findall(text):
        short = name.rsplit(".", 1)[-1]
        hits = index.get(short)
        if not hits:
            continue  # not a Lean declaration name (a file or module anchor)
        if int(line) not in {lineno for _f, lineno in hits}:
            found = ", ".join(f"{f}:{lineno}" for f, lineno in hits[:3])
            problems.append(f"{name}:{line} (source: {found})")
    return problems


def fix(doc: Path, index: dict[str, list[tuple[str, int]]]) -> int:
    text = doc.read_text(encoding="utf-8")
    count = 0

    def replace(match: re.Match) -> str:
        nonlocal count
        name, line = match.group(1), int(match.group(2))
        short = name.rsplit(".", 1)[-1]
        hits = index.get(short, [])
        files = {f for f, _ in hits}
        if line in {lineno for _f, lineno in hits} or len(files) != 1:
            return match.group(0)  # already right, or too ambiguous to touch
        lines = [lineno for _f, lineno in hits]
        if len(lines) != 1:
            return match.group(0)
        count += 1
        return f"`{name}:{lines[0]}`"

    doc.write_text(ANCHOR.sub(replace, text), encoding="utf-8", newline="\n")
    return count


def show(path: Path) -> str:
    try:
        return path.relative_to(ROOT).as_posix()
    except ValueError:  # a doc outside the repository (a test fixture)
        return path.name


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--fix", action="store_true", help="rewrite unambiguous stale anchors")
    ap.add_argument("--doc", action="append", help="restrict to these docs (repo-relative)")
    args = ap.parse_args()

    docs = [ROOT / d for d in args.doc] if args.doc else DOCS
    index = build_index()
    total = 0
    for doc in docs:
        if args.fix:
            n = fix(doc, index)
            print(f"{show(doc)}: {n} anchors rewritten")
            continue
        problems = check(doc, index)
        total += len(problems)
        if problems:
            print(f"{show(doc)}: {len(problems)} stale anchors")
            for problem in problems:
                print(f"  {problem}")
        else:
            print(f"{show(doc)}: anchors current")
    if not args.fix and total:
        print(f"doc anchor drift: {total} stale (run --fix where unambiguous)")
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
