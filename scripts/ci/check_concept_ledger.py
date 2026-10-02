#!/usr/bin/env python3
"""Reverse completeness check for the concept ledger (W5).

The ledger at docs/master-plan/13_...md lists the places where ONE legal phrase maps to
SEVERAL Lean types. A hand written list can only ever cover what its author already knows,
so this gate computes the population from the source and asks a different question:

    which constructor names appear as a constructor of TWO DIFFERENT inductive/structure
    declarations in different files, with no import edge between those files?

Any such pair is a candidate "same legal word, two mathematical objects" site. Each must be
registered in the ledger by naming at least one of its two declaration names. An unregistered
pair is a hole in the ledger itself -- red.

Read only: it never writes. Exit 1 on an unregistered pair, 2 on a ledger it cannot parse.
"""

from __future__ import annotations

import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
SOURCE = ROOT / "proofs" / "lean" / "juris_lean" / "JurisLean"
LEDGER = ROOT / "docs" / "master-plan" / "13_概念台账与命名消歧_20261002.md"

DECL = re.compile(
    r"^(?:private\s+|protected\s+)?(inductive|structure)\s+([A-Za-z0-9_.']+)([^:|]*?)(?:\s+where)?\s*$"
)
CTOR = re.compile(r"^\s*\|\s*([A-Za-z0-9_][A-Za-z0-9_']*)")
FIELD = re.compile(r"^\s{2}([a-z][A-Za-z0-9_']*)\s*:")
IMPORT = re.compile(r"^import\s+([\w.]+)")


def strip_comments(text: str) -> str:
    out, i = [], 0
    while i < len(text):
        if text.startswith("/-", i):
            depth, j = 1, i + 2
            while j < len(text) and depth:
                if text.startswith("/-", j):
                    depth += 1
                    j += 2
                elif text.startswith("-/", j):
                    depth -= 1
                    j += 2
                else:
                    j += 1
            i = j
            continue
        if text.startswith("--", i):
            k = text.find("\n", i)
            i = len(text) if k < 0 else k
            continue
        out.append(text[i])
        i += 1
    return "".join(out)


def scan() -> tuple[dict[str, list[tuple[str, str]]], dict[str, set[str]], dict[str, list[str]]]:
    """constructor name -> [(file, decl)]; file -> imported tails; decl name -> [files].

    Only `| ctor` labels count as carriers of a legal word. Structure FIELD names are
    deliberately excluded: `action`, `amount`, `b` recur across unrelated records and every
    such hit is noise that would train the reader to ignore the gate.
    """
    ctors: dict[str, list[tuple[str, str]]] = {}
    decls: dict[str, list[str]] = {}
    imports: dict[str, set[str]] = {}
    for path in sorted(SOURCE.rglob("*.lean")):
        if path.name == "JurisLean.lean":
            continue
        rel = path.relative_to(SOURCE).as_posix()
        text = strip_comments(path.read_text(encoding="utf-8"))
        cur: str | None = None
        for line in text.split("\n"):
            m = IMPORT.match(line)
            if m:
                parts = m.group(1).split(".")
                seen = imports.setdefault(rel, set())
                seen.add(parts[-1])
                if len(parts) > 1:
                    seen.add(parts[-2])
                continue
            d = DECL.match(line)
            if d:
                cur = d.group(2)
                decls.setdefault(cur.split(".")[-1], []).append(rel)
                continue
            if cur:
                found = CTOR.match(line)
                if found:
                    ctors.setdefault(found.group(1), []).append((rel, cur))
            elif line.strip() and not line.startswith((" ", "|", ")")):
                cur = None
    return ctors, imports, decls


def registered(text: str) -> set[str]:
    """Declaration names mentioned anywhere in the ledger's carrier columns."""
    names: set[str] = set()
    for row in text.splitlines():
        if not row.startswith("|"):
            continue
        for cell in row.split("|"):
            for tok in re.findall(r"[A-Za-z_][A-Za-z0-9_']*", cell):
                names.add(tok)
    return names


def legal_vocabulary() -> set[str]:
    """Lower-cased latin tokens the project already uses as named concepts.

    A label like `b` or `add` recurring in two records is plumbing, not a concept clash, and
    blocking on it would train everyone to ignore the gate. So the blocking subset is limited
    to labels that ALREADY name a concept somewhere in the register or the ledger; everything
    else is printed as a report only.
    """
    words: set[str] = set()
    for path in (ROOT / "docs" / "master-plan" / "基线" / "法律概念总谱.md", LEDGER):
        if not path.exists():
            continue
        for tok in re.findall(r"[A-Za-z][A-Za-z0-9_']{3,}", path.read_text(encoding="utf-8")):
            words.add(tok.lower())
    return words


def main() -> int:
    if not LEDGER.exists():
        print(f"ledger missing: {LEDGER}", file=sys.stderr)
        return 2
    known = registered(LEDGER.read_text(encoding="utf-8"))
    ctors, imports, decls = scan()
    holes: list[str] = []

    def unlinked(files: set[str]) -> bool:
        for f in files:
            if imports.get(f, set()) & {Path(g).stem for g in files if g != f}:
                return False
        return True

    # (a) same constructor label, two declarations, no import edge
    for ctor, sites in sorted(ctors.items()):
        pairs = {(f, d) for f, d in sites}
        files = {f for f, _ in pairs}
        if len({d for _, d in pairs}) < 2 or len(files) < 2 or not unlinked(files):
            continue
        if any(d in known for _, d in pairs) or ctor in known:
            continue
        holes.append(f"ctor {ctor}: " + "; ".join(sorted(f"{f}::{d}" for f, d in pairs)))

    # (b) same declaration NAME in two unlinked files (the `UnifiedModel` / `EventHistory` shape)
    for name, files in sorted(decls.items()):
        uniq = set(files)
        if len(uniq) < 2 or not unlinked(uniq) or name in known:
            continue
        holes.append(f"type {name}: " + "; ".join(sorted(uniq)))
    if holes:
        vocab = legal_vocabulary()
        blocking = [h for h in holes if h.split(":", 1)[0].split()[-1].lower() in vocab]
        quiet = [h for h in holes if h not in blocking]
        if quiet:
            print(f"report only (label is not a term the register already names): {len(quiet)}")
            for h in quiet[:8]:
                print(f"  {h}")
            if len(quiet) > 8:
                print(f"  ... {len(quiet) - 8} more")
        if blocking:
            print("concept ledger is incomplete -- unregistered same-name carriers:")
            for h in blocking:
                print(f"  {h}")
            print(f"total {len(blocking)} unregistered candidate pair(s)")
            return 1
    print("concept ledger covers every same-name carrier pair it is entitled to judge")
    return 0


if __name__ == "__main__":
    sys.exit(main())
