#!/usr/bin/env python3
"""Regenerate the probability/expectation block of ``JurisLean/AxiomAudit.lean``.

Qoder audit P1-11: the statistics theorems in ``FullMath/Probability/`` and the
rational-expectation results in ``BusinessRoot/Analytics.lean`` are compiled by
CI but appeared in no ``#print axioms`` line, so "axiom audit green" silently
excluded the most mathematical part of the repository. Names are re-derived from
the declaration sites together with their namespace nesting, so a renamed
theorem re-generates instead of rotting into a dangling audit target.

This changes only which declarations are *inspected*; it never touches a proof.
"""

from __future__ import annotations

import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
PKG = ROOT / "proofs" / "lean" / "juris_lean" / "JurisLean"
AUDIT = PKG / "AxiomAudit.lean"

PROB_DIR = "FullMath/Probability"
EXTRA_SOURCES = ("BusinessRoot/Analytics.lean",)

MARKER = "Generated probability / expectation audit surface"

DECL = re.compile(r"^(?:@\[[^\]]*\][ \t]*)*(?:theorem|lemma)\s+([^\s(:{]+)")


def names_in(rel: str) -> list[str]:
    """Fully qualified declaration names in one file, honouring namespace nesting."""
    ns: list[str] = []
    out: list[str] = []
    for line in (PKG / rel).read_text(encoding="utf-8").splitlines():
        head = re.match(r"^namespace (\S+)", line)
        if head:
            ns.append(head.group(1))
            continue
        tail = re.match(r"^end (\S+)", line)
        if tail and ns and tail.group(1) == ns[-1]:
            ns.pop()
            continue
        decl = DECL.match(line)
        if decl:
            out.append(".".join(ns + [decl.group(1)]))
    return out


def probability_modules() -> list[str]:
    return sorted(f.stem for f in (PKG / PROB_DIR).glob("*.lean"))


def collect() -> list[str]:
    names: list[str] = []
    for stem in probability_modules():
        names += names_in(f"{PROB_DIR}/{stem}.lean")
    for rel in EXTRA_SOURCES:
        names += names_in(rel)
    return sorted(set(names))


def audited_elsewhere() -> set[str]:
    """Leaf names already printed by another audit driver, so nothing duplicates."""
    taken: set[str] = set()
    for path in PKG.rglob("*.lean"):
        if path == AUDIT:
            continue
        for m in re.finditer(r"^#print axioms (\S+)", path.read_text(encoding="utf-8"), re.M):
            taken.add(m.group(1).rsplit(".", 1)[-1])
    return taken


def render_block(names: list[str]) -> list[str]:
    return [
        "",
        f"/-! {MARKER}. Regenerate with",
        "      scripts/ci/generate_probability_audit_surface.py --write",
        "    These declarations are elaborated by the all-module CI plan but were",
        "    absent from the release audit surface; the block is generated from the",
        "    declaration sites, so it cannot name a theorem that does not exist. -/",
    ] + ["#print axioms " + name for name in names]


def required_imports() -> list[str]:
    mods = [f"{PROB_DIR}/{stem}.lean" for stem in probability_modules()] + list(EXTRA_SOURCES)
    return sorted(
        "import JurisLean." + rel[:-5].replace("/", ".")
        for rel in mods
    )


def build(current: str) -> tuple[str, int]:
    lines = current.splitlines()
    head: list[str] = []
    # The generated block always sits at the end of the file, so the previous
    # render is simply truncated away; that keeps the tool idempotent.
    for line in lines:
        if MARKER in line:
            break
        head.append(line)
    while head and not head[-1].strip():
        head.pop()

    have = set(head)
    imports = [i for i in required_imports() if i not in have]
    if imports:
        last = max(i for i, l in enumerate(head) if l.startswith("import "))
        head[last + 1:last + 1] = [""] + imports

    names = [n for n in collect() if n.rsplit(".", 1)[-1] not in audited_elsewhere()]
    rendered = "\n".join(head + render_block(names)).rstrip("\n") + "\n"
    return re.sub(r"\n{3,}", "\n\n", rendered), len(names)


def main() -> int:
    current = AUDIT.read_text(encoding="utf-8")
    new, count = build(current)
    if "--check" in sys.argv:
        if new != current:
            print(
                "AxiomAudit probability surface is stale against the declaration "
                f"sites (expected {count} targets); run --write",
                file=sys.stderr,
            )
            return 1
        print(f"AxiomAudit probability surface current ({count} targets)")
        return 0
    if "--write" in sys.argv:
        AUDIT.write_text(new, encoding="utf-8", newline="\n")
        print(f"wrote {count} #print axioms targets into {AUDIT.name}")
        return 0
    print(f"{count} targets would be written; pass --write or --check")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
