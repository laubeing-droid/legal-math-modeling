#!/usr/bin/env python3
"""Regenerate the generated blocks of ``JurisLean/AxiomAudit.lean``.

Qoder audit P1-11: the statistics theorems in ``FullMath/Probability/`` and the
rational-expectation results in ``BusinessRoot/Analytics.lean`` are compiled by
CI but appeared in no ``#print axioms`` line, so "axiom audit green" silently
excluded the most mathematical part of the repository. Names are re-derived from
the declaration sites together with their namespace nesting, so a renamed
theorem re-generates instead of rotting into a dangling audit target.

The same omission recurred for the mandate layer: fifteen modules passed their CI
build (run 36293474352) while not one of their 126 theorems was named by an audit
command, so nothing in CI knew what those proofs rest on. Both surfaces are
generated here for that reason.

This changes only which declarations are *inspected*; it never touches a proof.
"""

from __future__ import annotations

import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
try:
    from scripts.lean_grammar import declarations
except ImportError:  # run as `python scripts/ci/<this>.py`: sys.path[0] is scripts/ci
    sys.path.insert(0, str(ROOT / "scripts"))
    from lean_grammar import declarations
PKG = ROOT / "proofs" / "lean" / "juris_lean" / "JurisLean"
AUDIT = PKG / "AxiomAudit.lean"

PROB_DIR = "FullMath/Probability"
EXTRA_SOURCES = ("BusinessRoot/Analytics.lean",)

PROB_MARKER = "Generated probability / expectation audit surface"
MANDATE_MARKER = "Generated mandate-layer audit surface"

# (marker, directories, extra single files) -- each surface is one generated block.
SURFACES = (
    (PROB_MARKER, ("FullMath/Probability",), ("BusinessRoot/Analytics.lean",)),
    (MANDATE_MARKER, ("Mandate",), ()),
)
MARKER = PROB_MARKER

DECL = re.compile(r"^(?:@\[[^\]]*\][ \t]*)*(?:theorem|lemma)\s+([^\s(:{]+)")


def names_in(rel: str) -> list[str]:
    """Fully qualified theorem/lemma names in one file.

    Delegates to `scripts/lean_grammar.py`, which strips comments before matching.
    An earlier version scanned raw lines here, and a doc comment whose second line
    happened to begin with the word `lemma` became an audit target: CI run
    36296061840 then failed on `Unknown constant
    'JurisLean.Mandate.DerivedCertificate.rather'`, the next word in that sentence.
    """
    text = (PKG / rel).read_text(encoding="utf-8")
    return [
        d["name"] for d in declarations(text, namespace=True)
        if d["keyword"] in ("theorem", "lemma")
    ]


def surface_modules(directory: str) -> list[str]:
    return sorted(f.stem for f in (PKG / directory).glob("*.lean"))


def collect(marker: str) -> list[str]:
    directory, extras = next((d, x) for m, d, x in SURFACES if m == marker)
    names: list[str] = []
    for dirn in directory:
        for stem in surface_modules(dirn):
            names += names_in(f"{dirn}/{stem}.lean")
    for rel in extras:
        names += names_in(rel)
    return sorted(set(names))


def audited_elsewhere() -> set[str]:
    """Fully qualified names already printed by another audit driver.

    Matching on the leaf name would drop, say, ``JurisLean.Mandate.GameTree.value``
    because some unrelated driver printed a name ending in ``value`` -- the theorem
    would go unaudited while the surface still looked complete.
    """
    taken: set[str] = set()
    for path in PKG.rglob("*.lean"):
        if path == AUDIT:
            continue
        for m in re.finditer(r"^#print axioms (\S+)", path.read_text(encoding="utf-8"), re.M):
            taken.add(m.group(1))
    return taken


def render_block(names: list[str], marker: str) -> list[str]:
    return [
        "",
        f"/-! {marker}. Regenerate with",
        "      scripts/ci/generate_probability_audit_surface.py --write",
        "    These declarations are elaborated by the all-module CI plan but were",
        "    absent from the release audit surface; the block is generated from the",
        "    declaration sites, so it cannot name a theorem that does not exist. -/",
    ] + ["#print axioms " + name for name in names]


def required_imports() -> list[str]:
    mods = [f"{dirn}/{stem}.lean" for _m, dirs, extras in SURFACES for dirn in dirs
            for stem in surface_modules(dirn)]
    mods += [rel for _m, _dirs, extras in SURFACES for rel in extras]
    return sorted(
        "import JurisLean." + rel[:-5].replace("/", ".")
        for rel in mods
    )


def build(current: str) -> tuple[str, int]:
    lines = current.splitlines()
    # The generated blocks always sit at the end of the file, so the previous render
    # is simply truncated away; that keeps the tool idempotent.
    cut = len(lines)
    for i, line in enumerate(lines):
        hits = [m for m, _d, _x in SURFACES if m in line]
        if hits:
            cut = i
            break
    head = lines[:cut]
    while head and not head[-1].strip():
        head.pop()

    have = set(head)
    imports = [i for i in required_imports() if i not in have]
    if imports:
        last = max(i for i, l in enumerate(head) if l.startswith("import "))
        head[last + 1:last + 1] = [""] + imports

    taken = audited_elsewhere()
    tail: list[str] = []
    total = 0
    for marker, _dirs, _extras in SURFACES:
        names = [n for n in collect(marker) if n not in taken]
        total += len(names)
        tail += render_block(names, marker)
    rendered = "\n".join(head + tail).rstrip("\n") + "\n"
    return re.sub(r"\n{3,}", "\n\n", rendered), total


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
