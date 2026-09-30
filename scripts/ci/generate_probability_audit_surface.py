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
EXTERNAL_MARKER = "Generated external-port audit surface"
SEAMS_MARKER = "Generated seam-wave audit surface"
BOUNDARY_MARKER = "Generated boundary-carrier audit surface"

# A seam file stays out of the audit surface until it has a build verdict of its own, because
# naming its theorems is what gives a later full-release round something to read; naming them
# from a red module would make the whole `AxiomAudit.lean` round fail for a reason that has
# nothing to do with the axioms. `Seams/Probability.lean` left this holdout on 2026-10-01 after
# run 36770138720 (subject c03663cb) built it green; `Seams/Unified.lean` (T2) left it the same
# way once its own run returned.

# (marker, directories, extra single files) -- each surface is one generated block.
SURFACES = (
    (PROB_MARKER, ("FullMath/Probability",), ("BusinessRoot/Analytics.lean",)),
    (MANDATE_MARKER, ("Mandate",), ()),
    # The seventh-round seam wave (JurisLean/Seams/) reaches the audit surface the same
    # way the mandate and external carriers did: a module first earns its own CI module
    # build, then its declarations get named here so a later full-release round reads
    # their axiom dependencies. Before this entry, a seam could be imported by the
    # release root while none of its theorems had ever been printed by `#print axioms`,
    # which is the "CI uploads the output but nobody reads it" defect the boundary
    # binding table records for the ⑤⑥ carriers.
    (SEAMS_MARKER, ("Seams",), ()),
    # The ⑤ out-of-trunk and ⑥ carriers. These eight theorems are the ones
    # `docs/master-plan/06_六类边界绑定表.md` claims are "具名入 AxiomAudit.lean", and they used
    # to live there as 40 hand-written lines -- which `build()` silently destroyed: it truncates
    # everything from the first marker line to EOF so the previous render can be rewritten, and
    # the hand-written block sat after that marker. They vanished at 52361a7 and every audit
    # round since (1853, 1949 targets) read the surface WITHOUT them, while the ledger kept
    # asserting they were named. Naming them from source is the only fix that cannot be lost a
    # second time: the renderer regenerates this block on every --write.
    (BOUNDARY_MARKER, (), ("ReceiptAuthority.lean", "AuthorityLattice.lean",
                           "TaintNoninterference.lean")),
    # The same-pin external ports (JurisLean/External/PROVENANCE.md) are quarantined
    # out of the release root until their own green build, and naming them here is
    # what gives that first build an axiom-audit verdict to return -- the same
    # upgrade order the mandate carriers took (build -> audit surface -> root).
    # These directories are recursive: the ports keep the upstream tree shape.
    # The neural-network backport (External/NeuralNetworkProofs/) is the cross-pin
    # exception -- mathlib drift repairs are expected there, so its files will not
    # stay byte-faithful -- but the audit order is the same.
    (EXTERNAL_MARKER, ("External/FixedPointTheorems", "External/GameTheory",
                       "External/NeuralNetworkProofs"), ()),
)

# Package-relative file -> why it is held off the surface. AxiomAudit.lean imports every
# module it names, so naming a seam that does not compile (or is not even committed) turns
# the audit driver itself red and burns a full-release run. Drop an entry as soon as that
# module has a build verdict of its own.
SURFACE_HOLDOUTS: dict[str, str] = {}
# Empty as of 2026-10-01: `Seams/FullProcess.lean` (S6) left after run 36772310980
# (subject 01ce4fff) built it green in 3.4 s over 2947 jobs, matching the main session's
# serial-window job count exactly. The mechanism stays -- a red or uncommitted seam must be
# held out of BOTH channels, names and imports -- because an `import` elaborates the module
# and turns `AxiomAudit.lean`, and with it the whole full-release round, red for a reason
# that has nothing to do with axioms.
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
    """Lean files under one surface directory, as package-relative paths.

    Recursive since the external-port surface arrived: the port mirrors the
    upstream tree (Concepts/, Core/, Theorems/Kuhn/, ...), while the two original
    surfaces are flat, where rglob degenerates to the old glob.
    """
    return sorted(
        p.relative_to(PKG).as_posix()
        for p in (PKG / directory).rglob("*.lean")
    )


def collect(marker: str) -> list[str]:
    directory, extras = next((d, x) for m, d, x in SURFACES if m == marker)
    names: list[str] = []
    for dirn in directory:
        for rel in surface_modules(dirn):
            if rel in SURFACE_HOLDOUTS:
                continue
            names += names_in(rel)
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
    mods = [rel for _m, dirs, extras in SURFACES for dirn in dirs for rel in surface_modules(dirn)]
    mods += [rel for _m, _dirs, extras in SURFACES for rel in extras]
    # Holdouts are filtered here as well as in `collect`. Naming is not the only way the audit
    # driver can go red on a broken seam: an `import` has to elaborate the module, so importing
    # a file that does not compile fails `AxiomAudit.lean` itself. The first version of this
    # table only skipped the names, and the generator kept re-adding `import
    # JurisLean.Seams.FullProcess` after it was deleted by hand -- which would have burned the
    # next full-release round on S6's unrelated proof errors.
    return sorted(
        "import JurisLean." + rel[:-5].replace("/", ".")
        for rel in mods
        if rel not in SURFACE_HOLDOUTS
    )


def held_out_imports() -> set[str]:
    """Import lines that name a held-out module, in package-relative form."""
    return {
        "import JurisLean." + rel[:-5].replace("/", ".")
        for rel in SURFACE_HOLDOUTS
    }


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

    # An import left by an earlier render must not outlive the holdout that removed its
    # names: prune it here, or re-adding a holdout would still leave the driver red.
    drop = held_out_imports()
    head = [line for line in head if line.strip() not in drop]

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
