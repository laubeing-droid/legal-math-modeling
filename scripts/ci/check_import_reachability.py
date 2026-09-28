#!/usr/bin/env python3
"""Make Lean build-graph reachability a checked property, not an accident.

Audit P1-12 asked whether `lake build` covers what the paper counts. It did not:
`lakefile.lean` declares one library root, and 45 + 64 modules sat outside that
root's transitive imports — including `FullMath/Probability/` (the repository's
only real probability mathematics) and `BanachCertificate.lean` (the certificate
the NN mandate cites). Only the CI all-module plan happened to build them, so a
third party reproducing from the README would skip most of the corpus while
quoting the same theorem count.

This tool:

* generates `JurisLean/FullMath/All.lean`, importing every module in that tree;
* generates a marked import block at the end of `JurisLean.lean` for whatever is
  still unreachable, so the single library root reaches everything that is not
  deliberately a standalone entry point;
* fails by default if anything is unreachable, or if an allow-listed name no
  longer exists, so exceptions have to be argued for rather than forgotten.
"""

from __future__ import annotations

import argparse
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
LEAN_BASE = ROOT / "proofs" / "lean" / "juris_lean"
PKG = LEAN_BASE / "JurisLean"
ROOT_MODULE = PKG.parent / "JurisLean.lean"
AGGREGATOR = PKG / "FullMath" / "All.lean"

ROOT_BLOCK_BEGIN = "-- BEGIN GENERATED reachability block (check_import_reachability.py --write)"
ROOT_BLOCK_END = "-- END GENERATED reachability block"

IMPORT_RE = re.compile(r"^import\s+(\S+)", re.M)

# Entry points CI runs directly with `lake env lean`; they are roots themselves.
STANDALONE_DRIVERS: dict[str, str] = {
    "JurisLean.AxiomAudit": "release axiom audit",
    "JurisLean.ULMAxiomAudit": "ULM audit driver",
    "JurisLean.ULMAllTheoremsAxiomAudit": "ULM audit driver",
    "JurisLean.ULMCoreCompAxiomAudit": "ULM core-composition audit driver",
    "JurisLean.BusinessRelationsAudit": "business-relations audit driver",
    "JurisLean.BusinessRelationsDelta": "delta audit driver",
    "JurisLean.UnifiedV2.Audit": "UnifiedV2 audit driver",
    "JurisLean.BusinessRoot.RootAudit": "root-environment audit driver",
    "JurisLean.BusinessRoot.SevenAxisAudit": "seven-axis audit driver",
    "JurisLean.FullMath.CompletionAudit": "generated completion audit",
}

# Quarantine for modules whose own CI module build has not passed yet: AGENTS.md
# forbids a new module reaching the release root before then, so it is listed here
# with a live reason rather than being left unreachable without record.
#
# The mandate wave is empty as of this commit, and the reason it may now be emptied
# is on file: `lean-full-clean-build` built all fifteen in run 36293474352, and run
# 36297146468 rebuilt them together with the corrected axiom-audit surface (126 of
# their theorems are named there). The mechanism stays because the next wave needs
# it, not because this one is still pending.
# Both mandate arrivals booked here have joined the release root. `Mandate/ReLUApprox.lean`
# (R-07, a two-layer ReLU network with a computed stability bound) elaborated green in run
# 36344882459 at subject 1b6a8d6a9; `Mandate/MixedPennies.lean` (R-03, a fully proved
# mixed-strategy Nash equilibrium for one game) in run 36351623739 at subject 71d2177bc.
# AGENTS requires a passing CI module build before root entry, and both have one, so they
# are now imported by the generated block. The mechanism stays because the next wave needs it.
PENDING_CI_MODULES: dict[str, str] = {
    # `Mandate/ZeroSumSion.lean` was built by `lean-full-clean-build` under its own subject
    # (78f627f) and stays in the root. `Mandate/SequentialGames.lean` is booked here because
    # the entry it carried in the root was never earned: its header cited run 36386527448 at
    # subject `7a2a65e`, a commit that predates the file, and runs 36392435547 / 36394196611
    # reported four errors in it. It may rejoin the root only on a green build whose subject
    # actually contains the repaired source.
    "JurisLean.Mandate.SequentialGames": (
        "multi-player sequential carrier; its nine theorems are built and audited green at "
        "649d0fd, but the root entry is a separate change needing its own build"
    ),
    # Three carriers written after the audit's game-theory item stayed open. All four booked
    # modules are now built and axiom-audited green at subject 649d0fd (run 36409348921, landed
    # under docs/formal-release/ci-evidence/); what they do not yet have is a root entry, and
    # AGENTS requires the root closure to be attested by the build that contains it. Booking them
    # here is also what
    # keeps `--write` from importing them into the release root -- the generator makes any
    # unbooked source reachable, which is how a module could enter the root without anyone
    # deciding to promote it.
    "JurisLean.Mandate.ZeroSumValue": (
        "R-03 value step: the two iterated values of a finite zero-sum payoff coincide over the "
        "subtype-indexed simplex, which `isSaddlePointOn_value` cannot state for `ℝ`; the fifteen "
        "theorems are built and audited green at 649d0fd, root entry still its own round"
    ),
    "JurisLean.Mandate.PureNash": (
        "R-02b general games: a `Decidable` instance for pure-strategy Nash existence in a "
        "bimatrix game over `ℚ`, with two computed labels of opposite verdict; twenty-seven "
        "theorems built and audited green at 649d0fd, not yet in the root"
    ),
    "JurisLean.Mandate.OneShotDeviation": (
        "R-02b sequential games: backward induction compared with following a strategy profile, "
        "and one-step deviation optimality along the induced path; twenty-five theorems built and "
        "audited green at 649d0fd, not yet in the root"
    ),
}

# Same-pin external ports (elazarg/GameTheory @ 107085bc4 and
# elazarg/fixed-point-theorems-lean4 @ 42d4b401f; both MIT, both pinning this
# repository's exact mathlib revision). The port changed only import roots and a
# provenance header -- tests/spec/test_external_port_provenance.py re-derives the
# upstream bytes from each file and compares sha256. Every module under External/
# is quarantined until its own green CI build: the reachability generator makes
# any unbooked source reachable, so without this block the ports would enter the
# release root before anyone decided to promote them (the round-73 lesson).
_EXTERNAL_PORT_REASON = (
    "same-pin external port (JurisLean/External/PROVENANCE.md); awaiting its first "
    "CI build -- no attestation claimed, release-root entry is a separate round"
)


def _external_port_modules() -> dict[str, str]:
    external = PKG / "External"
    if not external.is_dir():
        return {}
    return {
        "JurisLean." + p.relative_to(PKG).as_posix()[:-5].replace("/", "."):
            _EXTERNAL_PORT_REASON
        for p in sorted(external.rglob("*.lean"))
    }


PENDING_CI_MODULES.update(_external_port_modules())

ALLOWED_UNREACHABLE = {**STANDALONE_DRIVERS, **PENDING_CI_MODULES}


def module_of(path: Path) -> str:
    return str(path.relative_to(LEAN_BASE)).replace("\\", "/")[:-5].replace("/", ".")


def modules() -> dict[str, Path]:
    mods = {module_of(p): p for p in sorted(PKG.rglob("*.lean"))}
    mods["JurisLean"] = ROOT_MODULE  # the closure's entry point
    return mods


def closure(root_module: str, mods: dict[str, Path]) -> set[str]:
    seen: set[str] = set()
    stack = [root_module]
    while stack:
        name = stack.pop()
        if name in seen or name not in mods:
            continue
        seen.add(name)
        text = mods[name].read_text(encoding="utf-8", errors="replace")
        for imp in IMPORT_RE.findall(text):
            if imp.startswith("JurisLean"):
                stack.append(imp)
    return seen


def fullmath_modules(mods: dict[str, Path]) -> list[str]:
    return sorted(m for m in mods if m.startswith("JurisLean.FullMath."))


def render_aggregator(mods: dict[str, Path]) -> str:
    leaves = [m for m in fullmath_modules(mods) if m != "JurisLean.FullMath.All"]
    # Imports must come first: a module doc comment before them is itself a command,
    # and the compiler then rejects the `import` lines (CI found exactly that here).
    lines = [f"import {m}" for m in leaves]
    lines += [
        "",
        "/-!",
        "# FullMath aggregator",
        "",
        "Generated by `scripts/ci/check_import_reachability.py --write`; regenerate rather",
        "than hand-edit. `lakefile.lean` declares a single library root, so without this",
        "aggregator `lake build` never elaborates the FullMath tree while the paper still",
        "counts its theorems (audit P1-12).",
        "-/",
    ]
    return "\n".join(lines) + "\n"


def render_root_block(names: list[str]) -> str:
    lines = [
        "",
        ROOT_BLOCK_BEGIN,
        "-- Whatever is not an explicit standalone driver must be reachable from this file,",
        "-- otherwise `lake build` skips it while counts and papers still include it.",
    ]
    lines += [f"import {n}" for n in names]
    lines.append(ROOT_BLOCK_END)
    return "\n".join(lines) + "\n"


def split_root_block(text: str) -> tuple[str, str]:
    if ROOT_BLOCK_BEGIN in text:
        before, rest = text.split(ROOT_BLOCK_BEGIN, 1)
        _old, after = rest.split(ROOT_BLOCK_END, 1)
        return before.rstrip("\n") + "\n", after.lstrip("\n")
    return text.rstrip("\n") + "\n", ""


def unreachable_from(mods: dict[str, Path]) -> list[str]:
    reached = closure("JurisLean", mods)
    return sorted(set(mods) - {"JurisLean"} - reached - set(ALLOWED_UNREACHABLE))


def stale_allowances(mods: dict[str, Path]) -> list[str]:
    return sorted(a for a in ALLOWED_UNREACHABLE if a not in mods)


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--write", action="store_true",
                    help="regenerate FullMath/All.lean and the root reachability block")
    args = ap.parse_args()

    mods = modules()
    if args.write:
        AGGREGATOR.write_text(render_aggregator(mods), encoding="utf-8", newline="\n")
        # Recompute coverage from the base root only. Counting the previously
        # generated block as coverage made a second --write conclude nothing was
        # missing and delete the very imports that made that true.
        before, after = split_root_block(ROOT_MODULE.read_text(encoding="utf-8"))
        ROOT_MODULE.write_text(before, encoding="utf-8", newline="\n")
        mods = modules()  # aggregator in, previous block out
        pending = unreachable_from(mods)
        text = before + (render_root_block(pending) if pending else "") + after
        ROOT_MODULE.write_text(text.rstrip("\n") + "\n", encoding="utf-8", newline="\n")
        print(f"wrote {AGGREGATOR.name} ({len(fullmath_modules(mods)) - 1} imports) "
              f"and a root block with {len(pending)} imports")
        return 0

    if not AGGREGATOR.exists():
        print(f"missing aggregator {AGGREGATOR.relative_to(ROOT)}; run --write", file=sys.stderr)
        return 1

    stale = stale_allowances(mods)
    if stale:
        print(f"allow-list names no longer exist (remove them): {stale}", file=sys.stderr)
        return 1

    pending = unreachable_from(mods)
    if pending:
        print(f"{len(pending)} Lean module(s) unreachable from the release root:", file=sys.stderr)
        for name in pending[:40]:
            print(f"  {name}", file=sys.stderr)
        return 1

    reached = closure("JurisLean", mods)
    print(f"reachability ok: {len(reached) - 1} of {len(mods) - 1} modules, "
          f"{len(ALLOWED_UNREACHABLE)} allowed standalone/pending drivers")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
