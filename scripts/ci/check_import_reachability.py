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
    # Seventh-round seam wave (2026-09-30). Each entry is booked here until its own
    # CI module build passes; AGENTS forbids root entry before that.
    "JurisLean.Seams.Representation": (
        "S0 seam: representation layer, joint model + P-002 scope "
        "(wave 7, local build green at 617 jobs)"),
    "JurisLean.Seams.AdjudicationBridge": (
        "S2 seam: adjudication bridge, P-051 free-evaluation boundary "
        "(wave 7, still under construction -- snapshot, not yet built)"),
    "JurisLean.Seams.InstitutionalEffects": (
        "S5 seam: ledger+projection refinement and the non-adjudicative "
        "performance channel (wave 7, CI module build green in run 36756834804 "
        "at subject f0398f3; awaiting root entry with the batched rebind)"),
    "JurisLean.Seams.SourceNorms": (
        "S1 seam: Horn closure <-> semantic consequence, and the general "
        "finite acyclic priority maximal element (wave 7, snapshot -- "
        "under construction, no build verdict yet)"),
    "JurisLean.Seams.PrecedentFlow": (
        "S7 seam: precedent-driven version update, non-convergence of backflow, "
        "and the four-place competence gate for P-066 (wave 7, snapshot -- "
        "under construction, no build verdict yet)"),
    "JurisLean.Seams.Probability": (
        "S3 seam: likelihood->posterior segments, the finite-distribution/PMF "
        "bridge for P-114 and the allowed-reduction relation for P-098 "
        "(wave 7, snapshot -- under construction, no build verdict yet)"),
    "JurisLean.Seams.PayoffEquilibrium": (
        "S4 seam: declared legal->payoff valuation and the 2*eta deviation "
        "transport (wave 7, snapshot -- under construction, no build verdict yet)"),
    "JurisLean.Seams.Temporal": (
        "XT seam: non-anticipation of a truncated view, interval preservation, "
        "the quantified form of P-049 and late-insertion reordering "
        "(wave 7, local build green; awaiting its own CI module build)"),
    #
    # `JurisLean.Seams.ClaimBasis` (P-034 claim-basis chain, seam 1) left this table on
    # 2026-10-01: after the name-free Step inversion fixed its local build, run
    # 36749410410 (`mode=changed-module`, subject 6a30194d) built it green in 514 ms on
    # the pinned toolchain with the official Mathlib cloud cache. Its axiom-audit naming
    # is still outstanding and is tracked as boundary-seam task C2, exactly like the
    # nine ⑤⑥ theorems that were already in the root without it.
    #
    # The four game-theory carriers (SequentialGames, ZeroSumValue, PureNash,
    # OneShotDeviation) left this table in the first promotion round: all four were
    # built and axiom-audited green at subject 649d0fd (run 36409348921, landed under
    # docs/formal-release/ci-evidence/), and their root entry was then attested by the
    # build that contains it.
    #
    # ReLUFamily left in the third promotion round (ledger round 92): its thirteen
    # theorems were built and axiom-audited green by run 36468808532 (subject 3f44b8e)
    # and its root entry is attested by the build that contains it. The table stays
    # empty and alive: any new module that has not earned a build lands here first.
}

# Same-pin external ports (elazarg/GameTheory @ 107085bc4 and
# elazarg/fixed-point-theorems-lean4 @ 42d4b401f; both MIT, both pinning this
# repository's exact mathlib revision) plus the cross-pin neural backport
# (davorrunje/neural-network-proofs @ f909425, Apache-2.0). The same-pin port
# changed only import roots and a provenance header --
# tests/spec/test_external_port_provenance.py re-derives the upstream bytes
# from each file and compares sha256; the backport logs its drift repairs
# (tests/spec/test_neural_backport_provenance.py). Every module under External/
# is auto-quarantined: the reachability generator makes any unbooked source
# reachable, so without this block the ports would enter the release root
# before anyone decided to promote them (the round-73 lesson).
#
# All 57 landed modules are built and axiom-audited green by run 36456965606
# (subject c5830ed, the round-82 full-green attestation). They stay out of the
# release root until a promotion round decides otherwise: add a module's name
# to _EXTERNAL_ROOT_PROMOTED when (and only when) a green build of a commit
# that imports it into the root exists -- that set is the promotion path this
# table otherwise lacked (blind-audit finding P1-5).
# The reason stamped on a quarantined external module. Deliberately
# status-free: a future arrival has NOT been built by any past run, so the
# string must not cite one (the round-96 review caught the old wording, which
# hard-coded subject c5830ed and was false the moment a new file landed).
_EXTERNAL_PORT_REASON = (
    "external port (see JurisLean/External/PROVENANCE.md and "
    "External/NeuralNetworkProofs/PROVENANCE.md); awaiting its own CI build; "
    "release-root entry only via _EXTERNAL_ROOT_PROMOTED after a green build "
    "that contains it"
)

# Modules deliberately imported into the release root, each with the green
# build that contains its entry. Filled by the three promotion rounds (ledger
# rounds 88/90/92); empty again only by an explicit demotion decision.
# Batch two of the promotion rounds (ledger round 90): the 40 same-pin external
# ports (elazarg/GameTheory + elazarg/fixed-point-theorems-lean4) join the root.
# Their theorems were built and axiom-audited green by run 36456965606 (subject
# c5830ed, evidence landed under ci-evidence/); the root entry itself is attested
# by the build this change triggers. The 17 cross-pin neural modules stay out
# (batch three, together with ReLUFamily).
_EXTERNAL_ROOT_PROMOTED: set[str] = {
    "JurisLean.External.FixedPointTheorems",
    "JurisLean.External.FixedPointTheorems.apply_cubical_sperner",
    "JurisLean.External.FixedPointTheorems.brouwer",
    "JurisLean.External.FixedPointTheorems.convex_homeos",
    "JurisLean.External.FixedPointTheorems.cubical_sperner",
    "JurisLean.External.FixedPointTheorems.cubical_sperner_prep",
    "JurisLean.External.FixedPointTheorems.kakutani",
    "JurisLean.External.GameTheory.Concepts.ConstantSum",
    "JurisLean.External.GameTheory.Concepts.Deviation",
    "JurisLean.External.GameTheory.Concepts.Minimax",
    "JurisLean.External.GameTheory.Concepts.MixedExtension",
    "JurisLean.External.GameTheory.Concepts.ProductSimplexBrouwer",
    "JurisLean.External.GameTheory.Concepts.SecurityStrategy",
    "JurisLean.External.GameTheory.Concepts.SolutionConcepts",
    "JurisLean.External.GameTheory.Concepts.ZeroSum",
    "JurisLean.External.GameTheory.Concepts.ZeroSumNash",
    "JurisLean.External.GameTheory.Core.GameForm",
    "JurisLean.External.GameTheory.Core.GameProperties",
    "JurisLean.External.GameTheory.Core.KernelGame",
    "JurisLean.External.GameTheory.Languages.EFG.Refinements",
    "JurisLean.External.GameTheory.Languages.EFG.Syntax",
    "JurisLean.External.GameTheory.Math.Coupling",
    "JurisLean.External.GameTheory.Math.OptimizationLocalGlobal",
    "JurisLean.External.GameTheory.Math.PMFProduct",
    "JurisLean.External.GameTheory.Math.ParameterizedChain",
    "JurisLean.External.GameTheory.Math.Probability",
    "JurisLean.External.GameTheory.Math.ProbabilityMassFunction",
    "JurisLean.External.GameTheory.Math.TraceRun",
    "JurisLean.External.GameTheory.Semantics.DSMachine",
    "JurisLean.External.GameTheory.Semantics.TransitionTrace",
    "JurisLean.External.GameTheory.Theorems.Kuhn",
    "JurisLean.External.GameTheory.Theorems.Kuhn.BehavioralToMixed",
    "JurisLean.External.GameTheory.Theorems.Kuhn.BehavioralToMixedCore",
    "JurisLean.External.GameTheory.Theorems.Kuhn.CorrelatedRealization",
    "JurisLean.External.GameTheory.Theorems.Kuhn.KuhnModel",
    "JurisLean.External.GameTheory.Theorems.Kuhn.MixedToBehavioralCore",
    "JurisLean.External.GameTheory.Theorems.Kuhn.ObsModel",
    "JurisLean.External.GameTheory.Theorems.Minimax",
    "JurisLean.External.GameTheory.Theorems.NashExistenceMixed",
    "JurisLean.External.GameTheory.Theorems.OneShotDeviation",
    # Batch three (ledger round 92): the 17 cross-pin neural modules join; their
    # theorem bodies were adjudicated by run 36456965606 and the ReLU instantiation
    # by run 36468808532; the root entry is attested by the build this change triggers.
    "JurisLean.External.NeuralNetworkProofs.ForMathlib.ConvolutionDegreeBound",
    "JurisLean.External.NeuralNetworkProofs.ForMathlib.ConvolutionIteratedDeriv",
    "JurisLean.External.NeuralNetworkProofs.ForMathlib.ConvolutionPolynomial",
    "JurisLean.External.NeuralNetworkProofs.ForMathlib.IteratedDerivPolynomial",
    "JurisLean.External.NeuralNetworkProofs.ForMathlib.PolynomialDistribution",
    "JurisLean.External.NeuralNetworkProofs.ForMathlib.RidgePowersSpan",
    "JurisLean.External.NeuralNetworkProofs.ForMathlib.SmoothCompactAntideriv",
    "JurisLean.External.NeuralNetworkProofs.ForMathlib.UniformRiemannConvolution",
    "JurisLean.External.NeuralNetworkProofs.UniversalApproximation.Leshno",
    "JurisLean.External.NeuralNetworkProofs.UniversalApproximation.Leshno.ClassM",
    "JurisLean.External.NeuralNetworkProofs.UniversalApproximation.Leshno.Converse",
    "JurisLean.External.NeuralNetworkProofs.UniversalApproximation.Leshno.Family",
    "JurisLean.External.NeuralNetworkProofs.UniversalApproximation.Leshno.Mollify",
    "JurisLean.External.NeuralNetworkProofs.UniversalApproximation.Leshno.MollifyDef",
    "JurisLean.External.NeuralNetworkProofs.UniversalApproximation.Leshno.Ridge",
    "JurisLean.External.NeuralNetworkProofs.UniversalApproximation.Leshno.SmoothEngine",
    "JurisLean.External.NeuralNetworkProofs.UniversalApproximation.Leshno.Theorem",
}


def _external_port_modules() -> dict[str, str]:
    external = PKG / "External"
    if not external.is_dir():
        return {}
    out = {}
    for p in sorted(external.rglob("*.lean")):
        name = "JurisLean." + p.relative_to(PKG).as_posix()[:-5].replace("/", ".")
        if name in _EXTERNAL_ROOT_PROMOTED:
            continue
        out[name] = _EXTERNAL_PORT_REASON
    return out


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
    # A promoted name that matches no file on disk is a typo or a stale promotion,
    # and the damage is silent: the real module falls back into auto-quarantine,
    # --write drops it from the release root, and every later check stays green.
    # The quarantine table is already validated this way (stale_allowances); the
    # promotion table needs the same gate.
    ghost_promotions = sorted(_EXTERNAL_ROOT_PROMOTED - set(mods))
    if ghost_promotions:
        print(f"_EXTERNAL_ROOT_PROMOTED names match no module on disk: {ghost_promotions}",
              file=sys.stderr)
        return 1

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

    # Quarantine bypass alarm (blind-audit finding P1-5): a module booked in
    # PENDING_CI_MODULES must not actually be reachable from the release root.
    # Without this, a hand-added `import JurisLean.External.*` in any
    # root-reachable file would quietly promote the import while its table
    # entry still claimed quarantine -- the check only ever failed for
    # unaccounted-unreachable, never for allowed-but-reached. Standalone
    # drivers may legitimately be imported by other files, so they are exempt.
    reached = closure("JurisLean", mods)
    bypassed = sorted(set(PENDING_CI_MODULES) & reached)
    if bypassed:
        print("quarantined module(s) reached from the release root "
              "(promote them properly or remove the import):", file=sys.stderr)
        for name in bypassed[:40]:
            print(f"  {name}", file=sys.stderr)
        return 1

    print(f"reachability ok: {len(reached) - 1} of {len(mods) - 1} modules, "
          f"{len(ALLOWED_UNREACHABLE)} allowed standalone/pending drivers")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
