#!/usr/bin/env python3
"""Port the same-pin external Lean libraries into JurisLean/External/.

Why this exists: the 2026-09-28 owner directive closed the "build our own proof
islands" route for the three proof-level gaps. The general mixed-strategy Nash
existence, the sequential solution concepts, and their fixed-point infrastructure
must come from external literature carriers, aligned by byte with this
repository's pin (leanprover/lean4:v4.30.0, mathlib c5ea00351c28e24afc9f0f84379aa41082b1188f):

* https://github.com/elazarg/GameTheory            revision 107085bc4a0306672f2f35fce1abc1345d7975ed (MIT)
  -- GameTheory/Theorems/NashExistenceMixed.lean   (mixed_nash_exists)
  -- GameTheory/Theorems/OneShotDeviation.lean     (oneShotDeviation_iff_spe)
  -- GameTheory/Theorems/Kuhn.lean + Theorems/Kuhn/* (mixed/behavioral equivalence)
  -- GameTheory/Theorems/Minimax.lean              (von_neumann_minimax)
  -- plus the dependency cone those files import (Math.*, Semantics.*, Core.*, Concepts.*)
* https://github.com/elazarg/fixed-point-theorems-lean4 revision 42d4b401f7b6a6520e3bac3a76b8538d7f47ba3e (MIT)
  -- FixedPointTheorems/brouwer.lean, kakutani.lean and their cone.

Both revisions' lake-manifests pin exactly this repository's mathlib revision
(verified against proofs/lean/juris_lean/lake-manifest.json before writing).

The ONLY transformation applied to every file is:
  1. a provenance header block is prepended (strippable by its unique marker);
  2. `import` lines are rewritten from the upstream module roots to
     `JurisLean.External.*` roots.
Statements, proofs, namespaces and comments are otherwise untouched;
tests/spec/test_external_port_provenance.py re-derives the upstream bytes from
the committed files and compares hashes, so "we changed nothing else" is a
checked property, not a promise.

Usage (clone dirs must sit at exactly the expected revision):
    python scripts/port_external_same_pin.py \
        --gametheory <clone> --fixedpoint <clone> [--dry-run]
"""

from __future__ import annotations

import argparse
import hashlib
import json
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
PKG = ROOT / "proofs" / "lean" / "juris_lean" / "JurisLean"
DEST_ROOT = PKG / "External"

GAMETHEORY_REPO = "https://github.com/elazarg/GameTheory"
GAMETHEORY_REV = "107085bc4a0306672f2f35fce1abc1345d7975ed"
FPT_REPO = "https://github.com/elazarg/fixed-point-theorems-lean4"
FPT_REV = "42d4b401f7b6a6520e3bac3a76b8538d7f47ba3e"
EXPECTED_MATHLIB_REV = "c5ea00351c28e24afc9f0f84379aa41082b1188f"

HEADER_MARKER = "EXTERNAL-PORT-PROVENANCE-V1"

# Dependency cone of the four target files, computed from the upstream import
# graph at the pinned revisions (Mathlib/Lean/Batteries imports excluded).
GAMETHEORY_CONE = (
    "GameTheory/Concepts/ConstantSum.lean",
    "GameTheory/Concepts/Deviation.lean",
    "GameTheory/Concepts/Minimax.lean",
    "GameTheory/Concepts/MixedExtension.lean",
    "GameTheory/Concepts/ProductSimplexBrouwer.lean",
    "GameTheory/Concepts/SecurityStrategy.lean",
    "GameTheory/Concepts/SolutionConcepts.lean",
    "GameTheory/Concepts/ZeroSum.lean",
    "GameTheory/Concepts/ZeroSumNash.lean",
    "GameTheory/Core/GameForm.lean",
    "GameTheory/Core/GameProperties.lean",
    "GameTheory/Core/KernelGame.lean",
    "GameTheory/Languages/EFG/Refinements.lean",
    "GameTheory/Languages/EFG/Syntax.lean",
    "GameTheory/Theorems/Kuhn.lean",
    "GameTheory/Theorems/Kuhn/BehavioralToMixed.lean",
    "GameTheory/Theorems/Kuhn/BehavioralToMixedCore.lean",
    "GameTheory/Theorems/Kuhn/CorrelatedRealization.lean",
    "GameTheory/Theorems/Kuhn/KuhnModel.lean",
    "GameTheory/Theorems/Kuhn/MixedToBehavioralCore.lean",
    "GameTheory/Theorems/Kuhn/ObsModel.lean",
    "GameTheory/Theorems/Minimax.lean",
    "GameTheory/Theorems/NashExistenceMixed.lean",
    "GameTheory/Theorems/OneShotDeviation.lean",
    "Math/Coupling.lean",
    "Math/OptimizationLocalGlobal.lean",
    "Math/ParameterizedChain.lean",
    "Math/PMFProduct.lean",
    "Math/Probability.lean",
    "Math/ProbabilityMassFunction.lean",
    "Math/TraceRun.lean",
    "Semantics/DSMachine.lean",
    "Semantics/TransitionTrace.lean",
)

FPT_CONE = (
    "FixedPointTheorems.lean",
    "FixedPointTheorems/apply_cubical_sperner.lean",
    "FixedPointTheorems/brouwer.lean",
    "FixedPointTheorems/convex_homeos.lean",
    "FixedPointTheorems/cubical_sperner.lean",
    "FixedPointTheorems/cubical_sperner_prep.lean",
    "FixedPointTheorems/kakutani.lean",
)

# import-prefix rewrite, longest first so `GameTheory.` never shadows the
# `FixedPointTheorems.` rule and vice versa. Bare roots (no dot) are unused in
# this cone (checked), so only dotted forms are mapped.
REWRITES = (
    ("FixedPointTheorems.", "JurisLean.External.FixedPointTheorems."),
    ("GameTheory.", "JurisLean.External.GameTheory."),
    ("Math.", "JurisLean.External.GameTheory.Math."),
    ("Semantics.", "JurisLean.External.GameTheory.Semantics."),
)

# upstream package-relative path -> path under JurisLean/External/.
# The GameTheory package's own library files live under `GameTheory/` upstream;
# that prefix is dropped so a rewritten import `GameTheory.Core.KernelGame` ->
# `JurisLean.External.GameTheory.Core.KernelGame` resolves to the file placed at
# External/GameTheory/Core/KernelGame.lean (module == path, no double nesting).
def _gametheory_dest(rel: str) -> Path:
    parts = Path(rel).parts
    if parts[0] == "GameTheory":
        parts = parts[1:]
    return DEST_ROOT / "GameTheory" / Path(*parts)


DEST_FOR = {
    "gametheory": _gametheory_dest,
    "fixedpoint": lambda rel: DEST_ROOT / Path(rel),
}


def rewrite_imports(text: str) -> str:
    out = []
    for line in text.split("\n"):
        stripped = line.strip()
        if stripped.startswith("import "):
            for old, new in REWRITES:
                if stripped.startswith("import " + old):
                    line = "import " + new + stripped[len("import " + old):]
                    break
        out.append(line)
    return "\n".join(out)


def provenance_header(source: str, rel: str) -> str:
    if source == "gametheory":
        repo, rev, lic = GAMETHEORY_REPO, GAMETHEORY_REV, "MIT"
    else:
        repo, rev, lic = FPT_REPO, FPT_REV, "MIT"
    return "\n".join([
        "/-!",
        f"External port ({HEADER_MARKER}).",
        f"Upstream: {repo}",
        f"Revision: {rev}",
        f"Upstream file: {rel}",
        f"License: {lic} (see JurisLean/External/PROVENANCE.md for the notice).",
        "",
        "This copy differs from the revision above in exactly two ways: this",
        "header block, and `import` module paths rewritten to the",
        "`JurisLean.External.*` roots. Statements and proofs are unchanged;",
        "tests/spec/test_external_port_provenance.py re-derives the upstream",
        "bytes from this file and checks the recorded sha256.",
        "No build attestation is claimed here: the first compile of this port",
        "is booked in PENDING_CI_MODULES (scripts/ci/check_import_reachability.py)",
        "and only a green CI run of a commit containing this file can attest it.",
        "-/",
    ])


def git_show(clone: Path, rev: str, path: str) -> bytes:
    proc = subprocess.run(
        ["git", "show", f"{rev}:{path}"],
        cwd=clone, capture_output=True,
    )
    if proc.returncode != 0:
        raise SystemExit(f"git show {rev}:{path} failed in {clone}: {proc.stderr.decode(errors='replace')[:200]}")
    return proc.stdout


def require_revision(clone: Path, rev: str, label: str) -> None:
    head = subprocess.run(
        ["git", "rev-parse", "HEAD"], cwd=clone, capture_output=True, text=True
    ).stdout.strip()
    if head != rev:
        raise SystemExit(
            f"{label} clone is at {head[:9]}, expected {rev[:9]}; "
            "the port must be generated from the exact pinned bytes"
        )
    manifest = subprocess.run(
        ["git", "show", f"{rev}:lake-manifest.json"], cwd=clone, capture_output=True, text=True
    ).stdout
    if EXPECTED_MATHLIB_REV not in manifest:
        raise SystemExit(
            f"{label} at {rev[:9]} does not pin mathlib {EXPECTED_MATHLIB_REV[:9]}; refusing"
        )


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--gametheory", type=Path, required=True)
    ap.add_argument("--fixedpoint", type=Path, required=True)
    ap.add_argument("--dry-run", action="store_true")
    args = ap.parse_args()

    repo_manifest = (ROOT / "proofs/lean/juris_lean/lake-manifest.json").read_text(encoding="utf-8")
    if EXPECTED_MATHLIB_REV not in repo_manifest:
        raise SystemExit("repository mathlib pin moved; this port script is stale")

    require_revision(args.gametheory, GAMETHEORY_REV, "GameTheory")
    require_revision(args.fixedpoint, FPT_REV, "fixed-point-theorems-lean4")

    records = []
    for source, clone, rev, cone in (
        ("gametheory", args.gametheory, GAMETHEORY_REV, GAMETHEORY_CONE),
        ("fixedpoint", args.fixedpoint, FPT_REV, FPT_CONE),
    ):
        for rel in cone:
            original = git_show(clone, rev, rel).decode("utf-8")
            if original.startswith("\ufeff"):
                raise SystemExit(f"{rel}: unexpected BOM in upstream bytes")
            if not original.endswith("\n"):
                raise SystemExit(f"{rel}: upstream bytes do not end in a newline")
            rewritten = rewrite_imports(original)
            for line in rewritten.split("\n"):
                if line.strip().startswith("import JurisLean.External."):
                    continue
                if line.strip().startswith("import ") and not line.strip().startswith("import Mathlib") \
                        and not line.strip().startswith("import Lean") \
                        and not line.strip().startswith("import Batteries"):
                    raise SystemExit(f"{rel}: unmapped import line {line.strip()!r}")

            dest = DEST_FOR[source](rel)
            body = provenance_header(source, rel) + "\n" + rewritten
            # Byte-identity invariant: stripping the header (everything up to and
            # including the first line that is exactly '-/') must give back the
            # rewritten text exactly. A first version wrote `original` here and the
            # ports landed with un-rewritten imports; the provenance gate is what
            # must catch that, so the invariant is asserted at generation too.
            lines = body.split("\n")
            first = lines.index("-/")
            stripped = "\n".join(lines[first + 1:])
            if stripped != rewritten:
                raise SystemExit(f"{rel}: header strip is not exact; upstream may start with '-/'")
            if rewritten == original and any(
                l.strip().startswith("import ") for l in original.split("\n")
                if not l.strip().startswith(("import Mathlib", "import Lean", "import Batteries"))
            ):
                # A file with cone-internal imports that the rewrite did not touch
                # means the rewrite map is incomplete for this file.
                raise SystemExit(f"{rel}: rewrite left cone-internal imports untouched")
            module = "JurisLean." + str(dest.relative_to(PKG))[:-5].replace("\\", ".")
            records.append({
                "source": source,
                "upstream_path": rel,
                "upstream_sha256": hashlib.sha256(original.encode("utf-8")).hexdigest(),
                "repo_path": str(dest.relative_to(ROOT)).replace("\\", "/"),
                "module": module,
            })
            if not args.dry_run:
                dest.parent.mkdir(parents=True, exist_ok=True)
                dest.write_bytes(body.encode("utf-8"))
            print(f"ported {rel} -> {dest.relative_to(ROOT)}")

    # Structural cross-check: every rewritten External import must resolve to a
    # file this run places (module name == file path under the package). This is
    # what catches a rewrite-table/destination-table disagreement; the per-file
    # byte check above cannot see it.
    placed = {str(r["repo_path"]) for r in records}
    problems = []
    for rec in records:
        original = git_show(
            args.gametheory if rec["source"] == "gametheory" else args.fixedpoint,
            GAMETHEORY_REV if rec["source"] == "gametheory" else FPT_REV,
            rec["upstream_path"],
        ).decode("utf-8")
        for line in rewrite_imports(original).split("\n"):
            stripped = line.strip()
            if not stripped.startswith("import JurisLean.External."):
                continue
            module = stripped[len("import "):]
            rel_path = (
                "proofs/lean/juris_lean/" + module.replace(".", "/") + ".lean"
            )
            if rel_path not in placed:
                problems.append(f"{rec['upstream_path']}: {stripped} -> {rel_path} is not placed")
    if problems:
        for p in problems:
            print(p, file=sys.stderr)
        raise SystemExit(f"{len(problems)} rewritten imports do not resolve; see above")

    doc = {
        "schema_version": "external-port-provenance-v1",
        "header_marker": HEADER_MARKER,
        "method_note": (
            "Each listed file was produced by prepending the provenance header and "
            "rewriting import module roots (GameTheory./Math./Semantics./FixedPointTheorems. "
            "-> JurisLean.External.*) and nothing else; the gate test re-derives the "
            "upstream bytes by reversing exactly that and compares sha256."
        ),
        "sources": {
            "gametheory": {
                "repository": GAMETHEORY_REPO,
                "revision": GAMETHEORY_REV,
                "license": "MIT",
                "license_note": (
                    "LICENSE at the pinned revision: 'MIT License, Copyright (c) 2025 "
                    "Elazar Gershuni'; per-file headers carry the same notice."
                ),
            },
            "fixedpoint": {
                "repository": FPT_REPO,
                "revision": FPT_REV,
                "license": "MIT",
                "license_note": (
                    "No LICENSE file exists in the tree at this revision; the repository "
                    "reports MIT (same as upstream harfe/fixed-point-theorems-lean4), and "
                    "the LICENSE file entered a later commit (9571dd7)."
                ),
            },
        },
        "mathlib_pin_checked": EXPECTED_MATHLIB_REV,
        "files": records,
    }
    out = DEST_ROOT / "PROVENANCE.json"
    if not args.dry_run:
        out.write_text(
            json.dumps(doc, ensure_ascii=False, indent=2, sort_keys=True) + "\n",
            encoding="utf-8", newline="\n",
        )
        print(f"wrote {out.relative_to(ROOT)} ({len(records)} files)")
    else:
        print(f"dry run: would write {len(records)} files + {out.relative_to(ROOT)}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
