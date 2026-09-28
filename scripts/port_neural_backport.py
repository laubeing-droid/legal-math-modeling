#!/usr/bin/env python3
"""Backport the Leshno universal-approximation cone from mathlib v4.32.0-rc1 to v4.30.0.

Owner decision (2026-09-28, late): gap three (the ReLU universal-approximation
family conclusion) is routed through a CROSS-PIN BACKPORT of
https://github.com/davorrunje/neural-network-proofs (Apache-2.0, revision
f90942517be8b66dd34574212ada69b2130a48e5). That repository was born on mathlib
v4.32.0-rc1, so unlike the GameTheory / fixed-point ports there is NO same-pin
upstream revision: the 17 files land byte-identical first, and any mathlib API
drift (v4.32.0-rc1 -> v4.30.0) is then repaired edit by edit, with every edit
logged per file in PROVENANCE.json (`adaptations`). Byte-faithfulness is
therefore NOT an invariant here; the gate checks instead that the provenance
record's `adapted` flag matches the reconstruct-and-compare reality and that
every drifted file carries a non-empty adaptation log.

Target headline: `UniversalApproximation.Leshno.leshno_dense_iff` -- an M-class
activation densely approximates iff it is not a.e. a polynomial (Leshno, Lin,
Pinkus, Schocken 1993). The instantiation to ReLU (ReLU is in class M and is
not a.e. a polynomial) is deliberately NOT part of this port: it will be a
separate repository module citing the carrier, once the carrier compiles.

All 29 Mathlib imports used by the cone exist at identical paths in this
repository's pinned mathlib (c5ea00351c28e24afc9f0f84379aa41082b1188f),
checked file-by-file before writing; declaration-level drift only shows up at
elaboration and is what the adaptation log is for.

Usage:
    python scripts/port_neural_backport.py --repo <clone> [--dry-run]
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
PKG = ROOT / "proofs" / "lean" / "juris_lean" / "JurisLean"
DEST_ROOT = PKG / "External" / "NeuralNetworkProofs"

NNP_REPO = "https://github.com/davorrunje/neural-network-proofs"
NNP_REV = "f90942517be8b66dd34574212ada69b2130a48e5"
HEADER_MARKER = "NEURAL-BACKPORT-PROVENANCE-V1"

# Dependency cone of UniversalApproximation/Leshno.lean at the pinned revision
# (Mathlib/Lean/Batteries imports excluded), computed from the import graph.
CONE = (
    "ForMathlib/ConvolutionDegreeBound.lean",
    "ForMathlib/ConvolutionIteratedDeriv.lean",
    "ForMathlib/ConvolutionPolynomial.lean",
    "ForMathlib/IteratedDerivPolynomial.lean",
    "ForMathlib/PolynomialDistribution.lean",
    "ForMathlib/RidgePowersSpan.lean",
    "ForMathlib/SmoothCompactAntideriv.lean",
    "ForMathlib/UniformRiemannConvolution.lean",
    "UniversalApproximation/Leshno.lean",
    "UniversalApproximation/Leshno/ClassM.lean",
    "UniversalApproximation/Leshno/Converse.lean",
    "UniversalApproximation/Leshno/Family.lean",
    "UniversalApproximation/Leshno/Mollify.lean",
    "UniversalApproximation/Leshno/MollifyDef.lean",
    "UniversalApproximation/Leshno/Ridge.lean",
    "UniversalApproximation/Leshno/SmoothEngine.lean",
    "UniversalApproximation/Leshno/Theorem.lean",
)

REWRITES = (
    ("NeuralNetworkProofs.", "JurisLean.External.NeuralNetworkProofs."),
)


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


def provenance_header(rel: str) -> str:
    # Plain `/-` comment, NOT `/-!`: doc comments parse as commands and would push
    # the imports off the file head ("must be used in the beginning of the file")
    # -- the failure mode run 36445176605 caught in the same-pin port.
    return "\n".join([
        "/-",
        f"External backport ({HEADER_MARKER}).",
        f"Upstream: {NNP_REPO}",
        f"Revision: {NNP_REV}",
        f"Upstream file: NeuralNetworkProofs/{rel}",
        "License: Apache-2.0 (see JurisLean/External/NeuralNetworkProofs/PROVENANCE.md",
        "and the LICENSE copy beside it).",
        "",
        "This copy starts byte-identical to the revision above except for this header",
        "and the `import` roots rewritten to JurisLean.External.NeuralNetworkProofs.*.",
        "Unlike the same-pin ports, the upstream pin (mathlib v4.32.0-rc1) differs from",
        "this repository's (v4.30.0): mathlib API drift is repaired here edit by edit,",
        "and every edit is logged per file in PROVENANCE.json (`adaptations`).",
        "No build attestation is claimed: first compile pending in PENDING_CI_MODULES",
        "(scripts/ci/check_import_reachability.py); only a green CI run of a commit",
        "containing this file can attest it.",
        "-/",
    ])


def git_show(clone: Path, path: str) -> bytes:
    proc = subprocess.run(
        ["git", "show", f"{NNP_REV}:NeuralNetworkProofs/{path}"],
        cwd=clone, capture_output=True,
    )
    if proc.returncode != 0:
        raise SystemExit(
            f"git show {NNP_REV[:9]}:NeuralNetworkProofs/{path} failed: "
            f"{proc.stderr.decode(errors='replace')[:200]}"
        )
    return proc.stdout


def require_revision(clone: Path) -> None:
    head = subprocess.run(
        ["git", "rev-parse", "HEAD"], cwd=clone, capture_output=True, text=True
    ).stdout.strip()
    if head != NNP_REV:
        raise SystemExit(
            f"neural-network-proofs clone is at {head[:9]}, expected {NNP_REV[:9]}"
        )


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--repo", type=Path, required=True)
    ap.add_argument("--dry-run", action="store_true")
    args = ap.parse_args()

    require_revision(args.repo)

    records = []
    placed = set()
    for rel in CONE:
        original = git_show(args.repo, rel).decode("utf-8")
        if not original.endswith("\n"):
            raise SystemExit(f"{rel}: upstream bytes do not end in a newline")
        rewritten = rewrite_imports(original)
        for line in rewritten.split("\n"):
            stripped = line.strip()
            if stripped.startswith("import ") and not stripped.startswith(
                ("import Mathlib", "import Lean", "import Batteries",
                 "import JurisLean.External.")
            ):
                raise SystemExit(f"{rel}: unmapped import line {stripped!r}")

        dest = DEST_ROOT / Path(rel)
        body = provenance_header(rel) + "\n" + rewritten
        lines = body.split("\n")
        first = lines.index("-/")
        if "\n".join(lines[first + 1:]) != rewritten:
            raise SystemExit(f"{rel}: header strip is not exact")
        repo_path = str(dest.relative_to(ROOT)).replace("\\", "/")
        placed.add(repo_path)
        records.append({
            "upstream_path": f"NeuralNetworkProofs/{rel}",
            "upstream_sha256": hashlib.sha256(original.encode("utf-8")).hexdigest(),
            # Pinned so the statement-intactness gate works without the clone:
            # tests compare the tree's declaration headers against these lines
            # (blind-audit finding P1-6 -- "statements unchanged" must be a
            # checked property, not prose).
            "upstream_header_lines": sorted(
                " ".join(l.split())
                for l in original.split("\n")
                if re.match(r"^\s*(private\s+|protected\s+)*(theorem|lemma)\s", l)
            ),
            "repo_path": repo_path,
            "module": "JurisLean." + str(dest.relative_to(PKG))[:-5].replace("\\", "."),
            # filled in below from the reconstruction comparison
            "adapted": False,
            "adaptations": [],
        })
        if not args.dry_run:
            dest.parent.mkdir(parents=True, exist_ok=True)
            dest.write_bytes(body.encode("utf-8"))
        print(f"backported {rel} -> {repo_path}")

    # Structural cross-check: every rewritten import resolves to a placed file.
    problems = []
    for rel in CONE:
        original = git_show(args.repo, rel).decode("utf-8")
        for line in rewrite_imports(original).split("\n"):
            stripped = line.strip()
            if stripped.startswith("import JurisLean.External.NeuralNetworkProofs."):
                module = stripped[len("import "):]
                rel_path = "proofs/lean/juris_lean/" + module.replace(".", "/") + ".lean"
                if rel_path not in placed:
                    problems.append(f"{rel}: {stripped} -> {rel_path} is not placed")
    if problems:
        for p in problems:
            print(p, file=sys.stderr)
        raise SystemExit(f"{len(problems)} rewritten imports do not resolve")

    doc = {
        "schema_version": "neural-backport-provenance-v1",
        "header_marker": HEADER_MARKER,
        "method_note": (
            "Cross-pin backport (mathlib v4.32.0-rc1 -> v4.30.0). Files land "
            "byte-identical modulo the header and import roots; drift repairs are "
            "expected, and each is appended to that file's `adaptations` list with a "
            "one-line reason. `adapted` must equal whether strip+reverse still "
            "reproduces the recorded upstream sha256 (the gate checks this), so the "
            "record can never silently drift from the file."
        ),
        "sources": {
            "neuralnetworkproofs": {
                "repository": NNP_REPO,
                "revision": NNP_REV,
                "license": "Apache-2.0",
                "license_note": (
                    "Upstream LICENSE (Apache-2.0) is copied beside this record; each "
                    "upstream file header carries the same notice."
                ),
            },
        },
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
