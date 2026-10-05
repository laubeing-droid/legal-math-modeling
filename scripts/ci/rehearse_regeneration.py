#!/usr/bin/env python3
"""Rehearse the documented regeneration path in a throwaway clone.

The README tells a maintainer to regenerate the accounts and re-run pytest. Whether
that reproduces exactly what is committed is a claim, and it had never been checked:
in place on Windows the sequence dirties files by line endings alone, and in a fresh
clone the subject-bound manifest rebinds to the checked-out commit. This runs the
documented sequence in a clean clone of HEAD and reports the difference.

One drift is allowed and expected: `theorem_inventory_v3.json` records the subject
commit, tree and digest, so regenerating it at a newer commit must change those three
fields and nothing else. Anything beyond that means the committed accounts are not
what the sources imply.

    python scripts/ci/rehearse_regeneration.py
    python scripts/ci/rehearse_regeneration.py --with-tests   # also run pytest there
"""

from __future__ import annotations

import argparse
import json
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]

# The documented sequence, in the order README.md gives it.
SEQUENCE = (
    ("python", "scripts/ci/generate_t_coverage_ledger.py"),
    ("python", "scripts/ci/generate_probability_audit_surface.py", "--write"),
    ("python", "scripts/ci/check_import_reachability.py", "--write"),
    ("python", "scripts/ci/generate_structure_and_volume_reports.py"),
    ("python", "scripts/ci/generate_theorem_manifest.py"),
    ("python", "scripts/ci/generate_trivial_proof_census.py"),
    # Round-2 F7: the ten-gap closure status is a generated account like the others;
    # outside the sequence its --check could stay green over a stale claim.
    ("python", "scripts/ci/generate_gap_status.py", "--write"),
    # Both were missing from the sequence until a round added three mandate modules and the
    # committed duplication census went stale by 225 - 222 files without anything complaining
    # about the rehearsal. `build_statement_duplication_census.py` writes only with `--write`,
    # so an in-place run without the flag silently leaves the account behind the tree.
    ("python", "scripts/ci/generate_declaration_shape_report.py"),
    ("python", "scripts/ci/build_statement_duplication_census.py", "--write"),
)

MANIFEST = "docs/formal-release/theorem_inventory_v3.json"
MANIFEST_SUBJECT_FIELDS = ("source_inventory_digest", "subject")


def _json(path: Path):
    return json.loads(path.read_text(encoding="utf-8"))


def _strip_subject(doc: dict) -> dict:
    return {k: v for k, v in doc.items() if k not in MANIFEST_SUBJECT_FIELDS}


def porcelain(clone: Path) -> list[str]:
    out = subprocess.run(
        ["git", "status", "--porcelain"], cwd=clone,
        capture_output=True, text=True, encoding="utf-8", errors="replace", check=True,
    ).stdout
    return [line[3:] for line in out.splitlines() if line.strip()]


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--with-tests", action="store_true", help="also run the pytest suite in the clone")
    ap.add_argument("--keep", action="store_true", help="print the clone path instead of deleting it")
    args = ap.parse_args()

    clone = Path(tempfile.mkdtemp(prefix="legal-math-rehearsal-")) / "repo"
    keep = args.keep
    try:
        subprocess.run(
            ["git", "clone", "--no-hardlinks", "-q", str(ROOT), str(clone)],
            check=True, capture_output=True, text=True, encoding="utf-8", errors="replace",
        )
        for step in SEQUENCE:
            proc = subprocess.run(
                [sys.executable, *step[1:]], cwd=clone, capture_output=True, text=True, encoding="utf-8", errors="replace"
            )
            if proc.returncode != 0:
                print(f"documented step failed: {step}\n{proc.stderr.strip()[:400]}", file=sys.stderr)
                keep = True
                return 1

        dirty = porcelain(clone)
        unexpected = [p for p in dirty if p != MANIFEST]
        manifest_detail: list[str] = []
        if MANIFEST in dirty:
            before = subprocess.run(
                ["git", "show", f"HEAD:{MANIFEST}"], cwd=clone,
                capture_output=True, check=True,
            ).stdout.decode("utf-8")
            after = (clone / MANIFEST).read_text(encoding="utf-8")
            if _strip_subject(json.loads(before)) != _strip_subject(json.loads(after)):
                manifest_detail.append(
                    f"{MANIFEST} changed in fields other than subject/digest, which is real drift"
                )
            else:
                doc = _json(clone / MANIFEST)
                print(
                    f"expected: manifest rebound to subject {doc['subject']['commit'][:7]} "
                    f"(tree {doc['subject']['tree'][:7]})"
                )

        if args.with_tests:
            proc = subprocess.run(
                ["python", "-m", "pytest", "tests/", "-q", "-p", "no:cacheprovider"],
                cwd=clone, capture_output=True, text=True, encoding="utf-8",
            )
            tail = proc.stdout.strip().splitlines()[-1] if proc.stdout.strip() else proc.stderr[-200:]
            print(f"pytest in clone: exit={proc.returncode} :: {tail}")
            if proc.returncode != 0:
                unexpected.append(f"pytest failed in a fresh clone ({tail})")
                keep = True

        for path in unexpected + manifest_detail:
            print(f"UNREPRODUCIBLE: {path}", file=sys.stderr)
        if unexpected or manifest_detail:
            keep = True
            return 1

        print(
            f"rehearsal clean: {len(SEQUENCE)} documented steps reproduced every committed "
            f"account in a fresh clone of {subprocess.run(['git','rev-parse','--short','HEAD'], cwd=clone, capture_output=True, text=True, errors="replace").stdout.strip()}"
        )
        return 0
    finally:
        if keep:
            print(f"clone kept at {clone}", file=sys.stderr)
        else:
            shutil.rmtree(clone.parent, ignore_errors=True)


if __name__ == "__main__":
    sys.exit(main())
