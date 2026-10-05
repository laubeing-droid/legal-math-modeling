"""How many theorem declarations did a wave actually add, and are they all attested?

Built for the acceptance round of 2026-10-05: the ledger claimed "24 new theorems all entered
the axiom surface" while the surface holds 22, and a bare count written into prose cannot be
re-checked by anyone else. This script makes that claim a command.

    python scripts/ci/count_added_theorems.py 789ac09 5aa3863 \
        --attested-in docs/formal-release/ci-evidence/37227626074/axiom-audit/axiom-audit.raw.txt

A declaration is a line whose keyword `theorem` follows only indentation and optional
attribute prefixes; that is the same shape the inventory counts, which is why the two totals
agree where they overlap. Comment bodies never match because `theorem` there is not at a
line start followed by a name.
"""

from __future__ import annotations

import argparse
import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
DECL = re.compile(r"^\s*(?:@\[[^\]]*\]\s*)*theorem\s+([A-Za-z0-9_.']+)")


def names_at(sha: str) -> dict[str, str]:
    """theorem name -> the .lean file that declares it, for every tracked file at sha."""
    listing = subprocess.run(
        ["git", "ls-tree", "-r", "--name-only", f"{sha}^{{commit}}", "--", "proofs/lean"],
        cwd=ROOT, capture_output=True, text=True, encoding="utf-8", check=True,
    ).stdout
    found: dict[str, str] = {}
    for path in (line for line in listing.splitlines() if line.endswith(".lean")):
        shown = subprocess.run(
            ["git", "show", f"{sha}:{path}"], cwd=ROOT, capture_output=True,
            text=True, encoding="utf-8", errors="replace", check=False,
        )
        if shown.returncode != 0:
            continue
        for line in shown.stdout.splitlines():
            m = DECL.match(line)
            if m:
                found[m.group(1)] = path
    return found


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("old")
    ap.add_argument("new")
    ap.add_argument("--attested-in", type=Path, default=None,
                    help="axiom-audit.raw.txt to check every added name against")
    a = ap.parse_args()

    before, after = names_at(a.old), names_at(a.new)
    added = sorted(set(after) - set(before))
    removed = sorted(set(before) - set(after))
    print(f"theorem declarations at {a.old}: {len(before)}")
    print(f"theorem declarations at {a.new}: {len(after)}")
    print(f"ADDED={len(added)} REMOVED={len(removed)}")
    for name in added:
        print(f"  + {name}  [{after[name]}]")
    for name in removed:
        print(f"  - {name}  [{before[name]}]")

    rc = 0
    if a.attested_in:
        text = a.attested_in.read_text(encoding="utf-8", errors="replace")
        missing = [n for n in added if n.split(".")[-1] not in text]
        print(f"added names absent from {a.attested_in.name}: {len(missing)}")
        for name in missing:
            print(f"  UNATTESTED {name}")
        rc = 1 if missing else 0
    if removed:
        print("NOTE: declarations disappeared between the two subjects -- a deleted theorem "
              "is a contract change, not a count")
    return rc


if __name__ == "__main__":
    sys.exit(main())
