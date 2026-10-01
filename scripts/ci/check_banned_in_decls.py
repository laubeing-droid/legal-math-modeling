"""Declaration-level scan for the constructs the red lines forbid (master order §9.1).

Why a second instrument when `scripts/scan_lean_guards.py` already gates the same
five tokens:

1. Scope. The guard scanner takes `git ls-files`, so a `.lean` file that has been
   written but not yet committed is invisible to it. That is precisely when a
   `sorry` is most likely to be present. This scanner walks the working tree.
2. Evidence. §9.1 asks for a per-needle self-check, which means a violation has to
   be attributed to the declaration that carries it, not just to a line number.
   Every hit here names the enclosing declaration.

The comment state machine and the declaration grammar are imported, not
reimplemented, so the two scanners cannot drift into disagreeing about what a
comment or a declaration is. Raw `grep` over this tree is not a usable substitute:
`Genealogy/TSpectrum/Batch1.lean` lists the banned words one per line inside a doc
comment, so a grep-based check reports violations where the source has none.

This is a static text measurement. It is not elaboration evidence: a module that
passes here has merely not written a forbidden token in a declaration body.
"""

from __future__ import annotations

import argparse
import os
import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
sys.path.insert(0, str(ROOT / "scripts"))

from lean_grammar import strip_comments  # noqa: E402

BANNED = (
    ("sorry tactic", re.compile(r"\bsorry\b")),
    ("admit tactic", re.compile(r"\badmit\b")),
    ("native_decide tactic", re.compile(r"\bnative_decide\b")),
    ("axiom declaration", re.compile(r"^axiom\b")),
    ("theorem-of-True evasion", re.compile(r":\s*True\s*:=")),
)

# `axiom` is not in ENV_DECLARATION: it is not a declaration the environment lets
# collide, it is here a forbidden construct. Adding it as a boundary keeps a
# top-level `axiom` from hiding inside the preceding declaration's segment.
BOUNDARY = re.compile(
    r"^(?:@\[[^\]]*\][ \t]*)*"
    r"(axiom|theorem|lemma|def|abbrev|structure|inductive|class|opaque|macro)"
    r"\s+([^\s(:{=\[]+)"
)
OWNER = "(file preamble)"


def declaration_starts(lines: list[str]) -> dict[int, str]:
    """Map 1-based line numbers of declaration starts to the declared name."""

    starts: dict[int, str] = {}
    depth = 0
    for lineno, raw_line in enumerate(lines, start=1):
        code, depth = strip_comments(raw_line, depth)
        stripped = code.strip()
        if not stripped:
            continue
        match = BOUNDARY.match(stripped)
        if match:
            starts[lineno] = match.group(2)
    return starts


def display(path: Path) -> str:
    try:
        return path.relative_to(ROOT).as_posix()
    except ValueError:  # a file outside the repository (a test fixture)
        return path.as_posix()


def scan_file(path: Path) -> tuple[list[str], int]:
    """Return (violations, declarations inspected) for one file."""

    text = path.read_text(encoding="utf-8")
    lines = text.splitlines()
    starts = declaration_starts(lines)
    boundaries = sorted(starts) + [len(lines) + 1]

    violations: list[str] = []
    owner = OWNER
    depth = 0
    index = 0
    for lineno, raw_line in enumerate(lines, start=1):
        code, depth = strip_comments(raw_line, depth)
        stripped = code.strip()
        if stripped and lineno == boundaries[index]:
            owner = starts[lineno]
            index += 1
        if not stripped:
            continue
        for label, pattern in BANNED:
            if pattern.search(stripped):
                violations.append(
                    f"{display(path)}:{lineno}: "
                    f"{label} in {owner}: {stripped[:100]}"
                )
    return violations, len(starts)


def working_tree_lean_files(root: str) -> list[Path]:
    base = ROOT / root
    if not base.is_dir():
        raise SystemExit(f"missing path: {base}")
    return sorted(
        p for p in base.rglob("*.lean")
        if ".lake" not in p.parts and "resilient_cache" not in p.parts
    )


def tracked_lean_files() -> list[Path]:
    out = subprocess.run(
        ["git", "ls-files", "*.lean"], cwd=ROOT, capture_output=True, text=True
    )
    if out.returncode != 0:
        raise SystemExit(f"git ls-files failed: {out.stderr.strip()}")
    return sorted(ROOT / p for p in out.stdout.split() if p.startswith("proofs/"))


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--root", default="proofs", help="directory to walk (default: proofs)")
    ap.add_argument(
        "--all-tracked",
        action="store_true",
        help="scan git-tracked files instead of the working tree",
    )
    args = ap.parse_args()

    files = tracked_lean_files() if args.all_tracked else working_tree_lean_files(args.root)
    violations: list[str] = []
    declarations = 0
    for lean_file in files:
        found, count = scan_file(lean_file)
        violations.extend(found)
        declarations += count

    mode = "all-tracked" if args.all_tracked else f"working tree under {args.root}/"
    if violations:
        print(f"banned constructs found in declaration bodies ({mode}):")
        for line in violations:
            print(f"  {line}")
        print(f"files scanned: {len(files)}, declarations inspected: {declarations}")
        return 1

    print(
        f"declaration-level ban scan passed: {len(files)} files, "
        f"{declarations} declarations, 0 violations ({mode})"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
