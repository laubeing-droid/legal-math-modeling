"""Static Lean guard scan.

Two independent jobs, deliberately separated because conflating them is how the
repository ended up asserting a "tactic whitelist" that no tool enforced:

1. FORBIDDEN CONSTRUCTS — this is the gate. `sorry`, `admit`, a top-level
   `axiom`, `native_decide`, and the `: True :=` evasion are fail-closed: any
   hit exits non-zero. Comments are stripped first, so a commented-out
   `sorry` in a downgrade note does not trip the gate, and an uncommented one
   cannot hide.

2. TACTIC CENSUS — this is measurement, not enforcement. Per-file counts of the
   closing tactics actually used are published as JSON so any claim about which
   tactics a module uses can be checked against the report. Nothing here
   whitelists tactics; if a whitelist is ever wanted, it must be added as an
   explicit gate with its own scope, not as a header comment.

Scope: pass a root directory, or `--all-tracked` to cover every git-tracked
`.lean` under `proofs/`. The default in CI is `--all-tracked`, because a
theorem count that spans 216 files cannot be certified by scanning 201 of them.
"""

from __future__ import annotations

import argparse
import json
import os
import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
PROOFS = "proofs"

FORBIDDEN_PATTERNS = (
    ("sorry tactic", re.compile(r"\bsorry\b")),
    ("admit tactic", re.compile(r"\badmit\b")),
    ("axiom declaration", re.compile(r"^\s*axiom\b")),
    ("native_decide tactic", re.compile(r"\bnative_decide\b")),
    ("true theorem evasion", re.compile(r":\s*True\s*:=")),
)

# Vocabulary for the census only. Order matters: longest first so `simp only`
# is not double-counted as `simp`.
TACTIC_VOCAB = (
    "native_decide", "decide", "rfl", "simp only", "simpa", "simp", "omega",
    "linarith", "nlinarith", "norm_num", "induction", "cases", "rcases",
    "obtain", "rw", "exact", "have", "constructor", "intro", "apply", "refine",
    "ext", "funext", "calc", "conv", "ring", "grind", "tauto", "aesop",
    "by_cases", "by_contra", "trivial", "subcase", "next",
)

DECL_RE = re.compile(r"^(?:@\[[^\]]*\][ \t]*)*(?:theorem|lemma)\s+([^\s(:{]+)")


def strip_comments(line: str, block_depth: int) -> tuple[str, int]:
    result: list[str] = []
    i = 0
    in_string = False
    while i < len(line):
        ch = line[i]
        nxt = line[i + 1] if i + 1 < len(line) else ""

        if block_depth > 0:
            if ch == "/" and nxt == "-":
                block_depth += 1
                i += 2
                continue
            if ch == "-" and nxt == "/":
                block_depth -= 1
                i += 2
                continue
            i += 1
            continue

        if not in_string and ch == "-" and nxt == "-":
            break
        if not in_string and ch == "/" and nxt == "-":
            block_depth += 1
            i += 2
            continue
        if ch == '"':
            in_string = not in_string
            result.append(ch)
            i += 1
            continue

        result.append(ch)
        i += 1

    return "".join(result), block_depth


def tracked_lean_files() -> list[Path]:
    out = subprocess.run(
        ["git", "ls-files", "*.lean"],
        cwd=ROOT,
        capture_output=True,
        text=True,
    )
    if out.returncode != 0:
        raise SystemExit(f"git ls-files failed: {out.stderr.strip()}")
    paths = sorted(
        p for p in out.stdout.split()
        if p.startswith(PROOFS + "/") and "/.lake/" not in f"/{p}"
    )
    return [ROOT / p for p in paths]


def scan_file(path: Path) -> tuple[list[str], dict[str, int]]:
    issues: list[str] = []
    census: dict[str, int] = {}
    block_depth = 0
    for lineno, raw_line in enumerate(
        path.read_text(encoding="utf-8").splitlines(), start=1
    ):
        code, block_depth = strip_comments(raw_line, block_depth)
        if not code.strip():
            continue
        for label, pattern in FORBIDDEN_PATTERNS:
            if pattern.search(code):
                issues.append(f"{path}:{lineno}: {label}: {code.strip()}")
        for tactic in TACTIC_VOCAB:
            hits = len(re.findall(r"(?:^|[\s·])(?:" + re.escape(tactic) + r")(?:\b|\s|$)", code))
            if hits:
                census[tactic] = census.get(tactic, 0) + hits
    return issues, census


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("root", nargs="?", help="directory to scan recursively")
    ap.add_argument(
        "--all-tracked",
        action="store_true",
        help=f"scan every git-tracked .lean under {PROOFS}/ instead of one root",
    )
    ap.add_argument("--report", help="write a JSON census/issue report here")
    args = ap.parse_args()

    if args.all_tracked == bool(args.root):
        print("usage: scan_lean_guards.py <lean-root> | --all-tracked [--report PATH]", file=sys.stderr)
        return 2

    if args.all_tracked:
        files = tracked_lean_files()
    else:
        root = Path(args.root).resolve()
        if not root.exists():
            print(f"missing path: {root}", file=sys.stderr)
            return 2
        files = sorted(root.rglob("*.lean"))

    issues: list[str] = []
    per_file: dict[str, dict[str, int]] = {}
    for lean_file in files:
        found, census = scan_file(lean_file)
        issues.extend(found)
        rel = os.path.relpath(lean_file, ROOT).replace("\\", "/")
        per_file[rel] = census

    if args.report:
        payload = {
            "schema_version": "lean-guard-v2",
            "scope": "all_tracked_proofs" if args.all_tracked else str(args.root),
            "files_scanned": len(files),
            "forbidden_construct_count": len(issues),
            "forbidden_patterns": [label for label, _ in FORBIDDEN_PATTERNS],
            "note": (
                "Static text measurement with comments stripped. This is not a "
                "tactic whitelist gate and is not Lean elaboration evidence."
            ),
            "tactic_census": per_file,
        }
        report_path = Path(args.report)
        if not report_path.is_absolute():
            report_path = ROOT / report_path
        report_path.parent.mkdir(parents=True, exist_ok=True)
        report_path.write_text(
            json.dumps(payload, ensure_ascii=False, indent=1, sort_keys=True) + "\n",
            encoding="utf-8",
            newline="\n",
        )

    if issues:
        print("forbidden Lean constructs found:")
        for issue in issues:
            print(issue)
        return 1

    print(f"Lean guard scan passed ({len(files)} files, scope="
          f"{'all-tracked' if args.all_tracked else args.root}).")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
