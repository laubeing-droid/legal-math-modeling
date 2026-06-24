from __future__ import annotations

import re
import sys
from pathlib import Path


FORBIDDEN_PATTERNS = (
    ("sorry tactic", re.compile(r"\bsorry\b")),
    ("admit tactic", re.compile(r"\badmit\b")),
    ("axiom declaration", re.compile(r"^\s*axiom\b")),
    ("true theorem evasion", re.compile(r":\s*True\s*:=")),
)


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


def scan_file(path: Path) -> list[str]:
    issues: list[str] = []
    block_depth = 0
    for lineno, raw_line in enumerate(path.read_text(encoding="utf-8").splitlines(), start=1):
        code, block_depth = strip_comments(raw_line, block_depth)
        if not code.strip():
            continue
        for label, pattern in FORBIDDEN_PATTERNS:
            if pattern.search(code):
                issues.append(f"{path}:{lineno}: {label}: {code.strip()}")
    return issues


def main() -> int:
    if len(sys.argv) != 2:
        print("usage: scan_lean_guards.py <lean-root>", file=sys.stderr)
        return 2

    root = Path(sys.argv[1])
    if not root.exists():
        print(f"missing path: {root}", file=sys.stderr)
        return 2

    issues: list[str] = []
    for lean_file in sorted(root.rglob("*.lean")):
        issues.extend(scan_file(lean_file))

    if issues:
        print("forbidden Lean constructs found:")
        for issue in issues:
            print(issue)
        return 1

    print("Lean guard scan passed.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
