#!/usr/bin/env python3
"""CI helper: compute the Lean module matrix for changed-module runs.

Given a base and head commit (or `--all`), lists changed JurisLean modules
plus their reverse dependencies, derived from `import JurisLean.X` lines.
Output is a JSON matrix consumed by the GitHub Actions matrix job. This
script never executes Lean.
"""

from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
from pathlib import Path
from typing import Dict, List, Set

LEAN_DIR = Path("proofs/lean/juris_lean/JurisLean")
IMPORT_PATTERN = re.compile(r"^import\s+JurisLean\.([A-Za-z0-9_]+)", re.MULTILINE)


def module_name(path: Path) -> str:
    return path.stem


def build_dependency_index(repo_root: Path) -> Dict[str, Set[str]]:
    """Map module -> set of modules that import it (reverse dependencies)."""

    index: Dict[str, Set[str]] = {}
    lean_dir = repo_root / LEAN_DIR
    for lean_file in sorted(lean_dir.glob("*.lean")):
        text = lean_file.read_text(encoding="utf-8")
        for imported in IMPORT_PATTERN.findall(text):
            index.setdefault(imported, set()).add(module_name(lean_file))
    return index


def changed_modules(repo_root: Path, base: str, head: str) -> List[str]:
    output = subprocess.run(
        ["git", "diff", "--name-only", base, head, str(LEAN_DIR)],
        cwd=repo_root,
        capture_output=True,
        text=True,
        check=True,
    )
    names = []
    for line in output.stdout.splitlines():
        path = Path(line.strip())
        if path.suffix == ".lean" and path.parent.name == "JurisLean":
            names.append(path.stem)
    return sorted(set(names))


def all_modules(repo_root: Path) -> List[str]:
    lean_dir = repo_root / LEAN_DIR
    return sorted(path.stem for path in lean_dir.glob("*.lean"))


def expand_reverse_dependencies(
    modules: List[str], index: Dict[str, Set[str]]
) -> List[str]:
    expanded: Set[str] = set(modules)
    frontier = list(modules)
    while frontier:
        current = frontier.pop()
        for dependent in index.get(current, ()):
            if dependent not in expanded:
                expanded.add(dependent)
                frontier.append(dependent)
    return sorted(expanded)


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--repo-root", type=Path, default=Path.cwd())
    parser.add_argument("--all", action="store_true")
    parser.add_argument("--base", default="origin/main")
    parser.add_argument("--head", default="HEAD")
    parser.add_argument("--output", type=Path, default=None)
    args = parser.parse_args()

    if args.all:
        modules = all_modules(args.repo_root)
    else:
        modules = changed_modules(args.repo_root, args.base, args.head)
        index = build_dependency_index(args.repo_root)
        modules = expand_reverse_dependencies(modules, index)

    matrix = {
        "include": [
            {"module": name, "target": f"JurisLean.{name}"} for name in modules
        ]
    }
    rendered = json.dumps(matrix, ensure_ascii=False, indent=2)
    if args.output is not None:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(rendered + "\n", encoding="utf-8")
    print(rendered)
    return 0


if __name__ == "__main__":
    sys.exit(main())
