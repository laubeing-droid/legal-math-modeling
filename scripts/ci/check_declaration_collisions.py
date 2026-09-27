"""Fail if two modules that the same build imports declare one fully-qualified name.

Lean rejects an `import` whose environment already contains a declaration with the
same full name: `error: import X failed, environment already contains 'Y' from Z`.
Nothing static in this repository checked for that, so the reachability block added
by `check_import_reachability.py` -- whose whole purpose is to make modules elaborate
-- imported `JurisLean.TypedAttack` next to the pre-existing
`JurisLean.AttackDecision`, and both define `JurisLean.isSelfAttack`. The root build
then failed, which took a CI round to discover (run 36290409329).

This gate reproduces the compiler's condition from source text: walk the import
closure of each build root, collect the namespace-qualified names each module
declares, and report any name two modules both declare.
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from collections import defaultdict
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
try:
    from scripts.lean_grammar import declarations
    from scripts.scan_lean_guards import strip_comments
except ImportError:  # run as `python scripts/ci/<this>.py`: sys.path[0] is scripts/ci
    sys.path.insert(0, str(ROOT / "scripts"))
    from lean_grammar import declarations
    from scan_lean_guards import strip_comments

LEAN_ROOT = Path("proofs/lean/juris_lean")
IMPORT = re.compile(r"^import\s+([A-Za-z0-9_.]+)")


def module_name(path: Path, repo: Path) -> str:
    """`JurisLean.Mandate.Kernel` for `LEAN_ROOT/JurisLean/Mandate/Kernel.lean`."""
    return ".".join(path.relative_to(repo / LEAN_ROOT).with_suffix("").parts)


def imports_of(text: str) -> list[str]:
    found, depth = [], 0
    for line in text.splitlines():
        code, depth = strip_comments(line, depth)
        match = IMPORT.match(code.strip())
        if match:
            found.append(match.group(1))
    return found


def indexed(repo: Path) -> tuple[dict[str, list[dict]], dict[str, list[str]]]:
    mods: dict[str, list[dict]] = {}
    imports: dict[str, list[str]] = {}
    for path in sorted((repo / LEAN_ROOT).rglob("*.lean")):
        text = path.read_text(encoding="utf-8")
        rel = str(path.relative_to(repo)).replace("\\", "/")
        name = module_name(path, repo)
        imports[name] = [
            m for m in imports_of(text) if m != name
        ]
        mods[name] = [
            {**d, "path": rel} for d in declarations(text, namespace=True)
        ]
    return mods, imports


def closure_of(roots: list[str], imports: dict[str, list[str]]) -> list[str]:
    seen, queue, order = set(), list(roots), []
    while queue:
        mod = queue.pop(0)
        if mod in seen:
            continue
        seen.add(mod)
        order.append(mod)
        queue.extend(imports.get(mod, []))
    return sorted(order)


def collisions(mods: dict[str, list[dict]], modules: list[str]) -> dict[str, list[dict]]:
    by_name: dict[str, list[dict]] = defaultdict(list)
    for mod in modules:
        for decl in mods.get(mod, []):
            by_name[decl["name"]].append(
                {"module": mod, "path": decl["path"], "line": decl["line"],
                 "keyword": decl["keyword"]}
            )
    return {
        name: sites
        for name, sites in by_name.items()
        if len({s["module"] for s in sites}) > 1
    }


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo", default=".", type=Path)
    parser.add_argument("--root", action="append", default=None,
                        help="build root module (default: every lakefile root)")
    parser.add_argument("--json", dest="json_out", type=Path, default=None)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args(argv)

    repo = args.repo.resolve()
    mods, imports = indexed(repo)
    roots = args.root or [module_name(p, repo)
                          for p in sorted((repo / LEAN_ROOT).rglob("*.lean"))
                          if module_name(p, repo).count(".") == 0]
    modules = closure_of(roots, imports)
    found = collisions(mods, modules)
    payload = {
        "schema": "declaration_collisions.v1",
        "rule": "two modules in one build closure may not declare the same qualified name",
        "roots": sorted(roots),
        "modules_in_closure": len(modules),
        "collisions": {k: found[k] for k in sorted(found)},
        "collision_count": len(found),
    }
    if args.json_out:
        args.json_out.parent.mkdir(parents=True, exist_ok=True)
        args.json_out.write_text(json.dumps(payload, ensure_ascii=False, indent=2) + "\n",
                                 encoding="utf-8")
    if not args.check:
        print(json.dumps(payload, ensure_ascii=False, indent=2))
        return 0
    if found:
        print(f"declaration collisions in the build closure: {len(found)}")
        for name in sorted(found):
            sites = ", ".join(f"{s['path']}:{s['line']}" for s in found[name])
            print(f"  {name}: {sites}")
        return 1
    print(f"no declaration collisions among {len(modules)} modules reachable from "
          f"{len(roots)} roots")
    return 0


if __name__ == "__main__":
    sys.exit(main())
