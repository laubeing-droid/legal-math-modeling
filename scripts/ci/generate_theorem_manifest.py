#!/usr/bin/env python3
"""Generate a scope-labelled, reproducible Lean source inventory.

Replaces the hand-maintained theorem_manifest.json, whose file set predates the
ULM package and whose per-file hashes do not reproduce from the committed tree.

Hash contract (inventory-v3): sha256 over the exact bytes of each git-tracked
file, with no line-ending normalisation. Run --verify to re-check a written file.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
VERSION = "source-inventory-v3"
HASH_CONTRACT = "sha256-raw-committed-bytes-v1"

# `^theorem ` alone (the AGENTS.md convention) misses declarations that carry a
# same-line attribute, e.g. `@[simp] theorem map_failure`. Both are recorded.
DECL_RE = re.compile(
    r"^(?:@\[[^\]]*\][ \t]*)*(theorem|lemma|def|structure|inductive)\s+([^\s(:{]+)",
    re.MULTILINE,
)
BOL_DECL_RE = re.compile(
    r"^(theorem|lemma)\s+([^\s(:{]+)", re.MULTILINE
)
IMPORT_RE = re.compile(r"^import\s+(\S+)", re.MULTILINE)
AXIOM_PRINT_RE = re.compile(r"^#print\s+axioms\s+(\S+)", re.MULTILINE)
# Line-initial keywords inside comments are not declarations, so comments are
# removed before counting. Nested block comments are not modelled.
COMMENT_RE = re.compile(r"/-[-!]?.*?-/|--[^\n]*", re.DOTALL)
COUNTED_KINDS = ("theorem", "lemma")


def git(*args: str) -> str:
    return subprocess.run(
        ["git", *args], cwd=ROOT, capture_output=True, text=True, check=True
    ).stdout.strip()


def tracked_lean() -> list[Path]:
    out = git("ls-files", "-z", "--", "proofs")
    return sorted(Path(p) for p in out.split("\0") if p.endswith(".lean"))


def parse(path: Path) -> dict:
    text = path.read_text(encoding="utf-8", errors="replace")
    code = COMMENT_RE.sub(" ", text)
    decls = [{"name": n, "kind": k} for k, n in DECL_RE.findall(code)]
    col0 = [(k, n) for k, n in BOL_DECL_RE.findall(code)]
    return {
        "path": path.as_posix(),
        "sha256": hashlib.sha256(path.read_bytes()).hexdigest(),
        "size_bytes": path.stat().st_size,
        "declarations": decls,
        "theorem_count": sum(1 for d in decls if d["kind"] == "theorem"),
        "lemma_count": sum(1 for d in decls if d["kind"] == "lemma"),
        "theorem_count_bol_convention": sum(1 for k, _ in col0 if k == "theorem"),
        "imports": sorted({m for m in IMPORT_RE.findall(code)}),
        "print_axioms_targets": sorted({m for m in AXIOM_PRINT_RE.findall(code)}),
    }


def build_scopes(entries: list[dict]) -> dict[str, list[str]]:
    by_stem = {e["path"].rsplit("/", 1)[-1][: -len(".lean")]: e for e in entries}
    ulm = sorted(e["path"] for e in entries if e["path"].rsplit("/", 1)[-1].startswith("ULM"))

    # Transitive import closure of the ULM package, resolved textually.
    by_path = {e["path"]: e for e in entries}
    reached: set[str] = set(ulm)
    queue = list(ulm)
    while queue:
        entry = by_path[queue.pop()]
        for imp in entry["imports"]:
            if not imp.startswith("JurisLean"):
                continue
            target = by_stem.get(imp.split(".")[-1])
            if target and target["path"] not in reached:
                reached.add(target["path"])
                queue.append(target["path"])

    support = sorted(p for p in reached if p not in set(ulm))
    return {
        "ulm_package": ulm,
        "ulm_import_closure": support,
        "all_tracked_lean": sorted(e["path"] for e in entries),
    }


def summarise(entries: list[dict], paths: list[str]) -> dict:
    subset = [e for e in entries if e["path"] in set(paths)]
    audit_targets = sorted({t for e in subset for t in e["print_axioms_targets"]})
    return {
        "file_count": len(subset),
        "theorem_count": sum(e["theorem_count"] for e in subset),
        "lemma_count": sum(e["lemma_count"] for e in subset),
        "counted_declaration_count": sum(
            e["theorem_count"] + e["lemma_count"] for e in subset
        ),
        "theorem_count_bol_convention": sum(
            e["theorem_count_bol_convention"] for e in subset
        ),
        "print_axioms_command_count": sum(
            len(e["print_axioms_targets"]) for e in subset
        ),
        "print_axioms_distinct_targets": len(audit_targets),
    }


def find_gaps(entries: list[dict]) -> dict:
    declared = {d["name"] for e in entries for d in e["declarations"]}
    bare = {n.rsplit(".", 1)[-1] for n in declared}
    audit_files = [e for e in entries if "AxiomAudit" in e["path"]]
    unresolved = sorted(
        {
            t
            for e in audit_files
            for t in e["print_axioms_targets"]
            if t.rsplit(".", 1)[-1] not in bare
        }
    )
    return {
        "audit_targets_with_no_matching_declaration": unresolved,
        "note": (
            "Declaration kinds counted as proved statements are "
            + "/".join(COUNTED_KINDS)
            + "; `def`, `structure` and `inductive` are carriers, not proofs."
        ),
    }


def generate() -> dict:
    entries = [parse(p) for p in tracked_lean()]
    scopes = build_scopes(entries)
    return {
        "inventory_version": VERSION,
        "hash_contract": HASH_CONTRACT,
        "status": "static_source_inventory_not_release_certificate",
        "generated_by": "scripts/ci/generate_theorem_manifest.py",
        "subject": {"commit": git("rev-parse", "HEAD"),
                    "tree": git("rev-parse", "HEAD^{tree}"),
                    "branch": git("rev-parse", "--abbrev-ref", "HEAD")},
        "authority_note": (
            "Counts are static text measurements over git-tracked files at the "
            "recorded subject. They are not Lean elaboration evidence; build and "
            "axiom status is CI_NOT_RUN until an authorised GitHub Actions run "
            "binds them."
        ),
        "scope_definitions": {
            "ulm_package": "Files named ULM*.lean, including audit drivers.",
            "ulm_import_closure": "Files the ULM package reaches through JurisLean imports.",
            "all_tracked_lean": "Every git-tracked .lean file under proofs/.",
        },
        "scopes": scopes,
        "scope_summary": {k: summarise(entries, v) for k, v in scopes.items()},
        "files": entries,
        "gaps": find_gaps(entries),
    }


def inventory_digest(payload: dict) -> str:
    body = json.dumps(payload, sort_keys=True, ensure_ascii=False).encode("utf-8")
    return hashlib.sha256(body).hexdigest()


def verify(path: Path) -> int:
    doc = json.loads(path.read_text(encoding="utf-8"))
    problems = []
    for e in doc["files"]:
        f = ROOT / e["path"]
        if not f.exists():
            problems.append(f"missing file: {e['path']}")
        elif hashlib.sha256(f.read_bytes()).hexdigest() != e["sha256"]:
            problems.append(f"hash mismatch: {e['path']}")
    stored = doc.pop("source_inventory_digest", None)
    if stored is not None and inventory_digest(doc) != stored:
        problems.append("source_inventory_digest does not match content")
    for p in problems[:20]:
        print(f"  FAIL {p}")
    print(f"verified files={len(doc['files'])} problems={len(problems)}")
    return 1 if problems else 0


def resolve(arg: str) -> Path:
    path = Path(arg)
    return path if path.is_absolute() else ROOT / path


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--output", default="docs/formal-release/theorem_inventory_v3.json")
    ap.add_argument("--verify", help="re-check a previously written inventory")
    args = ap.parse_args()

    if args.verify:
        return verify(resolve(args.verify))

    doc = generate()
    doc["source_inventory_digest"] = inventory_digest(doc)
    out = resolve(args.output)
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(
        json.dumps(doc, sort_keys=True, indent=1, ensure_ascii=False) + "\n",
        encoding="utf-8",
    )

    print(f"wrote {out} at subject {doc['subject']['commit'][:12]}")
    for name, summary in sorted(doc["scope_summary"].items()):
        print(
            f"  {name:22s} files={summary['file_count']:4d} "
            f"theorems={summary['theorem_count']:5d} lemmas={summary['lemma_count']:4d} "
            f"#print axioms cmds={summary['print_axioms_command_count']:4d} "
            f"distinct={summary['print_axioms_distinct_targets']:4d}"
        )
    gaps = doc["gaps"]["audit_targets_with_no_matching_declaration"]
    print(f"  audit targets with no declaration: {len(gaps)} {gaps[:5]}")
    return 0


if __name__ == "__main__":
    sys.stdout.reconfigure(encoding="utf-8", errors="replace")
    raise SystemExit(main())
