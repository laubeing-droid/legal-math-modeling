#!/usr/bin/env python3
"""Census of literally duplicated theorem statements across module families (R-04).

Why: R-04 asks for Genealogy's declarations to be carried by the shared kernel instead
of restated. "Restated" has to mean something checkable, and the checkable reading is
*this statement type appears verbatim under two names*. Anything looser -- similar names,
similar ideas -- is judgement, and the ledger says so; this file only counts the exact
case, so a migration can be measured rather than asserted.

How a statement is read: everything between a `theorem`/`lemma` name and the first `:=`
at bracket depth zero -- binders included, so `(h : P) : Q` and `(h : R) : Q` do not
match. Annotations like `(x : ℚ)` sit at depth one and never end the header, and a
record update `{ ctx with f := v }` carries a `:=` two levels in, which is why braces
count in the depth. Whitespace is collapsed; comments are stripped by the repository's
own grammar helper. A match therefore means the two statements are written identically.

Known limit, stated rather than hidden: `@[...]` attributes, `where` clauses and
`private`/`protected` prefixes are not compared, and a restatement that unfolds a
definition is invisible here. A zero from this tool is therefore evidence about literal
duplication only -- not proof that no two modules overlap in substance.

    python scripts/ci/build_statement_duplication_census.py            # write
    python scripts/ci/build_statement_duplication_census.py --check    # fail on drift
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from collections import defaultdict
from pathlib import Path
from typing import Dict, List, Optional, Tuple

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
import lean_grammar as lg  # noqa: E402

ROOT = Path(__file__).resolve().parents[2]
PKG = ROOT / "proofs" / "lean" / "juris_lean" / "JurisLean"
OUT = ROOT / "docs" / "formal-release" / "statement_duplication_census.json"
MD = ROOT / "docs" / "formal-release" / "statement_duplication_census.md"
SCHEMA = "statement-duplication-census-v1"

HEADER = re.compile(r"^(?:private\s+|protected\s+)*(theorem|lemma)\s+")
WS = re.compile(r"\s+")


def family(rel: str) -> str:
    parts = Path(rel).parts
    if parts[0] == "Genealogy":
        return "Genealogy"
    if parts[0] == "Mandate":
        return "Mandate"
    if parts[0] == "FullMath":
        return "FullMath"
    if parts[0] == "External":
        # The byte-faithful ports carry upstream's own cross-file helper lemmas; a
        # separate family keeps those from masking a real cross-family match with
        # this repository's own modules.
        return "External"
    return "root/other"


def split_header(text: str) -> Tuple[str, str]:
    """Return (name, normalised statement type) for a header line, or ('', '').

    The statement type is the header with the declaration *name removed*: the two
    things being compared are the same statement written under two names, so the name
    is exactly the part that must not be in the key. Keeping it made renaming invisible
    -- `bb5_trustLE_trans` (Seams/BoundaryBridge5.lean) and `trustLE_trans`
    (Seams/BoundaryClosure.lean) are byte-identical apart from their names, and a
    name-inclusive key filed them as two distinct statements (W1b fix; the readings
    went 8 -> 40 duplicated types once the name left the key).
    """
    m = HEADER.match(text)
    if not m:
        return "", ""
    rest = text[m.end():]
    named = re.match(r"[A-Za-z0-9_']*", rest)
    name = named.group(0)
    # Everything after the name is what gets compared. A name can only hold
    # [A-Za-z0-9_'], so it carries no bracket and no depth-zero colon: cutting the
    # scan base from `rest` to `body` shifts indices but changes no grouping.
    body = rest[named.end():]
    # Braces count too: a statement like `check (writeDoc { meta := { ctx with
    # caseId := "X" } }) = false` has `:=` two levels in, and stopping at depth zero
    # for round brackets only truncates every such header to the same prefix, which
    # then reads as dozens of false duplicates.
    depth = 0
    colon = -1
    for i, ch in enumerate(body):
        if ch in "([{":
            depth += 1
        elif ch in ")]}":
            depth -= 1
        elif ch == ":" and depth == 0 and body[i:i + 2] != ":=":
            colon = i
            break
    if colon < 0:
        return name, ""
    end = len(body)
    depth = 0
    for i in range(colon, len(body)):
        ch = body[i]
        if ch in "([{":
            depth += 1
        elif ch in ")]}":
            depth -= 1
        elif body[i:i + 2] == ":=" and depth == 0:
            end = i
            break
    # The key is the WHOLE header minus the name: binders included. Counting only the
    # conclusion would let `theorem a (h : P) : Q` and `theorem b (h : R) : Q` match,
    # which is a shared shape, not a duplicated statement.
    header = body[:end]
    if ":" not in header:
        return name, ""
    stmt = WS.sub(" ", header).strip()
    if not stmt:
        return name, ""
    return name, stmt


def read_multiline(text: str) -> List[Tuple[str, str, int, bool]]:
    """Headers span lines; take a bounded lookahead per header and let `split_header`
    cut at the first depth-zero `:=`. Stopping at the first `:=` anywhere is wrong --
    a record update `{ ctx with assumptions := [...] }` carries one two levels in, and
    cutting there makes every such header collapse to the same prefix.

    The fourth slot says whether the header carried a `private`/`protected` prefix:
    the duplication analysis below still reads those statements, but the coverage
    identity against the theorem inventory must exclude them, because the inventory
    (like the repository's own `rg "^theorem "` counting convention) does not count
    private/protected declarations -- the neural backport's nine `private lemma`
    helpers drove the published blind-spot negative until the two sides agreed on
    this convention.
    """
    lines = text.splitlines()
    out: List[Tuple[str, str, int, bool]] = []
    for n, line in enumerate(lines, 1):
        m = HEADER.match(line)
        if not m:
            continue
        window = " ".join(lines[n - 1:min(n - 1 + 15, len(lines))])
        name, stmt = split_header(window)
        if name and stmt:
            out.append((name, stmt, n, line.lstrip().startswith(("private ", "protected "))))
    return out


INVENTORY = ROOT / "docs" / "formal-release" / "theorem_inventory_v3.json"


def inventory_count() -> int:
    """Declared theorem *and* lemma count in the package scope, from the generated account.

    The census reads fewer headers than that whenever a declaration hides behind an
    attribute line or a `where` clause, so the difference is published instead of
    smoothed over: it is this scanner's own blind spot, measured.

    The comparison basis is theorems **plus** lemmas because the scanner reads both
    keywords. Against theorem-count alone the difference could go negative the
    moment a ported library leans on `lemma` (the external game-theory cone does:
    134 package lemmas against 17 before it -- the "13" first written here was the
    old blind-spot count misread as a lemma count, blind-audit finding P2-1),
    which would read as a negative blind spot -- a nonsense the first
    external-port round actually produced.
    """
    if not INVENTORY.exists():
        return -1
    doc = json.loads(INVENTORY.read_text(encoding="utf-8"))
    scope = doc["scope_summary"]["juris_lean_package"]
    return scope["theorem_count"] + scope.get("lemma_count", 0)


def scan() -> Dict:
    by_stmt: Dict[str, List[Tuple[str, str, int]]] = defaultdict(list)
    files = sorted(p for p in PKG.rglob("*.lean") if p.name != "JurisLean.lean")
    private_headers = 0
    for path in files:
        rel = path.relative_to(PKG).as_posix()
        clean: List[str] = []
        depth = 0
        for line in path.read_text(encoding="utf-8").splitlines():
            code, depth = lg.strip_comments(line, depth)
            clean.append(code)
        for name, stmt, line, is_private in read_multiline("\n".join(clean)):
            by_stmt[stmt].append((f"{family(rel)}/{name}", rel, line))
            if is_private:
                private_headers += 1
    dupes = {s: sorted(v) for s, v in by_stmt.items() if len(v) > 1}
    cross = {
        s: v for s, v in dupes.items()
        if len({carrier.split("/", 1)[0] for carrier, _p, _l in v}) > 1
    }
    return {
        "schema_version": SCHEMA,
        "generated_by": "python scripts/ci/build_statement_duplication_census.py",
        "authority_note": (
            "Counts theorem/lemma headers whose normalised statement types are byte-identical "
            "across two declarations in the JurisLean package. A match is literal duplication "
            "only; the tool cannot see a restatement that unfolds a definition, so a zero is "
            "evidence about verbatim overlap, not about substantive overlap."
        ),
        "scan_scope": "proofs/lean/juris_lean/JurisLean/**/*.lean (tracked tree), comments stripped",
        "files_scanned": len(files),
        "inventory_package_theorems": inventory_count(),
        "private_protected_headers_read": private_headers,
        # The inventory (and the repository's `rg "^theorem "` convention) does not
        # count private/protected declarations; the scanner reads them for the
        # duplication analysis, so they are excluded from the identity below.
        "headers_missed_by_scanner": inventory_count() - (
            sum(len(v) for v in by_stmt.values()) - private_headers
        ),
        "statements_read": sum(len(v) for v in by_stmt.values()),
        "distinct_statement_types": len(by_stmt),
        "duplicated_statement_types": len(dupes),
        "cross_family_statement_types": len(cross),
        "duplicates": {
            stmt: [{"carrier": c, "path": p, "line": l} for c, p, l in v]
            for stmt, v in sorted(dupes.items(), key=lambda kv: kv[0])
        },
        "cross_family": {
            stmt: [{"carrier": c, "path": p, "line": l} for c, p, l in v]
            for stmt, v in sorted(cross.items(), key=lambda kv: kv[0])
        },
    }


def render(doc: Dict) -> str:
    lines = [
        "# Statement duplication census (generated)",
        "",
        f"`{doc['schema_version']}`; generated by `{doc['generated_by']}`.",
        "",
        doc["authority_note"],
        "",
        f"- files scanned: {doc['files_scanned']}",
        f"- theorem/lemma headers read: {doc['statements_read']}",
        f"- distinct statement types: {doc['distinct_statement_types']}",
        f"- statement types declared more than once: {doc['duplicated_statement_types']}",
        f"- of those spanning module families: {doc['cross_family_statement_types']}",
        "",
    ]
    for key, title in (("cross_family", "Across module families"),
                       ("duplicates", "Within the package")):
        block = doc[key]
        lines += [f"## {title} ({len(block)})", ""]
        if not block:
            lines += ["None.", ""]
        for stmt, hits in list(block.items())[:40]:
            where = ", ".join(f"`{h['path']}:{h['line']}` ({h['carrier']})" for h in hits)
            lines += [f"- `{stmt[:160]}` — {where}"]
        if len(block) > 40:
            lines += [f"- …{len(block) - 40} more in the JSON"]
        lines.append("")
    return "\n".join(lines)


def main(argv: Optional[List[str]] = None) -> int:
    ap = argparse.ArgumentParser(description="statement duplication census")
    ap.add_argument("--check", action="store_true", help="fail if the committed census drifts")
    ap.add_argument("--write", action="store_true", help="write the census and its table")
    args = ap.parse_args(argv)
    doc = scan()
    if args.check:
        if not OUT.exists():
            print("census missing; run without --check to generate it", file=sys.stderr)
            return 1
        committed = json.loads(OUT.read_text(encoding="utf-8"))
        for field in ("files_scanned", "statements_read", "distinct_statement_types",
                      "duplicated_statement_types", "cross_family_statement_types",
                      "inventory_package_theorems", "headers_missed_by_scanner"):
            if committed.get(field) != doc[field]:
                print(f"{field} drift: committed {committed.get(field)}, source says "
                      f"{doc[field]}; regenerate", file=sys.stderr)
                return 1
        if set(committed["duplicates"]) != set(doc["duplicates"]):
            extra = set(doc["duplicates"]) - set(committed["duplicates"])
            print(f"new duplicated statements not in the census: {sorted(extra)[:3]}",
                  file=sys.stderr)
            return 1
        print(f"statement duplication census ok: {doc['duplicated_statement_types']} "
              f"duplicated / {doc['distinct_statement_types']} distinct statements")
        return 0
    if args.write:
        OUT.write_text(json.dumps(doc, ensure_ascii=False, indent=2, sort_keys=True) + "\n",
                       encoding="utf-8", newline="\n")
        MD.write_text(render(doc), encoding="utf-8", newline="\n")
        print(f"wrote {OUT.relative_to(ROOT)} and {MD.relative_to(ROOT)}: "
              f"{doc['duplicated_statement_types']} duplicated statement types "
              f"({doc['cross_family_statement_types']} across families)")
        return 0
    print(json.dumps({k: v for k, v in doc.items()
                      if k not in ("duplicates", "cross_family")},
                     ensure_ascii=False, indent=2))
    return 0


if __name__ == "__main__":
    sys.exit(main())
