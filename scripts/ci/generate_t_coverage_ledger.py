#!/usr/bin/env python3
"""Generate the T-spectrum coverage ledger from the Lean carriers themselves.

Why this exists: the ledger used to be hand-written, so a row could be flipped
to ``COVERED``/``FULL`` without anyone adding an anchor. Qoder audit P0-1/P0-2
came from exactly that (127/127 rows claimed ``FULL`` while 124 of them named no
theorem at all, and one row pointed a sentencing target at an interpretation
theorem). The ledger is now a generated artifact: every claim has to be
re-derivable from the ``namespace T##`` block that carries it.

Coverage grades are mechanical, read off the anchored block:

* ``GENERAL``        - the statement binds variables and the proof does real
                       induction/arithmetic/rewriting work.
* ``DEF_PROJECTION`` - the statement binds variables but the proof is a
                       definitional read-back (``rfl``, ``cases x <;> rfl``,
                       ``exact h``), i.e. it restates a definition or a field.
* ``WITNESS``        - the statement has no variables at all: a literal example.

``coverage`` is ``FULL`` only when every anchor is ``GENERAL`` and the anchored
block carries no downgrade marker; otherwise ``PARTIAL``. The source markers
``降级注`` (recorded downgrade) and ``完整陈述仍缺`` (what the full statement
still needs) are copied into the row so the paper's number and the Lean comment
cannot drift apart again.
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parents[2]
LEAN_BASE = ROOT / "proofs" / "lean" / "juris_lean"
BATCH_DIR = LEAN_BASE / "JurisLean" / "Genealogy" / "TSpectrum"
LEDGER = ROOT / "theory" / "spec" / "lh_alignment" / "t_p_coverage.jsonl"

BATCH_MODULE = "JurisLean.Genealogy.TSpectrum.Batch{}"

# Secondary carriers: a T target may legitimately be carried by an older
# Genealogy namespace as well. Each entry was verified against the source
# comment of that namespace. T112 is deliberately absent: its previous
# Part4 anchor (``isolated_branch_preserved``) is about the five
# interpretation constructors, not about the two sentencing tracks, and was
# removed as a false anchor.
EXTRA_CARRIERS: dict[str, list[tuple[str, str, str]]] = {
    "T122": [("JurisLean.Genealogy.Part4", "isolated_branch_preserved", "SPECIALIZATION")],
    "T123": [("JurisLean.Genealogy.Part4", "pinned_reading_immune_to_low_attack", "SPECIALIZATION")],
}

# Python-side assets that the T target also depends on. Recorded separately so
# a Python module can never be counted as a Lean carrier.
PY_ASSETS: dict[str, list[str]] = {
    "T125": ["theory/spec/action_decision.py"],
    "T126": ["theory/spec/action_decision.py"],
    "T112": ["theory/spec/action_decision.py"],
    "T02": ["theory/spec/ontology_v3.py"],
    "T122": ["theory/legal_interpretation.py"],
}

def strip_comments(text: str) -> str:
    """Remove Lean comments before grading a carrier.

    Without this, prose inside a downgrade or strength note ("cases",
    "constructor", "rw") is read as a tactic and silently moves a carrier
    between grades — the ledger would then describe the comments, not the proof.
    """
    out_lines: list[str] = []
    depth = 0
    for line in text.splitlines():
        res: list[str] = []
        i = 0
        in_string = False
        while i < len(line):
            ch = line[i]
            nxt = line[i + 1] if i + 1 < len(line) else ""
            if depth > 0:
                if ch == "/" and nxt == "-":
                    depth += 1
                    i += 2
                    continue
                if ch == "-" and nxt == "/":
                    depth -= 1
                    i += 2
                    continue
                i += 1
                continue
            if not in_string and ch == "-" and nxt == "-":
                break
            if not in_string and ch == "/" and nxt == "-":
                depth += 1
                i += 2
                continue
            if ch == '"':
                in_string = not in_string
            res.append(ch)
            i += 1
        out_lines.append("".join(res) if depth == 0 else "")
    return "\n".join(out_lines)


NS_BLOCK = re.compile(r"^namespace (T\d+)\n(.*?)^end \1$", re.M | re.S)
THEOREM_RE = re.compile(r"^theorem ([^\s(:{]+)(.*?)(?=^(?:theorem|namespace|end|def|structure|inductive)\b|\Z)", re.M | re.S)
DOWNGRADE = "降级注"
MISSING_FULL = "完整陈述仍缺"

HEAVY_PROOF = re.compile(
    r"\b(induction|omega|linarith|norm_num|nlinarith|rcases|obtain|rw|funext|ext\b"
    r"|constructor|have|calc|suffices|by_cases)\b"
)
BINDER = re.compile(r"[({]|∀")


def statement_of(body: str) -> str:
    """Return the proposition part of a theorem body (drop the proof)."""
    idx = body.find(":=")
    return body if idx < 0 else body[:idx]


def proof_of(body: str) -> str:
    idx = body.find(":=")
    return "" if idx < 0 else body[idx + 2:]


def has_binders(stmt: str) -> bool:
    """Does the statement actually quantify over something?

    The previous rule searched the whole proposition for `(`, `{` or `∀`. That mislabels a
    binder-free literal such as `theorem foo : (0 : Nat) = 0 := rfl` as "quantified", because
    the parentheses belong to a type ascription INSIDE the conclusion -- 88 of the 127 targets
    were carried by exactly that kind of literal and graded DEF_PROJECTION, which reads like
    "a general statement proved definitionally" and is in fact "one fixed example".

    The shape to respect is `theorem NAME <binders> : conclusion`. Binders count only when they
    appear BEFORE the first top-level colon (brackets nested at depth > 0 are inside a type, so
    their colons do not end the binder run), or when the conclusion itself begins with `∀`
    (`theorem foo : ∀ x, P x` is still a general statement). Parameters may wrap across lines,
    so the scan runs over the whole statement with a depth counter, not line by line -- a
    first-line-only version silently demoted the six real induction carriers to WITNESS, which
    is how I caught it here.

    The rule can only move grades DOWN (GENERAL/DEF_PROJECTION -> WITNESS) relative to the old
    one on literals; narrowing the account is allowed, widening it is not.
    """
    body = stmt.split(":=", 1)[0]
    depth = 0
    seen_colon = False
    i = 0
    while i < len(body):
        ch = body[i]
        if ch in "({[":
            if seen_colon and depth == 0:
                break
            depth += 1
            if depth == 1 and not seen_colon:
                return True
        elif ch in ")}]":
            depth = max(0, depth - 1)
        elif ch == ":" and depth == 0:
            seen_colon = True
            rest = body[i + 1:].lstrip()
            if rest.startswith("∀") or rest.startswith("forall"):
                return True
        elif ch == "∀" and depth == 0 and not seen_colon:
            return True
        i += 1
    return False


def grade_theorem(body: str) -> str:
    stmt = statement_of(body)
    tail = proof_of(body)
    if not has_binders(stmt):
        return "WITNESS"
    if HEAVY_PROOF.search(tail):
        return "GENERAL"
    return "DEF_PROJECTION"


def scan_batches() -> dict[str, dict[str, Any]]:
    found: dict[str, dict[str, Any]] = {}
    for path in sorted(BATCH_DIR.glob("Batch*.lean")):
        batch = path.stem[len("Batch"):]
        text = path.read_text(encoding="utf-8")  # raw: downgrade markers live in comments
        for match in NS_BLOCK.finditer(text):
            tid, block = match.group(1), match.group(2)
            carriers = []
            # Names and grades come from the comment-stripped block, so prose
            # mentioning a tactic cannot move a carrier between grades; the
            # downgrade markers themselves are comments, so they are read from
            # the raw block.
            code_block = strip_comments(block)
            for th in THEOREM_RE.finditer(code_block):
                carriers.append(
                    {
                        "module": BATCH_MODULE.format(batch),
                        "theorem": th.group(1),
                        "proof_grade": grade_theorem(th.group(2)),
                        "relation": "EXACT",
                    }
                )
            found[tid] = {
                "carriers": carriers,
                "downgrade_noted": DOWNGRADE in block,
                "full_statement_missing": MISSING_FULL in block,
                "file": str(path.relative_to(ROOT)).replace("\\", "/"),
            }
    return found


def load_titles() -> list[dict[str, Any]]:
    if not LEDGER.exists():
        raise SystemExit(f"missing prior ledger to source titles from: {LEDGER}")
    return [
        json.loads(line)
        for line in LEDGER.read_text(encoding="utf-8").splitlines()
        if line.strip()
    ]


def t_ids_in_order() -> list[str]:
    return [f"T{i:02d}" if i < 10 else f"T{i}" for i in range(1, 128)]


def build_rows() -> list[dict[str, Any]]:
    scanned = scan_batches()
    prior = {r["t_id"]: r for r in load_titles()}
    want = t_ids_in_order()

    unowned = [t for t in want if t not in scanned]
    if unowned:
        raise SystemExit(f"T targets without a Lean namespace block: {unowned}")

    rows: list[dict[str, Any]] = []
    for tid in want:
        info = scanned[tid]
        anchors = list(info["carriers"])
        for module, theorem, relation in EXTRA_CARRIERS.get(tid, []):
            src = LEAN_BASE / (module.replace(".", "/") + ".lean")
            if not src.exists():
                raise SystemExit(f"{tid}: extra carrier module missing: {module}")
            if not re.search(r"^theorem " + re.escape(theorem) + r"\b", src.read_text(encoding="utf-8"), re.M):
                raise SystemExit(f"{tid}: extra carrier theorem not found in {module}: {theorem}")
            block_grade = "DEF_PROJECTION"
            anchors.append(
                {"module": module, "theorem": theorem, "proof_grade": block_grade, "relation": relation}
            )
        if not anchors:
            raise SystemExit(f"{tid}: namespace block carries no theorem")

        grades = {a["proof_grade"] for a in anchors}
        all_general = grades == {"GENERAL"}
        coverage = "FULL" if (all_general and not info["downgrade_noted"]) else "PARTIAL"
        prior_row = prior.get(tid, {})
        for a in anchors:
            if a["relation"] == "EXACT":
                a["coverage"] = coverage
            else:
                a["coverage"] = "SPECIALIZED"
        open_reason = None
        if coverage != "FULL":
            parts = []
            if info["downgrade_noted"]:
                parts.append("anchored block records a 降级注")
            if info["full_statement_missing"]:
                parts.append("anchored block records 完整陈述仍缺")
            if grades - {"GENERAL"}:
                parts.append("carrier grade " + "/".join(sorted(grades - {"GENERAL"})))
            open_reason = "carrier present; full T statement not closed: " + "; ".join(parts)

        rows.append(
            {
                "schema_version": "t_p_coverage.v2",
                "t_id": tid,
                "t_title": prior_row.get("t_title", ""),
                "layer": prior_row.get("layer", ""),
                "carrier_file": info["file"],
                "downgrade_noted": info["downgrade_noted"],
                "full_statement_missing": info["full_statement_missing"],
                "python_assets": PY_ASSETS.get(tid, []),
                "p_coverage": [
                    {
                        "p_id": a["theorem"],
                        "module": a["module"],
                        "theorem": a["theorem"],
                        "relation": a["relation"],
                        "coverage": a["coverage"],
                        "proof_grade": a["proof_grade"],
                    }
                    for a in anchors
                ],
                "status": "COVERED",
                "open_reason": open_reason,
            }
        )
    return rows


def serialize(rows: list[dict[str, Any]]) -> str:
    return "".join(
        json.dumps(r, ensure_ascii=False, sort_keys=False) + "\n" for r in rows
    )


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--output", default=str(LEDGER))
    ap.add_argument("--check", action="store_true", help="fail if the on-disk ledger is not what the sources imply")
    ap.add_argument("--summary", action="store_true")
    args = ap.parse_args()

    rows = build_rows()
    payload = serialize(rows)
    out = Path(args.output)
    if args.check:
        current = LEDGER.read_text(encoding="utf-8") if LEDGER.exists() else ""
        if current != payload:
            changed = [
                r["t_id"]
                for old, new in zip(load_titles(), rows)
                if old.get("p_coverage") != new["p_coverage"]
            ]
            print(f"ledger is stale against Lean carriers; {len(changed)} rows differ", file=sys.stderr)
            print(f"first differing rows: {changed[:10]}", file=sys.stderr)
            return 1
    else:
        out.write_text(payload, encoding="utf-8", newline="\n")
        print(f"wrote {out} ({len(rows)} rows)")

    if args.summary:
        from collections import Counter

        cov = Counter(c["coverage"] for r in rows for c in r["p_coverage"])
        grade = Counter(c["proof_grade"] for r in rows for c in r["p_coverage"])
        print("coverage:", dict(cov))
        print("proof grades:", dict(grade))
        print("rows with downgrade marker:", sum(1 for r in rows if r["downgrade_noted"]))
        print("rows missing full statement:", sum(1 for r in rows if r["full_statement_missing"]))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
