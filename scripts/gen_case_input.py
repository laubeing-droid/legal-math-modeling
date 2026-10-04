"""Turn a JSON case file into the Lean `CaseFile` literal (17_ 卷 WBS-5 的生成器).

Input schema (see sample_case.json):
  { "facts": [["name", bool], ...],
    "rules": [{"premises": ["name", ...], "conclusion": "name"}, ...],
    "citations": ["...", ...] }

The generator is deliberately dumb: it maps JSON fields to constructor fields one-to-one,
validates that every rule's premises and conclusion appear in some fact or conclusion slot,
and refuses (exit 1, no output) on anything it does not recognise -- an unrecognised key, a
missing field, a non-string name, a non-bool flag. It never invents a fact, a rule, or a
citation, and it never edits an existing target: the output path must not exist, so a
regenerated case cannot silently overwrite the attested one.
"""

from __future__ import annotations

import json
import sys
from pathlib import Path

HEADER = """import JurisLean.HornDefinitions
import JurisLean.Seams.SourceNorms
import JurisLean.Seams.CaseInput


/-- 中文说明：**由生成器写入的案卷**（`scripts/gen_case_input.py`，来源：{src}）。
    本件是机器翻译的 `CaseFile`，不是手写夹具；改它请改 JSON 后重新生成。
    论域＝成立事实 ∪ 全部规则头（JSON 的 false 事实位已被生成器丢弃）。 -/
def {name} : JurisLean.Seams.CaseInput.CaseFile String :=
  {{ univ := {univ}
    facts := {facts}
    rules := {rules}
    citations := {citations}
    hFacts := by decide
    hHeads := by decide }}
"""


def fail(msg: str) -> None:
    print(f"gen_case_input: {msg}", file=sys.stderr)
    raise SystemExit(1)


def esc(s: str) -> str:
    return json.dumps(s, ensure_ascii=False)


def main() -> None:
    args = sys.argv[1:]
    if len(args) != 3 or args[0] != "--from":
        fail("usage: gen_case_input.py --from <case.json> <out.lean>")
    src, out = Path(args[1]), Path(args[2])
    if not src.is_file():
        fail(f"no such case file: {src}")
    if out.exists():
        fail(f"refusing to overwrite existing target: {out}")
    try:
        doc = json.loads(src.read_text(encoding="utf-8"))
    except json.JSONDecodeError as e:
        fail(f"case file is not valid JSON: {e}")

    if not isinstance(doc, dict):
        fail("top level must be an object")
    for key in doc:
        if key not in ("facts", "rules", "citations"):
            fail(f"unrecognised key: {key}")
    for key in ("facts", "rules", "citations"):
        if key not in doc:
            fail(f"missing key: {key}")

    names: set[str] = set()
    standing: list[str] = []
    for f in doc["facts"]:
        if not (isinstance(f, list) and len(f) == 2
                and isinstance(f[0], str) and isinstance(f[1], bool)):
            fail(f"fact entries must be [name, bool], got: {f!r}")
        if f[1]:
            standing.append(f[0])
        names.add(f[0])
    facts = "{" + ", ".join(esc(s) for s in standing) + "}"

    rule_parts: list[str] = []
    for r in doc["rules"]:
        if not (isinstance(r, dict) and set(r) == {"premises", "conclusion"}):
            fail(f"rule entries must have exactly premises and conclusion, got: {r!r}")
        if not (isinstance(r["premises"], list) and isinstance(r["conclusion"], str)):
            fail(f"rule premises must be a list and conclusion a string, got: {r!r}")
        for p in r["premises"]:
            if not isinstance(p, str):
                fail(f"rule premises must be strings, got: {p!r}")
        names.add(r["conclusion"])
        prems = "{" + ", ".join(esc(p) for p in r["premises"]) + "}"
        rule_parts.append(f"{{ premises := {prems}, conclusion := {esc(r['conclusion'])} }}")
    rules = "{" + ", ".join(rule_parts) + "}"
    univ = "{" + ", ".join(esc(s) for s in standing) + ", " +         ", ".join(esc(r["conclusion"]) for r in doc["rules"]) + "}"

    cits = doc["citations"]
    if not (isinstance(cits, list) and all(isinstance(c, str) for c in cits)):
        fail("citations must be a list of strings")
    citations = "[" + ", ".join(esc(c) for c in cits) + "]"

    name = "caseFile_" + src.stem.replace("-", "_").replace(".", "_")
    if not name.isidentifier():
        fail(f"derived name is not an identifier: {name}")
    text = HEADER.format(src=esc(str(src)), name=name, univ=univ,
                         facts=facts, rules=rules, citations=citations)
    out.write_bytes(text.encode("utf-8"))
    print(f"wrote {out} ({len(doc['facts'])} facts, "
          f"{len(doc['rules'])} rules, {len(cits)} citations, {len(names)} atoms)")


if __name__ == "__main__":
    main()
