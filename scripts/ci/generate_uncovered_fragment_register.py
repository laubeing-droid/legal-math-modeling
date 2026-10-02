#!/usr/bin/env python3
"""Generate the uncovered-fragment register for this wave's Seams modules.

Why generated: the fragment lists live in the Lean files as their own closing sections.
Transcribing them into a hand-written document creates a second account that goes stale the
moment a proof lands, and a stale "what is missing" list is worse than none -- it reads as a
claim about the gaps. This script copies each section verbatim, so the register is as current
as the source it is generated from.

Not wired as a --check gate on purpose, and the register says so: the modules it reads are
being edited this same day, so a check that fails on every proof step would train people to
ignore it. Wiring becomes correct once the wave's modules stop moving.
"""
from __future__ import annotations

import argparse
import io
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
SEAMS = ROOT / "proofs" / "lean" / "juris_lean" / "JurisLean" / "Seams"
OUT = ROOT / "docs" / "master-plan" / "基线" / "未覆盖片段登记.md"

#: the modules this wave authored or rewrote; the register is scoped to the wave, not to the
#: whole tree, because 18 of 302 Lean files carry such a section and a tree-wide claim would be
#: a claim about files nobody touched here.
WAVE_MODULES = [
    "Transitions.lean",
    "ReductionConditions2.lean",
    "BurdenStatutes.lean",
    "LegacyConeBridge.lean",
    "UnifiedInstance.lean",
    "StatuteChain.lean",
    "SanctionInterest.lean",
]

MARKER = "未覆盖"
MAX_LINES = 30


def extract(path: Path) -> tuple[str, int, list[str]]:
    """Return the section that declares uncovered fragments, as written in the source.

    A section *header* is preferred over any mention: the word also appears inside prose and
    inside the self-describing boundary theorem, and anchoring on the last mention copied a
    theorem statement into a list that is supposed to name gaps.
    """
    text = path.read_text(encoding="utf-8", errors="replace")
    lines = text.splitlines()
    headers = [i for i, line in enumerate(lines)
               if MARKER in line and line.lstrip().startswith(("#", "-", "/"))
               and not line.lstrip().startswith(("theorem ", "def ", "lemma ", ">"))]
    hits = headers or [i for i, line in enumerate(lines) if MARKER in line]
    if not hits:
        return "", 0, []
    start = hits[-1] if headers else hits[-1]
    body: list[str] = []
    for line in lines[start + 1:start + MAX_LINES]:
        stripped = line.lstrip("-/! ").rstrip()
        if not stripped:
            continue
        if stripped.startswith(("theorem ", "def ", "lemma ", "structure ", "end ", "namespace ")):
            break
        body.append(stripped)
    return lines[start].strip(), start + 1, body


def build() -> str:
    parts = [
        "# 未覆盖片段登记（生成件，勿手改）",
        "",
        "> 生成命令：`python scripts/ci/generate_uncovered_fragment_register.py --write`",
        ">",
        "> 本卷由 `scripts/ci/generate_uncovered_fragment_register.py` 从各 Lean 件自己的收尾段",
        "> **逐字抽取**，不是任何人抄写的清单。哪一件补上了证明，重跑一次本脚本，条目自己消失。",
        ">",
        "> **本登记尚未接成 --check 门**：本轮这几件仍在动，每次补证明都会让登记变动，",
        "> 一道天天因进步而红的门只会训练人去忽略它。等这一波模块停下来再接线才是对的。",
        "",
        "| 文件 | 是否存在未覆盖段 | 抽取起点 |",
        "|------|------------------|----------|",
    ]
    detail: list[str] = []
    for name in WAVE_MODULES:
        path = SEAMS / name
        if not path.is_file():
            parts.append(f"| {name} | 文件不存在 | — |")
            detail.append(f"\n## {name}\n\n文件尚未落地（写手未完成）。\n")
            continue
        head, line_no, body = extract(path)
        if not body:
            parts.append(f"| {name} | **缺** | — |")
            detail.append(
                f"\n## {name}\n\n**缺未覆盖片段声明**：该件没有把'本件到不了哪里'写进源码。\n"
                "这比写错更糟——写错会被读出来，不写不会被读出来。\n"
            )
            continue
        rel = f"Seams/{name}:{line_no}"
        parts.append(f"| {name} | 有 | {rel} |")
        detail.append(f"\n## {name}  （源：`{rel}` 起）\n")
        for line in body:
            detail.append(f"> {line}\n")
    parts.append("\n---\n")
    parts.extend(detail)
    parts.append(
        "\n## 收尾口径\n\n"
        "1. 本登记只覆盖表中所列文件，不外推到全仓：全仓 302 个 Lean 件里 18 个带此类段落，"
        "其余 284 个的未覆盖面**本卷不作任何主张**。\n"
        "2. 段落在源文件里是散文，所以「哪些片段没建模」的最终依据仍是源文件本身；"
        "本卷的价值是把「漏在哪里」变成一处可读、可 diff、可随源码自动更新的清单。\n"
    )
    return "".join(p if p.endswith("\n") else p + "\n" for p in parts)


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--write", action="store_true")
    ap.add_argument("--check", action="store_true")
    args = ap.parse_args()

    generated = build()
    if args.write:
        OUT.parent.mkdir(parents=True, exist_ok=True)
        OUT.write_text(generated, encoding="utf-8", newline="\n")
        print(f"wrote {OUT.relative_to(ROOT).as_posix()}")
        return 0
    if args.check:
        if not OUT.is_file():
            print("register missing; run --write")
            return 1
        if OUT.read_text(encoding="utf-8") != generated:
            print("register is stale against the sources; run --write")
            return 1
        print("register current")
        return 0
    print(generated)
    return 0


if __name__ == "__main__":
    sys.exit(main())
