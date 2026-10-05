"""The papers' derived-accounting figures must be reproducible, not remembered.

Both drafts carry a section that says a generator writes it from the artifacts. For most of
2026-10-03 that sentence was false: four groups of numbers were retyped by hand after every
proof that landed, and one of those readings had already gone stale before a guard noticed.
`scripts/rebind_paper_derived_accounting.py` is now that generator, so the claim is checkable:
re-running it over the committed drafts must be a no-op, and every phrase template must still
match. A template that stops matching is reported rather than skipped, otherwise the section
could keep an old number in silence -- which is the failure mode this replaces.
"""

from __future__ import annotations

import importlib.util
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
SCRIPT = ROOT / "scripts" / "rebind_paper_derived_accounting.py"


def _load():
    spec = importlib.util.spec_from_file_location("rebind_paper", SCRIPT)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def test_every_phrase_template_still_matches_its_draft() -> None:
    mod = _load()
    figures = mod.figures()
    for lang, path, specs in (
        ("cn", mod.DRAFTS["cn"], mod.cn_specs(figures)),
        ("en", mod.DRAFTS["en"], mod.en_specs(figures)),
    ):
        text = path.read_text(encoding="utf-8")
        for pattern, _replacement in specs:
            assert re.search(pattern, text), (
                f"{lang} draft no longer carries the template {pattern[:60]!r}; the phrase "
                "was reworded, so the generator cannot rebind it and the number is now "
                "hand-maintained again"
            )


def test_the_committed_drafts_are_what_the_generator_produces() -> None:
    mod = _load()
    figures = mod.figures()
    for path, specs in ((mod.DRAFTS["cn"], mod.cn_specs(figures)),
                        (mod.DRAFTS["en"], mod.en_specs(figures))):
        text = path.read_text(encoding="utf-8")
        for pattern, replacement in specs:
            text = re.sub(pattern, replacement, text)
        assert text == path.read_text(encoding="utf-8"), (
            f"{path.name} carries an accounting figure that is not the artifact's; run "
            "`python scripts/rebind_paper_derived_accounting.py --write`"
        )


def test_the_generator_reads_the_artifacts_it_claims() -> None:
    """A figures() that silently fell back to constants would green-light any prose."""
    figures = _load().figures()
    assert figures["trivial"] + figures["decide"] + figures["tactic"] == figures["total"]
    assert figures["pkg_theorems"] + figures["pkg_lemmas"] == figures["pkg_counted"]
    assert figures["audit_cmds"] + figures["outside_audit"] == figures["cmds"]
    assert figures["tracked_theorems"] >= figures["pkg_theorems"]


# Every sentence that closes the three-way partition states its own total next to it, so the
# sum can be checked without knowing which subject the sentence was written against.
# This catches the failure the template checks cannot: `apply()` reports OK as soon as a
# pattern matches *somewhere*, so a duplicate claim elsewhere -- e.g. Chapter 5's
# "全仓 3240 条定理声明里，287 条…102 条…其余 3228 条", where 287+102+3228 = 3617 --
# keeps an old total while its parts were rebound. 2026-10-05 acceptance round.
CN_PARTITION = re.compile(
    r"(\d+) 条由单一反射项闭合、(\d+) 条由纯 decide 闭合、其余 (\d+) 条含 tactic"
)
EN_PARTITION = re.compile(
    r"(\d+) close on a single reflexivity term, (\d+) close on `decide` alone, "
    r"and (\d+) carry a tactic proof"
)
TOTAL_CN = re.compile(r"(\d+) 条定理声明")
TOTAL_EN = re.compile(r"of the (\d+) declarations")


def test_each_partition_sentence_adds_up_to_its_own_total() -> None:
    """Splitting on "." is not a sentence boundary in prose that quotes `json` filenames,
    so the total is looked up in a window around the partition instead of a split piece."""
    mod = _load()
    for path, part_re, total_re in (
        (mod.DRAFTS["cn"], CN_PARTITION, TOTAL_CN),
        (mod.DRAFTS["en"], EN_PARTITION, TOTAL_EN),
    ):
        text = path.read_text(encoding="utf-8").replace("\n", " ")
        checked = 0
        for m in part_re.finditer(text):
            checked += 1
            parts = sum(int(g) for g in m.groups())
            window = text[max(0, m.start() - 500):m.end() + 50]
            totals = total_re.findall(window)
            assert totals, (
                f"{path.name}: a partition lists its three classes but no total appears "
                f"within 500 characters before it: {window[-260:]!r}"
            )
            # the total the sentence applies to is the last one stated before the classes
            assert parts == int(totals[-1]), (
                f"{path.name}: the partition is stated against {totals[-1]} declarations but "
                f"its three closure classes sum to {parts} -- the classes were rebound and "
                "the total was left at an older subject's reading"
            )
        assert checked > 0, f"{path.name}: no partition sentence found; this gate is idle"

