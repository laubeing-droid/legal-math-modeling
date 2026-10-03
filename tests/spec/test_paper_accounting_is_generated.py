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
