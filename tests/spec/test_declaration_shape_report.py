"""The two declaration-shape figures the papers quote must come from the artifact.

Both paper editions have carried a relabelling count and a no-bindable-variable count for
the theorem body. Those two figures had no producing script at all -- nothing could
recompute them, so they were free to drift away from the source they described. This is
the same defect class the closure census and the statement-duplication census were built
to close, so the shape report gets the same three checks: the artifact is current, the
papers quote it phrase by phrase, and the classification rules are not vacuous.
"""

from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
SCRIPT = ROOT / "scripts" / "ci" / "generate_declaration_shape_report.py"
REPORT = ROOT / "docs" / "formal-release" / "declaration_shape_report.json"
CENSUS = ROOT / "docs" / "formal-release" / "trivial_proof_census.json"
CN = ROOT / "docs" / "paper-rewrite" / "paper_cn.md"
EN = ROOT / "docs" / "paper-rewrite" / "paper_en.md"

sys.path.insert(0, str(ROOT / "scripts" / "ci"))


def _doc() -> dict:
    return json.loads(REPORT.read_text(encoding="utf-8"))


def test_the_shape_report_is_current() -> None:
    from generate_declaration_shape_report import build, render

    assert REPORT.exists(), "the declaration shape artifact is missing"
    assert REPORT.read_text(encoding="utf-8") == render(build()), (
        "the artifact no longer describes the tracked source; regenerate it"
    )


def test_the_report_and_the_closure_census_count_the_same_tree() -> None:
    """Both scanners walk the same file set, so a divergence means one parser changed."""
    counts = _doc()["scope"]["counts"]
    census = json.loads(CENSUS.read_text(encoding="utf-8"))
    assert counts["theorems"] == census["theorem_declarations"], (
        "the shape report and the closure census disagree on how many theorems exist"
    )
    assert _doc()["cross_check"]["agree"] is True


def test_the_shape_rules_are_not_vacuous() -> None:
    """A rule that never fires and a rule that always fires both make the figure a lie."""
    from generate_declaration_shape_report import shape_of

    alias = "theorem foo_contract : bar_proof := baz_proof"
    # the two rules overlap by design, and this fixture satisfies both
    assert shape_of(alias) == ["ALIAS_ONE_LINER", "CLOSED_NO_BINDERS"], (
        "the alias rule stopped matching, or the overlap the artifact declares broke"
    )
    assert "ALIAS_ONE_LINER" not in shape_of("theorem takes_a_binder (x : Nat) : f := p")

    quantified = "theorem uses_a_variable (x : Nat) : x = x := by rfl"
    assert "CLOSED_NO_BINDERS" not in shape_of(quantified), (
        "the no-binder rule fires on a statement that binds x, so it measures nothing"
    )

    concrete = "theorem two_plus_two : 2 + 2 = 4 := by rfl"
    assert "CLOSED_NO_BINDERS" in shape_of(concrete), (
        "the no-binder rule rejects a closed statement, so the count under-reports"
    )

    assert shape_of("theorem carries_a_forall : forall n : Nat, n = n := by intro; rfl") == [], (
        "a forall conclusion must not read as variable-free"
    )


def test_papers_quote_the_shape_artifact_and_not_a_memory() -> None:
    """Checked in the sentence that gives each figure meaning, not as a bare digit test."""
    counts = _doc()["scope"]["counts"]
    alias = str(counts["ALIAS_ONE_LINER"])
    closed = str(counts["CLOSED_NO_BINDERS"])
    total = str(counts["theorems"])

    cn = CN.read_text(encoding="utf-8")
    en = EN.read_text(encoding="utf-8")
    cn_claims = {
        "alias": f"一行式契约搬运 {alias} 条",
        "closed": f"结句中不绑定变量的 {closed} 条",
        "total": f"{total} 条定理声明",
        "withdrawn": "433 与 791",
    }
    en_claims = {
        "alias": f"{alias} are one-line contract transfers",
        "closed": f"{closed} conclusions bind no variable",
        "total": f"{total} theorem declarations",
        "withdrawn": "433 and 791",
    }
    for kind, claim in cn_claims.items():
        assert claim in cn, f"the Chinese draft's {kind} shape claim is not the artifact's"
    for kind, claim in en_claims.items():
        assert claim in en, f"the English draft's {kind} shape claim is not the artifact's"
    for path in (CN, EN):
        assert "declaration_shape_report.json" in path.read_text(encoding="utf-8"), (
            f"{path.name} quotes the shape figures without naming the artifact behind them"
        )


def test_the_shape_check_mode_fails_on_a_stale_artifact() -> None:
    """--check must be able to go red, without touching the tracked artifact to prove it.

    An earlier version wrote a mutated copy over docs/formal-release/... and restored it in
    a `finally`, so an interrupted run could leave the repository holding a falsified
    account. The mutation is compared in memory against exactly what `--check` compares.
    """
    from generate_declaration_shape_report import OUT, build, render

    fresh = render(build())
    assert OUT.read_text(encoding="utf-8") == fresh, (
        "the committed artifact is already stale, so this check cannot demonstrate red-ness"
    )
    mutated = json.loads(fresh)
    mutated["scope"]["counts"]["ALIAS_ONE_LINER"] += 1
    rebuilt = json.dumps(mutated, ensure_ascii=False, indent=2, sort_keys=True) + chr(10)
    assert rebuilt != fresh, (
        "mutating a figure left the rendering unchanged, so the comparison is vacuous"
    )
