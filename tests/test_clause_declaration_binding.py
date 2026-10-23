"""The 50-clause ledger discharges live scope fields only from the re-extracted tip audit."""

from __future__ import annotations

import importlib.util
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
TOOL = ROOT / "scripts" / "ci" / "check_clause_declaration_binding.py"

_spec = importlib.util.spec_from_file_location("check_clause_declaration_binding", TOOL)
checker = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(checker)


def test_live_ledger_reextracts_axiom_audit_and_empties_scope_fields() -> None:
    proc = subprocess.run(
        [sys.executable, str(TOOL)],
        cwd=ROOT,
        capture_output=True,
        text=True,
        encoding="utf-8",
    )
    assert proc.returncode == 0, proc.stdout + proc.stderr
    assert "formal_ci_run_id 50" in proc.stdout
    assert "formal_ci_CI_NOT_RUN 0" in proc.stdout
    assert "legal_rows_daihe 0" in proc.stdout
    assert "legal_rows_wufayuan 7" in proc.stdout
    assert "exact_scope_empty 50" in proc.stdout
    assert "remaining_obligations_empty 50" in proc.stdout
    assert "axiom_audit PASS_REEXTRACTED_STANDARD_AXIOMS_ONLY" in proc.stdout
    assert "NOT_REEXTRACTED_FROM_ARTIFACT" not in proc.stdout


def test_daihe_row_rejects_a_filled_law_or_url() -> None:
    bad_law = "U01.4｜中华人民共和国民法典｜待核｜待核｜待核｜待核｜模型一句｜A.lean:1"
    bad_url = "U01.4｜待核｜待核｜待核｜https://example.com/a｜待核｜模型一句｜A.lean:1"
    assert checker.legal_line_errors(bad_law, "U01.4")
    assert checker.legal_line_errors(bad_url, "U01.4")


def test_wufayuan_requires_a_reason_and_rejects_an_article_number() -> None:
    bare = "U04.1｜无法源｜无法源｜无法源｜无法源｜无法源｜预测均值｜Probability.lean:155"
    cited = "U04.1｜无法源：见第1条｜无法源｜无法源｜无法源｜无法源｜预测均值｜Probability.lean:155"
    assert any("no reason" in error for error in checker.legal_line_errors(bare, "U04.1"))
    assert any("article" in error for error in checker.legal_line_errors(cited, "U04.1"))


def test_complete_row_rejects_an_unofficial_host() -> None:
    row = (
        "U01.4｜中华人民共和国民法典｜第一千条｜2020年公布｜"
        "https://example.com/law｜摘录｜模型一句｜A.lean:1"
    )
    errors = checker.legal_line_errors(row, "U01.4")
    assert errors
    assert any("unofficial" in error for error in errors)


def test_complete_row_accepts_the_statute_database_host() -> None:
    row = (
        "U01.4｜示例法｜第一条｜2020-01-01公布，2021-01-01施行｜"
        "https://flk.npc.gov.cn/detail.html｜原文摘录｜模型一句｜A.lean:1"
    )
    assert checker.legal_line_errors(row, "U01.4") == []


def test_shell_proof_is_rejected() -> None:
    text = "theorem witness : True := by\n  trivial\n"
    assert checker.body_violations(text, "witness")


def test_pass_token_in_obligations_is_rejected() -> None:
    assert checker.PASS_TOKEN.search("remaining obligations stay open") is None
    assert checker.PASS_TOKEN.search("marked PASS")
