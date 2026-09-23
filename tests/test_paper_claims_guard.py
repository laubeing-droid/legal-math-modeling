"""Failure-mode tests for the paper claim guard."""

import importlib.util
import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
SCRIPT = ROOT / "scripts" / "check_paper_claims.py"

BIB = "@article{Dung1995,\n title={Acceptability},\n author={Dung},\n year={1995}\n}\n"
SHA = "2a1d33df353a005dffc5d8b95faa591524e2636e"
TEX = (
    "\\section{T}\n"
    "This is \\formalized{} \\citep{Dung1995}; "
    f"145 declarations were audited at `{SHA}`.\n"
    "\\begin{equation}\\label{eq:a}\\dotfill\\end{equation}\n"
    "By Equation~\\eqref{eq:a}, done.\n"
)


def make_paper(tmp_path: Path, tex: str = TEX):
    (tmp_path / "sections").mkdir(parents=True, exist_ok=True)
    (tmp_path / "main.tex").write_text("\\documentclass{article}\n", encoding="utf-8")
    (tmp_path / "sections" / "01.tex").write_text(tex, encoding="utf-8")
    (tmp_path / "references.bib").write_text(BIB, encoding="utf-8")
    return tmp_path


def run(paper_dir: Path, *extra):
    return subprocess.run(
        [sys.executable, str(SCRIPT), "--paper-dir", str(paper_dir), *extra],
        capture_output=True,
        text=True,
    )


def load_script():
    spec = importlib.util.spec_from_file_location("cpc", SCRIPT)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


def test_fully_referenced_subject_bound_file_passes(tmp_path):
    assert run(make_paper(tmp_path)).returncode == 0


def test_dropped_label_regresses_against_baseline(tmp_path):
    base = tmp_path / "base.json"
    run(make_paper(tmp_path), "--json-out", str(base))
    make_paper(tmp_path, TEX.replace("This is \\formalized{} ", ""))
    bad = run(tmp_path, "--baseline", str(base))
    assert bad.returncode == 1
    assert "label count dropped" in bad.stdout


def test_undefined_citation_is_fail_closed(tmp_path):
    make_paper(tmp_path, TEX.replace("\\citep{Dung1995}", "\\citep{NotInBib2026}"))
    bad = run(tmp_path)
    assert bad.returncode == 1
    assert "absent from references.bib" in bad.stdout


def test_unbound_count_is_fail_closed(tmp_path):
    make_paper(tmp_path, TEX.replace(f"`{SHA}`", "the release build"))
    bad = run(tmp_path)
    assert bad.returncode == 1
    assert "subject SHA" in bad.stdout


def test_dead_equation_label_is_reported(tmp_path):
    make_paper(tmp_path, TEX + "\\begin{equation}\\label{eq:unused}\\dotfill\\end{equation}\n")
    bad = run(tmp_path)
    assert bad.returncode == 1
    assert "eq:unused" in bad.stdout


def test_equation_numbering_is_not_a_release_count():
    mod = load_script()
    assert not re.search(r"\b(?:145|27|46)\b", mod.prose_only("Equations (26)–(27) \\tag{27}"))
    assert not re.search(r"\b27\b", mod.prose_only("audited in `FORMALIZED` case (27)."))


def test_label_markup_variants_all_counted():
    mod = load_script()
    tex = len(mod.TEX_LABEL_RE.findall("\\formalized{} \\derived{} \\conjectured{}"))
    md = len(mod.MD_LABEL_RE.findall("**FORMALIZED.** `DERIVED` **conjecture**"))
    assert (tex, md) == (3, 3)
