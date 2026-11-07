"""Failure-mode tests for the paper claim guard."""

import importlib.util
import io
import json
import re
import subprocess
import sys
from pathlib import Path
from urllib.error import URLError

import pytest

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


DOI_BIB = '''@article{first,
 title={A {Nested} Synthetic Model}, author={Example, Alice},
 year=2021, journal="Synthetic Journal", doi={10.9999/First(A)/Ω}
}
@book{second, title={Without DOI}, author={Example, Bob}, year={2020}}
'''


def doi_metadata():
    return {"DOI": "10.9999/first(a)/Ω", "title": ["A Nested Synthetic Model"],
            "container-title": ["Synthetic Journal"],
            "author": [{"given": "Alice", "family": "Example"}],
            "issued": {"date-parts": [[2020]]},
            "published-print": {"date-parts": [[2021, 2]]}}


def test_bib_first_entry_nested_values_and_non_doi_denominator(tmp_path):
    mod = load_script()
    make_paper(tmp_path)
    (tmp_path / "references.bib").write_text(DOI_BIB, encoding="utf-8")
    report = mod.check_dois(tmp_path, {"10.9999/first(a)/Ω": doi_metadata()})
    assert (report["entries"], report["doi_entries"], report["without_doi"]) == (2, 1, 1)
    assert report["results"] == [{"key": "first", "doi": "10.9999/First(A)/Ω", "status": "MATCH", "issues": []}]


@pytest.mark.parametrize("bad", [
    '@article{first, title={unclosed}',
    '@article{first, title=macro}',
    '@article{first, title="a" # "b"}',
    '@string{macro="a"}',
    '@article{first, title={a}, title={b}}',
    '@article{first,title={a}}\n@article{first,title={b}}',
])
def test_unsupported_or_duplicate_bib_never_disappears_from_denominator(bad):
    with pytest.raises(ValueError):
        load_script().bib_entries(bad)


@pytest.mark.parametrize("change,issue", [
    ({"title": ["Model"]}, "TITLE_DIFFERS"),
    ({"title": ["完全不同的中文标题"]}, "TITLE_DIFFERS"),
    ({"DOI": "10.9999/different"}, "DOI_IDENTITY_MISMATCH"),
    ({"DOI": "10.9999/first(a)/ω"}, "DOI_IDENTITY_MISMATCH"),
    ({"author": [{"given": "Bob", "family": "Example"}]}, "AUTHOR_DIFFERS"),
    ({"author": []}, "AUTHOR_MISSING"),
    ({"issued": {}, "published-print": {}}, "YEAR_MISSING"),
    ({"issued": {"date-parts": [[2019]]}, "published-print": {}}, "YEAR_DIFFERS"),
    ({"container-title": ["Other Journal"]}, "JOURNAL_DIFFERS"),
])
def test_doi_partial_titles_wrong_identity_and_missing_metadata_cannot_match(change, issue):
    mod = load_script()
    fields = mod.bib_entries(DOI_BIB)["first"]
    assert issue in mod.compare_doi_metadata(fields, dict(doi_metadata(), **change))


def test_doi_transport_encodes_the_entire_identifier(monkeypatch):
    mod = load_script()
    requests = []
    def fake_open(request, timeout):
        requests.append((request.full_url, timeout))
        return io.StringIO(json.dumps({"message": doi_metadata()}))
    monkeypatch.setattr(mod, "urlopen", fake_open)
    assert mod.fetch_doi_metadata("10.9999/First(A)/Ω")["DOI"] == doi_metadata()["DOI"]
    assert requests == [("https://api.crossref.org/works/10.9999%2FFirst%28A%29%2F%CE%A9", 20)]


def test_doi_transport_failure_is_unverified(monkeypatch, tmp_path):
    mod = load_script()
    (tmp_path / "references.bib").write_text(DOI_BIB, encoding="utf-8")
    def unavailable(_doi):
        raise URLError("synthetic unavailable service")
    monkeypatch.setattr(mod, "fetch_doi_metadata", unavailable)
    result = mod.check_dois(tmp_path)["results"][0]
    assert result["status"] == "UNVERIFIED"
    assert "URLError" in result["issues"][0]


def test_doi_cli_uses_paper_directory_and_returns_nonzero_for_unresolved(tmp_path):
    paper = tmp_path / "paper"
    paper.mkdir()  # DOI mode needs the bibliography, not a TeX paper or cwd file.
    (paper / "references.bib").write_text(DOI_BIB, encoding="utf-8")
    metadata_path = tmp_path / "metadata.json"
    metadata_path.write_text(json.dumps({"10.9999/first(a)/Ω": doi_metadata()}), encoding="utf-8")
    assert run(paper, "--doi-metadata", str(metadata_path)).returncode == 0
    metadata_path.write_text("{}", encoding="utf-8")
    bad = run(paper, "--doi-metadata", str(metadata_path))
    assert bad.returncode == 1
    assert "UNVERIFIED" in bad.stdout


def test_malformed_first_bib_entry_is_a_cli_failure(tmp_path):
    paper = make_paper(tmp_path)
    (paper / "references.bib").write_text('@article{broken,title={missing', encoding="utf-8")
    metadata_path = tmp_path / "metadata.json"
    metadata_path.write_text("{}", encoding="utf-8")
    bad = run(paper, "--doi-metadata", str(metadata_path))
    assert bad.returncode == 1
    assert "DOI input error" in bad.stderr
