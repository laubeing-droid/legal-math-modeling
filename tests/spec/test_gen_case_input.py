"""Tests for the case-input generator (WBS-5).

The generator's whole value is what it refuses: an unrecognised key, a wrong-typed fact, a
target that already exists. Each test feeds it a hostile input and asserts the refusal, plus
one happy-path run whose output is checked field by field against the JSON.
"""

from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
GEN = ROOT / "scripts" / "gen_case_input.py"


def run(case: dict, out: Path) -> subprocess.CompletedProcess[str]:
    src = out.with_suffix(".json")
    src.write_text(json.dumps(case, ensure_ascii=False), encoding="utf-8")
    return subprocess.run([sys.executable, str(GEN), "--from", str(src), str(out)],
                          capture_output=True, text=True)


def test_happy_path_writes_the_literal(tmp_path: Path) -> None:
    out = tmp_path / "case.lean"
    proc = run({
        "facts": [["欠款", True], ["违约", False]],
        "rules": [{"premises": ["欠款"], "conclusion": "应付"}],
        "citations": ["585条2款"],
    }, out)
    assert proc.returncode == 0, proc.stderr
    text = out.read_text(encoding="utf-8")
    assert 'facts := {"欠款"}' in text
    assert "违约" not in text.split("facts :=")[1].split("rules :=")[0]
    assert 'conclusion := "应付"' in text
    assert '"585条2款"' in text
    assert 'univ := {"欠款", "应付"}' in text
    assert "hFacts := by decide" in text


def test_unrecognised_key_is_refused(tmp_path: Path) -> None:
    out = tmp_path / "case.lean"
    proc = run({
        "facts": [], "rules": [], "citations": [],
        "verdict": "支持",
    }, out)
    assert proc.returncode == 1
    assert "unrecognised key: verdict" in proc.stderr
    assert not out.exists()


def test_wrong_typed_fact_is_refused(tmp_path: Path) -> None:
    out = tmp_path / "case.lean"
    proc = run({"facts": [["欠款", "yes"]], "rules": [], "citations": []}, out)
    assert proc.returncode == 1
    assert "fact entries must be [name, bool]" in proc.stderr


def test_missing_field_is_refused(tmp_path: Path) -> None:
    out = tmp_path / "case.lean"
    proc = run({"facts": [], "rules": []}, out)
    assert proc.returncode == 1
    assert "missing key: citations" in proc.stderr


def test_existing_target_is_never_overwritten(tmp_path: Path) -> None:
    out = tmp_path / "case.lean"
    out.write_text("-- attested bytes", encoding="utf-8")
    proc = run({"facts": [], "rules": [], "citations": []}, out)
    assert proc.returncode == 1
    assert "refusing to overwrite" in proc.stderr
    assert out.read_text(encoding="utf-8") == "-- attested bytes"


def test_the_repository_sample_still_generates(tmp_path: Path) -> None:
    out = tmp_path / "sample.lean"
    src = ROOT / "proofs" / "lean" / "juris_lean" / "cases" / "sample_case.json"
    proc = subprocess.run([sys.executable, str(GEN), "--from", str(src), str(out)],
                          capture_output=True, text=True)
    assert proc.returncode == 0, proc.stderr
    assert "3 facts" in proc.stdout
