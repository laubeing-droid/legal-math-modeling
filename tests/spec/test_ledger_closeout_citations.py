"""The audit close-out table must not become the next unverified claim.

The 28-finding reconciliation in `03_证明战役台账.md` names gate tests and file
paths as its evidence. A test name that does not exist, or a path that is not in
the tree, is the same defect the audit was about -- a claim with a citation that
leads nowhere -- so the table is checked against the repository it cites.
"""

from __future__ import annotations

import re
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
LEDGER = ROOT / "docs" / "master-plan" / "03_证明战役台账.md"

TABLE_HEAD = "### 28 条发现逐条对账"
TEST_NAME_RE = re.compile(r"\btest_[a-zA-Z0-9_]+\b")
TEST_FILE_RE = re.compile(r"tests/[^\s`，、）)]+\.py")
BACKTICK_RE = re.compile(r"`([^`]+)`")


def _table() -> str:
    text = LEDGER.read_text(encoding="utf-8")
    assert TABLE_HEAD in text, "the finding-by-finding table was removed from the ledger"
    start = text.index(TABLE_HEAD)
    rest = text[start + len(TABLE_HEAD):]
    end = rest.index("\n## ")
    return rest[:end]


def _defined_test_names() -> set[str]:
    listing = subprocess.run(
        ["git", "ls-files", "-z", "tests/*.py"],
        cwd=ROOT, capture_output=True, text=True, encoding="utf-8", check=True,
    )
    names: set[str] = set()
    for rel in filter(None, listing.stdout.split("\0")):
        names.add(Path(rel).stem)  # a citation may name the file instead of a function
        for line in (ROOT / rel).read_text(encoding="utf-8").splitlines():
            m = re.match(r"def (test_[a-zA-Z0-9_]+)", line)
            if m:
                names.add(m.group(1))
    return names


def _undefined_gates(table: str, defined: set[str]) -> list[str]:
    cited = {n for n in TEST_NAME_RE.findall(table) if not n.endswith("_") and "*" not in n}
    return sorted(cited - defined)


def _missing_paths(table: str) -> list[str]:
    missing = []
    for token in BACKTICK_RE.findall(table):
        if "/" not in token or token.startswith("git ") or "..." in token or "{" in token:
            continue
        # `tests/x.py::test_y` is the most precise citation there is, so support it:
        # the file part is checked here and the test name by the gate above.
        candidate = token.split(" ")[0].split("::")[0]
        if candidate.startswith(("docs/", "proofs/", "scripts/", "theory/", "tests/")):
            if not (ROOT / candidate).exists():
                missing.append(candidate)
    return missing


def test_every_gate_named_in_the_table_exists() -> None:
    missing = _undefined_gates(_table(), _defined_test_names())
    assert not missing, f"the ledger cites gates that are not defined: {missing}"


def test_gate_citation_rule_rejects_a_fabricated_name() -> None:
    """Falsification: without this the table could cite anything and stay green."""

    defined = _defined_test_names()
    assert _undefined_gates("x | `test_a_gate_that_was_never_written` |", defined) == [
        "test_a_gate_that_was_never_written"
    ]
    assert _undefined_gates("x | `test_bucket_headers_match_row_counts` |", defined) == []


def test_path_citation_rule_rejects_a_fabricated_file() -> None:
    assert _missing_paths("`docs/master-plan/03_证明战役台账.md`") == []
    assert _missing_paths("`docs/master-plan/no_such_ledger.md`") == [
        "docs/master-plan/no_such_ledger.md"
    ]


def test_wildcard_gate_citations_match_a_real_test() -> None:
    defined = _defined_test_names()
    for token in TEST_NAME_RE.findall(_table()) + re.findall(r"test_[a-zA-Z0-9_]*\*", _table()):
        if token.endswith("_"):  # e.g. "test_crosscut_" prefix citations
            assert any(n.startswith(token) for n in defined), f"no gate starts with {token}"


def test_every_test_file_cited_in_the_table_exists() -> None:
    for rel in set(TEST_FILE_RE.findall(_table())):
        assert (ROOT / rel).exists(), f"ledger cites a missing file: {rel}"


def test_every_path_cited_in_the_table_exists() -> None:
    missing = _missing_paths(_table())
    assert not missing, f"ledger cites paths that are not in the tree: {missing}"
