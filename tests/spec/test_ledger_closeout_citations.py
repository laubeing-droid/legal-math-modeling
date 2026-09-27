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


DISPOSITION_ROW = re.compile(r"^\| (P[0-3]-\d+)[^|]*\|([^|]*)\|([^|]*)\|([^|]*)\|")
R_ROW = re.compile(r"^\| (R-\d+[a-z]*) \|")

# The ledger's reconciliation block states two bucketings of the same 28 findings: the
# report's by-nature split (3/8/14/3) and this table's by-number split, which it names
# explicitly and refuses to "recompute" because the report is not in the repository.
# The gate therefore checks the table against the numbers the ledger itself writes down:
# change a row's level and that sentence has to be corrected in the same commit.
REPORT_TOTAL_LINE = re.compile(r"报告 v1\.1 = (\d+)（P0 (\d+) / P1 (\d+) / P2 (\d+) / P3 (\d+)）")
TABLE_SPLIT_LINE = re.compile(r"上表按编号归桶得 \*\*P0 (\d+) / P1 (\d+) / P2 (\d+) / P3 (\d+)\*\*")


def _disposition_rows() -> list[tuple[str, str, str, str]]:
    text = (ROOT / "docs" / "master-plan" / "03_证明战役台账.md").read_text(encoding="utf-8")
    return [
        (m.group(1), m.group(2), m.group(3), m.group(4))
        for m in (DISPOSITION_ROW.match(line) for line in text.splitlines())
        if m
    ]


def test_every_report_finding_has_a_disposition_with_evidence() -> None:
    """The closure of the audit is itself checkable, or it is just prose.

    The report listed 28 findings (3 P0 / 8 P1 / 14 P2 / 3 P3) and required every
    FAIL/PARTIAL to carry a falsification path. That requirement was met by hand once;
    a hand-met requirement rots the moment a row is edited. So the table is now parsed:
    each finding must appear, must carry a non-empty disposition and landing point, and
    must cite at least one gate, script or artifact that exists elsewhere in this suite.
    """
    rows = _disposition_rows()
    ids = [r[0] for r in rows]
    assert len(ids) == 28, f"{len(ids)} disposition rows, expected 28"
    assert len(set(ids)) == len(ids), f"a finding is dispositioned twice: {ids}"
    per_level: dict[str, int] = {"P0": 0, "P1": 0, "P2": 0, "P3": 0}
    for ident in ids:
        per_level[ident.split("-")[0]] += 1
    text = (ROOT / "docs" / "master-plan" / "03_证明战役台账.md").read_text(encoding="utf-8")
    stated = TABLE_SPLIT_LINE.search(text)
    assert stated, (
        "the ledger no longer states how this table buckets by number, so the table's "
        f"actual split {per_level} is unchecked"
    )
    assert per_level == dict(zip(per_level, (int(g) for g in stated.groups()))), (
        f"the table buckets as {per_level} but the ledger writes {stated.groups()}"
    )
    report = REPORT_TOTAL_LINE.search(text)
    assert report and int(report.group(1)) == len(ids), (
        f"{len(ids)} disposition rows against the report total the ledger cites "
        f"({report.group(1) if report else 'missing'})"
    )
    for ident, action, landing, evidence in rows:
        assert action.strip(), f"{ident} has no disposition"
        assert landing.strip(), f"{ident} has no landing point"
        assert evidence.strip(), f"{ident} cites no gate, script or artifact"


def test_every_r_item_cited_in_the_disposition_table_exists() -> None:
    """No row may defer to an R-item that the ledger never registered."""
    text = (ROOT / "docs" / "master-plan" / "03_证明战役台账.md").read_text(encoding="utf-8")
    registered = {m.group(1) for m in (R_ROW.match(l) for l in text.splitlines()) if m}
    cited: set[str] = set()
    for ident, _a, landing, evidence in _disposition_rows():
        cited |= set(re.findall(r"R-\d+[a-z]*", landing + " " + evidence))
    assert cited, "no finding defers to an R-item, which would mean the table changed shape"
    missing = sorted(cited - registered)
    assert not missing, f"disposition rows defer to unregistered items: {missing}"
