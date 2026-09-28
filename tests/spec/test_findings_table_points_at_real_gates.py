"""Counts written into the 28-finding table must come with a route that recomputes them.

`tests/spec/test_ledger_closeout_citations.py` already parses that table: it checks the 28
rows exist, are unique, bucket the way the ledger claims, and each cites an evidence item
that exists in the suite. What it does not ask is whether a *number* written into the
mechanism or evidence cell still describes anything. A row asserting "232 files scanned"
keeps reading true after the tool starts reporting 236, and silent numeric drift inside an
account of findings is the same defect class the audit's P0-1 was about.

So this module checks one thing, in the cells the other gate leaves open: a row may state a
figure of three digits or more in its mechanism or evidence cells only if that same row
names how to recompute it -- a script, a `--check` mode, an artifact path, an attesting CI
run, or words saying the figure floats. The finding cell is exempt because there the table
quotes the auditor's original wording, including claims this repository later voided.
"""

from __future__ import annotations

import hashlib
import re
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
LEDGER = ROOT / "docs" / "master-plan" / "03_证明战役台账.md"

TABLE_HEAD = "### 28 条发现逐条对账"
EXEMPT_MARKERS = (".py", "--check", "run ", "docs/", "现算", "浮动", "勘误", "作废", "认定")
BARE_FIGURE = re.compile(r"(?<![:.\w-])(\d{3,})(?!\w)")
ROW = re.compile(r"^\|\s*P[0-3]-")


def _rows(text: str) -> list[str]:
    start = text.index(TABLE_HEAD)
    end = text.index("\n### ", start + len(TABLE_HEAD) + 1)
    return [line for line in text[start:end].splitlines() if ROW.match(line)]


def _offenders(rows: list[str]) -> list[tuple[str, str]]:
    """Figures stranded in a live cell of a row that offers no way to recompute them."""
    out: list[tuple[str, str]] = []
    for row in rows:
        if any(marker in row for marker in EXEMPT_MARKERS):
            continue
        for cell in row.split("|")[3:]:
            for match in BARE_FIGURE.finditer(cell):
                out.append((match.group(1), cell.strip()[:60]))
    return out


def test_the_table_this_rule_reads_is_the_one_it_claims() -> None:
    """A rule that silently parses zero rows is a rule that always passes."""
    rows = _rows(LEDGER.read_text(encoding="utf-8"))
    assert len(rows) == 28, (
        f"this rule sees {len(rows)} findings; the close-out gate pins the table at 28, so "
        "a different count here means the rule stopped covering the table it describes"
    )


def test_the_rule_fires_on_a_stranded_figure_and_not_on_a_routed_one() -> None:
    """Prove the check can go red, and that the exemption is a route rather than an escape."""
    stranded = "| P9-99 sample | conclusion | mechanism holds 236 of them | evidence cell |"
    routed = "| P9-99 sample | conclusion | mechanism holds 236 of them | `tool.py --check` |"
    quoted_only = "| P9-99 sample | the auditor counted 433 of them | mechanism | evidence |"

    assert _offenders([stranded]), "a bare figure in the mechanism cell slipped through"
    assert not _offenders([routed]), "a row that names its recompute route was flagged"
    assert not _offenders([quoted_only]), (
        "the finding cell quotes the auditor and must stay exempt, or the table cannot "
        "record a voided claim with its original number"
    )


def test_no_live_cell_carries_a_figure_without_a_recompute_route() -> None:
    offenders = _offenders(_rows(LEDGER.read_text(encoding="utf-8")))
    assert not offenders, (
        f"figure quoted in a mechanism or evidence cell with no way to recompute it: {offenders}"
    )


# The archived originals make this decidable: the campaign table claims to disposition the
# audit's findings, and "all of them" was previously a claim about a document the repository
# did not hold. Both the report and its supplement are now filed verbatim under
# docs/history/evidence-archive/, so the set of finding ids is comparable rather than recalled.
ARCHIVE = ROOT / "docs" / "history" / "evidence-archive" / "20260927_qoder_audit"
REPORT_FILES = ("AUDIT_REPORT_V1_20260927.md", "AUDIT_REPORT_V1_SUPPLEMENT_1.md")
FINDING_ID = re.compile(r"\bP[0-3]-\d+\b")


def _reported_ids() -> set[str]:
    text = "".join(
        (ARCHIVE / name).read_text(encoding="utf-8") for name in REPORT_FILES
    )
    return set(FINDING_ID.findall(text))


def test_the_archive_the_rule_compares_against_is_on_file() -> None:
    for name in REPORT_FILES:
        assert (ARCHIVE / name).exists(), f"the archived audit source {name} is missing"
    assert (ARCHIVE / "README.md").exists(), (
        "the archive has no provenance note, so its text cannot be attributed"
    )


def test_the_table_dispositions_exactly_the_findings_the_report_listed() -> None:
    """Same ids, none invented, none dropped -- the objective is this equality, not a prose claim."""
    reported = _reported_ids()
    tabled = {FINDING_ID.search(row).group(0) for row in _rows(LEDGER.read_text(encoding="utf-8"))}
    assert tabled == reported, (
        f"rows with no finding behind them: {sorted(tabled - reported)}; "
        f"findings with no row: {sorted(reported - tabled)}"
    )


def test_dropping_a_finding_from_the_table_would_be_caught() -> None:
    """Prove the equality is load-bearing on a copy with one row removed."""
    rows = _rows(LEDGER.read_text(encoding="utf-8"))
    surviving = {FINDING_ID.search(r).group(0) for r in rows[1:]}
    assert surviving != _reported_ids(), (
        "removing a row left the id set unchanged, so the comparison cannot notice"
    )


# The archive README states a byte count and a sha256 for every extracted document, and the
# id-equality rule above reads those documents. If the files and their stated hashes drift,
# the equality is checked against text nobody can tie back to the session record, so the
# provenance claim is verified here rather than trusted.
ARCHIVE_DIR = ROOT / "docs" / "history" / "evidence-archive" / "20260927_qoder_audit"
PROVENANCE = re.compile(r"`([A-Za-z0-9_.]+\.md)`.*?(\d+) 字节，sha256 `([0-9a-f]{64})`", re.S)


def _committed_blob(path: Path) -> bytes:
    """The bytes the repository holds, not whatever the checkout's line endings did.

    A first version hashed the working copy, and CI's checkout -- where git has normalized
    the endings -- produced different bytes, so the provenance note was right about my
    machine and wrong about the repository. The inventory declares the same rule: hash the
    raw committed bytes.
    """
    proc = subprocess.run(
        ["git", "show", f"HEAD:{path.relative_to(ROOT).as_posix()}"],
        cwd=ROOT, capture_output=True,
    )
    assert proc.returncode == 0, proc.stderr
    return proc.stdout


def test_the_archive_provenance_matches_the_bytes_on_disk() -> None:
    readme = (ARCHIVE_DIR / "README.md").read_text(encoding="utf-8")
    entries = PROVENANCE.findall(readme)
    assert len(entries) == len(REPORT_FILES) + 1, (
        f"the README states provenance for {len(entries)} documents; expected the report, "
        "its supplement and the task brief"
    )
    wrong = []
    for name, size, digest in entries:
        path = ARCHIVE_DIR / name
        assert path.exists(), f"the README describes a missing file: {name}"
        blob = _committed_blob(path)
        if len(blob) != int(size):
            wrong.append(f"{name}: README says {size} bytes, committed blob is {len(blob)}")
        if hashlib.sha256(blob).hexdigest() != digest:
            wrong.append(f"{name}: recorded sha256 does not match the committed blob")
    assert not wrong, "archive provenance has drifted:\n  " + "\n  ".join(wrong)
