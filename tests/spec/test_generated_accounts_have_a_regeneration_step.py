"""An account that names its generator must be reachable from the documented regeneration path.

This round is the reason the rule exists. `build_statement_duplication_census.py` writes only
when passed `--write`, and neither it nor `generate_declaration_shape_report.py` appeared in the
README sequence or in `rehearse_regeneration.py`. Three modules then entered the package and the
committed census stayed at 222 files / 1959 theorems while its own `--check` reported *ok* --
comparing a stale product against itself, which is the one thing a regeneration check must never
do quietly.

The rule reads the artifacts rather than a list: any tracked JSON under `docs/formal-release`
that carries a `generated_by` naming a repository script must be produced by a step the
rehearsal runs, or be excluded below with a reason that can be argued with.
"""

from __future__ import annotations

import json
import re
import subprocess
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[2]
RELEASE = ROOT / "docs" / "formal-release"
REHEARSAL = ROOT / "scripts" / "ci" / "rehearse_regeneration.py"
README = ROOT / "README.md"

GENERIC = re.compile(r"([A-Za-z0-9_/\\.-]+\.py)")

# Empirical probes, not accounts: each one reads a corpus delivery that is not in the
# repository, so a clean clone cannot reproduce them and pretending otherwise would make
# the rehearsal fail for a reason unrelated to drift.
NOT_REGENERABLE = {
    "docs/formal-release/real_cohort_probe.json": "needs the local cohort delivery",
    "docs/formal-release/wave_cohort_probe.json": "needs the WAVE-ALL-001 delivery on D:",
}


def _tracked_release_json() -> list[Path]:
    out = subprocess.run(
        ["git", "ls-files", "docs/formal-release/*.json"],
        cwd=ROOT, capture_output=True, text=True, check=True,
    )
    return [ROOT / p for p in out.stdout.split()]


def _script_of(generated_by: str) -> str:
    m = GENERIC.search(generated_by)
    assert m, f"generated_by names no script: {generated_by!r}"
    return m.group(1).replace("\\", "/")


def _rehearsal_scripts() -> set[str]:
    text = REHEARSAL.read_text(encoding="utf-8")
    block = text[text.index("SEQUENCE = ("): text.index("\n)\n", text.index("SEQUENCE = ("))]
    return {GENERIC.search(line).group(1).replace("\\", "/")
            for line in block.splitlines() if GENERIC.search(line)}


def test_the_rule_reads_real_artifacts_and_a_real_sequence() -> None:
    """Non-vacuity: an empty scan would pass forever."""
    named = [
        p for p in _tracked_release_json()
        if "generated_by" in p.read_text(encoding="utf-8", errors="replace")
    ]
    assert len(named) >= 5, (
        f"only {len(named)} release artifacts declare a generator; either the field was "
        "renamed away or this rule stopped reading the tree"
    )
    assert len(_rehearsal_scripts()) >= 6, "the rehearsal sequence shrank"


def test_every_generated_account_is_reachable_from_the_rehearsal() -> None:
    sequence = _rehearsal_scripts()
    uncovered = []
    for path in _tracked_release_json():
        rel = path.relative_to(ROOT).as_posix()
        m = re.search(r'"generated_by"\s*:\s*"([^"]+)"',
                      path.read_text(encoding="utf-8", errors="replace"))
        if not m:
            continue
        script = _script_of(m.group(1))
        if rel in NOT_REGENERABLE:
            continue
        if script not in sequence:
            uncovered.append(f"{rel} <- {script}")
    assert not uncovered, (
        "these accounts are produced by a step the documented sequence never runs, so they "
        "can go stale while their own --check stays green:\n  " + "\n  ".join(uncovered)
    )


def _readme_script_names() -> set[str]:
    """The steps README.md tells a human to run, as bare file names."""
    text = README.read_text(encoding="utf-8")
    opened = text.index("```bash", text.index("are **generated**")) + len("```bash")
    block = text[opened : text.index("```", opened)]
    return {Path(_script_of(line)).name for line in block.splitlines() if ".py" in line}


def test_the_readme_lists_the_same_generators_the_rehearsal_runs() -> None:
    """The README is the human-facing copy of the sequence; a step in one and not the other
    is how a maintainer ends up regenerating six accounts when eight exist."""
    documented = _readme_script_names()
    sequence = {Path(s).name for s in _rehearsal_scripts()}
    missing_from_readme = sorted(sequence - documented)
    assert not missing_from_readme, (
        f"the rehearsal runs steps README.md never tells anyone to run: {missing_from_readme}"
    )
    assert len(documented) >= 7, (
        f"README's block names {len(documented)} scripts; it moved or shrank and this "
        "comparison stopped reading it"
    )


def test_a_step_dropped_from_the_readme_would_be_caught() -> None:
    """The comparison is `sequence - readme`, so withdrawing one documented step must go red."""
    sequence = {Path(s).name for s in _rehearsal_scripts()}
    documented = _readme_script_names()
    assert sequence <= documented, "the live sequence already outruns the README"
    assert sequence, "the rehearsal runs no steps, so nothing could ever be missed"
    withdrawn = documented - {sorted(sequence)[0]}
    assert sequence - withdrawn, (
        f"README could lose {sorted(sequence)[0]!r} and the check would still pass"
    )


@pytest.mark.parametrize("rel", sorted(NOT_REGENERABLE))
def test_an_excluded_account_still_explains_itself(rel: str) -> None:
    """An exclusion is a claim, so it must keep a reason and keep the field it was made for."""
    assert NOT_REGENERABLE[rel]
    doc = json.loads((ROOT / rel).read_text(encoding="utf-8"))
    assert "generated_by" in doc, f"{rel} no longer needs an exclusion"
