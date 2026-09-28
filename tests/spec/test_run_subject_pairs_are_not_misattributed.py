"""Every "run N (subject S)" the prose writes must be the pairing GitHub recorded.

The index gate already checks that a quoted run id exists, that its recorded subject is a
real commit, and that a couple of specific pairings hold. What it never asked is whether a
sentence that names a run *and* a hash next to each other pairs the right two. That is the
shape an attestation takes when it drifts: the run is real, the commit is real, and the
claim is bound to neither. Mis-pairing them is how a paper credits a verdict to the wrong
subject, which is the exact failure the "counts and build status are never timeless facts"
rule exists to prevent.

So each pairing in the two paper editions and the campaign ledger is compared against
`ci_run_index.json`, the artifact that recorded GitHub's own answer for that run.
"""

from __future__ import annotations

import json
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
INDEX = ROOT / "docs" / "formal-release" / "ci_run_index.json"
SURFACES = (
    "docs/paper-rewrite/paper_cn.md",
    "docs/paper-rewrite/paper_en.md",
    "docs/master-plan/03_证明战役台账.md",
)

# `run 36351623739（subject `71d2177bc`）` / "run 36351623739 at subject 71d2177bc".
# The gap must not cross a sentence end: "run A. Run B at subject S" pairs B with S, and a
# first draft that allowed any non-newline text produced exactly that false positive.
PAIR = re.compile(
    r"run (\d{8,})[^\n.。;；!！]{0,40}?subject\s*[`（(]?\s*([0-9a-f]{7,40})", re.I
)


def _index() -> dict[str, str]:
    doc = json.loads(INDEX.read_text(encoding="utf-8"))
    return {str(run["run_id"]): (run.get("head_sha") or "") for run in doc["runs"]}


def _pairs(rel: str) -> list[tuple[str, str]]:
    text = (ROOT / rel).read_text(encoding="utf-8")
    return [(run, subj) for run, subj in PAIR.findall(text)]


def test_the_pairing_rule_sees_the_pairs_it_claims() -> None:
    seen = sum(len(_pairs(rel)) for rel in SURFACES)
    assert seen >= 10, (
        f"only {seen} run/subject pairs parsed across the surfaces; the prose or the "
        "pattern moved, so this gate is checking almost nothing"
    )


def test_every_named_pair_matches_the_index_record() -> None:
    by_id = _index()
    wrong: list[str] = []
    for rel in SURFACES:
        for run, subj in _pairs(rel):
            recorded = by_id.get(run)
            if recorded is None:
                wrong.append(f"{rel}: run {run} is not in the index")
            elif not recorded.startswith(subj):
                wrong.append(
                    f"{rel}: run {run} recorded at {recorded[:9]} but prose says {subj}"
                )
    assert not wrong, "attestation pairing does not match the recorded subject:\n  " + "\n  ".join(wrong)


def test_a_mispaired_attestation_would_actually_be_caught() -> None:
    """Prove the comparison bites: swap two subjects and the rule must fail."""
    by_id = _index()
    pairs = [(rel, p) for rel in SURFACES for p in _pairs(rel)]
    assert len({subj for _rel, (_run, subj) in pairs}) >= 2, (
        "every prose pair names the same subject, so a swap cannot be detected"
    )
    run_a, subj_a = next(p for _rel, p in pairs)
    _run_b, subj_b = next(p for _rel, p in pairs if p[1] != subj_a)
    assert not by_id[run_a].startswith(subj_b) or by_id[run_a].startswith(subj_a), (
        "the index does not distinguish subjects, so this gate cannot fail"
    )
