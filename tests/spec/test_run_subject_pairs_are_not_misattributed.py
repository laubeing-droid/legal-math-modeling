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

The second rule below covers the half this gate missed while it was green. A module header may
cite a real run at a real subject and still attest nothing, if the file it vouches for did not
exist at that subject -- which is exactly what `Mandate/SequentialGames.lean` did with run
36386527448 at `7a2a65e`. So a subject named inside a Lean source must be a commit whose tree
contains that source.
"""

from __future__ import annotations

import json
import re
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
INDEX = ROOT / "docs" / "formal-release" / "ci_run_index.json"
LEAN_PKG = ROOT / "proofs" / "lean" / "juris_lean" / "JurisLean"
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


def _mismatches(pairs: list[tuple[str, str]], by_id: dict[str, str]) -> list[str]:
    """The comparison, factored out so a deliberately swapped pairing can drive it."""
    out = []
    for run, subj in pairs:
        recorded = by_id.get(run)
        if recorded is None:
            out.append(f"run {run} is not in the index")
        elif not recorded.startswith(subj):
            out.append(f"run {run} recorded at {recorded[:9]} but prose says {subj}")
    return out


def test_a_mispaired_attestation_would_actually_be_caught() -> None:
    """Prove the rule bites: rotate every subject and the same comparison must report it."""
    by_id = _index()
    pairs = [p for rel in SURFACES for p in _pairs(rel)]
    assert not _mismatches(pairs, by_id), (
        "the live prose already fails, so the mutation case would prove nothing"
    )
    subjects = sorted({subj for _run, subj in pairs})
    assert len(subjects) >= 2, "every pair names one subject, so a swap cannot be detected"
    rotated = [
        (run, subjects[(subjects.index(subj) + 1) % len(subjects)])
        for run, subj in pairs
    ]
    assert _mismatches(rotated, by_id), (
        "rotating every subject left the comparison clean, so it cannot notice a swap"
    )


# What a Lean header writes when it binds its own build verdict to a commit:
# "at subject `e9abf6a`", "in run ... at subject 1b6a8d6a9".
HEADER_SUBJECT = re.compile(r"subject\s*[`（(]?\s*([0-9a-f]{7,40})", re.I)


def _header_subjects() -> list[tuple[str, str]]:
    """(module path relative to the repo, cited subject) for every Lean source."""
    out = []
    for path in sorted(LEAN_PKG.rglob("*.lean")):
        rel = path.relative_to(ROOT).as_posix()
        for subj in HEADER_SUBJECT.findall(path.read_text(encoding="utf-8")):
            out.append((rel, subj))
    return out


def _git(*args: str) -> int:
    return subprocess.run(
        ["git", *args], cwd=ROOT, capture_output=True, text=True
    ).returncode


def test_the_subject_rule_sees_the_headers_it_claims() -> None:
    seen = _header_subjects()
    assert len(seen) >= 10, (
        f"only {len(seen)} subject citations found in Lean sources; either the headers stopped "
        "binding their builds or this rule stopped reading them"
    )
    assert len({subj for _rel, subj in seen}) >= 5, (
        "every citation names the same commit, so no per-file check is being made"
    )


def test_an_attested_subject_is_a_commit_that_contains_the_file() -> None:
    """A verdict can only cover a build input that existed where the verdict was recorded."""
    unknown: list[str] = []
    absent: list[str] = []
    for rel, subj in _header_subjects():
        if _git("rev-parse", "--verify", "--quiet", f"{subj}^{{commit}}") != 0:
            unknown.append(f"{rel}: {subj} is not a commit of this repository")
        elif _git("cat-file", "-e", f"{subj}:{rel}") != 0:
            absent.append(f"{rel}: cited {subj}, whose tree does not contain it")
    assert not unknown, "a header cites a subject that cannot be checked:\n  " + "\n  ".join(unknown)
    assert not absent, (
        "a header attests its own source to a commit whose tree lacks it:\n  "
        + "\n  ".join(absent)
    )


def test_the_rule_would_reject_the_verdict_this_module_once_wrote() -> None:
    """Not a fixture: `7a2a65e` is the commit `SequentialGames.lean` really did cite, and it
    has no such file, which is the whole reason the rule above exists."""
    rel = "proofs/lean/juris_lean/JurisLean/Mandate/SequentialGames.lean"
    assert _git("cat-file", "-e", f"7a2a65e:{rel}") != 0, (
        "the pairing the header now repudiates has become true, so the retraction prose and "
        "this check both need rewriting"
    )
