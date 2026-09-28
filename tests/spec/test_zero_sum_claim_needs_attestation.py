"""A saddle-point sentence in either edition must be caveated or cite a green run.

The repository is one clean build away from being able to say that every finite two-player
zero-sum game has a value in mixed strategies, and the failure mode the audit kept naming is
the paper stating such a thing before a run has attested the subject it describes. This rule
exists before that sentence is written, so the discipline is not a promise made afterwards.

It is deliberately narrow: it fires only on the minimax and saddle-point vocabulary, which is
the exact axis where an imported library theorem can be mistaken for this repository's own
result. Anything else the papers claim is bound by the count and attestation gates elsewhere.
"""

from __future__ import annotations

import json
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
CN = ROOT / "docs" / "paper-rewrite" / "paper_cn.md"
EN = ROOT / "docs" / "paper-rewrite" / "paper_en.md"
INDEX = ROOT / "docs" / "formal-release" / "ci_run_index.json"

TRIGGERS = ("鞍点", "极小极大", "saddle point", "minimax")
# Multi-character phrases only. The first draft of this list allowed "不", "无", "未", "尚",
# "待" as separate caveats, and since almost any Chinese sentence contains one of them, the
# exemption swallowed the rule: a bare minimax assertion with no hedge at all could still be
# waved through by an unrelated "不同" two clauses away.
CAVEATS = ("尚未", "未经", "未认定", "未被", "未主张", "不主张", "仍不", "没有", "无法",
           "not yet", "no carrier", "pending", "awaiting", "does not", "not established",
           "no proof", "not claimed", "no build", "still open")
RUN_ID = re.compile(r"run (\d{8,})")
SENTENCE = re.compile(r"[^。；！？\n.!?]+[。；！？\n.!?]?")


def _green_runs() -> set[str]:
    doc = json.loads(INDEX.read_text(encoding="utf-8"))
    return {
        str(run["run_id"]) for run in doc["runs"] if run.get("conclusion") == "success"
    }


def _unbound_sentences(text: str, green: set[str]) -> list[str]:
    out = []
    for sentence in SENTENCE.findall(text):
        if not any(trigger in sentence for trigger in TRIGGERS):
            continue
        if any(caveat in sentence for caveat in CAVEATS):
            continue
        cited = RUN_ID.findall(sentence)
        if cited and all(run in green for run in cited):
            continue
        out.append(sentence.strip()[:90])
    return out


def test_the_scan_sees_the_vocabulary_it_claims() -> None:
    """A pattern matching nothing would pass forever, so each edition must contain triggers."""
    for path in (CN, EN):
        text = path.read_text(encoding="utf-8")
        hits = [w for w in TRIGGERS if w in text]
        assert hits, f"{path.name} contains no minimax or saddle-point wording at all"
    green = _green_runs()
    cited = [
        sentence
        for path in (CN, EN)
        for sentence in SENTENCE.findall(path.read_text(encoding="utf-8"))
        if any(t in sentence for t in TRIGGERS) and RUN_ID.search(sentence)
    ]
    assert green, "no green run is indexed, so a citation could never satisfy the rule"
    assert len(cited) >= 2, (
        f"only {len(cited)} trigger sentence(s) cite a run, so the citation half of the rule "
        "is untested; the editions used to carry one per saddle-point claim"
    )
    assert all(_unbound_sentences(s, green) == [] for s in cited), (
        "a citing sentence is itself the offender, so the non-vacuity check below proves "
        "nothing about the live prose"
    )


def test_the_two_editions_carry_no_unbound_minimax_claim() -> None:
    green = _green_runs()
    assert green, "the run index lists no green runs, so the check has lost its reference"
    offenders = []
    for path in (CN, EN):
        text = path.read_text(encoding="utf-8")
        offenders += [(path.name, s) for s in _unbound_sentences(text, green)]
    assert not offenders, (
        f"a saddle-point or minimax sentence states a fact with neither a caveat nor a "
        f"green run: {offenders}"
    )


def test_the_rule_fires_on_a_bare_claim_and_stays_quiet_on_the_two_bound_forms() -> None:
    """A guard nobody can trip is decoration; this one is tripped on a fixture here."""
    green = _green_runs()
    assert green
    run = sorted(green)[0]

    bare = "每个有限零和博弈在混合策略下都有鞍点。"
    caveated = "每个有限零和博弈在混合策略下都有鞍点，这一条尚未被本轮构建认定。"
    attested = f"每个有限零和博弈在混合策略下都有鞍点，认定见 run {run}。"

    assert _unbound_sentences(bare, green), "a bare claim slipped through"
    assert not _unbound_sentences(caveated, green), "a caveated sentence was flagged"
    assert not _unbound_sentences(attested, green), "a green-run citation was rejected"
