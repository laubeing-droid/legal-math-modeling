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
CAVEATS = ("未", "尚", "不", "无", "待", "路线", "not yet", "no carrier", "pending",
           "awaiting", "does not", "not established", "no proof")
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
