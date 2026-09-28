"""A verdict a header claims must be re-readable from bytes in this repository.

Round 72 is the reason: `SequentialGames.lean` carried a verdict whose run/subject pairing was
perfectly real and which nevertheless attested nothing, because the subject predated the file.
Pairing gates cannot catch that; only the round's own bytes can, and only if they are here. So
the rule is: a module whose header cites build rounds must cite at least one round whose landed
`axiom-audit` output actually names that module's declarations. "The job was green" is a colour;
"`'JurisLean.Mandate.X.theorem_name' does not depend on any axioms`" is evidence.

Citations of red rounds stay unconstrained here -- headers are required to name their failures
too, and those are already bound to the run index elsewhere. What this gate demands is that
among everything a header cites, the verdict is somewhere a reader can recompute it.
"""

from __future__ import annotations

import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
PKG = ROOT / "proofs" / "lean" / "juris_lean" / "JurisLean"
EVIDENCE = ROOT / "docs" / "formal-release" / "ci-evidence"
RUN = re.compile(r"\brun\s+(\d{8,})", re.I)
NAMESPACE = re.compile(r"^namespace\s+([\w.]+)", re.M)


def _landed_names(run: str) -> set[str] | None:
    """The qualified names that run's landed audit text prints, or None if nothing landed."""
    path = EVIDENCE / run / "axiom-audit" / "axiom-audit.raw.txt"
    if not path.exists():
        return None
    out: set[str] = set()
    for line in path.read_text(encoding="utf-8", errors="replace").splitlines():
        if line.startswith("'") and "'" in line[1:]:
            out.add(line.split("'", 2)[1])
    return out


def _modules() -> list[tuple[str, str, list[str]]]:
    """(stem, namespace, cited runs) for every package module whose header cites runs."""
    rows = []
    for path in sorted(PKG.rglob("*.lean")):
        text = path.read_text(encoding="utf-8", errors="replace")
        header = _header(text)
        runs = sorted(set(RUN.findall(header)))
        if not runs:
            continue
        ns = NAMESPACE.search(text)
        rows.append((path.stem, ns.group(1) if ns else "", runs))
    return rows


def _header(text: str) -> str:
    i = text.find("/-!")
    j = text.find("-/", i)
    return text[i:j] if 0 <= i < j else text[:4000]


def test_the_rule_reads_real_headers_and_real_evidence() -> None:
    rows = _modules()
    assert len(rows) >= 15, (
        f"only {len(rows)} modules cite build rounds; either headers stopped attesting or "
        "this gate stopped reading them"
    )
    landed = {p.parent.parent.name for p in EVIDENCE.glob("*/axiom-audit/axiom-audit.raw.txt")}
    assert len(landed) >= 10, (
        f"only {len(landed)} rounds have landed audit bytes, so the reference set is too thin "
        "to demand anything"
    )


def test_every_attesting_header_cites_at_least_one_landed_round() -> None:
    unsatisfied: list[str] = []
    for stem, namespace, runs in _modules():
        prefix = f"{namespace}." if namespace else ""
        if not any(
            (names := _landed_names(run)) is not None
            and any(n.startswith(prefix) for n in names)
            for run in runs
        ):
            unsatisfied.append(f"{stem}: cites {runs}, none landed names {prefix}*")
    assert not unsatisfied, (
        "these headers claim build verdicts that no landed audit text in this repository can "
        "re-read; land the round with `build_ci_run_index.py --fetch-evidence <id>` or correct "
        "the header:\n  " + "\n  ".join(unsatisfied)
    )


def test_the_gate_can_actually_go_red() -> None:
    """Drive the comparison with a module whose runs are known not to cover it."""
    stem, namespace, runs = next(
        (s, n, r) for s, n, r in _modules() if s == "PureNash"
    )
    assert runs, "PureNash's header stopped citing rounds; update this test"
    prefix = f"{namespace}."
    wrong = "36298572193"  # a real landed round from a different era
    names = _landed_names(wrong)
    assert names is not None and not any(n.startswith(prefix) for n in names), (
        "the chosen wrong round now covers this module, so the negative case proves nothing"
    )
