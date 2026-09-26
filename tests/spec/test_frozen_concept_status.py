"""P2-27: the four ❓ concepts must be described the same way everywhere.

The audit caught one-tier-two-rules: the concept register marked P-034/P-051/P-066/
P-098 as ❓ (gap) and the campaign ledger called them "定理级 OPEN_THEOREM", while the
Lean corpus actually carries audited theorems for each of them. Both statements were
defensible read alone and contradictory read together, which is how a frozen register
turns into noise.

The reconciliation is that ❓ means *the concept's registered proof goal is not met*,
not *no theorem exists*. This file pins all three halves of that sentence: the named
carriers exist and are on the axiom-audit surface, the register still marks exactly
these four as ❓, and the ledger says what is open per item instead of the blanket.
"""

from __future__ import annotations

import json
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
INVENTORY = ROOT / "docs" / "formal-release" / "theorem_inventory_v3.json"
AUDIT = ROOT / "proofs" / "lean" / "juris_lean" / "JurisLean" / "AxiomAudit.lean"
REGISTER = ROOT / "docs" / "master-plan" / "基线" / "法律概念总谱.md"
LEDGER = ROOT / "docs" / "master-plan" / "03_证明战役台账.md"

# concept id -> (namespace, carriers the documents point at)
FROZEN_FOUR: dict[str, tuple[str, tuple[str, ...]]] = {
    "P-034": ("Part2.P034", ("claim_available_complete_iff", "unregistered_basis_unknown")),
    "P-051": ("Part3.P051", ("boundary_inputs_complete", "boundary_records_input_only")),
    "P-066": ("Part4.P066", ("gap_detection_preserves_signal_roster", "gap_signal_detected")),
    "P-098": (
        "Part5.P098",
        (
            "clamp_below_to_low",
            "clamp_below_in_band",
            "clamp_above_to_high",
            "clamp_above_in_band",
            "clamp_inside_fixed",
            "clamp_inside_idempotent",
        ),
    ),
}


def _declarations() -> set[str]:
    doc = json.loads(INVENTORY.read_text(encoding="utf-8"))
    return {d["name"] for f in doc["files"] for d in f["declarations"]}


def _audited_full_names() -> set[str]:
    return {
        m.group(1).strip()
        for m in re.finditer(r"^#print axioms (\S+)$", AUDIT.read_text(encoding="utf-8"), re.M)
    }


def test_every_named_carrier_is_a_real_declaration() -> None:
    declared = _declarations()
    missing = [
        f"{pid}:{sym}"
        for pid, (_ns, syms) in FROZEN_FOUR.items()
        for sym in syms
        if sym not in declared
    ]
    assert not missing, f"frozen-concept carriers that name no declaration: {missing}"


def test_every_named_carrier_is_on_the_axiom_audit_surface() -> None:
    """An anchor the documents lean on must be covered by the audit, not just exist."""

    audited = _audited_full_names()
    missing = [
        f"JurisLean.Genealogy.{ns}.{sym}"
        for ns, syms in (FROZEN_FOUR[pid] for pid in FROZEN_FOUR)
        for sym in syms
        if f"JurisLean.Genealogy.{ns}.{sym}" not in audited
    ]
    assert not missing, f"carriers outside the audit surface: {missing}"


def test_register_still_marks_exactly_these_four_as_gaps() -> None:
    """The ❓ set is pinned: upgrading one is a register act, not a quiet edit."""

    text = REGISTER.read_text(encoding="utf-8")
    marked = {
        m.group(1)
        for m in re.finditer(r"^\| (P-\d{3}) \|[^|]*\|[^|]*\|[^|]*\|[^|]*\|[^|]*\| ❓ \|", text, re.M)
    }
    assert marked == set(FROZEN_FOUR), f"❓ set moved: {sorted(marked ^ set(FROZEN_FOUR))}"


def test_the_ledger_names_the_carriers_instead_of_a_blanket_status() -> None:
    text = LEDGER.read_text(encoding="utf-8")
    line = next(
        (l for l in text.splitlines() if "四个 ❓" in l), None
    )
    assert line, "the four-concept paragraph disappeared from the ledger"
    block = text[text.index(line): text.index(line) + 1600]
    assert "OPEN_THEOREM" not in block, (
        "the blanket wording is back: these four have audited carriers, so the open "
        "part must be stated per concept"
    )
    for _pid, (_ns, syms) in FROZEN_FOUR.items():
        assert any(sym in block for sym in syms), f"{_pid} carriers not named in the ledger"


def test_each_concept_states_what_remains_open_beyond_its_carriers() -> None:
    """"Gap" must mean an unmet registered goal, and the text has to say so."""

    text = LEDGER.read_text(encoding="utf-8")
    block = text[text.index("四个 ❓"): text.index("四个 ❓") + 1600]
    for phrase in ("证明目标", "升档"):
        assert phrase in block, f"the reconciliation lost “{phrase}”"
