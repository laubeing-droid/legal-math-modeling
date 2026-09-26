"""Gate tests for the RC-01 receipt authorization ledger (ruling #6).

The ledger is the machine-readable seven-layer x seven-domain table. These
gates enforce the mechanism, not editorial choices: full explicit coverage,
the domain list stays in lockstep with the prose in
certificate_checker_boundary.md, no-receipt layers downgrade to UNCLAIMABLE
and may issue NOT_ISSUED receipts only, multi-domain outputs cap at the
weakest cited domain, and nothing from the ledger leaks into the canonical
type registry.
"""

from __future__ import annotations

import re
from pathlib import Path

import pytest

from theory.spec.receipt_ledger import CROSSCUT_AXES  # noqa: F401 (re-exported below)
from theory.spec.receipt_ledger import (
    CELL_PENDING,
    LAYERS,
    LEDGER_PATH,
    RECEIPT_DOMAINS,
    UNCLAIMABLE,
    REFERENCE,
    CONCLUSIVE,
    NOT_ISSUED,
    LedgerDefect,
    ReceiptLedger,
)
from theory.spec.canonical_v2 import canonical_v2_type_names

ROOT = Path(__file__).resolve().parents[2]
BOUNDARY_DOC = ROOT / "docs" / "spec" / "certificate_checker_boundary.md"


def test_ledger_covers_every_layer_and_domain_explicitly() -> None:
    ledger = ReceiptLedger.load()

    assert ledger.unclaimable_layers() == frozenset({"L0", "L2", "L3"})
    for layer in LAYERS:
        for domain in RECEIPT_DOMAINS:
            assert ledger.cell_status(layer, domain) in {"AUTHORIZED", CELL_PENDING}


def test_domain_list_matches_boundary_prose() -> None:
    """Drift gate: the seven domain names come out of the prose doc itself,
    so the ledger and certificate_checker_boundary.md cannot diverge."""

    text = BOUNDARY_DOC.read_text(encoding="utf-8")
    match = re.search(
        r"`(\w+Receipt)`[^`]*`(\w+Receipt)`[^`]*`(\w+Receipt)`[^`]*"
        r"`(\w+Receipt)`[^`]*`(\w+Receipt)`[^`]*`(\w+Receipt)`[^`]*"
        r"`(\w+)` have separate subjects",
        text,
    )
    assert match is not None, "seven-domain sentence not found in boundary prose"
    prose_domains = {
        name[: -len("Receipt")] if name.endswith("Receipt") else name
        for name in match.groups()
    }
    assert prose_domains == set(RECEIPT_DOMAINS)


def test_no_receipt_layer_outputs_are_unclaimable() -> None:
    ledger = ReceiptLedger.load()

    # L0/L2/L3 have zero authorized cells: whatever a model cites, the
    # output is UNCLAIMABLE and every domain is NOT_ISSUED.
    for layer in ("L0", "L2", "L3"):
        assert ledger.effective_claim_level(layer, ("LeanProof", "HumanLegalReview")) == UNCLAIMABLE
        for domain in RECEIPT_DOMAINS:
            assert ledger.issuance_status(layer, domain) == NOT_ISSUED


def test_authorized_layers_cap_at_weakest_cited_domain() -> None:
    ledger = ReceiptLedger.load()

    assert ledger.effective_claim_level("L4", ("LeanProof",)) == CONCLUSIVE
    assert ledger.effective_claim_level("L1", ("HumanLegalReview",)) == REFERENCE
    # L5 citing a CONCLUSIVE and a REFERENCE domain caps at REFERENCE.
    assert (
        ledger.effective_claim_level("L5", ("LeanProof", "RuntimeRefinement")) == REFERENCE
    )
    # Citing only domains pending for that layer buys nothing.
    assert ledger.effective_claim_level("L5", ("HumanLegalReview",)) == UNCLAIMABLE
    assert ledger.effective_claim_level("L6", ("LeanProof",)) == UNCLAIMABLE


def test_ledger_stays_out_of_the_canonical_type_registry() -> None:
    names = set(canonical_v2_type_names())
    assert set(RECEIPT_DOMAINS).isdisjoint(names)
    assert set(LAYERS).isdisjoint(names)
    assert LEDGER_PATH.name not in {p.name for p in (ROOT / "theory/spec/canonical_v2").iterdir()}


def test_tampered_ledger_fails_closed() -> None:
    import copy

    good = ReceiptLedger.load()

    def as_layers(cells):
        return {"layers": [{"id": lid, "domains": cells[lid]} for lid in LAYERS]}

    # Missing a domain on one layer -> defect.
    holed = copy.deepcopy(good.cells)
    del holed["L4"]["LeanProof"]
    with pytest.raises(LedgerDefect):
        ReceiptLedger._validate_layers(as_layers(holed))

    # Unknown cell status -> defect.
    bad_status = copy.deepcopy(good.cells)
    bad_status["L1"]["HumanLegalReview"] = "MAYBE"
    with pytest.raises(LedgerDefect):
        ReceiptLedger._validate_layers(as_layers(bad_status))

    # Ceiling outside {REFERENCE, CONCLUSIVE} -> defect.
    bad_ceiling = dict(good.ceilings, LeanProof="UNLIMITED")
    with pytest.raises(LedgerDefect):
        ReceiptLedger._validate_ceilings({"domain_claim_ceiling": bad_ceiling})


CROSSCUT_EXPECTED = {
    ("crosscutA", "empirical_output"): "REFERENCE",
    ("crosscutA", "retrieved_cohort_rate"): "REFERENCE",
    ("crosscutA", "synthetic_data"): "NOT_CLAIMABLE",
    ("crosscutA", "unidentifiable_target"): "NOT_CLAIMABLE",
    ("crosscutB", "receipt_missing"): "UNCLAIMABLE",
    ("crosscutB", "citation_unverified"): "UNCLAIMABLE",
    ("crosscutB", "hallucination_pattern_detected"): "UNCLAIMABLE",
    ("crosscutB", "unadapted_jurisdiction"): "UNCLAIMABLE",
    ("crosscutB", "human_gate_pending"): "UNCLAIMABLE",
}


def test_crosscut_axes_are_declared_and_graded() -> None:
    """Audit P2-25: the two cross-cut axes had no rows in the 49-cell grid."""

    ledger = ReceiptLedger.load()
    assert (ledger.cells and len(ledger.cells)) == 7, "the ruled 7-layer grid changed"
    for (axis, channel), grade in CROSSCUT_EXPECTED.items():
        assert ledger.crosscut_ceiling(axis, channel) == grade, (axis, channel)


def test_crosscut_validation_is_fail_closed() -> None:
    import copy

    ledger = ReceiptLedger.load()
    good = copy.deepcopy(ledger.crosscuts)

    with pytest.raises(LedgerDefect):
        ReceiptLedger._validate_crosscuts({"crosscut_grades": {"crosscutA": {}}})
    with pytest.raises(LedgerDefect):
        ReceiptLedger._validate_crosscuts(
            {"crosscut_grades": dict(good, crosscutZ={"a": "REFERENCE"})}
        )
    bad_grade = copy.deepcopy(good)
    bad_grade["crosscutB"]["receipt_missing"] = "MAYBE"
    with pytest.raises(LedgerDefect):
        ReceiptLedger._validate_crosscuts({"crosscut_grades": bad_grade})
    # absent key is allowed: nothing claimed on the axes is not a defect
    assert ReceiptLedger._validate_crosscuts({}) == {}


def test_crosscut_unknown_names_raise_instead_of_defaulting() -> None:
    ledger = ReceiptLedger.load()
    with pytest.raises(LedgerDefect):
        ledger.crosscut_ceiling("crosscutQ", "empirical_output")
    with pytest.raises(LedgerDefect):
        ledger.crosscut_ceiling("crosscutA", "invented_channel")
    with pytest.raises(LedgerDefect):
        ledger.crosscut_channels("nope")


def test_every_declared_crosscut_channel_is_claimed_in_the_papers() -> None:
    """No dead channels: a ceiling nobody cites is decoration, not discipline."""

    ledger = ReceiptLedger.load()
    texts = " ".join(
        (ROOT / rel).read_text(encoding="utf-8")
        for rel in ("docs/paper-rewrite/paper_cn.md", "docs/paper-rewrite/paper_en.md")
    )
    for axis in CROSSCUT_AXES:
        channels = ledger.crosscut_channels(axis)
        assert channels, axis
        for channel in channels:
            assert channel.replace("_", " ") in texts.lower() or channel in texts, (
                f"{axis}|{channel} is graded in the ledger but never claimed in the papers"
            )


def test_papers_point_at_the_crosscut_artifact() -> None:
    """The prose claim and the machine-readable ceiling must name each other."""

    for rel in ("docs/paper-rewrite/paper_cn.md", "docs/paper-rewrite/paper_en.md"):
        assert "crosscut_grades" in (ROOT / rel).read_text(encoding="utf-8"), (
            f"{rel} must cite the cross-cut ledger key"
        )
