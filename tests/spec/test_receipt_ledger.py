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
