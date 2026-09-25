"""TY-05: ReceiptDomain enum registration in the canonical manifest.

The seven domain values are copied verbatim from the authoritative
machine-readable receipt ledger (RC-01), never invented here; the enum rides
ENUM_REGISTRY only and never touches TYPE_LAYERS or the type theorems.
"""

from __future__ import annotations

from theory.spec.canonical_v2 import ENUM_REGISTRY, TYPE_LAYERS, canonical_v2_type_names
from theory.spec.receipt_ledger import RECEIPT_DOMAINS


def test_receipt_domain_registered_with_ledger_values() -> None:
    values = ENUM_REGISTRY["ReceiptDomain"]
    assert values == list(RECEIPT_DOMAINS)
    assert len(values) == 7
    assert len(set(values)) == 7


def test_receipt_domain_stays_out_of_type_layers() -> None:
    assert "ReceiptDomain" not in TYPE_LAYERS
    assert "ReceiptDomain" not in canonical_v2_type_names()
    for layer in TYPE_LAYERS.values():
        assert "ReceiptDomain" not in layer
