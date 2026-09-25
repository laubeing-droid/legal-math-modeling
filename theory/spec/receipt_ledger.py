#!/usr/bin/env python3
"""RC-01 receipt authorization ledger: loader and fail-closed claim gates.

The ledger (`receipt_ledger.json`) is the single machine-readable authority
for which semantic layer may claim which evidence receipt domain (ruling #6;
seven domains as named in docs/spec/certificate_checker_boundary.md). It is
deliberately independent of the canonical_v2 type registry: layer
claimability never rides the manifest. A layer supported only by
NO_RECEIPT_PENDING cells may issue NOT_ISSUED receipts only, and its
outputs are UNCLAIMABLE regardless of what any model or document asserts.
"""

from __future__ import annotations

import json
from dataclasses import dataclass
from pathlib import Path
from typing import Dict, FrozenSet, List, Tuple

LEDGER_PATH = Path(__file__).with_name("receipt_ledger.json")

RECEIPT_DOMAINS: Tuple[str, ...] = (
    "LeanProof",
    "FiniteModelCheck",
    "SolverWitness",
    "Translation",
    "RuntimeRefinement",
    "HumanLegalReview",
    "FormalReleaseCertificate",
)

LAYERS: Tuple[str, ...] = ("L0", "L1", "L2", "L3", "L4", "L5", "L6")

CELL_AUTHORIZED = "AUTHORIZED"
CELL_PENDING = "NO_RECEIPT_PENDING"
VALID_CELL_STATUSES = frozenset({CELL_AUTHORIZED, CELL_PENDING})

# Claim levels, weakest to strongest; receipts never promote past the
# weakest cited domain (certificate checker boundary rule).
CLAIM_ORDER: Tuple[str, ...] = ("UNCLAIMABLE", "REFERENCE", "CONCLUSIVE")
UNCLAIMABLE, REFERENCE, CONCLUSIVE = CLAIM_ORDER

NOT_ISSUED = "NOT_ISSUED"


class LedgerDefect(ValueError):
    """Raised when the ledger file violates its own invariants (fail-closed)."""


@dataclass(frozen=True)
class ReceiptLedger:
    """Validated view over receipt_ledger.json; all gates are methods here."""

    cells: Dict[str, Dict[str, str]]
    ceilings: Dict[str, str]

    @classmethod
    def load(cls) -> "ReceiptLedger":
        raw = json.loads(LEDGER_PATH.read_text(encoding="utf-8"))
        return cls(cells=cls._validate_layers(raw), ceilings=cls._validate_ceilings(raw))

    @staticmethod
    def _validate_layers(raw: dict) -> Dict[str, Dict[str, str]]:
        layers = raw.get("layers")
        if not isinstance(layers, list) or len(layers) != len(LAYERS):
            raise LedgerDefect("ledger must list exactly seven layers")

        cells: Dict[str, Dict[str, str]] = {}
        for layer in layers:
            lid = layer.get("id")
            if lid not in LAYERS:
                raise LedgerDefect(f"unknown layer id: {lid!r}")
            if lid in cells:
                raise LedgerDefect(f"duplicate layer id: {lid!r}")
            domains = layer.get("domains")
            if not isinstance(domains, dict) or set(domains) != set(RECEIPT_DOMAINS):
                raise LedgerDefect(f"layer {lid} must address every receipt domain explicitly")
            for domain, status in domains.items():
                if status not in VALID_CELL_STATUSES:
                    raise LedgerDefect(f"unknown cell status {status!r} at {lid}|{domain}")
            cells[lid] = dict(domains)
        return cells

    @staticmethod
    def _validate_ceilings(raw: dict) -> Dict[str, str]:
        ceilings = raw.get("domain_claim_ceiling")
        if not isinstance(ceilings, dict) or set(ceilings) != set(RECEIPT_DOMAINS):
            raise LedgerDefect("every receipt domain needs a claim ceiling")
        for domain, ceiling in ceilings.items():
            if ceiling not in CLAIM_ORDER[1:]:
                raise LedgerDefect(f"invalid ceiling {ceiling!r} for {domain}")
        return dict(ceilings)

    def cell_status(self, layer: str, domain: str) -> str:
        self._require_layer(layer)
        if domain not in RECEIPT_DOMAINS:
            raise ValueError(f"unknown receipt domain: {domain!r}")
        return self.cells[layer][domain]

    def authorized_domains(self, layer: str) -> List[str]:
        self._require_layer(layer)
        return [d for d in RECEIPT_DOMAINS if self.cells[layer][d] == CELL_AUTHORIZED]

    def issuance_status(self, layer: str, domain: str) -> str:
        """Pending cells issue NOT_ISSUED receipts only (ruling #6)."""

        return NOT_ISSUED if self.cell_status(layer, domain) == CELL_PENDING else "ISSUABLE"

    def claim_ceiling(self, domain: str) -> str:
        ceiling = self.ceilings.get(domain)
        if ceiling is None:
            raise ValueError(f"unknown receipt domain: {domain!r}")
        return ceiling

    def effective_claim_level(self, layer: str, cited_domains: Tuple[str, ...]) -> str:
        """Claim level of an output on `layer` backed by `cited_domains`.

        Fail-closed downgrade chain: no authorized domain for the layer (or
        no citation that survives filtering) -> UNCLAIMABLE; otherwise the
        output may claim no more than the weakest cited authorized domain.
        """

        self._require_layer(layer)
        authorized = frozenset(self.authorized_domains(layer))
        if not authorized:
            return UNCLAIMABLE
        surviving = [d for d in cited_domains if d in authorized]
        if not surviving:
            return UNCLAIMABLE
        return min((self.claim_ceiling(d) for d in surviving), key=CLAIM_ORDER.index)

    def unclaimable_layers(self) -> FrozenSet[str]:
        """Layers with zero authorized cells: outputs there are UNCLAIMABLE."""

        return frozenset(l for l in LAYERS if not self.authorized_domains(l))

    @staticmethod
    def _require_layer(layer: str) -> None:
        if layer not in LAYERS:
            raise ValueError(f"unknown layer: {layer!r}")
