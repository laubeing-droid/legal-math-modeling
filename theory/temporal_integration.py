#!/usr/bin/env python3
"""
F1: Temporal Law Integration
============================

Provides temporal filtering for the legal reasoning pipeline.
Integrates governing_law_snapshot() to filter rules by applicable date.
"""

from __future__ import annotations

import sys
from datetime import date
from pathlib import Path
from typing import List, Optional, Set

_PROJECT_ROOT = Path(__file__).resolve().parent.parent
if str(_PROJECT_ROOT) not in sys.path:
    sys.path.insert(0, str(_PROJECT_ROOT))

from theory.argumentation_horn_unification import HornRule, HornToDungBridge
from theory.temporal_law_engine import TemporalLawEngine, LegalRule, LawType


class TemporalFilter:
    """Filters rules by temporal applicability before inference."""

    def __init__(self):
        self.engine = TemporalLawEngine()
        self._rules_by_id = {}

    def add_rule(self, rule: HornRule, effective_date: date,
                 expiry_date: Optional[date] = None,
                 law_type: str = "substantive"):
        """Register a Horn rule with temporal metadata."""
        lt = LawType.SUBSTANTIVE if law_type == "substantive" else LawType.PROCEDURAL
        lr = LegalRule(
            id=rule.id, statute=rule.namespace, article=rule.id,
            content=rule.head, law_type=lt,
            effective_date=effective_date, expiry_date=expiry_date,
        )
        self.engine.add_rule(lr)
        self._rules_by_id[rule.id] = rule

    def filter_rules(self, query_date: date,
                     law_type: Optional[str] = None) -> List[HornRule]:
        """Return only rules applicable at query_date."""
        lt = None
        if law_type == "substantive":
            lt = LawType.SUBSTANTIVE
        elif law_type == "procedural":
            lt = LawType.PROCEDURAL

        applicable = self.engine.snapshot(query_date, lt)
        return [self._rules_by_id[r.id] for r in applicable
                if r.id in self._rules_by_id]

    def infer_with_temporal_filter(
        self, facts: Set[str], rules: List[HornRule],
        fact_date: date, current_date: date,
    ) -> dict:
        """Run inference with temporal filtering.

        Substantive law: filter by fact_date (实体从旧)
        Procedural law: filter by current_date (程序从新)
        """
        substantive = self.filter_rules(fact_date, "substantive")
        procedural = self.filter_rules(current_date, "procedural")
        applicable = substantive + procedural

        bridge = HornToDungBridge(applicable, facts)
        frame = bridge.construct_frame()

        return {
            "applicable_rules": len(applicable),
            "substantive_rules": len(substantive),
            "procedural_rules": len(procedural),
            "accepted_claims": [a.claim for a in frame.args],
            "attacks": len(frame.attacks),
            "fact_date": str(fact_date),
            "current_date": str(current_date),
        }


def demo():
    """Demo: contract signed in 2020, dispute filed in 2022."""
    print("=" * 60)
    print("Temporal Law Integration — Demo")
    print("=" * 60)

    tf = TemporalFilter()

    # Old contract law (1999-2020)
    tf.add_rule(
        HornRule(id="old_contract", premises=["contract_signed"],
                 head="OLD_LAW_APPLIES", exceptions=["new_civil_code"]),
        effective_date=date(1999, 10, 1), expiry_date=date(2021, 1, 1),
        law_type="substantive",
    )
    # New Civil Code (2021-)
    tf.add_rule(
        HornRule(id="new_civil_code", premises=["dispute_filed_after_2021"],
                 head="NEW_LAW_APPLIES", exceptions=[]),
        effective_date=date(2021, 1, 1), law_type="substantive",
    )
    # Procedural rule (always current)
    tf.add_rule(
        HornRule(id="proc_rule", premises=["filing_complete"],
                 head="CASE_ACCEPTED", exceptions=[]),
        effective_date=date(2020, 1, 1), law_type="procedural",
    )

    facts = {"contract_signed", "dispute_filed_after_2021", "filing_complete"}

    result = tf.infer_with_temporal_filter(
        facts, [], fact_date=date(2020, 6, 1), current_date=date(2022, 3, 15),
    )
    print(f"Fact date: {result['fact_date']}")
    print(f"Current date: {result['current_date']}")
    print(f"Applicable rules: {result['applicable_rules']}")
    print(f"  Substantive: {result['substantive_rules']}")
    print(f"  Procedural: {result['procedural_rules']}")
    print(f"Accepted claims: {result['accepted_claims']}")
    print("=" * 60)


if __name__ == "__main__":
    demo()
