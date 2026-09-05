#!/usr/bin/env python3
"""
Temporal Statute Law — Dual-Timestamp Model (Direction 5)

Formalizes the governing_law_snapshot model with two timestamps:
- fact_occurrence_date → loads substantive law (实体法)
- procedural_current_date → loads procedural law (程序法)

Key legal principles encoded:
- 法不溯及既往 (Lex retro non agit): Law does not apply retroactively
- 程序从新 (Procedural law follows new rules): Procedural rules apply immediately
- 实体从旧 (Substantive law follows old rules): Substantive rules from time of fact

PRC examples:
- 民法典生效 (2021-01-01): Before → 合同法; After → 民法典合同编
- 民事诉讼法修正 (2024-01-01): Applies to all pending cases
"""
from __future__ import annotations
from dataclasses import dataclass, field
from datetime import date, datetime
from enum import Enum
from typing import Dict, List, Optional, Set, Tuple


class LawType(Enum):
    SUBSTANTIVE = "substantive"    # 实体法 (contracts, torts, etc.)
    PROCEDURAL = "procedural"      # 程序法 (civil procedure, evidence rules)
    ADMINISTRATIVE = "admin"       # 行政法 (regulatory)


@dataclass(frozen=True)
class StatuteVersion:
    """A version of a statute with its effective date range."""
    statute_id: str               # e.g., "PRC_Contract_Law"
    law_type: LawType
    effective_from: date          # 生效日期
    effective_until: Optional[date] = None  # 失效日期 (None = still effective)
    article_count: int = 0
    superseded_by: Optional[str] = None  # e.g., "PRC_Civil_Code_Contract_Book"

    @property
    def is_current(self) -> bool:
        return self.effective_until is None


@dataclass
class LegalTimeline:
    """
    Manages the temporal dimension of legal rules.

    Core model: governing_law_snapshot(t) returns the applicable law
    at time t, separated into substantive and procedural streams.
    """
    statutes: List[StatuteVersion] = field(default_factory=list)

    def add_statute(self, statute: StatuteVersion):
        self.statutes.append(statute)

    def governing_law_snapshot(self, snapshot_date: date, law_type: LawType) -> List[StatuteVersion]:
        """
        Returns all statutes of the given type effective at snapshot_date.

        Convention: effective_until is EXCLUSIVE (the statute is effective
        up to but NOT including this date). Example:
          effective_from=1999-10-01, effective_until=2021-01-01
          means effective from Oct 1 1999 through Dec 31 2020.

        For SUBSTANTIVE law: snapshot = fact_occurrence_date (实体从旧)
        For PROCEDURAL law: snapshot = procedural_current_date (程序从新)
        """
        return [
            s for s in self.statutes
            if s.law_type == law_type
            and s.effective_from <= snapshot_date
            and (s.effective_until is None or s.effective_until > snapshot_date)
        ]

    def get_applicable_statutes(
        self,
        fact_date: date,
        procedure_date: date,
    ) -> Dict[LawType, List[StatuteVersion]]:
        """
        Get the full applicable law set for a case.

        Substantive law: governed by fact_occurrence_date
        Procedural law: governed by procedural_current_date
        """
        return {
            LawType.SUBSTANTIVE: self.governing_law_snapshot(fact_date, LawType.SUBSTANTIVE),
            LawType.PROCEDURAL: self.governing_law_snapshot(procedure_date, LawType.PROCEDURAL),
        }

    def check_retroactivity(self, statute: StatuteVersion, fact_date: date) -> Dict:
        """
        Check if applying a statute would violate 法不溯及既往.

        Returns violation details if the statute post-dates the facts.
        """
        if statute.law_type == LawType.SUBSTANTIVE and statute.effective_from > fact_date:
            return {
                "violation": True,
                "principle": "法不溯及既往 (Lex retro non agit)",
                "statute": statute.statute_id,
                "statute_effective": statute.effective_from.isoformat(),
                "fact_date": fact_date.isoformat(),
                "recommendation": f"Apply {statute.superseded_by or 'prior law'} instead",
            }
        elif statute.law_type == LawType.PROCEDURAL:
            return {
                "violation": False,
                "principle": "程序从新 (Procedural law applies immediately)",
                "statute": statute.statute_id,
                "note": "Procedural rules apply to all pending cases regardless of fact date",
            }
        return {"violation": False, "statute": statute.statute_id, "principle": "实体法在生效期间适用"}


def build_prc_legal_timeline() -> LegalTimeline:
    """Build a representative PRC legal timeline."""
    timeline = LegalTimeline()

    # 合同法 (Contract Law, 1999-2021)
    timeline.add_statute(StatuteVersion(
        statute_id="PRC_Contract_Law",
        law_type=LawType.SUBSTANTIVE,
        effective_from=date(1999, 10, 1),
        effective_until=date(2021, 1, 1),
        article_count=428,
        superseded_by="PRC_Civil_Code_Contract_Book",
    ))

    # 民法典合同编 (Civil Code Contract Book, 2021-)
    timeline.add_statute(StatuteVersion(
        statute_id="PRC_Civil_Code_Contract_Book",
        law_type=LawType.SUBSTANTIVE,
        effective_from=date(2021, 1, 1),
        article_count=526,
    ))

    # 侵权责任法 (Tort Liability Law, 2010-2021)
    timeline.add_statute(StatuteVersion(
        statute_id="PRC_Tort_Liability_Law",
        law_type=LawType.SUBSTANTIVE,
        effective_from=date(2010, 7, 1),
        effective_until=date(2021, 1, 1),
        article_count=92,
        superseded_by="PRC_Civil_Code_Tort_Book",
    ))

    # 民法典侵权责任编 (2021-)
    timeline.add_statute(StatuteVersion(
        statute_id="PRC_Civil_Code_Tort_Book",
        law_type=LawType.SUBSTANTIVE,
        effective_from=date(2021, 1, 1),
        article_count=95,
    ))

    # 民事诉讼法 (2024 修正)
    timeline.add_statute(StatuteVersion(
        statute_id="PRC_Civil_Procedure_Law_2024",
        law_type=LawType.PROCEDURAL,
        effective_from=date(2024, 1, 1),
        article_count=302,
    ))

    # 民事诉讼法 (2021 修正, 被 2024 版取代)
    timeline.add_statute(StatuteVersion(
        statute_id="PRC_Civil_Procedure_Law_2021",
        law_type=LawType.PROCEDURAL,
        effective_from=date(2022, 1, 1),
        effective_until=date(2024, 1, 1),
        article_count=291,
        superseded_by="PRC_Civil_Procedure_Law_2024",
    ))

    return timeline


def demo_temporal_analysis():
    """Demo: Temporal statute law analysis for real scenarios."""
    print("=" * 72)
    print("TEMPORAL STATUTE LAW — DUAL-TIMESTAMP MODEL")
    print("Demo: 民法典 transition + procedural law update")
    print("=" * 72)

    timeline = build_prc_legal_timeline()

    # Scenario 1: Contract signed in 2019, dispute in 2024
    print("\n--- Scenario 1: Contract signed 2019, dispute filed 2024 ---")
    fact_date = date(2019, 6, 15)
    procedure_date = date(2024, 3, 1)

    applicable = timeline.get_applicable_statutes(fact_date, procedure_date)

    print(f"Fact date: {fact_date} → Substantive law:")
    for s in applicable[LawType.SUBSTANTIVE]:
        print(f"  {s.statute_id} (effective {s.effective_from})")

    print(f"Procedure date: {procedure_date} → Procedural law:")
    for s in applicable[LawType.PROCEDURAL]:
        print(f"  {s.statute_id} (effective {s.effective_from})")

    # Check retroactivity
    civil_code = [s for s in timeline.statutes if s.statute_id == "PRC_Civil_Code_Contract_Book"][0]
    retro = timeline.check_retroactivity(civil_code, fact_date)
    print(f"\nRetroactivity check (Civil Code vs 2019 facts):")
    print(f"  Violation: {retro['violation']}")
    print(f"  Principle: {retro['principle']}")
    if retro.get("recommendation"):
        print(f"  Recommendation: {retro['recommendation']}")

    # Scenario 2: Contract signed in 2022, dispute in 2024
    print("\n--- Scenario 2: Contract signed 2022, dispute filed 2024 ---")
    fact_date2 = date(2022, 3, 20)
    procedure_date2 = date(2024, 6, 1)

    applicable2 = timeline.get_applicable_statutes(fact_date2, procedure_date2)

    print(f"Fact date: {fact_date2} → Substantive law:")
    for s in applicable2[LawType.SUBSTANTIVE]:
        print(f"  {s.statute_id} (effective {s.effective_from})")

    retro2 = timeline.check_retroactivity(civil_code, fact_date2)
    print(f"\nRetroactivity check: violation={retro2['violation']}")

    # Scenario 3: Tort in 2020
    print("\n--- Scenario 3: Tort in 2020, procedural filing in 2024 ---")
    fact_date3 = date(2020, 8, 10)
    applicable3 = timeline.get_applicable_statutes(fact_date3, date(2024, 1, 15))

    print(f"Substantive law for 2020 tort:")
    for s in applicable3[LawType.SUBSTANTIVE]:
        print(f"  {s.statute_id} (effective {s.effective_from})")

    tort_law = [s for s in timeline.statutes if s.statute_id == "PRC_Tort_Liability_Law"][0]
    retro3 = timeline.check_retroactivity(tort_law, fact_date3)
    print(f"Retroactivity: {retro3['principle']}")

    print(f"\n{'=' * 72}")
    print("KEY RESULT: Dual-timestamp model correctly separates")
    print("substantive law (fact_date) from procedural law (current_date).")
    print("法不溯及既往 is enforced for substantive law.")
    print("程序从新 is correctly applied for procedural law.")
    print(f"{'=' * 72}")


if __name__ == "__main__":
    demo_temporal_analysis()
