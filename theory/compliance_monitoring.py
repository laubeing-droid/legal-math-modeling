"""Compliance Monitoring: regulation change detection, scoring, and risk classification.

Mathematical Framework
---------------------
1. Regulation change detection:
   Given a set of compliance requirements, each requirement has a status
   (compliant / non-compliant / pending).  When a new regulation is enacted,
   we compute the delta = items affected by the change.

2. Compliance score:
   CS = items_compliant / items_total  *  100

3. Risk classification (for each affected requirement):
   risk_score = impact * probability_of_enforcement
   HIGH:   risk_score >= 0.6
   MEDIUM: risk_score >= 0.3
   LOW:    risk_score <  0.3

This module provides a lightweight framework for organisations to track
regulatory changes and assess compliance posture.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from enum import Enum
from typing import Dict, List


# ---------------------------------------------------------------------------
# Enums & data structures
# ---------------------------------------------------------------------------

class ComplianceStatus(Enum):
    COMPLIANT = "compliant"
    NON_COMPLIANT = "non_compliant"
    PENDING = "pending"
    NOT_APPLICABLE = "n/a"


class RiskLevel(Enum):
    HIGH = "HIGH"
    MEDIUM = "MEDIUM"
    LOW = "LOW"


@dataclass
class ComplianceItem:
    """A single regulatory requirement."""
    id: str
    description: str
    category: str
    status: ComplianceStatus
    # Impact of non-compliance [0, 1]
    impact: float = 0.5
    # Probability of enforcement action [0, 1]
    enforcement_probability: float = 0.5

    @property
    def risk_score(self) -> float:
        return self.impact * self.enforcement_probability

    @property
    def risk_level(self) -> RiskLevel:
        rs = self.risk_score
        if rs >= 0.6:
            return RiskLevel.HIGH
        elif rs >= 0.3:
            return RiskLevel.MEDIUM
        return RiskLevel.LOW


@dataclass
class RegulationChange:
    """Describes a new regulation or amendment."""
    name: str
    effective_date: str
    affected_items: List[str]    # IDs of affected ComplianceItems
    description: str = ""


@dataclass
class ImpactAssessment:
    """Result of assessing a regulation change."""
    change: RegulationChange
    affected_count: int
    total_count: int
    non_compliant_count: int
    compliance_gap: float        # fraction of affected items that are non-compliant
    risk_distribution: Dict[str, int]  # risk level -> count


# ---------------------------------------------------------------------------
# Compliance monitor
# ---------------------------------------------------------------------------

@dataclass
class ComplianceMonitor:
    """Monitors compliance posture and assesses regulation changes."""
    items: List[ComplianceItem]

    @property
    def total(self) -> int:
        return len(self.items)

    @property
    def compliant_count(self) -> int:
        return sum(1 for it in self.items
                   if it.status == ComplianceStatus.COMPLIANT)

    @property
    def compliance_score(self) -> float:
        if self.total == 0:
            return 100.0
        return (self.compliant_count / self.total) * 100

    def get_item(self, item_id: str) -> ComplianceItem:
        for it in self.items:
            if it.id == item_id:
                return it
        raise KeyError(f"Item '{item_id}' not found")

    def assess_change(self, change: RegulationChange) -> ImpactAssessment:
        affected = [self.get_item(iid) for iid in change.affected_items]
        non_compliant = [it for it in affected
                         if it.status != ComplianceStatus.COMPLIANT]

        risk_dist: Dict[str, int] = {lv.value: 0 for lv in RiskLevel}
        for it in affected:
            risk_dist[it.risk_level.value] += 1

        gap = len(non_compliant) / len(affected) if affected else 0.0

        return ImpactAssessment(
            change=change,
            affected_count=len(affected),
            total_count=self.total,
            non_compliant_count=len(non_compliant),
            compliance_gap=gap,
            risk_distribution=risk_dist,
        )


# ---------------------------------------------------------------------------
# Demo
# ---------------------------------------------------------------------------

def demo() -> None:
    print("=" * 70)
    print("Compliance Monitoring — Demo")
    print("=" * 70)

    items = [
        ComplianceItem("C1", "Data minimisation", "privacy",
                        ComplianceStatus.COMPLIANT, 0.8, 0.7),
        ComplianceItem("C2", "User consent management", "privacy",
                        ComplianceStatus.NON_COMPLIANT, 0.9, 0.8),
        ComplianceItem("C3", "Data retention policy", "privacy",
                        ComplianceStatus.COMPLIANT, 0.7, 0.6),
        ComplianceItem("C4", "Cross-border transfer safeguards", "privacy",
                        ComplianceStatus.NON_COMPLIANT, 0.95, 0.9),
        ComplianceItem("C5", "Breach notification procedures", "security",
                        ComplianceStatus.COMPLIANT, 0.85, 0.5),
        ComplianceItem("C6", "Financial reporting accuracy", "finance",
                        ComplianceStatus.COMPLIANT, 0.6, 0.4),
        ComplianceItem("C7", "KYC/AML procedures", "finance",
                        ComplianceStatus.PENDING, 0.9, 0.85),
    ]

    monitor = ComplianceMonitor(items=items)
    print(f"\nTotal requirements: {monitor.total}")
    print(f"Compliant:          {monitor.compliant_count}")
    print(f"Compliance score:   {monitor.compliance_score:.1f}%")

    # New regulation change
    change = RegulationChange(
        name="Data Privacy Enhancement Act 2026",
        effective_date="2026-09-01",
        affected_items=["C1", "C2", "C3", "C4"],
        description="Strengthened requirements for data minimisation, "
                    "consent, retention, and cross-border transfers.",
    )

    assessment = monitor.assess_change(change)

    print(f"\nRegulation Change: {assessment.change.name}")
    print(f"  Effective: {assessment.change.effective_date}")
    print(f"  Requirements affected: {assessment.affected_count}/{assessment.total_count}")
    print(f"  Non-compliant among affected: {assessment.non_compliant_count}")
    print(f"  Compliance gap: {assessment.compliance_gap:.0%}")
    print(f"  Risk distribution: {assessment.risk_distribution}")

    print("\n  Detailed risk per affected item:")
    for iid in change.affected_items:
        it = monitor.get_item(iid)
        print(f"    {iid}: {it.description:<35s}  "
              f"status={it.status.value:<14s}  "
              f"risk={it.risk_level.value:<7s} "
              f"(score={it.risk_score:.2f})")

    print("\nDemo completed successfully.")


if __name__ == "__main__":
    demo()
