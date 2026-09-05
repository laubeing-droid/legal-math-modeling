"""Arbitration Reasoning: modelling arbitration-specific features vs litigation.

Mathematical Framework
---------------------
1. Party autonomy score:
   A = sum(w_i * choice_i)  where w_i is the weight of each autonomy dimension
   (arbitrator selection, seat, rules, language, applicable law).

2. Confidentiality score:
   C = procedural_confidentiality * award_confidentiality
   (each in [0, 1]).

3. Finality probability:
   P(final) = 1 - P(set_aside) where P(set_aside) depends on jurisdiction.

4. Arbitrator selection model:
   - Party-appointed: each side picks one co-arbitrator; they agree on chair.
   - Institutional: the institution appoints all three from its roster.

5. Award enforcement probability:
   P(enforce | jurisdiction) = base_rate * treaty_factor * reciprocity_factor
   Uses New York Convention (1958) as baseline.

Key differences from litigation:
  - Party autonomy (vs court assignment)
  - Confidentiality (vs public proceedings)
  - Finality (limited appeal)
  - Cross-border enforceability via NY Convention
"""

from __future__ import annotations

from dataclasses import dataclass, field
from enum import Enum
from typing import Dict, List, Optional


# ---------------------------------------------------------------------------
# Enums
# ---------------------------------------------------------------------------

class ArbitratorSelectionMethod(Enum):
    PARTY_APPOINTED = "party-appointed"
    INSTITUTIONAL = "institutional"
    SOLE_ARBITRATOR = "sole_arbitrator"


class InstitutionType(Enum):
    ICC = "ICC (International Chamber of Commerce)"
    LCIA = "LCIA (London Court of International Arbitration)"
    HKIAC = "HKIAC (Hong Kong International Arbitration Centre)"
    CIETAC = "CIETAC (China International Economic and Trade Arbitration Commission)"
    SIAC = "SIAC (Singapore International Arbitration Centre)"
    AAA_ICDR = "AAA-ICDR (American Arbitration Association)"


class NYConventionStatus(Enum):
    SIGNATORY = "signatory"
    NON_SIGNATORY = "non_signatory"
    SIGNATORY_WITH_RESERVATIONS = "signatory_with_reservations"


# ---------------------------------------------------------------------------
# Data structures
# ---------------------------------------------------------------------------

@dataclass
class Jurisdiction:
    """A legal jurisdiction relevant to arbitration."""
    name: str
    code: str
    ny_convention: NYConventionStatus
    set_aside_rate: float        # historical rate of award annulment [0, 1]
    base_enforcement_rate: float  # baseline enforcement rate [0, 1]
    reciprocity_reservation: bool = False


@dataclass
class ArbitrationClause:
    """Terms of the arbitration agreement."""
    seat: str
    institution: Optional[InstitutionType]
    selection_method: ArbitratorSelectionMethod
    number_of_arbitrators: int = 3
    language: str = "English"
    applicable_law: str = "UNCITRAL Model Law"
    confidentiality: bool = True
    rules: str = "institutional"


@dataclass
class ArbitrationCase:
    """Models a complete arbitration case."""
    name: str
    claimant_jurisdiction: Jurisdiction
    respondent_jurisdiction: Jurisdiction
    clause: ArbitrationClause
    dispute_value: float   # currency units

    @property
    def party_autonomy_score(self) -> float:
        """Score reflecting the degree of party autonomy exercised."""
        dimensions = {
            "arbitrator_selection": 0.25,
            "seat_choice": 0.20,
            "rules_choice": 0.15,
            "language_choice": 0.10,
            "applicable_law": 0.15,
            "institutional_support": 0.15,
        }
        score = 0.0
        score += dimensions["arbitrator_selection"]   # always present
        score += dimensions["seat_choice"]             # always present
        score += dimensions["rules_choice"]
        score += dimensions["language_choice"]
        score += dimensions["applicable_law"]
        if self.clause.institution is not None:
            score += dimensions["institutional_support"]
        return min(score, 1.0)

    @property
    def confidentiality_score(self) -> float:
        proc = 1.0 if self.clause.confidentiality else 0.2
        award = 0.8 if self.clause.confidentiality else 0.1
        return proc * award

    @property
    def finality_probability(self) -> float:
        """Probability the award survives set-aside proceedings."""
        seat_sa_rate = 0.05  # default for well-established seats
        return 1 - seat_sa_rate

    def enforcement_probability(self, target_jurisdiction: Jurisdiction) -> float:
        """Probability of enforcement in a given jurisdiction."""
        base = target_jurisdiction.base_enforcement_rate
        treaty = 1.0
        if target_jurisdiction.ny_convention == NYConventionStatus.SIGNATORY:
            treaty = 1.0
        elif target_jurisdiction.ny_convention == NYConventionStatus.SIGNATORY_WITH_RESERVATIONS:
            treaty = 0.85
        else:
            treaty = 0.40

        reciprocity = 0.90 if target_jurisdiction.reciprocity_reservation else 1.0
        return min(base * treaty * reciprocity, 1.0)

    def report(self) -> str:
        lines = [
            "Arbitration Case Report",
            "=" * 60,
            f"Case:            {self.name}",
            f"Dispute value:   ${self.dispute_value:>14,.0f}",
            f"Seat:            {self.clause.seat}",
            f"Institution:     {self.clause.institution.value if self.clause.institution else 'Ad hoc'}",
            f"Arbitrators:     {self.clause.number_of_arbitrators}"
            f" ({self.clause.selection_method.value})",
            f"Language:        {self.clause.language}",
            f"Applicable law:  {self.clause.applicable_law}",
            "-" * 60,
            f"Party autonomy:      {self.party_autonomy_score:.2f} / 1.00",
            f"Confidentiality:     {self.confidentiality_score:.2f} / 1.00",
            f"Finality:            {self.finality_probability:.2f} / 1.00",
        ]
        return "\n".join(lines)


# ---------------------------------------------------------------------------
# Demo
# ---------------------------------------------------------------------------

def demo() -> None:
    print("=" * 70)
    print("Arbitration Reasoning — Demo")
    print("=" * 70)

    # Jurisdictions
    china = Jurisdiction(
        name="People's Republic of China",
        code="CN",
        ny_convention=NYConventionStatus.SIGNATORY,
        set_aside_rate=0.08,
        base_enforcement_rate=0.88,
        reciprocity_reservation=True,
    )
    uk = Jurisdiction(
        name="United Kingdom",
        code="GB",
        ny_convention=NYConventionStatus.SIGNATORY,
        set_aside_rate=0.04,
        base_enforcement_rate=0.95,
    )
    usa = Jurisdiction(
        name="United States",
        code="US",
        ny_convention=NYConventionStatus.SIGNATORY,
        set_aside_rate=0.05,
        base_enforcement_rate=0.93,
    )
    non_signatory_country = Jurisdiction(
        name="Non-Convention Country",
        code="XX",
        ny_convention=NYConventionStatus.NON_SIGNATORY,
        set_aside_rate=0.20,
        base_enforcement_rate=0.50,
    )

    # Arbitration clause
    clause = ArbitrationClause(
        seat="Hong Kong SAR",
        institution=InstitutionType.HKIAC,
        selection_method=ArbitratorSelectionMethod.PARTY_APPOINTED,
        number_of_arbitrators=3,
        language="English",
        applicable_law="UNCITRAL Model Law",
        confidentiality=True,
    )

    # Case: Chinese company vs UK company
    case = ArbitrationCase(
        name="Shenzhen TechCo v. London TradeLtd",
        claimant_jurisdiction=china,
        respondent_jurisdiction=uk,
        clause=clause,
        dispute_value=12_000_000,
    )

    print(f"\n{case.report()}")

    print("\nEnforcement prospects:")
    print("-" * 60)
    for name, jurisdiction in [
        ("China", china), ("UK", uk), ("USA", usa),
        ("Non-signatory country", non_signatory_country),
    ]:
        p = case.enforcement_probability(jurisdiction)
        print(f"  {name:<25s}  P(enforce) = {p:.2f}")

    print("\nArbitration vs Litigation comparison:")
    print("-" * 60)
    comparison = [
        ("Feature",              "Arbitration",        "Litigation"),
        ("Party autonomy",       "HIGH (0.85)",        "LOW (0.10)"),
        ("Confidentiality",      "HIGH (0.80)",        "LOW (0.10)"),
        ("Finality",             "HIGH (0.95)",        "MEDIUM (0.60)"),
        ("Cross-border enforce", "NY Convention",      "Varies by treaty"),
        ("Cost at $12M dispute", "~$500K-$1M",         "~$300K-$800K"),
        ("Timeline",             "12-18 months",       "24-48 months"),
    ]
    for row in comparison:
        print(f"  {row[0]:<26s} {row[1]:<22s} {row[2]}")

    print("\nDemo completed successfully.")


if __name__ == "__main__":
    demo()
