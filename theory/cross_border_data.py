"""Cross-Border Data: GDPR/PIPL collision detection and data flow legality.

Mathematical Framework
---------------------
1. GDPR + PIPL collision detection:
   Given a data transfer from country A to country B with data type T,
   check whether both GDPR Art. 44-49 and PIPL Art. 38-43 apply, and
   whether their requirements conflict.

2. Data flow legality matrix:
   legal(A, B, T) in {LEGAL, CONDITIONAL, ILLEGAL}
   determined by source adequacy, destination adequacy, safeguards, and
   data sensitivity.

3. Adequacy assessment:
   adeq(B) = f(legal_framework, enforcement, independence, redress)
   Each factor in [0, 1]; overall adequacy in [0, 1].
   "Adequate" threshold: 0.7.

This module helps organisations identify regulatory conflicts in
cross-border data transfers and determine the lawful basis for each flow.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from enum import Enum
from typing import Dict, List, Optional, Tuple


# ---------------------------------------------------------------------------
# Enums
# ---------------------------------------------------------------------------

class DataSensitivity(Enum):
    """Sensitivity level of personal data."""
    PUBLIC = "public"
    BASIC = "basic"             # name, email, phone
    SENSITIVE = "sensitive"     # health, biometric, financial
    RESTRICTED = "restricted"   # state secrets, genetic


class TransferLegality(Enum):
    LEGAL = "LEGAL"
    CONDITIONAL = "CONDITIONAL"
    ILLEGAL = "ILLEGAL"


class RegulationType(Enum):
    GDPR = "GDPR (EU General Data Protection Regulation)"
    PIPL = "PIPL (China Personal Information Protection Law)"
    CCPA = "CCPA (California Consumer Privacy Act)"
    PDPA_SG = "PDPA (Singapore Personal Data Protection Act)"
    LGPD = "LGPD (Brazil Lei Geral de Protecao de Dados)"


# ---------------------------------------------------------------------------
# Data structures
# ---------------------------------------------------------------------------

@dataclass
class AdequacyAssessment:
    """Measures the data protection adequacy of a jurisdiction."""
    jurisdiction: str
    code: str
    legal_framework: float     # [0, 1] comprehensiveness of law
    enforcement: float         # [0, 1] DPA enforcement effectiveness
    independence: float        # [0, 1] DPA independence
    redress: float             # [0, 1] judicial redress availability
    applicable_regulations: List[RegulationType] = field(default_factory=list)
    eu_adequacy_decision: bool = False
    china_cross_border_approval: bool = False

    @property
    def overall_adequacy(self) -> float:
        return (self.legal_framework * 0.30 +
                self.enforcement * 0.30 +
                self.independence * 0.20 +
                self.redress * 0.20)

    @property
    def is_adequate(self) -> bool:
        return self.overall_adequacy >= 0.70


@dataclass
class DataTransfer:
    """A cross-border data transfer scenario."""
    id: str
    description: str
    source: AdequacyAssessment
    destination: AdequacyAssessment
    data_type: DataSensitivity
    has_consent: bool = False
    has_standard_contractual_clauses: bool = False
    has_binding_corporate_rules: bool = False


@dataclass
class TransferAnalysis:
    """Result of analysing a data transfer."""
    transfer: DataTransfer
    gdpr_applies: bool
    pipl_applies: bool
    collision_detected: bool
    legality: TransferLegality
    reasons: List[str]
    recommendations: List[str]


# ---------------------------------------------------------------------------
# Transfer analyser
# ---------------------------------------------------------------------------

def has_regulation(adeq: AdequacyAssessment, reg: RegulationType) -> bool:
    return reg in adeq.applicable_regulations


def analyse_transfer(transfer: DataTransfer) -> TransferAnalysis:
    """Determine legality and regulatory conflicts for a data transfer."""
    reasons: List[str] = []
    recommendations: List[str] = []

    gdpr_applies = has_regulation(transfer.source, RegulationType.GDPR) or \
                   has_regulation(transfer.destination, RegulationType.GDPR)
    pipl_applies = has_regulation(transfer.source, RegulationType.PIPL) or \
                   has_regulation(transfer.destination, RegulationType.PIPL)

    collision = gdpr_applies and pipl_applies
    if collision:
        reasons.append("Both GDPR and PIPL apply to this transfer.")

    # Determine legality
    legality = TransferLegality.LEGAL

    # Check destination adequacy
    if not transfer.destination.is_adequate:
        reasons.append(
            f"Destination '{transfer.destination.jurisdiction}' inadequacy: "
            f"{transfer.destination.overall_adequacy:.2f} < 0.70 threshold."
        )
        legality = TransferLegality.CONDITIONAL
        recommendations.append("Implement supplementary safeguards (SCCs, BCRs).")

    # Sensitive data additional checks
    if transfer.data_type in (DataSensitivity.SENSITIVE, DataSensitivity.RESTRICTED):
        if not transfer.has_consent:
            reasons.append(
                f"Sensitive data ({transfer.data_type.value}) requires explicit consent."
            )
            legality = TransferLegality.CONDITIONAL
            recommendations.append("Obtain explicit data subject consent.")
        if transfer.data_type == DataSensitivity.RESTRICTED:
            if not transfer.has_binding_corporate_rules:
                legality = TransferLegality.ILLEGAL
                reasons.append(
                    "Restricted data transfer without BCRs is prohibited."
                )
                recommendations.append("Implement Binding Corporate Rules or localise data.")

    # PIPL-specific: cross-border transfer needs security assessment or certification
    if pipl_applies:
        if not transfer.source.china_cross_border_approval and \
           not transfer.destination.china_cross_border_approval:
            reasons.append("PIPL requires CAC security assessment or standard contract filing.")
            recommendations.append(
                "File standard contract with Cyberspace Administration of China."
            )

    # GDPR-specific
    if gdpr_applies:
        if transfer.destination.eu_adequacy_decision:
            reasons.append("Destination has EU adequacy decision (GDPR Art. 45).")
        elif not (transfer.has_standard_contractual_clauses or
                  transfer.has_binding_corporate_rules):
            legality = TransferLegality.CONDITIONAL
            reasons.append("No GDPR-compliant safeguard mechanism (SCCs or BCRs).")
            recommendations.append("Execute Standard Contractual Clauses (SCCs).")

    # If SCCs present, upgrade CONDITIONAL to LEGAL (if other checks pass)
    if legality == TransferLegality.CONDITIONAL and transfer.has_standard_contractual_clauses:
        if not (transfer.data_type == DataSensitivity.RESTRICTED and
                not transfer.has_binding_corporate_rules):
            # SCCs can help, but record that conditions still apply
            recommendations.append("SCCs in place; ensure TIA (Transfer Impact Assessment) is filed.")

    return TransferAnalysis(
        transfer=transfer,
        gdpr_applies=gdpr_applies,
        pipl_applies=pipl_applies,
        collision_detected=collision,
        legality=legality,
        reasons=reasons,
        recommendations=recommendations,
    )


# ---------------------------------------------------------------------------
# Demo
# ---------------------------------------------------------------------------

def demo() -> None:
    print("=" * 75)
    print("Cross-Border Data Transfer — Demo")
    print("=" * 75)

    # Jurisdictions
    eu_germany = AdequacyAssessment(
        jurisdiction="Germany (EU)", code="DE",
        legal_framework=0.95, enforcement=0.90,
        independence=0.95, redress=0.90,
        applicable_regulations=[RegulationType.GDPR],
        eu_adequacy_decision=True,
    )
    china = AdequacyAssessment(
        jurisdiction="People's Republic of China", code="CN",
        legal_framework=0.85, enforcement=0.80,
        independence=0.70, redress=0.65,
        applicable_regulations=[RegulationType.PIPL],
        china_cross_border_approval=False,
    )
    singapore = AdequacyAssessment(
        jurisdiction="Singapore", code="SG",
        legal_framework=0.88, enforcement=0.85,
        independence=0.90, redress=0.85,
        applicable_regulations=[RegulationType.PDPA_SG],
        eu_adequacy_decision=False,
    )

    # Transfer scenarios
    transfers = [
        DataTransfer(
            id="T1",
            description="EU subsidiary sends employee HR data to China HQ",
            source=eu_germany,
            destination=china,
            data_type=DataSensitivity.SENSITIVE,
            has_consent=True,
            has_standard_contractual_clauses=True,
        ),
        DataTransfer(
            id="T2",
            description="China office shares customer analytics with Singapore partner",
            source=china,
            destination=singapore,
            data_type=DataSensitivity.BASIC,
            has_consent=False,
            has_standard_contractual_clauses=False,
        ),
        DataTransfer(
            id="T3",
            description="China R&D centre transfers biometric data to EU for processing",
            source=china,
            destination=eu_germany,
            data_type=DataSensitivity.RESTRICTED,
            has_consent=True,
            has_binding_corporate_rules=True,
        ),
    ]

    for t in transfers:
        result = analyse_transfer(t)
        print(f"\n[Transfer {t.id}] {t.description}")
        print(f"  Route: {t.source.code} -> {t.destination.code}")
        print(f"  Data sensitivity: {t.data_type.value}")
        print(f"  GDPR applies:     {result.gdpr_applies}")
        print(f"  PIPL applies:     {result.pipl_applies}")
        print(f"  Collision:        {result.collision_detected}")
        print(f"  Legality:         {result.legality.value}")
        if result.reasons:
            print("  Reasons:")
            for r in result.reasons:
                print(f"    - {r}")
        if result.recommendations:
            print("  Recommendations:")
            for r in result.recommendations:
                print(f"    - {r}")

    # Adequacy comparison table
    print("\nAdequacy Scores:")
    print("-" * 75)
    print(f"  {'Jurisdiction':<25s} {'Framework':>10s} {'Enforce':>8s}"
          f" {'Independ':>9s} {'Redress':>8s} {'Overall':>8s} {'Adequate':>9s}")
    print("-" * 75)
    for a in [eu_germany, china, singapore]:
        print(f"  {a.jurisdiction:<25s} {a.legal_framework:>10.2f} {a.enforcement:>8.2f}"
              f" {a.independence:>9.2f} {a.redress:>8.2f}"
              f" {a.overall_adequacy:>8.2f} {'YES' if a.is_adequate else 'NO':>9s}")

    print("\nDemo completed successfully.")


if __name__ == "__main__":
    demo()
