"""Criminal Sentencing: guideline-based sentence calculation with Chinese-law factors.

Mathematical Framework
---------------------
A guideline sentencing model computes:

    base_months = f(offense_category)
    adjustments = sum(aggravating_adjustments) - sum(mitigating_adjustments)
    adjustment_factor = max(0.1, 1 + adjustments)
    sentence_months = base_months * adjustment_factor

Chinese Criminal Law mitigating factors (reducing sentence):
  - zishou  (自首, voluntary surrender):  -20% to -40%
  - ligong   (立功, meritorious service): -10% to -30%
  - renzui   (认罪认罚, plea of guilty):  -10% to -30%

Aggravating factors (increasing sentence):
  - zhufan   (主犯, principal offender):   +10% to +30%
  - leifan   (累犯, recidivist):           +10% to +40%

The final sentence is clamped to the statutory range for the offense.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from enum import Enum
from typing import Dict, List, Optional, Tuple


# ---------------------------------------------------------------------------
# Enums
# ---------------------------------------------------------------------------

class OffenseCategory(Enum):
    """Common offense categories with base sentencing ranges (months)."""
    THEFT_MINOR = ("theft (minor)", 6, 36)
    THEFT_MAJOR = ("theft (major)", 36, 120)
    FRAUD = ("fraud", 6, 120)
    ASSAULT = ("assault", 6, 60)
    DRUG_TRAFFICKING = ("drug trafficking", 36, 180)
    EMBEZZLEMENT = ("embezzlement", 12, 180)

    def __init__(self, label: str, min_months: int, max_months: int):
        self.label = label
        self.min_months = min_months
        self.max_months = max_months


# ---------------------------------------------------------------------------
# Factor definitions
# ---------------------------------------------------------------------------

@dataclass
class SentencingFactor:
    """A single aggravating or mitigating factor."""
    name_en: str
    name_zh: str
    is_mitigating: bool
    adjustment_range: Tuple[float, float]   # e.g., (-0.40, -0.20)
    applied_adjustment: float = 0.0         # chosen value within range

    @property
    def label(self) -> str:
        direction = "mitigating" if self.is_mitigating else "aggravating"
        return f"{self.name_zh} ({self.name_en}) [{direction}]"


# Preset factor library
FACTOR_LIBRARY: Dict[str, SentencingFactor] = {
    "zishou": SentencingFactor(
        name_en="voluntary surrender",
        name_zh="自首",
        is_mitigating=True,
        adjustment_range=(-0.40, -0.20),
    ),
    "ligong": SentencingFactor(
        name_en="meritorious service",
        name_zh="立功",
        is_mitigating=True,
        adjustment_range=(-0.30, -0.10),
    ),
    "renzui": SentencingFactor(
        name_en="plea of guilty",
        name_zh="认罪认罚",
        is_mitigating=True,
        adjustment_range=(-0.30, -0.10),
    ),
    "zhufan": SentencingFactor(
        name_en="principal offender",
        name_zh="主犯",
        is_mitigating=False,
        adjustment_range=(0.10, 0.30),
    ),
    "leifan": SentencingFactor(
        name_en="recidivist",
        name_zh="累犯",
        is_mitigating=False,
        adjustment_range=(0.10, 0.40),
    ),
}


# ---------------------------------------------------------------------------
# Sentence calculator
# ---------------------------------------------------------------------------

@dataclass
class SentencingCase:
    """Calculates a guideline sentence."""
    offense: OffenseCategory
    base_months: float                       # starting point within range
    factors: List[SentencingFactor] = field(default_factory=list)

    def __post_init__(self) -> None:
        # Clamp base to statutory range
        self.base_months = max(self.offense.min_months,
                               min(self.offense.max_months, self.base_months))

    @property
    def total_adjustment(self) -> float:
        return sum(f.applied_adjustment for f in self.factors)

    @property
    def adjustment_factor(self) -> float:
        return max(0.1, 1.0 + self.total_adjustment)

    @property
    def raw_sentence_months(self) -> float:
        return self.base_months * self.adjustment_factor

    @property
    def sentence_months(self) -> float:
        """Clamp to statutory range."""
        raw = self.raw_sentence_months
        return max(self.offense.min_months,
                   min(self.offense.max_months, raw))

    @property
    def sentence_years(self) -> float:
        return self.sentence_months / 12.0

    def report(self) -> str:
        lines = [
            "Criminal Sentencing Report",
            "=" * 55,
            f"Offense:       {self.offense.label}",
            f"Base sentence: {self.base_months:.0f} months"
            f" (statutory: {self.offense.min_months}-{self.offense.max_months})",
        ]
        if self.factors:
            lines.append("\nFactors applied:")
            for f in self.factors:
                sign = "+" if f.applied_adjustment >= 0 else ""
                lines.append(f"  {f.label:<45s} {sign}{f.applied_adjustment:.0%}")
        lines += [
            "-" * 55,
            f"Total adjustment:    {self.total_adjustment:+.0%}",
            f"Adjustment factor:   {self.adjustment_factor:.4f}",
            f"Raw sentence:        {self.raw_sentence_months:.1f} months",
            f"Clamped sentence:    {self.sentence_months:.1f} months"
            f" ({self.sentence_years:.2f} years)",
        ]
        return "\n".join(lines)


# ---------------------------------------------------------------------------
# Demo
# ---------------------------------------------------------------------------

def demo() -> None:
    import copy
    print("=" * 65)
    print("Criminal Sentencing — Demo")
    print("=" * 65)

    # Case: theft (minor) with base 18 months, mitigating factors
    zishou = copy.deepcopy(FACTOR_LIBRARY["zishou"])
    zishou.applied_adjustment = -0.30  # 30% reduction

    renzui = copy.deepcopy(FACTOR_LIBRARY["renzui"])
    renzui.applied_adjustment = -0.20  # 20% reduction

    case = SentencingCase(
        offense=OffenseCategory.THEFT_MINOR,
        base_months=18,
        factors=[zishou, renzui],
    )
    print(f"\n{case.report()}")

    print("\n")

    # Case 2: drug trafficking, aggravating factors
    zhufan = FACTOR_LIBRARY["zhufan"]
    zhufan.applied_adjustment = 0.20

    leifan = FACTOR_LIBRARY["leifan"]
    leifan.applied_adjustment = 0.30

    case2 = SentencingCase(
        offense=OffenseCategory.DRUG_TRAFFICKING,
        base_months=96,
        factors=[zhufan, leifan],
    )
    print(case2.report())

    print("\nDemo completed successfully.")


if __name__ == "__main__":
    demo()
