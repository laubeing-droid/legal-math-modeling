"""IP Valuation: patent decay, trademark strength, and licensing royalty models.

Mathematical Framework
---------------------
1. Patent value decay (exponential):
   V(t) = V_0 * exp(-lambda * t)
   where V_0 is the initial assessed value, lambda is the decay constant,
   and t is years elapsed (or years remaining determines remaining value).

2. Trademark strength (multiplicative):
   S = brand_recognition * distinctiveness * market_share
   Each factor is in [0, 1].

3. Licensing royalty:
   R = base_rate * IP_strength * market_size
   where base_rate is a percentage (e.g. 5%), IP_strength is the composite
   strength score, and market_size is in currency units.
"""

from __future__ import annotations

import math
from dataclasses import dataclass, field
from typing import List


# ---------------------------------------------------------------------------
# Patent valuation
# ---------------------------------------------------------------------------

@dataclass
class Patent:
    """A patent with exponential value decay."""
    name: str
    initial_value: float       # V_0 (currency units)
    decay_lambda: float        # decay rate per year
    years_to_expiry: int       # remaining life

    def value_at(self, t: float) -> float:
        """Value at time t years from now."""
        return self.initial_value * math.exp(-self.decay_lambda * t)

    @property
    def current_value(self) -> float:
        return self.value_at(0)

    @property
    def value_at_expiry(self) -> float:
        return self.value_at(self.years_to_expiry)

    @property
    def remaining_value_ratio(self) -> float:
        return math.exp(-self.decay_lambda * self.years_to_expiry)

    def value_schedule(self) -> List[tuple]:
        """Value at each year from now to expiry."""
        return [(t, self.value_at(t)) for t in range(self.years_to_expiry + 1)]


# ---------------------------------------------------------------------------
# Trademark strength
# ---------------------------------------------------------------------------

@dataclass
class Trademark:
    """A trademark with composite strength model."""
    name: str
    brand_recognition: float   # [0, 1]
    distinctiveness: float     # [0, 1]
    market_share: float        # [0, 1]
    annual_revenue: float      # revenue attributable to mark

    @property
    def strength(self) -> float:
        return self.brand_recognition * self.distinctiveness * self.market_share

    @property
    def estimated_value(self) -> float:
        """Rough valuation: strength * revenue multiplier."""
        return self.strength * self.annual_revenue * 5  # 5-year multiplier


# ---------------------------------------------------------------------------
# Licensing royalty
# ---------------------------------------------------------------------------

@dataclass
class LicenseAgreement:
    """Licensing royalty computation."""
    base_rate: float           # e.g., 0.05 for 5%
    ip_strength: float         # composite IP strength [0, 1]
    market_size: float         # total addressable market (currency)

    @property
    def annual_royalty(self) -> float:
        return self.base_rate * self.ip_strength * self.market_size

    def royalty_over_term(self, years: int) -> float:
        return self.annual_royalty * years


# ---------------------------------------------------------------------------
# Demo
# ---------------------------------------------------------------------------

def demo() -> None:
    print("=" * 70)
    print("IP Valuation — Demo")
    print("=" * 70)

    # 1. Patent valuation
    patent = Patent(
        name="US Patent 10,XXX,XXX — Method for Automated Contract Analysis",
        initial_value=5_000_000,
        decay_lambda=0.15,
        years_to_expiry=8,
    )
    print(f"\n[Patent] {patent.name}")
    print(f"  Initial value:    ${patent.initial_value:>14,.0f}")
    print(f"  Decay rate (lambda): {patent.decay_lambda:.2f}/year")
    print(f"  Years to expiry:  {patent.years_to_expiry}")
    print(f"  Current value:    ${patent.current_value:>14,.0f}")
    print(f"  Value at expiry:  ${patent.value_at_expiry:>14,.0f}")
    print(f"  Remaining ratio:  {patent.remaining_value_ratio:.4f}")
    print("\n  Year-by-year schedule:")
    for yr, val in patent.value_schedule():
        bar = "#" * int(val / patent.initial_value * 40)
        print(f"    Year {yr:>2}: ${val:>12,.0f}  {bar}")

    # 2. Trademark strength
    tm = Trademark(
        name="LegalMind(R)",
        brand_recognition=0.85,
        distinctiveness=0.90,
        market_share=0.35,
        annual_revenue=2_000_000,
    )
    print(f"\n[Trademark] {tm.name}")
    print(f"  Brand recognition: {tm.brand_recognition:.2f}")
    print(f"  Distinctiveness:   {tm.distinctiveness:.2f}")
    print(f"  Market share:      {tm.market_share:.2f}")
    print(f"  Strength S:        {tm.strength:.4f}")
    print(f"  Annual revenue:    ${tm.annual_revenue:>12,.0f}")
    print(f"  Estimated value:   ${tm.estimated_value:>12,.0f}")

    # 3. Licensing royalty
    license_agr = LicenseAgreement(
        base_rate=0.05,
        ip_strength=tm.strength,
        market_size=50_000_000,
    )
    print(f"\n[Licensing Royalty]")
    print(f"  Base royalty rate: {license_agr.base_rate:.0%}")
    print(f"  IP strength:      {license_agr.ip_strength:.4f}")
    print(f"  Market size:      ${license_agr.market_size:>14,.0f}")
    print(f"  Annual royalty:   ${license_agr.annual_royalty:>14,.0f}")
    print(f"  5-year royalty:   ${license_agr.royalty_over_term(5):>14,.0f}")

    print("\nDemo completed successfully.")


if __name__ == "__main__":
    demo()
