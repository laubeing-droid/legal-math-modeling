"""Probabilistic Damages: expected-value damage computation under uncertainty.

Mathematical Framework
---------------------
Legal damages are often uncertain.  Instead of a single figure we model
multiple scenarios, each with a probability and an estimated damage amount.

Expected damages:

    E[D] = sum_{i=1}^{n} P(scenario_i) * D(scenario_i)

Confidence interval (assuming independence of scenarios):

    Var[D] = sum P(scenario_i) * (D(scenario_i) - E[D])^2
    CI = E[D] +/- z * sqrt(Var[D])

Risk-adjusted damages account for litigation risk (probability that
plaintiff loses on liability):

    D_risk = E[D] * (1 - litigation_risk)

This models the rational settlement calculus: a plaintiff should accept
any settlement >= D_risk.
"""

from __future__ import annotations

import math
from dataclasses import dataclass, field
from typing import List


# ---------------------------------------------------------------------------
# Data structures
# ---------------------------------------------------------------------------

@dataclass
class DamageScenario:
    """One possible damage outcome."""
    name: str
    probability: float       # P(scenario)
    damage_amount: float     # D(scenario) in currency units
    description: str = ""


@dataclass
class ProbabilisticDamages:
    """Compute expected, variance, CI, and risk-adjusted damages."""
    scenarios: List[DamageScenario]
    litigation_risk: float = 0.20    # probability plaintiff loses liability
    confidence_level: float = 0.95   # for CI computation

    @property
    def expected(self) -> float:
        return sum(s.probability * s.damage_amount for s in self.scenarios)

    @property
    def variance(self) -> float:
        mu = self.expected
        return sum(s.probability * (s.damage_amount - mu) ** 2
                   for s in self.scenarios)

    @property
    def std_dev(self) -> float:
        return math.sqrt(self.variance)

    @property
    def confidence_interval(self) -> tuple:
        z = _z_score(self.confidence_level)
        mu = self.expected
        half = z * self.std_dev
        return (max(mu - half, 0), mu + half)

    @property
    def risk_adjusted(self) -> float:
        return self.expected * (1 - self.litigation_risk)

    def report(self) -> str:
        ci_lo, ci_hi = self.confidence_interval
        lines = [
            "Probabilistic Damages Report",
            "-" * 50,
        ]
        for s in self.scenarios:
            lines.append(
                f"  {s.name:<30s}  P={s.probability:.2f}"
                f"  D={s.damage_amount:>12,.0f}"
            )
        lines += [
            "-" * 50,
            f"  E[D]           = {self.expected:>14,.2f}",
            f"  Std Dev        = {self.std_dev:>14,.2f}",
            f"  95% CI         = [{ci_lo:>12,.2f}, {ci_hi:>12,.2f}]",
            f"  Litigation risk= {self.litigation_risk:.2f}",
            f"  Risk-adjusted  = {self.risk_adjusted:>14,.2f}",
        ]
        return "\n".join(lines)


# ---------------------------------------------------------------------------
# Z-score approximation (rational approximation of inverse normal CDF)
# ---------------------------------------------------------------------------

def _z_score(confidence: float) -> float:
    """Approximate two-tailed z-score for common confidence levels."""
    _table = {0.90: 1.645, 0.95: 1.960, 0.99: 2.576}
    if confidence in _table:
        return _table[confidence]
    # Fallback: use scipy-free rational approximation
    alpha = 1 - confidence
    p = 1 - alpha / 2
    # Abramowitz & Stegun approximation
    t = math.sqrt(-2 * math.log(1 - p))
    c0, c1, c2 = 2.515517, 0.802853, 0.010328
    d1, d2, d3 = 1.432788, 0.189269, 0.001308
    return t - (c0 + c1 * t + c2 * t * t) / (1 + d1 * t + d2 * t * t + d3 * t * t * t)


# ---------------------------------------------------------------------------
# Demo
# ---------------------------------------------------------------------------

def demo() -> None:
    print("=" * 65)
    print("Probabilistic Damages — Demo")
    print("=" * 65)

    scenarios = [
        DamageScenario(
            name="Full loss (goods destroyed)",
            probability=0.30,
            damage_amount=500_000,
            description="Complete destruction of the shipment",
        ),
        DamageScenario(
            name="Partial loss (damaged goods)",
            probability=0.45,
            damage_amount=200_000,
            description="Goods arrived but were damaged",
        ),
        DamageScenario(
            name="Negligible loss (delay only)",
            probability=0.25,
            damage_amount=50_000,
            description="Goods arrived intact but late",
        ),
    ]

    pd = ProbabilisticDamages(
        scenarios=scenarios,
        litigation_risk=0.20,
        confidence_level=0.95,
    )

    print(f"\n{pd.report()}")
    print(f"\nSettlement recommendation: accept any offer >= {pd.risk_adjusted:,.0f}")
    print("\nDemo completed successfully.")


if __name__ == "__main__":
    demo()
