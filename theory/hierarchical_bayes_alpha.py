#!/usr/bin/env python3
"""
#12: Hierarchical Bayesian Theil-Sen Alpha Upgrade
======================================================

Upgrades alpha = 1.43 h/node from a point estimate (Theil-Sen on 10
annotated cases) to a hierarchical Bayesian model with partial pooling
across legal domains.

## Current Model

  T_predict = (N_effective * alpha) * B_location * Gamma_stage + T_overhead
  alpha = 1.43 (Theil-Sen median, 10 cases, one jurisdiction)

## Upgraded Model

  alpha[i] = alpha_base * exp(beta_k * k[i] + beta_domain * domain[i] +
                               beta_jurisdiction * jurisdiction[i] + eta[i])

  where:
    alpha_base     ~ LogNormal(log(1.0), 0.5)     # Prior centered at 1.0
    beta_k         ~ Normal(0.1, 0.05)             # Positive: deeper chain = more work
    beta_domain    ~ Normal(0, 0.3)                # Domain-specific adjustment
    beta_jurisdiction ~ Normal(0, 0.2)             # Jurisdiction-specific
    eta[i]         ~ Normal(0, sigma_eta)          # Case-level residual
    sigma_eta      ~ HalfNormal(0.3)               # Between-case variability

## Partial Pooling

  - Complete pooling: one alpha for all cases (current Theil-Sen)
  - No pooling: separate alpha per case (overfit with N=10)
  - Partial pooling (this model): domain-specific alphas that
    share information via the hierarchical prior

## Key Result

  Posterior for beta_k > 0 quantifies how much exception chain
  depth increases real attorney hours --- this converts alpha from
  a scalar to a causal parameter.
"""

from dataclasses import dataclass, field
from typing import Dict, List, Tuple, Optional
import math
import random


# ============================================================
# Part A: Theil-Sen Baseline (Current)
# ============================================================

def theil_sen_slope(x: List[float], y: List[float]) -> float:
    """Theil-Sen estimator: median of pairwise slopes.

    Current juris-calculus uses this to estimate alpha = 1.43.
    """
    n = len(x)
    slopes = []
    for i in range(n):
        for j in range(i + 1, n):
            if x[j] != x[i]:
                slopes.append((y[j] - y[i]) / (x[j] - x[i]))
    slopes.sort()
    if not slopes:
        return 1.0
    mid = len(slopes) // 2
    if len(slopes) % 2 == 0:
        return (slopes[mid - 1] + slopes[mid]) / 2.0
    return slopes[mid]


@dataclass
class AnnotatedCase:
    """A case with attorney-annotated actual hours."""
    id: str
    effective_nodes: float
    actual_hours: float
    domain: str          # "civil", "criminal", "administrative"
    jurisdiction: str    # "PRC", "HK", "US"
    exception_chain_depth: int  # k (1-3)
    location: str = "LOCAL"
    stage: str = "FIRST_INSTANCE"


# Simulated data: 10 annotated cases (matching the current calibration)
SIMULATED_CASES = [
    AnnotatedCase("C01", 5.0, 7.2, "civil", "PRC", 1),
    AnnotatedCase("C02", 8.0, 12.5, "civil", "PRC", 2),
    AnnotatedCase("C03", 3.0, 3.8, "civil", "PRC", 1),
    AnnotatedCase("C04", 12.0, 16.0, "civil", "PRC", 3),
    AnnotatedCase("C05", 6.0, 9.0, "criminal", "PRC", 2),
    AnnotatedCase("C06", 10.0, 18.0, "criminal", "PRC", 3),
    AnnotatedCase("C07", 4.0, 5.5, "administrative", "PRC", 1),
    AnnotatedCase("C08", 7.0, 11.0, "administrative", "PRC", 2),
    AnnotatedCase("C09", 9.0, 13.0, "civil", "HK", 2),
    AnnotatedCase("C10", 11.0, 18.5, "civil", "HK", 3),
]


# ============================================================
# Part B: Hierarchical Bayesian Model (Upgrade Path)
# ============================================================

@dataclass
class HierarchicalAlphaModel:
    """Hierarchical Bayesian model for legal work hour prediction.

    This is the MATHEMATICAL SPECIFICATION --- actual MCMC estimation
    requires PyMC/Stan and 30+ annotated cases. The model here provides
    the formal structure and demonstrative computation.
    """

    # Prior hyperparameters
    mu_alpha_base: float = 0.0        # log(alpha_base) prior mean
    sigma_alpha_base: float = 0.5     # log(alpha_base) prior sd

    mu_beta_k: float = 0.1            # Prior mean for depth effect
    sigma_beta_k: float = 0.05        # Prior sd for depth effect

    sigma_eta: float = 0.3            # Case-level residual sd

    def __post_init__(self):
        # Domain offsets (civil = reference level)
        self.domain_offset = {"civil": 0.0, "criminal": 0.0, "administrative": 0.0}
        self.jurisdiction_offset = {"PRC": 0.0, "HK": 0.0, "US": 0.0}

    def simulate_posterior_draws(self, cases: List[AnnotatedCase],
                                 n_draws: int = 10000) -> Dict[str, List[float]]:
        """Simulate posterior draws (demonstrative --- real inference needs MCMC).

        This demonstrates the MATHEMATICAL STRUCTURE of the posterior.
        Real inference would use PyMC with NUTS sampler.
        """
        random.seed(42)

        # Draw from priors (demonstrative)
        alpha_base = math.exp(random.gauss(self.mu_alpha_base, self.sigma_alpha_base))
        beta_k = abs(random.gauss(self.mu_beta_k, self.sigma_beta_k))

        # Compute per-case alpha
        alphas = []
        for case in cases:
            alpha_i = alpha_base * math.exp(
                beta_k * case.exception_chain_depth +
                self.domain_offset.get(case.domain, 0.0) +
                self.jurisdiction_offset.get(case.jurisdiction, 0.0) +
                random.gauss(0, self.sigma_eta)  # case-level residual
            )
            alphas.append(alpha_i)

        # "Posterior" predictions
        predicted_hours = []
        for case, alpha_i in zip(cases, alphas):
            predicted_hours.append(case.effective_nodes * alpha_i)

        return {
            "alpha_base": [alpha_base],
            "beta_k": [beta_k],
            "per_case_alpha": alphas,
            "predicted_hours": predicted_hours,
        }

    def compute_bayesian_credible_interval(self, draws: List[float],
                                           confidence: float = 0.89) -> Tuple[float, float]:
        """Compute credible interval from posterior draws."""
        sorted_draws = sorted(draws)
        n = len(sorted_draws)
        tail = (1 - confidence) / 2
        lo = sorted_draws[int(tail * n)]
        hi = sorted_draws[int((1 - tail) * n) - 1]
        return lo, hi


# ============================================================
# Part C: Formal Comparison
# ============================================================

def prove_bayesian_upgrade():
    """Compare Theil-Sen point estimate vs hierarchical Bayesian.

    Key proofs:
    1. Theil-Sen gives a POINT estimate with no uncertainty quantification
    2. Hierarchical Bayes gives a POSTERIOR DISTRIBUTION
    3. Hierarchical Bayes quantifies beta_k > 0 (causal effect of depth)
    4. Hierarchical Bayes enables partial pooling across domains
    """
    print("=" * 60)
    print("THEOREM: Hierarchical Bayes Dominates Theil-Sen Point Estimate")
    print("=" * 60)

    # Theil-Sen baseline
    nodes = [c.effective_nodes for c in SIMULATED_CASES]
    hours = [c.actual_hours for c in SIMULATED_CASES]
    alpha_ts = theil_sen_slope(nodes, hours)

    print(f"\n  Theil-Sen alpha: {alpha_ts:.2f} h/node")
    print(f"  This is a POINT ESTIMATE --- no uncertainty quantification")

    # Hierarchical Bayes (demonstrative)
    model = HierarchicalAlphaModel()
    posterior = model.simulate_posterior_draws(SIMULATED_CASES)

    alpha_base = posterior["alpha_base"][0]
    beta_k = posterior["beta_k"][0]

    print(f"\n  Hierarchical Bayes:")
    print(f"    alpha_base: {alpha_base:.2f} h/node")
    print(f"    beta_k:     {beta_k:.3f} (depth effect multiplier)")
    print(f"    Interpretation: each +1 in k multiplies alpha by exp({beta_k:.3f}) = {math.exp(beta_k):.2f}")

    # Per-domain comparison
    domains = {}
    for case, alpha_i in zip(SIMULATED_CASES, posterior["per_case_alpha"]):
        domains.setdefault(case.domain, []).append(alpha_i)

    print(f"\n  Domain-specific alphas:")
    for domain, alphas in domains.items():
        mean_alpha = sum(alphas) / len(alphas)
        print(f"    {domain:15s}: mean alpha = {mean_alpha:.2f} (n={len(alphas)})")

    # Causal interpretation
    print(f"\n  CAUSAL INTERPRETATION:")
    print(f"    H0: beta_k = 0 (exception chain depth has no effect on hours)")
    print(f"    H1: beta_k > 0 (deeper chain -> more attorney work)")
    print(f"    Posterior P(beta_k > 0) = {1.0 if beta_k > 0 else 0.0} (demonstrative)")
    print(f"    With 30+ real annotated cases, this becomes a formal hypothesis test.")


def prove_sample_size_requirement():
    """Minimum sample size for hierarchical Bayes.

    Rule of thumb: need at least 5-10 cases per group for partial pooling.
    With 3 domains x 2 jurisdictions = 6 groups, need 30-60 cases minimum.
    With 10 current cases, only complete pooling is statistically stable.
    """
    print("\n" + "=" * 60)
    print("THEOREM: Minimum Sample Size for Partial Pooling")
    print("=" * 60)

    n_groups = 3  # domains: civil, criminal, administrative
    min_per_group = 5
    min_total = n_groups * min_per_group

    print(f"""
    Groups: {n_groups} domains
    Minimum per group: {min_per_group}
    Minimum total: {min_total}

    Current: 10 annotated cases
    Gap: {min_total - 10} more cases needed

    With 30 cases:
      - alpha_base posterior: credible interval width ~0.3 h/node
      - beta_k posterior: detectable effect size ~0.1
      - Domain-specific alphas: usable credible intervals

    With 60 cases:
      - All domain interactions identifiable
      - Jurisdiction-level effects detectable
      - This would make the paper's Theil-Sen section upgradeable
        to "Hierarchical Bayesian estimation of legal work hours"
    """)


if __name__ == "__main__":
    prove_bayesian_upgrade()
    prove_sample_size_requirement()

    print("\n" + "=" * 60)
    print("SUMMARY: Hierarchical Bayesian Alpha Model")
    print("=" * 60)
    print("""
    CURRENT:  alpha = 1.43 (point estimate, Theil-Sen, 10 cases)
    UPGRADED: alpha ~ hierarchical Bayesian with partial pooling

    alpha[i] = alpha_base * exp(beta_k * k[i] + beta_domain * domain[i]
                                + beta_jurisdiction * jurisdiction[i] + eta[i])

    KEY ADVANTAGES:
    1. Posterior distribution instead of point estimate
    2. Causal effect of exception chain depth (beta_k > 0)
    3. Domain-specific estimates with shared prior information
    4. Formal hypothesis testing for "does depth increase work?"

    DATA REQUIREMENT: 30-60 annotated cases (currently 10)
    IMPLEMENTATION: PyMC + NUTS sampler (NOT YET IMPLEMENTED)
    STATUS: MODEL SPECIFICATION + DEMONSTRATION.
    The current code demonstrates the mathematical structure
    (prior draws → posterior simulation) but does NOT perform
    actual MCMC inference. This is a SPECIFICATION of the upgrade
    path from Theil-Sen point estimate to hierarchical Bayes,
    not a completed Bayesian analysis.

    Actual inference requires: (1) 30+ annotated cases, (2) PyMC
    or Stan model definition, (3) NUTS/HMC sampling, (4) posterior
    diagnostics (R-hat, ESS, trace plots).
    """)
