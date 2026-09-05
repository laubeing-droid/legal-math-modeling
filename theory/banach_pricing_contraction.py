#!/usr/bin/env python3
"""
#17: Banach Contraction --- Pricing Model Boundary
===================================================

The early draft claimed a production pricing Banach contraction.
The 2026-06-11 strict proof and legal-data validation baselines now
separate this into:

  C-real: DATA_INSUFFICIENT_FOR_PROOF
  C-toy:  TOY_SYNTHETIC_PROOF_ONLY

The scalar/effective-node smoothing map below remains useful as a toy
or experimental submodel. It must not be used as evidence that the real
LegalOS pricing system is a full-dimensional contraction.

## Current Accepted Position

  The production pricing data currently available is fee-schedule proxy
  data, not real law-firm timesheets. It can validate schemas and
  downgrade gates, not real convergence.

## Toy/Scalar Banach Submodel

  Banach's theorem: contraction mapping on complete metric space
  has a UNIQUE fixpoint, and the sequence x_{n+1} = f(x_n)
  converges with GEOMETRIC rate:

    d(x_n, x*) <= c^n / (1-c) * d(x_1, x_0)

  where c < 1 is the contraction factor.

## Allowed Claim

  The map:

    new_nodes = beta * target_nodes + (1 - beta) * current_nodes

  is a scalar contraction when 0 < beta <= 1 under the stated metric.

## Forbidden Claim

  Do not claim full-dimensional production pricing is Banach-proved.
"""

import math
from dataclasses import dataclass
from typing import Dict, Tuple, List

try:
    from model_status import get_claim
except ImportError:
    get_claim = None


# ============================================================
# Part A: Metric Space and Contraction Definition
# ============================================================

@dataclass
class PricingPoint:
    """A point in the pricing metric space."""
    effective_nodes: float
    location_factor: float
    stage_factor: float
    travel_overhead: float
    total_hours: float

    @staticmethod
    def distance(p1: "PricingPoint", p2: "PricingPoint") -> float:
        """d_abs metric on effective_nodes.

        Only effective_nodes changes across iterations; location,
        stage, and travel_overhead are FROZEN per case.
        The contraction applies to effective_nodes specifically.
        """
        return abs(p1.effective_nodes - p2.effective_nodes)


def is_contraction(f, x0, c: float, n_pairs: int = 100) -> Tuple[bool, List[float]]:
    """Verify contraction property: d(f(x), f(y)) <= c * d(x, y) for random pairs.

    Returns (holds, max_observed_ratios).
    """
    import random
    random.seed(42)
    max_ratios = []
    for _ in range(n_pairs):
        # Generate two random points
        x = PricingPoint(
            effective_nodes=random.uniform(1, 100),
            location_factor=random.choice([1.0, 1.3, 1.8]),
            stage_factor=random.choice([1.0, 1.25, 1.1]),
            travel_overhead=random.choice([0.0, 8.0, 16.0]),
            total_hours=random.uniform(1, 500),
        )
        y = PricingPoint(
            effective_nodes=random.uniform(1, 100),
            location_factor=random.choice([1.0, 1.3, 1.8]),
            stage_factor=random.choice([1.0, 1.25, 1.1]),
            travel_overhead=random.choice([0.0, 8.0, 16.0]),
            total_hours=random.uniform(1, 500),
        )
        dfx_fy = PricingPoint.distance(f(x), f(y))
        dxy = PricingPoint.distance(x, y)
        ratio = dfx_fy / dxy if dxy > 0 else 0.0
        max_ratios.append(ratio)
    holds = all(r <= c + 1e-6 for r in max_ratios)  # numerical tolerance
    assert holds, f"Banach contraction violated: max ratio {max_ratios[0] if max_ratios else 0} > c={c}"
    return holds, max_ratios


def banach_iteration(f, x0, c: float, epsilon: float = 1e-6,
                     max_iter: int = 100) -> Tuple[PricingPoint, int, List[float]]:
    """Banach fixed-point iteration with convergence tracking.

    Returns: (fixpoint, iterations, error_history)
    """
    x_curr = x0
    errors = []

    for i in range(max_iter):
        x_next = f(x_curr)
        err = PricingPoint.distance(x_next, x_curr)
        errors.append(err)

        # A priori error bound (Banach theorem)
        if i > 0:
            bound = (c ** i) / (1 - c) * errors[0]

        if err < epsilon:
            return x_next, i + 1, errors

        x_curr = x_next

    return x_curr, max_iter, errors


# ============================================================
# Part B: Pricing as Contraction Mapping
# ============================================================

class PricingContraction:
    """Toy scalar/effective-node contraction model.

    This is not a production pricing proof. The real pricing gate remains
    DATA_INSUFFICIENT_FOR_PROOF until real paired timesheet/invoice data is
    available and the production map is shown to be a contraction on a
    complete metric space.
    """

    def __init__(self, alpha: float = 1.43, target_nodes: float = None):
        self.alpha = alpha
        self.target_nodes = target_nodes  # fixed-point target (exogenous)

        # Lipschitz constants per coordinate:
        # effective_nodes: converges toward target_nodes at rate beta
        self.beta = 0.5   # exponential smoothing weight
        self.c_nodes = abs(1.0 - self.beta)  # = 0.5 < 1  (contraction proven)
        self.c_loc = 0.0    # location frozen per case
        self.c_stage = 0.0  # stage frozen per case
        self.c_travel = 0.0 # travel overhead frozen

        # Overall contraction factor
        self.c = max(self.c_nodes, self.c_loc, self.c_stage, self.c_travel)
        assert self.c < 1.0, f"Contraction factor c={self.c} must be < 1"

    def __call__(self, p: PricingPoint) -> PricingPoint:
        """One iteration of the pricing fixpoint: exponential smoothing toward target.

        new_nodes = beta * target_nodes + (1 - beta) * current_nodes

        This IS a Banach contraction on (R+, d_abs) with c = |1-beta| = 0.5.
        Two points with different N converge toward target, distance halving each step.
        """
        target = self.target_nodes if self.target_nodes is not None else p.effective_nodes
        new_nodes = self.beta * target + (1.0 - self.beta) * p.effective_nodes

        # Location and stage factors: constant per iteration (frozen per case)
        new_loc = p.location_factor
        new_stage = p.stage_factor

        # Total hours
        new_total = (new_nodes * self.alpha) * new_loc * new_stage + p.travel_overhead

        return PricingPoint(
            effective_nodes=round(new_nodes, 4),
            location_factor=new_loc,
            stage_factor=new_stage,
            travel_overhead=p.travel_overhead,
            total_hours=round(new_total, 2)
        )


# ============================================================
# Part C: Formal Comparison --- Tarski vs Banach
# ============================================================

def prove_banach_upgrade():
    """Toy theorem: scalar smoothing gives geometric convergence.

    Compare:
      Tarski:  "Fixpoint exists. Will converge eventually."
      Banach:  "Fixpoint exists. Unique. Converges at rate c^n.
                Error after n iterations: <= c^n/(1-c) * d_1"
    """
    print("=" * 60)
    print("TOY THEOREM: Scalar effective_nodes smoothing is a contraction")
    print("=" * 60)

    f = PricingContraction(alpha=1.43, target_nodes=8.0)

    # Initial point
    x0 = PricingPoint(
        effective_nodes=12.0,
        location_factor=1.8,
        stage_factor=1.25,
        travel_overhead=16.0,
        total_hours=0.0
    )

    # Run Banach iteration
    fixpoint, iterations, errors = banach_iteration(f, x0, f.c)

    print(f"\n  Contraction factor c = {f.c}")
    print(f"  Starting point: N_eff = {x0.effective_nodes}")
    print(f"  Fixpoint: N_eff = {fixpoint.effective_nodes}")
    print(f"  Total hours: {fixpoint.total_hours}h")
    print(f"  Iterations to converge: {iterations}")
    print(f"  Error history: {[f'{e:.6f}' for e in errors[:5]]}" +
          ("..." if len(errors) > 5 else ""))

    # Demonstrate geometric convergence
    print(f"\n  GEOMETRIC CONVERGENCE:")
    print(f"  Error bound after 10 iterations: c^10/(1-c) * d_1")
    theoretical_bound = (f.c ** 10) / (1 - f.c) * errors[0]
    print(f"    = {f.c}^10 / (1-{f.c}) * {errors[0]:.4f}")
    print(f"    = {theoretical_bound:.10f}")
    print(f"  Actual error after {iterations} iters: {errors[-1]:.10f}")

    # Tarski comparison
    print(f"\n  TARSKI GUARANTEE:  'Will converge' (no rate)")
    print(f"  BANACH GUARANTEE:  'Converges at rate {f.c}^n' (explicit)")
    print(f"  UPGRADE: From non-constructive existence to explicit convergence rate")

    # Verify contraction property: ANALYTICAL PROOF
    # f(x) = beta * T + (1-beta) * x
    # d(f(x), f(y)) = |beta*T + (1-beta)*x - beta*T - (1-beta)*y|
    #               = (1-beta) * |x - y|
    # Therefore c = 1-beta = 0.5 < 1. Contraction proven.
    from math import isclose
    assert isclose(1.0 - f.beta, f.c), "c must equal 1-beta"
    assert f.c < 1.0, f"c={f.c} must be < 1 for contraction"
    print(f"\n  CONTRACTION VERIFICATION (analytical):")
    print(f"    f(x) = beta*T + (1-beta)*x with beta={f.beta}")
    print(f"    Lipschitz constant c = 1-beta = {f.c}")
    print(f"    c < 1: {f.c < 1.0} (toy scalar contraction)")

    return True


def prove_unique_fixpoint():
    """Toy theorem: the scalar smoothing fixpoint is unique.

    This statement applies only to the scalar/effective_nodes submodel
    implemented above. It is not a production pricing guarantee.
    """
    print("\n" + "=" * 60)
    print("TOY THEOREM: Scalar smoothing fixpoint is unique")
    print("=" * 60)

    # Proof by contraction property
    print("""
    PROOF:

    Suppose x* and y* are both fixpoints of the pricing function f.
    Then:  f(x*) = x*  and  f(y*) = y*

    Contraction property:  d(f(x*), f(y*)) <= c * d(x*, y*)
    But f(x*) = x*, f(y*) = y*, so:
      d(x*, y*) <= c * d(x*, y*)

    Since c < 1, this requires d(x*, y*) = 0.
    Therefore x* = y* --- the fixpoint is UNIQUE.

    ENGINEERING CONSEQUENCE:
    A production pricing engine may reuse this scalar smoother only as
    an experimental component. The full pricing model must still pass a
    data-quality gate and a separate contraction/calibration check.
    """)


if __name__ == "__main__":
    holds = prove_banach_upgrade()
    prove_unique_fixpoint()

    assert holds, "Banach contraction verification FAILED"

    print("\n" + "=" * 60)
    print("SUMMARY: Toy Scalar Banach Submodel")
    print("=" * 60)
    print("""
    CLAIM 1 (Toy scalar contraction):
      The effective_nodes smoothing map is a contraction with c < 1
      under the stated scalar metric.

    CLAIM 2 (Toy unique fixpoint):
      The scalar fixpoint is unique.

    CLAIM 3 (Toy geometric rate):
      Error after n iterations <= c^n / (1-c) * d(x_1, x_0).
      With c = 0.5: error halves each iteration.

    REAL PRICING STATUS:
      DATA_INSUFFICIENT_FOR_PROOF. Current pricing observations are
      fee-schedule proxies, not real paired timesheets/invoices.

    ENGINEERING IMPLICATION:
      Implement pricing as a calibrated module with explicit
      data_quality labels. Do not promote proxy data into a real
      Banach proof.
    """)
