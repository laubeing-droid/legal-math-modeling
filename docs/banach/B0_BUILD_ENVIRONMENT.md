# Track B0: Banach Build Environment -- Blocked

## Blocker: Lake Build Timeout

The Banach modules (WeightedSupNorm.lean, ContractionCondition.lean) require
Mathlib Analysis imports which pull in ~2951 dependency files. First build
after lake clean requires 15-20 minutes on Windows.

## Scaling Isomorphism Route (from Playbook B1)

Define S_w(x)_i = x_i / w_i  (diagonal scaling). Then:
  d_w(x,y) = ||S_w(x) - S_w(y)||_inf

With strictly positive weights, S_w is a bijection. Pull back the standard
finite-dimensional sup-space metric through S_w to inherit completeness.

## Conjugate Operator

  T_tilde = S_w o T o S_w^{-1}

Prove T_tilde is a contraction in the standard sup metric, then use
Mathlib's ContractingWith API (fixed_point, fixed_point_unique,
tendsto_iterate_fixedPoint, apriori/aposteriori error bounds).

## What Remains (Track B1-B3)

- B1: Prove weighted space is complete metric space (via scaling isomorphism)
- B2: Prove Lw <= qw => ContractingWith q T
- B3: Instantiate Mathlib fixed-point, convergence, error bounds API
- Python: BanachCertificate verifier with exact rational arithmetic

## Prerequisites

- Working lake build (need ~20 min or WSL2)
- Mathlib Analysis imports: Topology/MetricSpace/Contracting
