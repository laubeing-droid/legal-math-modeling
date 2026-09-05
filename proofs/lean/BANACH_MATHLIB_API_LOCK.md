# Mathlib Banach API Lock

This file pins the exact Mathlib API surface used by the Lean formalization.
Commit: **v4.30.0** (`c5ea00351c`).

Any change to these signatures requires a new GitHub Actions clean build and an update to this lock. Lean/Lake must not run locally for this repository.

## Core Banach / Contraction API

Import: `Mathlib.Topology.MetricSpace.Contracting`

| API | Signature | Line | Description |
|-----|-----------|:----:|-------------|
| `ContractingWith` | `ContractingWith (K : NNReal) (f : α → α)` — `LipschitzWith K f ∧ K < 1` | 40 | Contraction mapping predicate |
| `efixedPoint` | `efixedPoint (hf : ContractingWith K f) (x₀ : α) (hx : edist x₀ (f x₀) ≠ ∞) : α` | 110 | Unique fixed point (extended-metric variant) |
| `efixedPoint_isFixedPt` | `IsFixedPt f (efixedPoint hf x₀ hx)` | 113 | Witness that efixedPoint is a fixed point |
| `fixedPoint` | Metric-space variant of `efixedPoint` (finite diameter) | 274 | Fixed point when `MetricSpace` is available |
| `tendsto_iterate_efixedPoint` | `Tendsto (f^[·] x₀) atTop (nhds (efixedPoint hf x₀ hx))` | 117 | Iterates converge to the fixed point |
| `apriori_edist_iterate_efixedPoint_le` | `edist (f^[n] x₀) (efixedPoint hf x₀ hx) ≤ K^n / (1 - K) * edist x₀ (f x₀)` | 121 | A-priori error bound |
| `aposteriori_edist_iterate_efixedPoint_le'` | `edist (f^[n] x₀) (efixedPoint hf x₀ hx) ≤ K^n / (1 - K) * edist (f^[n] x₀) (f^[n+1] x₀)` | 189 | A-posteriori error bound |

Source file: `Mathlib/Topology/MetricSpace/Contracting.lean`

## CompleteSpace on Pi Types

Import: `Mathlib.Analysis.Normed.Lp.PiLp`

| API | Signature | Description |
|-----|-----------|-------------|
| `Pi.complete` | `CompleteSpace (∀ i, α i)` | Finite Pi types inherit completeness from each component |

This is used to discharge the `CompleteSpace` hypothesis required by `ContractingWith.efixedPoint` when the domain is a finite product space.

Source file: `Mathlib/Analysis/Normed/Lp/PiLp.lean`

## Import Block

The following imports are used across the formalization to access the Banach API:

```lean
import Mathlib.Topology.MetricSpace.Contracting   -- ContractingWith, efixedPoint, fixedPoint, convergence
import Mathlib.Analysis.Normed.Lp.PiLp             -- Pi.complete for finite product spaces
```

## Pinned Versions

| Dependency | Version | Commit |
|------------|---------|--------|
| Lean | 4.30.0 | — |
| Mathlib | v4.30.0 | `c5ea00351c` |

## Verification

GitHub Actions, not the local machine, confirms this lock against the pinned Mathlib version. The workflow runs:

```bash
cd proofs/lean/juris_lean

# Rebuild everything (must pass with 0 incomplete-proof-token)
lake build

# Print assumption dependencies for Banach-related theorems
lake env lean JurisLean/AxiomAudit.lean
```

If the CI clean build fails after a Mathlib update, bisect the diff against the API signatures above, then update both the Lean source and this lock document.
