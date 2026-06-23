# B0: Mathlib Banach API Lock

mathlib commit: v4.30.0 (c5ea00351c)

## Core Banach/Contraction API

| API | Signature | Source |
|-----|-----------|--------|
| `ContractingWith (K : NNReal) (f : α → α)` | `LipschitzWith K f ∧ K < 1` | `Topology/MetricSpace/Contracting.lean:40` |
| `efixedPoint (hf : ContractingWith K f) (x : α) (hx : edist x (f x) ≠ ∞) : α` | Unique fixed point | `Contracting.lean:110` |
| `efixedPoint_isFixedPt` | `IsFixedPt f (efixedPoint f hf x hx)` | `Contracting.lean:113` |
| `fixedPoint` | Metric space version | `Contracting.lean:274` |
| `tendsto_iterate_efixedPoint` | Iterates converge to fixed point | `Contracting.lean:117` |
| `apriori_edist_iterate_efixedPoint_le` | A-priori error bound | `Contracting.lean:121` |
| `aposteriori_edist_iterate_efixedPoint_le'` | A-posteriori error bound | `Contracting.lean:189` |

## CompleteSpace on Pi types

| API | Signature | Source |
|-----|-----------|--------|
| `Pi.complete` | `CompleteSpace (∀ i, α i)` | `Analysis/Normed/...` |

## Import paths

```
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Analysis.Normed.Lp.PiLp
```