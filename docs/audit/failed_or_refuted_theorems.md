# Failed or Refuted Theorems

**Date:** 2026-06-27
**Project:** legal-math-modeling
**Source of truth:** `proofs/lean/juris_lean/JurisLean/JC_Formalization.lean`

---

## Status Register

`JC_Formalization.lean` defines a `refuted_theorems` Finset with cardinality 1:

```
def refuted_theorems : Finset CoreTheorem :=
  {CoreTheorem.T18_DPPrivilege}

theorem refuted_theorems_card : refuted_theorems.card = 1 := by decide
```

There is exactly **one** refuted theorem in the formal status register.

---

## T18_DPPrivilege: DP Floor Clipping Does Not Satisfy Epsilon-DP

**CoreTheorem constructor:** `T18_DPPrivilege`
**Status:** `REFUTED`
**Evidence type:** `COUNTEREXAMPLE`
**Domain bound:** "infinite privacy ratio counterexample"

### Original Claim

The mechanism `max(0.3 * x0, x0 + Lap(Delta / epsilon))` satisfies epsilon-DP.

### Why It Fails

The floor `0.3 * x0` depends on the sensitive raw value `x0`. For two neighboring databases D, D' with `f(D) = 100` and `f(D') = 200`:

- Mechanism on D: outputs in [30, +infinity)
- Mechanism on D': outputs in [60, +infinity)
- The gap [30, 60) distinguishes D from D' with certainty
- Privacy ratio = infinity in the gap region

### Counterexample

```
f(D) = 100.0, f(D') = 200.0
epsilon = 1.0, delta = 0.0
For output y = 45.0:
  Pr[M(D)=45] > 0  (since 45 >= 0.3 * 100 = 30)
  Pr[M(D')=45] = 0  (since 45 < 0.3 * 200 = 60)
  Ratio = infinity -> violates epsilon-DP for ANY epsilon
```

### Corrected Statement

The floor-clipping mechanism does NOT satisfy epsilon-DP. Three remedies:

1. **Private floor:** Add Laplace noise to the floor threshold, compose with epsilon_1 + epsilon_2.
2. **Fixed public floor:** Use a constant c independent of data.
3. **Approximate DP:** Accept (epsilon, delta) with delta > 0.

### Artifact

`proofs/engineering_proof_artifacts/dp/dp_floor_clipping_analysis.py`

### Engineering Implications

- Replace or compose the floor clipping mechanism.
- ABSOLUTE privilege level should block release entirely; do not use epsilon=0.1 approximation.
- Add unit test for DP boundary detection.

---

## Additional Engineering-Level Refutations (Proof Artifacts)

The following refutations exist at the engineering proof artifact level but are not separately registered as `CoreTheorem` constructors in `JC_Formalization.lean`. They correspond to `REFUTED` entries in the 17-artifact proof run.

### ART-012: Graph Metric Counterexamples

**Original claim:** Graph similarity is a metric (satisfies reflexivity, symmetry, triangle inequality).

**Why it fails:**
- Reflexivity FAILS: Under conservative empty-feature policy, self-similarity is 0.4, not 1.0.
- Identity FAILS: Two non-isomorphic graphs with same |V| and |E| can score 1.0.
- Symmetry HOLDS by construction.
- Triangle inequality: NOT PROVEN, NOT REFUTED (search up to 3-vertex graphs found no violation).

**Corrected statement:** Graph similarity is a symmetric score in [0,1]. It is NOT a metric.

**Artifact:** `proofs/engineering_proof_artifacts/graph_similarity/metric_counterexamples.py`

### ART-013: DP Floor Clipping Analysis

(See T18_DPPrivilege above; this is the engineering artifact for the same refutation.)

### ART-014: Clipped Theil-Sen Refutation

**Original claim:** The clipped Theil-Sen estimator retains the 50% breakdown point guarantee of pure Theil-Sen.

**Why it fails:** The current implementation filters slopes (removes outliers) and clamps the output. Both operations change the median slope. For crafted datasets where the true median slope is outside the clip bounds, the clipped output differs from the pure median.

**Corrected statement:** The clipped pairwise median slope estimator is NOT the pure Theil-Sen estimator. It is a bounded-bias variant with no proven breakdown guarantee.

**Artifact:** `proofs/engineering_proof_artifacts/statistics/clipped_theilsen_refutation.py`

---

## Summary

| Refuted item | Scope | Source |
|---|---|---|
| T18_DPPrivilege | JC_Formalization.lean refuted_theorems | Formal status register |
| ART-012 Graph Metric | Proof artifact | metric_counterexamples.py |
| ART-013 DP Floor Clipping | Proof artifact | dp_floor_clipping_analysis.py |
| ART-014 Clipped Theil-Sen | Proof artifact | clipped_theilsen_refutation.py |

Total refuted in JC_Formalization.lean: **1** (T18_DPPrivilege).
Total refuted proof artifacts: **3** (ART-012, ART-013, ART-014).
