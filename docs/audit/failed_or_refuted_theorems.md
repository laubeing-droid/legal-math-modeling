# Failed or Refuted Theorems

**Date:** 2026-06-11  
**Project:** juris-calculus

---

## FR-001: Graph Similarity Strict Reflexivity

**Original Claim:**  
Graph similarity satisfies strict reflexivity: sim(G, G) = 1.0 for all G.

**Why It Fails:**  
Under the conservative empty-feature policy, a graph with no feature attributes has self-similarity measured as 0.4 (not 1.0). The similarity formula combines Jaccard and size ratios, and when features are empty, the contribution structure yields 0.4, not 1.0.

**Counterexample:**
```python
G = Graph(nodes={A,B,C}, edges={(A,B)}, features={})
# Empty features → conservative policy
sim(G, G) = 0.64  # NOT 1.0
```
Measured values: `sim_empty_self = 0.4`, `sim_feature_self = 1.0`.

**Corrected Theorem:**  
Graph similarity satisfies reflexivity ONLY when all nodes have non-empty feature sets. Under conservative empty-feature policy, self-similarity of empty-feature graphs is 0.4 by design.

**Artifact:** `proof_artifacts/graph_similarity/metric_counterexamples.py`  
**Engineering Implication:**  
- Do NOT change empty_feature default to 1.0  
- If reflexive behavior needed, enable via explicit `empty_feature_policy="reflexive"`  
- Document that similarity is NOT a metric

---

## FR-002: Graph Similarity Identity of Indiscernibles

**Original Claim:**  
Graph similarity satisfies identity: sim(G1, G2) = 1.0 ⇒ G1 = G2.

**Why It Fails:**  
The size_ratio component uses only vertex count and edge count, not actual graph structure. Two non-isomorphic graphs with the same |V| and |E| but different topology can achieve score=1.0.

**Counterexample:**
```
G1 = Cycle C4 on {A,B,C,D}: edges (A,B),(B,C),(C,D),(D,A)
G2 = Star+edge on {A,B,C,D}: edges (A,B),(A,C),(A,D),(B,C)
|V|(G1)=|V|(G2)=4, |E|(G1)=|E|(G2)=4
Assuming identical feature Jaccard=1.0:
  size_ratio = 0.5*1.0 + 0.5*1.0 = 1.0
  score = 0.6*1.0 + 0.4*1.0 = 1.0
But G1 ≠ G2 (non-isomorphic)
```

**Corrected Theorem:**  
Identity of indiscernibles does NOT hold. score=1.0 implies |V| and |E| match and feature Jaccard=1.0, but not graph isomorphism.

**Artifact:** `proof_artifacts/graph_similarity/metric_counterexamples.py`  
**Engineering Implication:**  
- Document that score=1.0 does not mean identical graphs  
- Do not use as equality test  
- Add structural component if identity desired

---

## FR-003: Graph Similarity Metric Claim

**Original Claim:**  
Graph similarity is a metric (satisfies reflexivity, symmetry, triangle inequality).

**Why It Fails:**  
- Reflexivity: FAILS (see FR-001)
- Identity: FAILS (see FR-002)
- Symmetry: HOLDS (by construction of formula)
- Triangle inequality: NOT PROVEN and NOT REFUTED (exhaustive search on small graphs found no violation, but not proven)

**Corrected Theorem:**  
Graph similarity is a symmetric score in [0,1]. It is NOT a metric. Triangle inequality status: unproven, not refuted in search up to 3-vertex graphs.

**Artifact:** `proof_artifacts/graph_similarity/metric_counterexamples.py`  
**Engineering Implication:**  
- Remove all "metric" claims from documentation  
- Document as "contextual overlap score" not distance metric  
- Do not rely on metric properties for clustering thresholds

---

## FR-004: DP Floor Clipping Satisfies ε-DP

**Original Claim:**  
The mechanism `max(0.3*x0, x0 + Lap(Δ/ε))` satisfies ε-DP.

**Why It Fails:**  
The floor `0.3*x0` depends on the sensitive raw value `x0`. For two neighboring databases D, D' with `f(D)=100` and `f(D')=200`:
- Mechanism on D: outputs in [30, +∞)
- Mechanism on D': outputs in [60, +∞)
- The gap [30, 60) distinguishes D from D' with certainty
- Privacy ratio = ∞ in the gap region

**Counterexample:**
```python
f(D) = 100.0, f(D') = 200.0
epsilon = 1.0, delta = 0.0
# For output y = 45.0:
Pr[M(D)=45] > 0   (since 45 >= 0.3*100 = 30)
Pr[M(D')=45] = 0  (since 45 < 0.3*200 = 60)
# Ratio = ∞ → violates ε-DP for ANY ε
```

**Corrected Theorem:**  
The floor-clipping mechanism does NOT satisfy ε-DP. Three remedies:
1. Private floor: add Lap noise to floor threshold, compose with ε₁+ε₂
2. Fixed public floor: use constant c independent of data
3. Approximate DP: accept (ε, δ) with δ > 0

**Artifact:** `proof_artifacts/dp/dp_floor_clipping_analysis.py`  
**Engineering Implication:**  
- Replace or compose floor clipping mechanism  
- ABSOLUTE privilege level should block release entirely, not use ε=0.1 approximation  
- Add unit test for DP boundary detection

---

## FR-005: Clipped Theil-Sen Retains Breakdown Guarantee

**Original Claim:**  
The clipped Theil-Sen estimator `calibrate_theilsen()` retains the 50% breakdown point guarantee of pure Theil-Sen.

**Why It Fails:**  
The current implementation filters slopes (removes outliers) and clamps the output. Both operations change the median slope. For a crafted dataset where the true median slope is outside the clip bounds, the clipped output differs from the pure median.

**Counterexample:**
```python
dataset = [(1,2), (2,4), (3,100), (4,8), (5,10), (6,12)]
# Pure Theil-Sen median slope: includes the outlier influence
# Clipped estimator: clamps output to [min_slope, max_slope]
# Result: difference of 11.5 to 15.3 in verified tests
```
5/6 counterexamples show non-zero differences.

**Corrected Theorem:**  
The clipped pairwise median slope estimator is NOT the pure Theil-Sen estimator. It is a bounded-bias variant with no proven breakdown guarantee. Rename to `calibrate_clipped_pairwise_median`.

**Artifact:** `proof_artifacts/statistics/clipped_theilsen_refutation.py`  
**Engineering Implication:**  
- Rename `calibrate_theilsen` → `calibrate_clipped_pairwise_median` (keep wrapper)  
- Add `calibrate_siegel_repeated_median` as robust alternative  
- Document that clipped estimator does NOT have 50% breakdown guarantee  
- Users requiring robustness should use Siegel repeated median

---

## FR-006: Tarski Global Monotone Fixpoint (Evaluator)

**Original Claim (implicit):**  
The production evaluator converges by Tarski's fixpoint theorem on a complete lattice.

**Why It Fails:**  
The production evaluator contains:
- Rebuttal mechanism (non-monotonic)
- Confidence zeroing (non-monotonic)
- State tracker mutation (breaks purity)
- Constraint rules (can remove facts)
- CriticalClarityFailure (absorbing state)
- MAX_MODIFICATION_COUNT (hard bound)

These break the complete lattice and monotonicity prerequisites for Tarski's theorem.

**Corrected Theorem:**  
The evaluator satisfies BOUNDED OPERATIONAL TERMINATION (verified):
1. iteration_count ≤ max_iterations
2. rules_applied grows monotonically
3. exception_visited set blocks recursion cycles
4. CriticalClarityFailure is absorbing
5. MAX_MODIFICATION_COUNT bounds rebuttal mutation

**Artifact:** `proof_artifacts/fixpoint/production_bounded_termination.py`  
**Engineering Implication:**  
- Do NOT replace FixpointEvaluator with Tarski-based proof  
- Document bounded operational termination as design guarantee  
- Shadow-mode Dung AAF evaluator available as alternative
