# Graph Similarity: Range Proof + Metric Refutation

## Summary

This directory contains formal proofs and counterexamples for the graph similarity score:

```
score = 0.6 * jaccard + 0.4 * size_ratio
size_ratio = 0.5 * vertex_ratio + 0.5 * edge_ratio
```

**Key Results:**
| Property | Status | Evidence |
|----------|--------|----------|
| Range [0,1] | **PROVEN** | Symbolic (sympy) + Exhaustive + Z3 (pending) |
| Reflexivity | **REFUTED** | Empty-feature graph: score(G,G) = 0.64 |
| Identity of Indiscernibles | **REFUTED** | G1 != G2 but score(G1,G2) = 1.0 |
| Triangle Inequality | **NOT REFUTED** | Unproven; small-graph search exhausted |

**Conclusion: The score is NOT a metric.**

---

## Part A: Range Proof [0,1]

### Files
- `graph_similarity_range.py` — SymPy symbolic proof + exhaustive enumeration
- `graph_similarity_range_z3.py` — Z3 script (PENDING_TOOLCHAIN)
- `graph_similarity_range.smt2` — SMT-LIB2 artifact for offline verification

### Proof Method 1: Symbolic (SymPy)

The score expands to:
```
score = 0.6*jaccard + 0.2*vertex_ratio + 0.2*edge_ratio
```

Weights (0.6, 0.2, 0.2) are all **non-negative** and sum to **1.0**.
Therefore `score` is a **convex combination** of three variables in [0,1].

- Partial derivatives: all >= 0 (monotonically increasing)
- Minimum: 0 (all inputs = 0)
- Maximum: 1 (all inputs = 1)
- **Range: [0, 1]**  QED.

### Proof Method 2: Exhaustive Enumeration

Grid search over 21x21x21 = 9,261 combinations:
- Min score: 0.0000000000 at (0,0,0)
- Max score: 1.0000000000 at (1,1,1)
- **All combinations within [0,1]**  Verified.

### Proof Method 3: Z3 (Pending)

Status: `z3-solver` not installed in current environment.
The `.smt2` file is ready for offline verification:
```bash
z3 graph_similarity_range.smt2
```

---

## Part B: Metric Refutation

### File
- `metric_counterexamples.py` — All counterexamples + triangle search

### B1: Reflexivity Counterexample

**Claim:** sim(G, G) = 1 for all G  (reflexivity)

**Refutation:** Graph with all-empty features under conservative policy.

```
Graph G: vertices={A,B,C}, edges={(A,B),(B,C)}, all features=EMPTY

feature_jaccard(G, G) = 0.4    (conservative empty-feature policy)
vertex_ratio(G, G)    = 1.0
edge_ratio(G, G)      = 1.0
size_ratio(G, G)      = 1.0

score(G, G) = 0.6 * 0.4 + 0.4 * 1.0 = 0.24 + 0.40 = 0.64
```

**Result:** score(G, G) = **0.64 != 1.0**  -> Reflexivity REFUTED.

### B2: Identity Counterexample (score = 1.0)

**Claim:** score(G1, G2) = 1  =>  G1 = G2  (identity of indiscernibles)

**Refutation:** Two structurally different graphs with identical feature sets and identical |V|, |E|.

Using **min/max size ratios** (cardinality-only, blind to actual elements):
```
vertex_ratio = min(|V1|,|V2|) / max(|V1|,|V2|)
edge_ratio   = min(|E1|,|E2|) / max(|E1|,|E2|)
```

**G1:** Cycle C4 — edges (A,B), (B,C), (C,D), (D,A)  
**G2:** Star+edge — edges (A,B), (A,C), (A,D), (B,C)  
Both: |V| = 4, |E| = 4, identical global features {f1, f2, f3, f4}

```
feature_jaccard = 1.0    (identical global feature sets)
vertex_ratio    = 1.0    (min(4,4)/max(4,4) = 1.0)
edge_ratio      = 1.0    (min(4,4)/max(4,4) = 1.0)
size_ratio      = 1.0

score = 0.6 * 1.0 + 0.4 * 1.0 = 1.0
```

**Result:** G1 != G2 but score(G1, G2) = **1.0**  -> Identity REFUTED.

**Why this matters:** The min/max ratio formulation is a common variant in graph similarity libraries. It measures only *cardinality*, not *content*, making it blind to structural differences.

### B3: Triangle Inequality

**Search method:** Exhaustive search over:
- All 2-vertex graphs (2 graphs, 8 triples)
- 3-vertex graphs with <= 2 edges (7 graphs, 343 triples)
- All 3-vertex graphs (8 graphs, 512 triples)
- 3-vertex graphs with features (189 graphs, ~6.7M triples)

**Result:** No counterexample found in searched spaces.

**Status:** **unproven, not refuted** (search space exhausted)

> **IMPORTANT:** This does NOT mean the triangle inequality holds. The exhaustive search was limited to small graphs (up to 3 vertices). Triangle inequality may still fail for larger graphs or different feature configurations. We do NOT claim the score is a metric.

---

## Critical Rules Followed

1. **Empty-feature self-similarity = 0.4** (NOT 1.0) — conservative policy maintained throughout.
2. **NOT claiming the score is a metric** — reflexivity and identity are refuted.
3. **Triangle inequality** — honestly reported as "unproven, not refuted."

---

## Artifact List

| File | Description |
|------|-------------|
| `graph_similarity_range.py` | Range proof: SymPy + exhaustive |
| `graph_similarity_range_z3.py` | Z3 verification script (pending toolchain) |
| `graph_similarity_range.smt2` | SMT-LIB2 for offline Z3/CVC5 |
| `metric_counterexamples.py` | All metric counterexamples + search |
| `README.md` | This file |

## Reproduction

```bash
# Run range proof
python graph_similarity_range.py

# Run Z3 verification (requires z3-solver)
pip install z3-solver
python graph_similarity_range_z3.py

# Or use SMT2 directly
z3 graph_similarity_range.smt2

# Run metric counterexamples
python metric_counterexamples.py
```
