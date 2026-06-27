# Graph Similarity: Range Proof + Metric Refutation -- Engineering Verification

> **Nature of artifact:** Python SymPy symbolic proof + exhaustive enumeration
> + counterexample construction. NOT a Lean formal proof.

## Score definition

```
score = 0.6 * jaccard + 0.4 * size_ratio
size_ratio = 0.5 * vertex_ratio + 0.5 * edge_ratio
```

## Summary of results

| Property | Status | Evidence |
|----------|--------|----------|
| Range [0, 1] | **PROVEN** | SymPy symbolic proof + exhaustive grid (21^3 = 9,261 points) |
| Reflexivity | **REFUTED** | Empty-feature graph: score(G, G) = 0.64 |
| Identity of indiscernibles | **REFUTED** | G1 != G2 but score(G1, G2) = 1.0 |
| Triangle inequality | **NOT REFUTED, NOT PROVEN** | Exhaustive search on small graphs found no counterexample |

**Conclusion: The score is NOT a metric.**

## Part A: Range proof [0, 1]

### Method 1: Symbolic (SymPy)

The score expands to:

```
score = 0.6 * jaccard + 0.2 * vertex_ratio + 0.2 * edge_ratio
```

Weights (0.6, 0.2, 0.2) are all non-negative and sum to 1.0. Therefore
`score` is a **convex combination** of three variables in [0, 1].

- Partial derivatives: all >= 0 (monotonically increasing in each input)
- Minimum: 0 (all inputs = 0)
- Maximum: 1 (all inputs = 1)
- **Range: [0, 1] -- proven.**

### Method 2: Exhaustive enumeration

Grid search over 21 * 21 * 21 = 9,261 combinations:

- Min score: 0.0 at (0, 0, 0)
- Max score: 1.0 at (1, 1, 1)
- **All combinations within [0, 1] -- verified.**

### Method 3: Z3 (pending)

The `.smt2` file is ready for offline verification but Z3 is not installed
in the current environment.

## Part B: Metric refutation

### B1: Reflexivity counterexample

**Claim:** sim(G, G) = 1 for all G

**Refutation:** Graph with all-empty features under conservative policy.

```
Graph G: vertices={A, B, C}, edges={(A,B), (B,C)}, all features=EMPTY

feature_jaccard(G, G) = 0.4    (conservative empty-feature policy)
vertex_ratio(G, G)    = 1.0
edge_ratio(G, G)      = 1.0
size_ratio(G, G)      = 1.0

score(G, G) = 0.6 * 0.4 + 0.4 * 1.0 = 0.24 + 0.40 = 0.64
```

score(G, G) = **0.64 != 1.0** -- reflexivity REFUTED.

### B2: Identity counterexample

**Claim:** score(G1, G2) = 1 implies G1 = G2

**Refutation:** Two structurally different graphs with identical feature sets
and identical |V|, |E|, using min/max size ratios (cardinality-only, blind to
actual elements):

```
G1: Cycle C4 -- edges (A,B), (B,C), (C,D), (D,A)
G2: Star+edge -- edges (A,B), (A,C), (A,D), (B,C)
Both: |V| = 4, |E| = 4, identical global features {f1, f2, f3, f4}

feature_jaccard = 1.0
vertex_ratio    = 1.0    (min(4,4) / max(4,4))
edge_ratio      = 1.0
size_ratio      = 1.0

score = 0.6 * 1.0 + 0.4 * 1.0 = 1.0
```

G1 != G2 but score(G1, G2) = **1.0** -- identity REFUTED.

The min/max ratio formulation measures only *cardinality*, not *content*,
making it blind to structural differences.

### B3: Triangle inequality

**Search method:** Exhaustive search over:

- All 2-vertex graphs (2 graphs, 8 triples)
- 3-vertex graphs with <= 2 edges (7 graphs, 343 triples)
- All 3-vertex graphs (8 graphs, 512 triples)
- 3-vertex graphs with features (189 graphs, ~6.7M triples)

**Result:** No counterexample found in the searched spaces.

**Status:** Unproven, not refuted. This does NOT mean the triangle inequality
holds -- the search was limited to small graphs (up to 3 vertices). Triangle
inequality may still fail for larger graphs or different feature configurations.

## Artifacts

| File | Description |
|------|-------------|
| `graph_similarity_range.py` | Range proof: SymPy + exhaustive |
| `graph_similarity_range_z3.py` | Z3 verification script (PENDING_TOOLCHAIN) |
| `graph_similarity_range.smt2` | SMT-LIB2 for offline Z3/CVC5 |
| `metric_counterexamples.py` | All metric counterexamples + triangle search |

## Running

```bash
python graph_similarity_range.py
python metric_counterexamples.py

# Z3 verification (requires z3-solver)
pip install z3-solver
python graph_similarity_range_z3.py
```
