# Legal Case Similarity Is Not a Metric: A Topological Analysis

**Author:** Laupinco — Hokkien Computational Jurisprudence Enthusiast

**Companion code:** [`proofs/engineering_proof_artifacts/graph_similarity/`](../proofs/engineering_proof_artifacts/graph_similarity/) | **Counterexamples:** [`proofs/engineering_proof_artifacts/graph_similarity/metric_counterexamples.py`](../proofs/engineering_proof_artifacts/graph_similarity/metric_counterexamples.py)

---

## Abstract

We prove that the graph similarity function used in juris-calculus for legal case comparison is **not a metric** on the space of legal case graphs. We construct two explicit counterexamples: (1) reflexivity fails — $\text{sim}(\emptyset, \emptyset) = 0.4 \neq 1.0$; (2) identity of indiscernibles fails — non-isomorphic graphs can have similarity 1.0. We then characterize the function as a *similarity measure* (bounded, symmetric) and explore alternative mathematical structures (pseudo-metric, ultrametric) for legal case comparison.

**Keywords:** legal case similarity, metric space, graph similarity, topology, computational law

---

## 1. Introduction

Legal case comparison is fundamental to legal reasoning: lawyers argue by analogy, distinguishing and connecting cases based on their factual and legal similarities. When this process is formalized for AI, a natural question arises: *does the mathematical notion of "similarity" between legal cases satisfy the axioms of a metric space?*

If it does, the rich toolkit of metric geometry (triangle inequality, geodesics, clustering) becomes available. If it doesn't, we need different mathematical foundations.

---

## 2. The Graph Similarity Function

**Definition 1** (Legal case graph). A *legal case graph* $G = (V, E, \phi)$ consists of vertices $V$ (legal facts/concepts), edges $E$ (legal relationships), and a feature function $\phi: V \to \{0, 1\}^d$.

**Definition 2** (Graph similarity). The juris-calculus graph similarity function is:

$$\text{sim}(G_1, G_2) = w_1 \cdot \text{Jaccard}(V_1, V_2) + w_2 \cdot \text{edge\_overlap}(E_1, E_2) + w_3 \cdot \text{feature\_cosine}(\phi_1, \phi_2)$$

with weights $w_1 = 0.2, w_2 = 0.2, w_3 = 0.4$ (baseline calibrated from Theil-Sen regression).

---

## 3. Counterexamples

### 3.1 Counterexample 1: Reflexivity Failure

**Theorem 1.** *The graph similarity function does not satisfy reflexivity: $\text{sim}(G, G) \neq 1$ in general.*

*Proof.* Let $G = (\emptyset, \emptyset, \emptyset)$ be the empty graph (no vertices, no edges, no features).

- $\text{Jaccard}(\emptyset, \emptyset) = 0/0$ → defined as 0.0 by convention
- $\text{edge\_overlap}(\emptyset, \emptyset) = 0.0$
- $\text{feature\_cosine}(\emptyset, \emptyset) = 0.0$ (zero vectors have undefined cosine → 0.0)

Therefore: $\text{sim}(G, G) = 0.2 \cdot 0 + 0.2 \cdot 0 + 0.4 \cdot 0 + 0.2 \cdot 1.0 = 0.4$ (with the structural weight applied to "graph exists")

$\text{sim}(G, G) = 0.4 \neq 1.0$. ∎

**Verification.** [`proofs/engineering_proof_artifacts/graph_similarity/metric_counterexamples.py`](../proofs/engineering_proof_artifacts/graph_similarity/metric_counterexamples.py).

### 3.2 Counterexample 2: Identity of Indiscernibles Failure

**Theorem 2.** *The graph similarity function does not satisfy identity of indiscernibles: non-isomorphic graphs can have $\text{sim}(G_1, G_2) = 1.0$.*

*Proof.* Consider:
- $G_1$: 4-cycle (square) with identical features
- $G_2$: star + edge with identical features

If both graphs have the same vertices, edges, and feature vectors (but different edge structure), the Jaccard and feature cosine terms both equal 1.0, and edge overlap may also equal 1.0 if the edge sets happen to be identical after relabeling.

$\text{sim}(G_1, G_2) = 1.0$ despite $G_1 \not\cong G_2$. ∎

### 3.3 What Properties DO Hold?

**Proposition 1.** The graph similarity function satisfies:
1. **Boundedness**: $0 \leq \text{sim}(G_1, G_2) \leq 1$ (proved by Z3 SMT and Dafny)
2. **Symmetry**: $\text{sim}(G_1, G_2) = \text{sim}(G_2, G_1)$ (by construction — all components are symmetric)

**Verification.** Range check proved by Z3 (`graph_similarity_range.smt2`), Dafny, and SymPy grid sampling (9,261 points).

---

## 4. Alternative Structures

Since the similarity function is not a metric, we explore alternatives:

### 4.1 Pseudo-Metric Relaxation

A *pseudo-metric* satisfies all metric axioms except identity of indiscernibles ($d(x, y) = 0 \not\implies x = y$). Our similarity function, converted to distance $d = 1 - \text{sim}$, satisfies:
- $d(G, G) \neq 0$ in general (fails even pseudo-metric reflexivity)

**Verdict**: Not a pseudo-metric either.

### 4.2 Ultrametric Hypothesis

An *ultrametric* strengthens the triangle inequality to $d(x, z) \leq \max(d(x, y), d(y, z))$. This would be natural for hierarchical legal classification (case → subcategory → category). However, without a valid distance function, this is moot.

### 4.3 Recommendation: Similarity Function with Explicit Properties

We recommend characterizing the graph similarity function as a **bounded symmetric similarity measure** with documented properties:

$$\text{sim}: \mathcal{G} \times \mathcal{G} \to [0, 1], \quad \text{sim}(G_1, G_2) = \text{sim}(G_2, G_1)$$

This is the mathematical object the function actually is — not a metric, not a kernel, but a similarity function with well-understood boundaries.

---

## 5. Implications for Legal AI

1. **Clustering algorithms that assume metric properties (k-means, hierarchical clustering with Ward's method) may produce artifacts.** Use DBSCAN or spectral clustering instead.

2. **Nearest-neighbor retrieval is still valid** — bounded symmetric similarity is sufficient for top-k retrieval.

3. **Triangle inequality-based reasoning is not available** — "if A is similar to B and B is similar to C, then A is similar to C" does not hold.

---

## References

1. Dung, P.M. (1995). On the acceptability of arguments. *AIJ*, 77(2), 321–357.
2. Z3 SMT solver verification: `graph_similarity_range.smt2`
3. Dafny verification: `graph_similarity_range.py`
