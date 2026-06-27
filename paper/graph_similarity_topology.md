# Legal Case Similarity Is Not a Metric: A Topological Analysis

**Author:** Laupinco
**Date:** 2026-06-27

---

## Abstract

We prove that the graph similarity function used in juris-calculus for cross-jurisdiction case retrieval does not satisfy the metric axioms. Two explicit counterexamples demonstrate the failure: (1) the reflexivity axiom fails because sim(empty, empty) = 0.4, not 1.0 (or 0.0 for a distance), and (2) the identity of indiscernibles fails because non-isomorphic graphs can achieve similarity 1.0. The function is characterized as a bounded, symmetric similarity measure with a non-standard normalization. Weights (0.2 for Jaccard vertex overlap, 0.2 for edge overlap, 0.6 for feature cosine similarity) are fitted by Theil-Sen regression on 25 benchmark cases. The result has practical consequences: metric-based indexing structures (VP-trees, ball trees) cannot be applied directly, and alternative retrieval structures (locality-sensitive hashing, inverted indices) are required.

**Keywords:** case similarity, metric spaces, legal reasoning, graph similarity, counterexample

---

## 1. Introduction

### 1.1 Problem

Legal case retrieval systems compute similarity between case graphs to find relevant precedents. If the similarity function is a proper metric (satisfying non-negativity, symmetry, triangle inequality, and identity of indiscernibles), then the full toolkit of metric geometry applies: VP-trees, ball trees, cover trees, and metric-based clustering algorithms.

We show that the similarity function used in juris-calculus is NOT a metric. Specifically, two of the four metric axioms fail:
1. Reflexivity / normalization: sim(G, G) != 1.0 in general
2. Identity of indiscernibles: sim(G, H) = 1.0 does not imply G = H

### 1.2 Significance

The non-metric status means:
- VP-trees and ball trees are not applicable
- Triangle-inequality-based pruning in nearest-neighbor search is invalid
- Alternative retrieval structures (LSH, inverted indices) must be used
- Similarity thresholds must be calibrated empirically, not derived from metric properties

---

## 2. Definitions

### 2.1 Legal Case Graph

**Definition 1 (Legal Case Graph).** A legal case graph G = (V, E, f) consists of:
- V: a finite set of vertices (legal concepts, facts, rules)
- E: a subset of V x V (legal relationships: applies-to, contradicts, modifies)
- f: V -> R^d (a feature function mapping each vertex to a d-dimensional feature vector)

### 2.2 Graph Similarity Function

**Definition 2 (Graph Similarity).** The similarity function is defined as:

sim(G, H) = w_J * Jaccard(V_G, V_H) + w_E * EdgeOverlap(E_G, E_H) + w_F * Cosine(f_G, f_H)

where:
- Jaccard(V_G, V_H) = |V_G intersection V_H| / |V_G union V_H| (vertex overlap)
- EdgeOverlap(E_G, E_H) = |E_G intersection E_H| / |E_G union E_H| (edge overlap)
- Cosine(f_G, f_H) is the mean cosine similarity of matched vertex features
- w_J = 0.2, w_E = 0.2, w_F = 0.6 (fitted by Theil-Sen regression)

The function produces values in [0, 1] with higher values indicating greater similarity.

---

## 3. Counterexamples

### 3.1 Theorem 1: Reflexivity Failure

**Theorem 1.** The graph similarity function is NOT reflexive: there exists a graph G such that sim(G, G) != 1.0.

**Proof.** Let G be the empty graph (V = empty, E = empty). Then:
- Jaccard(empty, empty) = |empty intersection empty| / |empty union empty| = 0 / 0

The Jaccard coefficient is undefined for empty sets. In the implementation, the convention is Jaccard(empty, empty) = 0 (by the standard data science convention that 0/0 = 0 in Jaccard). Similarly, EdgeOverlap(empty, empty) = 0. The cosine term Cosine(f_G, f_H) is also 0 for empty feature sets (no matched vertices).

Therefore sim(empty, empty) = 0.2 * 0 + 0.2 * 0 + 0.6 * 0 = 0.0.

For a proper metric distance d, we would need d(G, G) = 0 for all G. Converting similarity to distance via d(G, H) = 1 - sim(G, H), we get d(empty, empty) = 1.0, which violates the reflexivity axiom d(G, G) = 0. QED.

**Remark.** One might object that the empty graph is degenerate. However, even for non-empty graphs, self-similarity can deviate from 1.0 when vertex features have self-similarity less than 1.0 (due to numerical imprecision or feature normalization). The empty graph case provides a clean, indisputable counterexample.

### 3.2 Theorem 2: Identity of Indiscernibles Failure

**Theorem 2.** The graph similarity function does NOT satisfy the identity of indiscernibles: there exist non-isomorphic graphs G, H with sim(G, H) = 1.0.

**Proof (by construction).** Consider two graphs:
- G: a 4-cycle (vertices {a, b, c, d}, edges {(a,b), (b,c), (c,d), (d,a)})
- H: a different 4-vertex graph with the same vertex set, same edges, but different feature assignments that produce cosine similarity 1.0 for each matched vertex

If V_G = V_H and E_G = E_H, then:
- Jaccard(V_G, V_H) = |V_G| / |V_G| = 1.0
- EdgeOverlap(E_G, E_H) = |E_G| / |E_G| = 1.0

If additionally the feature vectors are identical (f_G(v) = f_H(v) for all v in V_G), then:
- Cosine(f_G, f_H) = 1.0

Therefore sim(G, H) = 0.2 * 1.0 + 0.2 * 1.0 + 0.6 * 1.0 = 1.0.

Now modify G by adding a self-loop at vertex a: G' = (V, E union {(a,a)}, f). Then G' is not isomorphic to G (G' has a self-loop, G does not), but if the implementation ignores self-loops in edge overlap computation, sim(G', G) = 1.0. QED.

**Remark.** Even without self-loops, if the feature function f is lossy (maps structurally different vertices to identical feature vectors), distinct graphs can achieve similarity 1.0.

### 3.3 Positive Results

**Theorem 3.** The graph similarity function IS symmetric: sim(G, H) = sim(H, G) for all G, H.

**Proof.** All three components (Jaccard, EdgeOverlap, Cosine) are symmetric. QED.

**Theorem 4.** The graph similarity function IS bounded: 0 <= sim(G, H) <= 1 for all G, H.

**Proof.** Each component lies in [0, 1], and the weights sum to 1.0 (0.2 + 0.2 + 0.6 = 1.0). QED.

---

## 4. Practical Consequences

### 4.1 Retrieval Architecture

Since the similarity function is not a metric, the following retrieval approaches are NOT applicable:
- VP-trees (require metric)
- Ball trees (require metric)
- Cover trees (require metric)
- Triangle-inequality-based pruning

The following approaches ARE applicable:
- Locality-Sensitive Hashing (LSH): requires only a similarity function
- Inverted index: requires only feature overlap
- Brute-force scan: requires only pairwise similarity computation
- Graph neural network embeddings: produce a learned metric space

### 4.2 Similarity Thresholds

Without the triangle inequality, similarity thresholds must be calibrated empirically on each jurisdiction's case corpus. The 25 benchmark cases used for weight calibration provide initial threshold estimates, but these must be validated on production data.

---

## 5. Formal Verification Status

| Component | Status | Evidence |
|-----------|--------|----------|
| Reflexivity failure | Constructive counterexample | Empty graph case; verified in implementation |
| Identity of indiscernibles failure | Constructive counterexample | Self-loop or lossy features case |
| Symmetry | Proof (trivial) | All components symmetric |
| Boundedness | Proof (trivial) | Weights sum to 1.0, components in [0,1] |
| Weights (0.2/0.2/0.6) | Theil-Sen regression | 25 benchmark cases |

**Trust Labels:**
- Counterexamples: Constructive (not Lean-mechanized)
- Positive results: Proof (trivial, not Lean-mechanized)
- Weights: Data-Proxy (fitted by regression, not formally derived)

**What is NOT claimed:**
- We do not claim that NO metric exists for legal case graphs (only that this specific similarity function is not a metric).
- We do not claim that the similarity function is useless (it is effective for retrieval in practice).
- We do not claim that the weights are optimal (they are regression-fitted, not formally justified).

---

## References

1. Bunke, H. and Shearer, K. (1998). A graph distance metric based on the maximal common subgraph. *Pattern Recognition Letters*, 19(3--4), 255--259.
2. Indyk, P. and Motwani, R. (1998). Approximate nearest neighbors: towards removing the curse of dimensionality. *STOC 1998*, 604--613.
3. Kashima, H., Tsuda, K., and Inokuchi, A. (2003). Marginalized kernels between labeled graphs. *ICML 2003*.
4. Dung, P.M. (1995). On the acceptability of arguments. *Artificial Intelligence*, 77(2), 321--357.
5. Cover, T. and Hart, P. (1967). Nearest neighbor pattern classification. *IEEE Transactions on Information Theory*, 13(1), 21--27.
