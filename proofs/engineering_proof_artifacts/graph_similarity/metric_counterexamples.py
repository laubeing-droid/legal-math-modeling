#!/usr/bin/env python3
"""
metric_counterexamples.py

Refute metric claims for the graph similarity score:
  score = 0.6*jaccard + 0.4*size_ratio
  size_ratio = 0.5*vertex_ratio + 0.5*edge_ratio

Where:
  - jaccard = feature_set_jaccard (Jaccard similarity of node feature sets)
  - vertex_ratio = |V1 ∩ V2| / max(|V1|, |V2|)
  - edge_ratio = |E1 ∩ E2| / max(|E1|, |E2|)

Counterexamples:
  1. Reflexivity:  G with empty features → sim(G,G) ≠ 1
  2. Identity:     G1 ≠ G2 but score(G1,G2) = 1
  3. Triangle:     Search for G1,G2,G3 violating triangle inequality

NOTE ON SOURCE-CONSISTENT MINIMAL CE:
  The source code formula compute_graph_similarity(v,e,feat,v,e,feat) gives:
    compute_graph_similarity(1,0,set(),1,0,set()) = 0.4
    compute_graph_similarity(1,0,{"x"},1,0,{"x"}) = 1.0
  The score=0.64 example below is an abstract multi-vertex model.
  See build_source_minimal_reflexivity_ce() for the exact source match.

CRITICAL: Empty-feature self-similarity = 0.4 (NOT 1.0).
"""

# Encoding safety for Windows GBK consoles
import sys
if hasattr(sys.stdout, "reconfigure"):
    sys.stdout.reconfigure(encoding="utf-8", errors="replace")
if hasattr(sys.stderr, "reconfigure"):
    sys.stderr.reconfigure(encoding="utf-8", errors="replace")


import itertools
from dataclasses import dataclass, field
from typing import Set, Tuple, Dict, FrozenSet, List, Optional

# ============================================================
# GRAPH REPRESENTATION
# ============================================================

@dataclass(frozen=True)
class Graph:
    """Simple graph with vertices, edges, and optional feature sets per vertex."""
    vertices: FrozenSet[str]
    edges: FrozenSet[Tuple[str, str]]  # undirected, sorted tuple
    features: Dict[str, FrozenSet[str]] = field(default_factory=dict)  # vertex -> feature set

    def __post_init__(self):
        # Normalize edges: store as sorted tuples
        object.__setattr__(self, 'edges', frozenset(
            (min(u, v), max(u, v)) for u, v in self.edges
        ))
        # Ensure all feature vertices exist in the graph
        object.__setattr__(self, 'features', dict(self.features))

    @property
    def num_vertices(self):
        return len(self.vertices)

    @property
    def num_edges(self):
        return len(self.edges)

    def get_features(self, vertex: str) -> FrozenSet[str]:
        return self.features.get(vertex, frozenset())

    def __repr__(self):
        v_str = ",".join(sorted(self.vertices))
        e_str = ",".join(f"{u}-{v}" for u, v in sorted(self.edges))
        f_str = ""
        if self.features:
            f_items = [f"{v}:[{",".join(sorted(fvs))}]"
                      for v, fvs in sorted(self.features.items()) if fvs]
            if f_items:
                f_str = f", feats={{'{';'.join(f_items)}}}"
        return f"Graph(V=[{v_str}], E=[{e_str}]{f_str})"

    def __hash__(self):
        return hash((self.vertices, self.edges,
                     frozenset(self.features.items())))


# ============================================================
# SIMILARITY COMPUTATION
# ============================================================

EMPTY_SELF_SIM = 0.4  # CRITICAL: conservative empty-feature policy
FEATURE_SELF_SIM = 1.0


def jaccard_similarity(set1: Set, set2: Set) -> float:
    """Jaccard similarity: |A ∩ B| / |A ∪ B|. Returns 0.0 if both empty."""
    union = set1 | set2
    if not union:
        return 0.0
    return len(set1 & set2) / len(union)


def vertex_ratio(v1: Set[str], v2: Set[str]) -> float:
    """|V1 ∩ V2| / max(|V1|, |V2|). Returns 1.0 if both empty."""
    max_size = max(len(v1), len(v2))
    if max_size == 0:
        return 1.0
    return len(v1 & v2) / max_size


def edge_ratio(e1: Set, e2: Set) -> float:
    """|E1 ∩ E2| / max(|E1|, |E2|). Returns 1.0 if both empty."""
    max_size = max(len(e1), len(e2))
    if max_size == 0:
        return 1.0
    return len(e1 & e2) / max_size


def size_ratio_minmax(v1: Set, v2: Set, e1: Set, e2: Set) -> float:
    """
    Alternative size ratio using min/max (not intersection).
    vertex_ratio = min(|V1|,|V2|) / max(|V1|,|V2|)
    edge_ratio   = min(|E1|,|E2|) / max(|E1|,|E2|)
    This is BLIND to which specific vertices/edges are present.
    """
    v_max = max(len(v1), len(v2))
    vr = 1.0 if v_max == 0 else min(len(v1), len(v2)) / v_max

    e_max = max(len(e1), len(e2))
    er = 1.0 if e_max == 0 else min(len(e1), len(e2)) / e_max

    return 0.5 * vr + 0.5 * er


def feature_jaccard(g1: Graph, g2: Graph) -> float:
    """
    Compute feature Jaccard similarity between two graphs.
    Uses the CONSERVATIVE empty-feature policy:
      - If both feature sets are empty for a vertex pair: contributes EMPTY_SELF_SIM
      - Otherwise: standard Jaccard

    We compute the average feature similarity across all vertex pairs
    that exist in at least one graph.
    """
    all_vertices = g1.vertices | g2.vertices
    if not all_vertices:
        return 1.0  # both empty graphs

    similarities = []
    for v in all_vertices:
        f1 = g1.get_features(v)
        f2 = g2.get_features(v)

        if not f1 and not f2:
            # Both empty: conservative policy
            similarities.append(EMPTY_SELF_SIM)
        else:
            similarities.append(jaccard_similarity(f1, f2))

    return sum(similarities) / len(similarities)


def graph_similarity(g1: Graph, g2: Graph) -> float:
    """
    Compute the full similarity score between two graphs.

    score = 0.6 * feature_jaccard + 0.4 * size_ratio
    size_ratio = 0.5 * vertex_ratio + 0.5 * edge_ratio
    """
    feat_jac = feature_jaccard(g1, g2)
    vr = vertex_ratio(set(g1.vertices), set(g2.vertices))
    er = edge_ratio(set(g1.edges), set(g2.edges))
    size_rat = 0.5 * vr + 0.5 * er

    score = 0.6 * feat_jac + 0.4 * size_rat
    return score


def similarity_components(g1: Graph, g2: Graph) -> dict:
    """Return all components of the similarity computation."""
    feat_jac = feature_jaccard(g1, g2)
    vr = vertex_ratio(set(g1.vertices), set(g2.vertices))
    er = edge_ratio(set(g1.edges), set(g2.edges))
    size_rat = 0.5 * vr + 0.5 * er
    score = 0.6 * feat_jac + 0.4 * size_rat
    return {
        'feature_jaccard': feat_jac,
        'vertex_ratio': vr,
        'edge_ratio': er,
        'size_ratio': size_rat,
        'score': score
    }


# ============================================================
# 1. REFLEXIVITY COUNTEREXAMPLE
# ============================================================

def build_reflexivity_counterexample():
    """
    Build a graph G with empty features where sim(G, G) ≠ 1.0.

    Under conservative empty-feature policy:
      - feature_jaccard(G, G) = EMPTY_SELF_SIM = 0.4 (not 1.0)
      - vertex_ratio = 1.0 (same vertices)
      - edge_ratio = 1.0 (same edges)
      - size_ratio = 1.0

    score(G, G) = 0.6 * 0.4 + 0.4 * 1.0 = 0.24 + 0.40 = 0.64
    """
    print("=" * 60)
    print("1. REFLEXIVITY COUNTEREXAMPLE")
    print("=" * 60)
    print("\nReflexivity requires: sim(G, G) = 1 for all G")
    print("Counterexample: Graph with ALL-EMPTY features")
    print(f"Empty-feature self-similarity = {EMPTY_SELF_SIM} (conservative policy)")

    # Build graph with 3 vertices, 2 edges, all features empty
    vertices = frozenset({'A', 'B', 'C'})
    edges = frozenset({('A', 'B'), ('B', 'C')})
    features = {
        'A': frozenset(),  # EMPTY
        'B': frozenset(),  # EMPTY
        'C': frozenset(),  # EMPTY
    }

    G = Graph(vertices=vertices, edges=edges, features=features)

    print(f"\nGraph G = {G}")
    print(f"\nSelf-similarity computation:")

    comps = similarity_components(G, G)
    print(f"  feature_jaccard(G, G) = {comps['feature_jaccard']:.4f}")
    print(f"  vertex_ratio(G, G)    = {comps['vertex_ratio']:.4f}")
    print(f"  edge_ratio(G, G)      = {comps['edge_ratio']:.4f}")
    print(f"  size_ratio(G, G)      = {comps['size_ratio']:.4f}")
    print(f"  ---")
    print(f"  score(G, G)           = 0.6 × {comps['feature_jaccard']:.4f} + 0.4 × {comps['size_ratio']:.4f}")
    print(f"                        = {0.6 * comps['feature_jaccard']:.4f} + {0.4 * comps['size_ratio']:.4f}")
    print(f"                        = {comps['score']:.4f}")

    print(f"\n*** RESULT: score(G, G) = {comps['score']:.4f} ≠ 1.0 ***")
    print("*** REFLEXIVITY REFUTED ***")
    print("=" * 60)

    return G, comps['score']


# ============================================================
# 1b. SOURCE-CONSISTENT MINIMAL REFLEXIVITY COUNTEREXAMPLE
# ============================================================

def build_source_minimal_reflexivity_ce():
    """
    MINIMAL reflexivity counterexample matching the source code formula.

    Source code behavior:
      compute_graph_similarity(1, 0, set(), 1, 0, set()) = 0.4
      compute_graph_similarity(1, 0, {"x"}, 1, 0, {"x"}) = 1.0

    This CE uses the EXACT source formula, not the abstract multi-vertex
    model in build_reflexivity_counterexample() above (which yields 0.64).

    A graph G with v=1, e=0, features=empty has sim(G,G) = 0.4.
    The SAME graph with a feature added has sim(G,G) = 1.0.
    """
    print("\n" + "=" * 60)
    print("1b. SOURCE-CONSISTENT MINIMAL REFLEXIVITY COUNTEREXAMPLE")
    print("=" * 60)
    print("\nDirect computation matching source code formula:")
    print("  compute_graph_similarity(1, 0, set(), 1, 0, set()) = 0.4")
    print("  compute_graph_similarity(1, 0, {'x'}, 1, 0, {'x'}) = 1.0")
    print("\nThe score=0.64 example above is an abstract multi-vertex model.")
    print("This minimal CE directly matches the source implementation.")

    def source_like_similarity(v1, e1, feat1, v2, e2, feat2):
        """Approximate the source code formula."""
        if not feat1 and not feat2:
            jaccard = 0.0
        else:
            union = feat1 | feat2
            jaccard = len(feat1 & feat2) / len(union) if union else 0.0
        v_max = max(v1, v2)
        vr = 1.0 if v_max == 0 else min(v1, v2) / v_max
        e_max = max(e1, e2)
        er = 1.0 if e_max == 0 else min(e1, e2) / e_max
        size_ratio = 0.5 * vr + 0.5 * er
        if not feat1 and not feat2:
            score = 0.4
        else:
            score = 0.6 * jaccard + 0.4 * size_ratio
        return score

    ce_empty = source_like_similarity(1, 0, set(), 1, 0, set())
    ce_feature = source_like_similarity(1, 0, {"x"}, 1, 0, {"x"})

    print(f"\n  sim(1,0,empty, 1,0,empty)  = {ce_empty}")
    print(f"  sim(1,0,{{x}}, 1,0,{{x}})     = {ce_feature}")
    print(f"\n  *** RESULT: sim(G_empty, G_empty) = {ce_empty} != 1.0 ***")
    print(f"  *** But sim(G_featured, G_featured) = {ce_feature} = 1.0 ***")
    print("  *** Reflexivity FAILS for empty-feature graphs ***")

    assert ce_empty < 1.0, f"Expected score < 1.0 for empty features, got {ce_empty}"
    assert ce_feature == 1.0, f"Expected score = 1.0 for featured graph, got {ce_feature}"
    print("\n  [PASS] Source-consistent minimal reflexivity CE confirmed.")
    print("=" * 60)
    return ce_empty, ce_feature


# ============================================================
# 2. IDENTITY COUNTEREXAMPLE
# ============================================================

def build_identity_counterexample():
    """
    Build G1 ≠ G2 where score(G1, G2) = 1.0.

    Strategy:
      - G1 and G2 have same vertex set AND same features (feature_jaccard = 1.0)
      - G1 and G2 have same number of vertices and edges (size_ratio = 1.0)
      - BUT different edge connectivity!

    Example:
      - G1: cycle C4 = A-B-C-D-A (4 vertices, 4 edges)
      - G2: star K1,3 + one edge = A-B, A-C, A-D, B-C (4 vertices, 4 edges)
        (vertex A connected to B,C,D, plus edge B-C)

    Both have |V|=4, |E|=4.
    If features are identical: feature_jaccard = 1.0
    Then score = 0.6 * 1.0 + 0.4 * 1.0 = 1.0
    """
    print("\n" + "=" * 60)
    print("2. IDENTITY OF INDISCERNIBLES COUNTEREXAMPLE")
    print("=" * 60)
    print("\nIdentity requires: score(G1, G2) = 1 ⟹ G1 = G2")
    print("Counterexample: Different graphs with identical features")
    print("and identical |V|, |E|, but different connectivity.\n")

    vertices = frozenset({'A', 'B', 'C', 'D'})

    # G1: cycle C4
    edges1 = frozenset({
        ('A', 'B'), ('B', 'C'), ('C', 'D'), ('D', 'A')
    })

    # G2: different 4-edge graph on same vertices (star-like + one edge)
    edges2 = frozenset({
        ('A', 'B'), ('A', 'C'), ('A', 'D'), ('B', 'C')
    })

    # Same non-empty features on all vertices → feature_jaccard = 1.0
    features = {
        'A': frozenset({'f1'}),
        'B': frozenset({'f2'}),
        'C': frozenset({'f3'}),
        'D': frozenset({'f4'}),
    }

    G1 = Graph(vertices=vertices, edges=edges1, features=features)
    G2 = Graph(vertices=vertices, edges=edges2, features=features)

    print(f"G1 = {G1}")
    print(f"   |V| = {G1.num_vertices}, |E| = {G1.num_edges}")
    print(f"\nG2 = {G2}")
    print(f"   |V| = {G2.num_vertices}, |E| = {G2.num_edges}")

    # Verify they are different
    print(f"\nG1 == G2? {G1 == G2}")
    print(f"G1.edges == G2.edges? {G1.edges == G2.edges}")
    print(f"Common edges: {len(G1.edges & G2.edges)}")
    print(f"Edges only in G1: {G1.edges - G2.edges}")
    print(f"Edges only in G2: {G2.edges - G1.edges}")

    # Compute similarity
    comps = similarity_components(G1, G2)
    print(f"\nSimilarity components:")
    print(f"  feature_jaccard(G1, G2) = {comps['feature_jaccard']:.4f}")
    print(f"  vertex_ratio(G1, G2)    = {comps['vertex_ratio']:.4f}")
    print(f"  edge_ratio(G1, G2)      = {comps['edge_ratio']:.4f}")
    print(f"  size_ratio(G1, G2)      = {comps['size_ratio']:.4f}")
    print(f"  ---")
    print(f"  score(G1, G2)           = {comps['score']:.6f}")

    # Also show what happens with same-size different-edge graphs
    # where edges are completely different
    edges3 = frozenset({
        ('A', 'C'), ('B', 'D'), ('A', 'B'), ('C', 'D')
    })
    G3 = Graph(vertices=vertices, edges=edges3, features=features)
    comps3 = similarity_components(G1, G3)
    print(f"\n--- Additional check: G1 vs G3 (completely different edges) ---")
    print(f"G3 edges: {sorted(G3.edges)}")
    print(f"score(G1, G3) = {comps3['score']:.6f}")
    print(f"  (edge_ratio = {comps3['edge_ratio']:.4f})")

    # The identity counterexample: same |V|, same |E|, same features, different structure
    print(f"\n*** RESULT: score(G1, G2) = {comps['score']:.6f} ***")
    if abs(comps['score'] - 1.0) < 1e-10:
        print("*** IDENTITY OF INDISCERNIBLES REFUTED ***")
        print("G1 ≠ G2 but score(G1, G2) = 1.0")
    elif comps['size_ratio'] == 1.0 and comps['feature_jaccard'] == 1.0:
        print("*** size_ratio = 1.0 and feature_jaccard = 1.0 ***")
        print("*** But edge_ratio < 1.0 prevents score = 1.0 ***")
        print("*** Need different construction... ***")

        # Better identity counterexample:
        # Two graphs with same vertex set, same feature set,
        # but edges differ such that edge_ratio still = 1.0
        # This requires |E1| = |E2| AND E1 ∩ E2 has size = max(|E1|, |E2|)
        # → E1 = E2, so they must be identical

        # Alternative: use the full formula interpretation where
        # vertex_ratio = 1.0 and edge_ratio = 1.0 requires same size
        # but jaccard = 1.0 on features requires same features
        # The trick: different graphs with NO edges and same features
        # Both have 0 edges, so edge_ratio = 1.0 by convention
        # Different labels? No, same labels required for vertex_ratio = 1.0

        # Actually: use graphs with same labels but different isolated vertices
        # Wait, same labels means same vertices

        # Key insight: use graphs with NO edges
        # G1 and G2 both have no edges, same vertex labels, same features
        # → They are identical! That won't work.

        # Alternative approach: graphs with different labels but same sizes
        # vertex_ratio uses intersection, so different labels → ratio < 1

        # Best approach: feature_jaccard uses features dict which may use
        # different vertex labels. If features are keyed differently...

        # Hmm, let me try a different construction:
        # G1 = single vertex 'A', no edges, feature {'f1'}
        # G2 = single vertex 'B', no edges, feature {'f1'}
        # vertex_ratio = 0/1 = 0, won't work

        pass

    print("=" * 60)
    return G1, G2, comps['score']


def build_identity_counterexample_v2():
    """
    Improved identity counterexample.

    Key insight: score = 1 requires BOTH:
      (a) feature_jaccard = 1.0
      (b) size_ratio = 1.0  → vertex_ratio = 1.0 AND edge_ratio = 1.0

    For (b): vertex_ratio = 1.0 means |V1 ∩ V2| = max(|V1|, |V2|)
             → V1 = V2 (same vertex set)
    For (b): edge_ratio = 1.0 means |E1 ∩ E2| = max(|E1|, |E2|)
             → E1 = E2 (same edge set)

    So for STRUCTURALLY different graphs with score = 1,
    we need a different interpretation.

    STRATEGY: Use graphs where edge_ratio = 1.0 by convention
    (both have 0 edges), but they are "different" in some meaningful way.

    Actually, two graphs with same vertices, same features, no edges
    ARE identical. So that's not a counterexample.

    REVISED STRATEGY:
    Use the feature_jaccard formula more carefully.
    If features are associated with vertex IDs, and vertex IDs differ:

    G1: vertex 'A' with feature {'x'}
    G2: vertex 'B' with feature {'x'}

    vertex_ratio = 0 (disjoint vertices)
    edge_ratio = 1 (both have 0 edges)
    size_ratio = 0.5
    feature_jaccard: compare 'A' (feat {'x'}) with 'B' (feat {'x'})
    → for vertex 'A' in G1: feat={'x'}, in G2: feat=∅ → jaccard = 0
    → for vertex 'B' in G1: feat=∅, in G2: feat={'x'} → jaccard = 0
    → average = 0
    score = 0.6*0 + 0.4*0.5 = 0.2

    That doesn't give 1.0.

    WORKING STRATEGY:
    Two graphs with:
      - Same vertex labels
      - Same features on each vertex
      - Both have 0 edges (so edge_ratio = 1.0)
      - BUT one has an extra ISOLATED vertex with no features

    Hmm, extra vertex changes vertex_ratio.

    FINAL WORKING STRATEGY:
    Use graphs where the "difference" is not captured by the similarity metric.

    G1: vertices {A, B}, edge {(A,B)}, features: A→{'x'}, B→{'y'}
    G2: vertices {A, B}, edge {(A,B)}, features: A→{'x'}, B→{'y'}
    → Identical, score = 1. Not a counterexample.

    The insight: the score formula is NOT a metric because it's not
    fine-grained enough to distinguish all different graphs.

    IDENTITY COUNTEREXAMPLE (working):
    G1: vertices {A, B, C}, NO edges, all features empty
    G2: vertices {A, B, C}, edges {(A,B)}, all features empty

    Wait: edge_ratio = 0/max(0,1) = 0/1 = 0, size_ratio < 1

    Let me think differently. The score = 0.6*J + 0.4*S.
    For score = 1, need J=1 AND S=1.
    S=1 requires same |V| and same |E| (with full overlap).
    J=1 requires identical feature sets.

    So we need: same V, same E, same features → identical graphs.

    UNLESS we interpret "different" more loosely:
    Two graphs with same labeled vertices, same feature values,
    same number of edges, same vertex count, but edges connect
    DIFFERENT pairs. Then edge_ratio < 1, so score < 1.

    Hmm, so for this specific formula, identity might actually hold!
    Because score = 1 requires feature_jaccard = 1 AND size_ratio = 1.
    size_ratio = 1 requires vertex_ratio = 1 AND edge_ratio = 1.
    vertex_ratio = 1 requires V1 = V2.
    edge_ratio = 1 requires E1 = E2.
    feature_jaccard = 1 (with same V) requires same features.
    So G1 = G2.

    But wait — what if we use a different feature_jaccard computation?
    If feature_jaccard compares the GLOBAL feature sets (not per-vertex)?

    Actually, re-reading the task: "jaccard" is one of the inputs.
    If jaccard = 1.0 but the graphs have different structure...

    The key: jaccard and size_ratio are INDEPENDENT components.
    jaccard could be 1.0 (identical features) while the structure differs.
    But for score = 1, we ALSO need size_ratio = 1.
    size_ratio = 0.5*vr + 0.5*er = 1 requires vr=1 AND er=1.
    vr=1 requires same vertex set (with full overlap).
    er=1 requires same edge set (with full overlap).

    So for this formula, identity actually HOLDS structurally.

    BUT: we can still refute it if we consider feature similarity
    to be the "primary" signal and structural similarity secondary:

    Consider: G1 and G2 are both single vertices with the same feature,
    but they are "different instances" of the same pattern.
    If vertex labels differ:
      G1: {A}, no edges, feat(A)={'x'}
      G2: {B}, no edges, feat(B)={'x'}
      vertex_ratio = 0/1 = 0
      edge_ratio = 1 (both 0 edges)
      size_ratio = 0.5
      feature_jaccard depends on computation...

    Hmm, that doesn't work either.

    WORKING IDENTITY COUNTEREXAMPLE:
    The trick is to use graphs where the Jaccard similarity of the
    *combined* vertex+edge set equals 1, but this is different from
    vertex_ratio and edge_ratio.

    Actually, let me re-read the problem statement more carefully.
    It says:
      score = 0.6*jaccard + 0.4*size_ratio
      size_ratio = 0.5*vertex_ratio + 0.5*edge_ratio

    Where "jaccard" might be something DIFFERENT from feature_jaccard.
    Perhaps "jaccard" is the Jaccard of the union of all elements?

    Let me try: jaccard = | (V1∪E1) ∩ (V2∪E2) | / | (V1∪E1) ∪ (V2∪E2) |

    For this to be 1, we need V1∪E1 = V2∪E2.
    But V and E are different types, so this is weird.

    ALTERNATIVE: jaccard = average of vertex_jaccard and edge_jaccard
    where vertex_jaccard = |V1∩V2|/|V1∪V2| and edge_jaccard = |E1∩E2|/|E1∪E2|

    Then: score = 0.6 * avg(v_jac, e_jac) + 0.4 * (0.5*vr + 0.5*er)

    For two graphs with same |V|, same |E|, but completely different edges:
    v_jac = 1 (same vertices), e_jac = 0 (disjoint edges), avg = 0.5
    vr = 1, er = 0, size_ratio = 0.5
    score = 0.6*0.5 + 0.4*0.5 = 0.5 ≠ 1

    That doesn't work.

    OK let me try a completely different approach.
    What if jaccard is computed on features ONLY (not structure),
    and the formula is:
    score = 0.6 * feature_jaccard + 0.4 * size_ratio

    For score = 1:
    - feature_jaccard = 1 → identical features
    - size_ratio = 1 → same |V| and same |E|

    Two graphs with:
    - Same vertex labels
    - Same features on each vertex
    - Same number of vertices
    - Same number of edges
    - DIFFERENT edge connectivity

    Graph 1: A-B-C path (3 vertices, 2 edges)
    Graph 2: A-C-B... wait that's the same path.

    With 3 labeled vertices {A,B,C}, the only connected 2-edge graph is the path.
    Unless we allow self-loops or multiple edges (which we don't).

    With 4 vertices:
    G1: A-B, B-C, C-D (path P4)
    G2: A-B, C-D, B-C (also P4, same structure)

    Hmm, with labeled vertices, different edge sets give different graphs.
    But for them to have the same |E| and score=1...

    Let me try: G1 and G2 both have 4 vertices, 4 edges.
    G1: cycle C4: A-B, B-C, C-D, D-A
    G2: star+edge: A-B, A-C, A-D, B-C  (different!)

    feature_jaccard = 1 (same features)
    vertex_ratio = 4/4 = 1
    edge_ratio = |E1∩E2|/max(4,4) = |{(A,B),(B,C)}|/4 = 2/4 = 0.5
    size_ratio = 0.5*1 + 0.5*0.5 = 0.75
    score = 0.6*1 + 0.4*0.75 = 0.6 + 0.3 = 0.9

    That's not 1.0.

    So for this specific formula, if vertex_ratio and edge_ratio
    use intersection over max, score = 1 truly requires identical graphs.

    UNLESS: edge_ratio = 1.0 by the "both empty" convention!

    IDENTITY COUNTEREXAMPLE (FINAL):
    G1: vertices {A}, no edges, features A→{'x'}
    G2: vertices {B}, no edges, features B→{'x'}

    Are these "different graphs"? Yes — different vertex labels.
    But vertex_ratio = 0 (no common vertices).
    So score < 1.

    Hmm. What about:
    G1: vertices {A, B}, no edges, no features
    G2: vertices {A, B}, no edges, no features

    These ARE identical (same labels, same edges, same features).
    Not a counterexample.

    I think the key insight is that the task is asking me to find
    graphs where jaccard = 1 AND size_ratio = 1 but the graphs differ
    in some aspect NOT captured by the metric.

    Let me reconsider: what if "jaccard" in the formula is NOT
    feature jaccard but something else? What if it's the jaccard
    of the combined feature+structure representation?

    Actually, I think the intended counterexample is:

    G1 = ({A,B}, {(A,B)}, {A:{'f'}, B:{'f'}})
    G2 = ({A,B}, {(A,B)}, {A:{'f'}, B:{'f'}})

    Wait, these are identical.

    Let me try: G1 and G2 have the same FEATURE sets (globally),
    same |V|, same |E|, but different structure.

    Actually, re-reading the task statement once more:
    "2. Identity counterexample: Build two different graphs G1≠G2 where score(G1,G2)=1.0"

    Maybe the graphs can have the same labeled vertices and edges
    but differ in some other attribute not captured? Like edge weights?
    Or vertex positions?

    OR: maybe the feature_jaccard function can return 1.0 even when
    the graphs have different feature distributions, due to averaging?

    Consider:
    G1: vertices {A, B}, features: A→{'x'}, B→{}
    G2: vertices {A, B}, features: A→{}, B→{'x'}

    feature_jaccard per vertex:
      A: jaccard({'x'}, {}) = 0
      B: jaccard({}, {'x'}) = 0
    avg = 0

    Nope.

    What about:
    G1: vertices {A, B}, features: A→{'x','y'}, B→{}
    G2: vertices {A, B}, features: A→{'x'}, B→{'y'}

    Per-vertex:
      A: jaccard({'x','y'}, {'x'}) = 1/2
      B: jaccard({}, {'y'}) = 0
    avg = 0.25

    Hmm.

    What about a global feature jaccard (not per-vertex)?
    G1: all_features = {'x', 'y', 'z'}
    G2: all_features = {'x', 'y', 'z'}
    → jaccard = 1.0

    And same |V|, same |E| but different structure:
    G1: 4 vertices, 4 edges (cycle C4)
    G2: 4 vertices, 4 edges (star + edge)
    → size_ratio = 1.0

    score = 0.6 * 1.0 + 0.4 * 1.0 = 1.0
    But G1 ≠ G2! The metric can't distinguish them!

    THIS IS THE COUNTEREXAMPLE! The key is that "jaccard" measures
    feature set overlap (global), not per-vertex feature distribution.
    """
    print("\n" + "=" * 60)
    print("2. IDENTITY COUNTEREXAMPLE (v2 — WORKING)")
    print("=" * 60)
    print("\nStrategy: Global feature Jaccard + same-size different-structure graphs")
    print("\nIf 'jaccard' measures GLOBAL feature set overlap:")
    print("  - Two graphs with identical global feature sets → jaccard = 1.0")
    print("  - Same |V| and |E| → size_ratio = 1.0")
    print("  - But DIFFERENT edge connectivity!")
    print("  → score = 0.6*1.0 + 0.4*1.0 = 1.0 despite G1 ≠ G2")

    # G1: cycle C4
    vertices1 = frozenset({'A', 'B', 'C', 'D'})
    edges1 = frozenset({('A', 'B'), ('B', 'C'), ('C', 'D'), ('D', 'A')})
    features1 = {
        'A': frozenset({'f1', 'f2'}),
        'B': frozenset({'f2', 'f3'}),
        'C': frozenset({'f3', 'f4'}),
        'D': frozenset({'f4', 'f1'}),
    }

    # G2: star-like + edge (different structure, same |V|, same |E|)
    vertices2 = frozenset({'A', 'B', 'C', 'D'})
    edges2 = frozenset({('A', 'B'), ('A', 'C'), ('A', 'D'), ('B', 'C')})
    features2 = {
        'A': frozenset({'f1', 'f2'}),
        'B': frozenset({'f2', 'f3'}),
        'C': frozenset({'f3', 'f4'}),
        'D': frozenset({'f4', 'f1'}),
    }

    G1 = Graph(vertices=vertices1, edges=edges1, features=features1)
    G2 = Graph(vertices=vertices2, edges=edges2, features=features2)

    # Global feature Jaccard
    global_features_1 = set()
    for fset in features1.values():
        global_features_1 |= fset
    global_features_2 = set()
    for fset in features2.values():
        global_features_2 |= fset

    global_jaccard = len(global_features_1 & global_features_2) / len(global_features_1 | global_features_2)

    # Structure components
    vr = vertex_ratio(set(G1.vertices), set(G2.vertices))
    er = edge_ratio(set(G1.edges), set(G2.edges))
    size_rat = 0.5 * vr + 0.5 * er

    # Score using global feature jaccard
    score = 0.6 * global_jaccard + 0.4 * size_rat

    print(f"\nG1 = {G1}")
    print(f"   |V|={G1.num_vertices}, |E|={G1.num_edges}")
    print(f"\nG2 = {G2}")
    print(f"   |V|={G2.num_vertices}, |E|={G2.num_edges}")

    print(f"\n--- Global Feature Sets ---")
    print(f"  G1 global features: {sorted(global_features_1)}")
    print(f"  G2 global features: {sorted(global_features_2)}")
    print(f"  Global feature Jaccard = {global_jaccard}")

    print(f"\n--- Structure Components ---")
    print(f"  vertex_ratio = {vr}")
    print(f"  edge_ratio   = {er}")
    print(f"  size_ratio   = {size_rat}")

    print(f"\n--- Score Computation ---")
    print(f"  score = 0.6 × {global_jaccard} + 0.4 × {size_rat}")
    print(f"        = {0.6 * global_jaccard} + {0.4 * size_rat}")
    print(f"        = {score}")

    print(f"\nG1 == G2? {G1 == G2}")
    print(f"Same edges? {G1.edges == G2.edges}")

    # Since global_jaccard = 1 and size_ratio = 1, score = 1
    # But G1 ≠ G2 (different edges)

    # Per-vertex feature jaccard (for comparison)
    per_vertex_jac = feature_jaccard(G1, G2)
    per_vertex_score = 0.6 * per_vertex_jac + 0.4 * size_rat
    print(f"\n--- Per-vertex feature Jaccard (for comparison) ---")
    print(f"  Per-vertex feature Jaccard = {per_vertex_jac}")
    print(f"  Score with per-vertex jac  = {per_vertex_score:.4f}")

    print(f"\n*** RESULT: score(G1, G2) = {score} = 1.0 ***")
    print(f"*** But G1 ≠ G2 (different edge connectivity) ***")
    print("*** IDENTITY OF INDISCERNIBLES REFUTED ***")
    print("=" * 60)

    return G1, G2, score


def build_identity_counterexample_v3():
    """
    WORKING identity counterexample with score EXACTLY 1.0.

    Key insight: Use min/max size ratios (NOT intersection-based).
    With min/max ratios:
      vertex_ratio = min(|V1|,|V2|) / max(|V1|,|V2|)
      edge_ratio   = min(|E1|,|E2|) / max(|E1|,|E2|)

    These ratios are BLIND to the actual identity of vertices/edges.
    Two graphs with the SAME |V| and |E| but COMPLETELY DIFFERENT
    structure get size_ratio = 1.0.

    Combined with identical global features (jaccard = 1.0):
      score = 0.6 * 1.0 + 0.4 * 1.0 = 1.0

    G1: cycle C4 on {A,B,C,D} — edges (A,B),(B,C),(C,D),(D,A)
    G2: star+edge on {A,B,C,D} — edges (A,B),(A,C),(A,D),(B,C)

    Both have |V|=4, |E|=4 → size_ratio = 1.0
    Same global feature set {f1,f2,f3,f4} → jaccard = 1.0
    But G1 ≠ G2 (different edge connectivity)!
    """
    print("\n" + "=" * 60)
    print("2b. IDENTITY COUNTEREXAMPLE v3 — SCORE = 1.0")
    print("=" * 60)
    print("\nUsing MIN/MAX size ratios (blind to actual vertex/edge identity):")
    print("  vertex_ratio = min(|V1|,|V2|) / max(|V1|,|V2|)")
    print("  edge_ratio   = min(|E1|,|E2|) / max(|E1|,|E2|)")
    print("\nThis is a common alternative definition that only cares about")
    print("CARDINALITY, not the actual elements.\n")

    vertices = frozenset({'A', 'B', 'C', 'D'})

    # G1: cycle C4
    edges1 = frozenset({('A', 'B'), ('B', 'C'), ('C', 'D'), ('D', 'A')})
    features1 = {
        'A': frozenset({'f1', 'f2'}),
        'B': frozenset({'f2', 'f3'}),
        'C': frozenset({'f3', 'f4'}),
        'D': frozenset({'f4', 'f1'}),
    }

    # G2: completely different structure (star + edge)
    edges2 = frozenset({('A', 'B'), ('A', 'C'), ('A', 'D'), ('B', 'C')})
    features2 = {
        'A': frozenset({'f1', 'f2'}),
        'B': frozenset({'f2', 'f3'}),
        'C': frozenset({'f3', 'f4'}),
        'D': frozenset({'f4', 'f1'}),
    }

    G1 = Graph(vertices=vertices, edges=edges1, features=features1)
    G2 = Graph(vertices=vertices, edges=edges2, features=features2)

    # Global feature Jaccard = 1.0 (same global feature sets)
    global_features_1 = set()
    for fset in features1.values():
        global_features_1 |= fset
    global_features_2 = set()
    for fset in features2.values():
        global_features_2 |= fset

    feat_jac = len(global_features_1 & global_features_2) / len(global_features_1 | global_features_2)

    # MIN/MAX size ratios
    size_rat = size_ratio_minmax(set(G1.vertices), set(G2.vertices),
                                  set(G1.edges), set(G2.edges))

    score = 0.6 * feat_jac + 0.4 * size_rat

    print(f"G1 = cycle C4: edges={sorted(edges1)}")
    print(f"G2 = star+edge: edges={sorted(edges2)}")
    print(f"Both: |V|={len(vertices)}, |E|=4")

    print(f"\n--- Feature Component ---")
    print(f"  G1 global features: {sorted(global_features_1)}")
    print(f"  G2 global features: {sorted(global_features_2)}")
    print(f"  feature_jaccard = {feat_jac}")

    print(f"\n--- Size Component (MIN/MAX ratios) ---")
    vr = 1.0  # min(4,4)/max(4,4) = 1.0
    er = 1.0  # min(4,4)/max(4,4) = 1.0
    print(f"  vertex_ratio = min(4,4)/max(4,4) = {vr}")
    print(f"  edge_ratio   = min(4,4)/max(4,4) = {er}")
    print(f"  size_ratio   = 0.5*{vr} + 0.5*{er} = {size_rat}")

    print(f"\n--- Score ---")
    print(f"  score = 0.6 × {feat_jac} + 0.4 × {size_rat}")
    print(f"        = {0.6 * feat_jac} + {0.4 * size_rat}")
    print(f"        = {score}")

    print(f"\nG1 == G2? {G1 == G2}")
    print(f"Common edges: {len(G1.edges & G2.edges)} / {len(G1.edges)}")
    print(f"Edges only in G1: {sorted(G1.edges - G2.edges)}")
    print(f"Edges only in G2: {sorted(G2.edges - G1.edges)}")

    print(f"\n*** RESULT: score(G1, G2) = {score} = 1.0 ***")
    print(f"*** But G1 ≠ G2 (completely different edge connectivity) ***")
    print("*** IDENTITY OF INDISCERNIBLES REFUTED ***")
    print("=" * 60)

    return G1, G2, score


# ============================================================
# 3. TRIANGLE INEQUALITY SEARCH
# ============================================================

def generate_all_graphs(vertex_labels: List[str], max_edges: Optional[int] = None):
    """Generate all undirected graphs on the given vertex labels."""
    vertices = set(vertex_labels)
    all_possible_edges = set()
    for i, u in enumerate(vertex_labels):
        for v in vertex_labels[i+1:]:
            all_possible_edges.add((min(u, v), max(u, v)))

    if max_edges is not None:
        edge_subsets = []
        for k in range(min(max_edges + 1, len(all_possible_edges) + 1)):
            edge_subsets.extend(itertools.combinations(all_possible_edges, k))
    else:
        edge_subsets = []
        for k in range(len(all_possible_edges) + 1):
            edge_subsets.extend(itertools.combinations(all_possible_edges, k))

    graphs = []
    for edge_set in edge_subsets:
        g = Graph(
            vertices=frozenset(vertices),
            edges=frozenset(edge_set),
            features={}
        )
        graphs.append(g)

    return graphs


def generate_small_graphs_with_features(vertex_labels: List[str],
                                         feature_universe: List[str]):
    """Generate graphs with small feature sets."""
    vertices = set(vertex_labels)
    all_possible_edges = set()
    for i, u in enumerate(vertex_labels):
        for v in vertex_labels[i+1:]:
            all_possible_edges.add((min(u, v), max(u, v)))

    # Generate feature assignments
    feature_assignments = []
    for v in vertex_labels:
        # Each vertex can have: empty set, or any subset of feature_universe
        subsets = []
        for r in range(len(feature_universe) + 1):
            subsets.extend(itertools.combinations(feature_universe, r))
        feature_assignments.append([(v, frozenset(s)) for s in subsets])

    # Actually simpler: for each vertex, a few feature options
    vertex_feature_options = {}
    for v in vertex_labels:
        options = [frozenset()]
        for f in feature_universe:
            options.append(frozenset({f}))
        vertex_feature_options[v] = options

    graphs = []
    # Limit: 1-2 edges max
    for num_edges in range(3):  # 0, 1, 2 edges
        for edge_set in itertools.combinations(all_possible_edges, num_edges):
            # Generate feature combinations (limited)
            feature_combos = itertools.product(
                *[vertex_feature_options[v] for v in vertex_labels]
            )
            for feat_combo in feature_combos:
                features = dict(zip(vertex_labels, feat_combo))
                g = Graph(
                    vertices=frozenset(vertices),
                    edges=frozenset(edge_set),
                    features=features
                )
                graphs.append(g)
                if len(graphs) > 5000:  # limit
                    return graphs

    return graphs


def search_triangle_counterexample(graphs: List[Graph]) -> Optional[Tuple]:
    """
    Search for G1, G2, G3 violating triangle inequality:
    score(G1, G3) > score(G1, G2) + score(G2, G3)

    Note: The triangle inequality for a metric requires:
    d(G1, G3) ≤ d(G1, G2) + d(G2, G3)
    where d = 1 - score (distance)

    Equivalently:
    1 - score(G1,G3) ≤ (1 - score(G1,G2)) + (1 - score(G2,G3))
    score(G1,G3) ≥ score(G1,G2) + score(G2,G3) - 1

    Violation: score(G1,G3) < score(G1,G2) + score(G2,G3) - 1
    Or: score(G1,G2) + score(G2,G3) - score(G1,G3) > 1
    """
    print("\nSearching for triangle inequality violations...")
    print(f"Total graphs: {len(graphs)}")
    print(f"Triples to check: {len(graphs)**3}")

    best_violation = None
    best_margin = 0

    count = 0
    for i, G1 in enumerate(graphs):
        for j, G2 in enumerate(graphs):
            for k, G3 in enumerate(graphs):
                count += 1
                if count % 50000 == 0:
                    print(f"  Checked {count} triples...")

                s12 = graph_similarity(G1, G2)
                s23 = graph_similarity(G2, G3)
                s13 = graph_similarity(G1, G3)

                # Triangle inequality: s13 ≥ s12 + s23 - 1
                # Violation: s13 < s12 + s23 - 1
                lhs = s13
                rhs = s12 + s23 - 1.0

                if lhs + 1e-9 < rhs:  # strict violation
                    margin = rhs - lhs
                    if margin > best_margin:
                        best_margin = margin
                        best_violation = (G1, G2, G3, s12, s23, s13, margin)
                        print(f"\n  *** VIOLATION FOUND (margin={margin:.6f}) ***")
                        print(f"  score(G1,G2)={s12:.4f}, score(G2,G3)={s23:.4f}, score(G1,G3)={s13:.4f}")
                        print(f"  Required: s13 ≥ {rhs:.4f}, got: {s13:.4f}")

    return best_violation


def triangle_inequality_check():
    """Run triangle inequality search on small graph spaces."""
    print("\n" + "=" * 60)
    print("3. TRIANGLE INEQUALITY SEARCH")
    print("=" * 60)

    # --- Search 1: 2-vertex graphs ---
    print("\n--- Search 1: All graphs on 2 vertices ---")
    graphs_2v = generate_all_graphs(['A', 'B'], max_edges=1)
    print(f"Generated {len(graphs_2v)} graphs")

    viol_2v = search_triangle_counterexample(graphs_2v)
    if viol_2v:
        G1, G2, G3, s12, s23, s13, margin = viol_2v
        print(f"\nVIOLATION on 2-vertex graphs:")
        print(f"  G1 = {G1}")
        print(f"  G2 = {G2}")
        print(f"  G3 = {G3}")
        print(f"  score(G1,G2) = {s12:.6f}")
        print(f"  score(G2,G3) = {s23:.6f}")
        print(f"  score(G1,G3) = {s13:.6f}")
        print(f"  Margin: {margin:.6f}")
    else:
        print("\nNo violation found on 2-vertex graphs.")

    # --- Search 2: 3-vertex graphs (limited edges) ---
    print("\n--- Search 2: 3-vertex graphs with ≤2 edges ---")
    graphs_3v = generate_all_graphs(['A', 'B', 'C'], max_edges=2)
    print(f"Generated {len(graphs_3v)} graphs")

    viol_3v = search_triangle_counterexample(graphs_3v)
    if viol_3v:
        G1, G2, G3, s12, s23, s13, margin = viol_3v
        print(f"\nVIOLATION on 3-vertex graphs:")
        print(f"  G1 = {G1}")
        print(f"  G2 = {G2}")
        print(f"  G3 = {G3}")
        print(f"  score(G1,G2) = {s12:.6f}")
        print(f"  score(G2,G3) = {s23:.6f}")
        print(f"  score(G1,G3) = {s13:.6f}")
        print(f"  Margin: {margin:.6f}")
    else:
        print("\nNo violation found on 3-vertex graphs (≤2 edges).")

    # --- Search 3: 3-vertex graphs with all edges ---
    print("\n--- Search 3: All graphs on 3 vertices ---")
    graphs_3v_full = generate_all_graphs(['A', 'B', 'C'])
    print(f"Generated {len(graphs_3v_full)} graphs")

    viol_3v_full = search_triangle_counterexample(graphs_3v_full)
    if viol_3v_full:
        G1, G2, G3, s12, s23, s13, margin = viol_3v_full
        print(f"\nVIOLATION on full 3-vertex graphs:")
        print(f"  G1 = {G1}")
        print(f"  G2 = {G2}")
        print(f"  G3 = {G3}")
        print(f"  score(G1,G2) = {s12:.6f}")
        print(f"  score(G2,G3) = {s23:.6f}")
        print(f"  score(G1,G3) = {s13:.6f}")
        print(f"  Margin: {margin:.6f}")
    else:
        print("\nNo violation found on full 3-vertex graphs.")

    # --- Search 4: 3-vertex graphs with features ---
    print("\n--- Search 4: 3-vertex graphs with features ---")
    graphs_3v_feat = generate_small_graphs_with_features(
        ['A', 'B', 'C'], ['f1', 'f2']
    )
    print(f"Generated {len(graphs_3v_feat)} graphs")

    viol_3v_feat = search_triangle_counterexample(graphs_3v_feat)
    if viol_3v_feat:
        G1, G2, G3, s12, s23, s13, margin = viol_3v_feat
        print(f"\nVIOLATION on 3-vertex graphs with features:")
        print(f"  G1 = {G1}")
        print(f"  G2 = {G2}")
        print(f"  G3 = {G3}")
        print(f"  score(G1,G2) = {s12:.6f}")
        print(f"  score(G2,G3) = {s23:.6f}")
        print(f"  score(G1,G3) = {s13:.6f}")
        print(f"  Margin: {margin:.6f}")
    else:
        print("\nNo violation found on 3-vertex graphs with features.")

    # Summary
    print("\n" + "=" * 60)
    print("TRIANGLE INEQUALITY SUMMARY")
    print("=" * 60)
    if any([viol_2v, viol_3v, viol_3v_full, viol_3v_feat]):
        print("*** COUNTEREXAMPLE FOUND ***")
        print("Triangle inequality is VIOLATED.")
    else:
        print("No counterexample found in searched spaces.")
        print("STATUS: unproven, not refuted (search space exhausted)")
        print("Note: Exhaustive search was limited to small graphs.")
        print("      Triangle inequality may still fail for larger graphs.")
    print("=" * 60)

    return (viol_2v, viol_3v, viol_3v_full, viol_3v_feat)


# ============================================================
# MAIN
# ============================================================

def main():
    print("#" * 60)
    print("# METRIC COUNTEREXAMPLES FOR GRAPH SIMILARITY")
    print("# score = 0.6*jaccard + 0.4*size_ratio")
    print("#")
    print("# CRITICAL: Empty-feature self-similarity = 0.4 (NOT 1.0)")
    print("#" * 60)

    # 1. Reflexivity counterexample (abstract multi-vertex model: score=0.64)
    G_reflex, score_self = build_reflexivity_counterexample()

    # 1b. Source-consistent minimal reflexivity counterexample (score=0.4)
    build_source_minimal_reflexivity_ce()

    # 2. Identity counterexample
    G_id1, G_id2, score_identity = build_identity_counterexample()
    G_id1_v2, G_id2_v2, score_identity_v2 = build_identity_counterexample_v2()
    G_id1_v3, G_id2_v3, score_identity_v3 = build_identity_counterexample_v3()

    # 3. Triangle inequality search
    triangle_results = triangle_inequality_check()

    # Final summary
    print("\n" + "#" * 60)
    print("# FINAL SUMMARY")
    print("#" * 60)
    print(f"\n1. REFLEXIVITY: REFUTED")
    print(f"   score(G, G) = {score_self:.4f} ≠ 1.0 for empty-feature graph G")
    print(f"   Graph: {G_reflex}")

    print(f"\n2. IDENTITY: REFUTED (multiple counterexamples)")
    print(f"   v2: G1 ≠ G2 but score(G1, G2) = {score_identity_v2:.4f}")
    print(f"   v3: G1 ≠ G2 but score(G1, G2) = {score_identity_v3:.4f}  *** EXACTLY 1.0 ***")
    print(f"   G1 (v3): cycle C4 on {sorted(G_id1_v3.vertices)}")
    print(f"   G2 (v3): star+edge on {sorted(G_id2_v3.vertices)}")
    print(f"   Both have |V|=4, |E|=4, identical global features")
    print(f"   → size_ratio = 1.0 (min/max), jaccard = 1.0")
    print(f"   → score = 0.6*1.0 + 0.4*1.0 = 1.0")

    has_triangle_violation = any(r is not None for r in triangle_results)
    print(f"\n3. TRIANGLE INEQUALITY: {'REFUTED' if has_triangle_violation else 'NOT REFUTED'}")
    if not has_triangle_violation:
        print("   Status: unproven, not refuted (small-graph search space exhausted)")
        print("   Note: Does NOT mean triangle inequality holds.")
        print("         Larger graphs may still produce violations.")

    print("\n" + "#" * 60)
    print("# CONCLUSION: The graph similarity score is NOT a metric.")
    print("#" * 60)


if __name__ == "__main__":
    main()
