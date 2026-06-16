"""
Argument Clustering for Legal Argumentation.

Mathematical definition
-----------------------
Given a set of arguments A = {a1, ..., an}, each described by:
  - premises(a)    : set of propositional premises
  - conclusions(a) : set of conclusions
  - legal_concepts(a) : set of legal concepts/theories invoked

Similarity function:
  sim(a, b) = alpha * premise_overlap(a, b)
            + beta  * conclusion_overlap(a, b)
            + gamma * concept_overlap(a, b)

where overlap(X, Y) = |X intersection Y| / |X union Y|  (Jaccard index)
and alpha + beta + gamma = 1, alpha, beta, gamma >= 0

Single-linkage clustering:
  1. Start with each argument in its own cluster
  2. Find the most similar pair of clusters C_i, C_j
     where dist(C_i, C_j) = max_{a in C_i, b in C_j} sim(a, b)
  3. If sim >= threshold tau, merge C_i and C_j
  4. Repeat until no pair exceeds threshold

Cluster merging:
  When two clusters merge:
    support(merged) = support(C_i) union support(C_j)
    conclusion(merged) = most common conclusion in C_i union C_j
    label(merged) = set-theoretic union of all premises and concepts
"""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import Optional


# ------------------------------------------------------------------ #
#  Data structures                                                     #
# ------------------------------------------------------------------ #

@dataclass
class LegalArgument:
    """An argument represented by its components for clustering."""
    name: str
    premises: frozenset[str]
    conclusions: frozenset[str]
    legal_concepts: frozenset[str]
    source: str = ""  # case source / citation


@dataclass
class Cluster:
    """A cluster of similar legal arguments."""
    id: int
    members: list[LegalArgument] = field(default_factory=list)
    combined_premises: frozenset[str] = field(default_factory=frozenset)
    combined_conclusions: frozenset[str] = field(default_factory=frozenset)
    combined_concepts: frozenset[str] = field(default_factory=frozenset)

    def recompute_combined(self) -> None:
        """Recompute combined feature sets from members."""
        if not self.members:
            return
        self.combined_premises = frozenset().union(
            *(m.premises for m in self.members)
        )
        self.combined_conclusions = frozenset().union(
            *(m.conclusions for m in self.members)
        )
        self.combined_concepts = frozenset().union(
            *(m.legal_concepts for m in self.members)
        )

    def __str__(self) -> str:
        names = [m.name for m in self.members]
        return (
            f"Cluster#{self.id} ({len(self.members)} args): "
            f"{', '.join(names)}"
        )


# ------------------------------------------------------------------ #
#  Similarity computation                                              #
# ------------------------------------------------------------------ #

def jaccard(set_a: frozenset[str], set_b: frozenset[str]) -> float:
    """Jaccard index: |A intersection B| / |A union B|."""
    if not set_a and not set_b:
        return 1.0  # both empty => fully similar
    union = set_a | set_b
    inter = set_a & set_b
    return len(inter) / len(union)


def similarity(
    a: LegalArgument,
    b: LegalArgument,
    alpha: float = 0.4,
    beta: float = 0.35,
    gamma: float = 0.25,
) -> float:
    """
    Compute similarity between two arguments.

    sim(a, b) = alpha * jaccard(premises)
              + beta  * jaccard(conclusions)
              + gamma * jaccard(concepts)
    """
    p_sim = jaccard(a.premises, b.premises)
    c_sim = jaccard(a.conclusions, b.conclusions)
    l_sim = jaccard(a.legal_concepts, b.legal_concepts)
    return alpha * p_sim + beta * c_sim + gamma * l_sim


def cluster_similarity(
    c1: Cluster,
    c2: Cluster,
    alpha: float = 0.4,
    beta: float = 0.35,
    gamma: float = 0.25,
) -> float:
    """
    Single-linkage: max pairwise similarity between members of two clusters.
    """
    best = 0.0
    for a in c1.members:
        for b in c2.members:
            s = similarity(a, b, alpha, beta, gamma)
            if s > best:
                best = s
    return best


# ------------------------------------------------------------------ #
#  Single-linkage clustering                                           #
# ------------------------------------------------------------------ #

def single_linkage_cluster(
    arguments: list[LegalArgument],
    threshold: float = 0.30,
    alpha: float = 0.4,
    beta: float = 0.35,
    gamma: float = 0.25,
    max_clusters: int | None = None,
) -> list[Cluster]:
    """
    Agglomerative single-linkage clustering.

    1. Initialize: each argument is its own cluster
    2. Repeat until no pair exceeds `threshold` (or max_clusters reached):
       a. Find the most similar pair of clusters
       b. If similarity >= threshold, merge them
       c. Otherwise stop

    Returns list of final clusters.
    """
    clusters: list[Cluster] = []
    for i, arg in enumerate(arguments):
        cl = Cluster(id=i)
        cl.members.append(arg)
        cl.recompute_combined()
        clusters.append(cl)

    next_id = len(arguments)

    while len(clusters) > 1:
        if max_clusters is not None and len(clusters) <= max_clusters:
            break

        # Find best pair
        best_sim = -1.0
        best_i, best_j = -1, -1
        for i in range(len(clusters)):
            for j in range(i + 1, len(clusters)):
                s = cluster_similarity(clusters[i], clusters[j],
                                       alpha, beta, gamma)
                if s > best_sim:
                    best_sim = s
                    best_i, best_j = i, j

        if best_sim < threshold:
            break

        # Merge clusters[best_i] and clusters[best_j]
        merged = Cluster(id=next_id)
        next_id += 1
        merged.members = clusters[best_i].members + clusters[best_j].members
        merged.recompute_combined()

        # Remove old, add merged
        new_clusters = []
        for k, cl in enumerate(clusters):
            if k != best_i and k != best_j:
                new_clusters.append(cl)
        new_clusters.append(merged)
        clusters = new_clusters

    return clusters


# ------------------------------------------------------------------ #
#  Demo: 5 legal arguments about employment discrimination             #
# ------------------------------------------------------------------ #

def demo() -> None:
    print("=" * 64)
    print("Argument Clustering Demo")
    print("Scenario: Employment Discrimination Arguments")
    print("=" * 64)

    arguments = [
        LegalArgument(
            name="Disparate Treatment (Plaintiff 1)",
            premises=frozenset({
                "plaintiff_belonged_to_protected_class",
                "qualified_for_position",
                "adverse_employment_action",
                "similarly_situated_not_treated_adversely",
            }),
            conclusions=frozenset({"discrimination_established"}),
            legal_concepts=frozenset({
                "Title_VII", "disparate_treatment", "prima_facie_case",
            }),
            source="Smith v. Corp A",
        ),
        LegalArgument(
            name="Disparate Treatment (Plaintiff 2)",
            premises=frozenset({
                "plaintiff_belonged_to_protected_class",
                "qualified_for_position",
                "terminated_from_employment",
                "replacement_outside_protected_class",
            }),
            conclusions=frozenset({"discrimination_established"}),
            legal_concepts=frozenset({
                "Title_VII", "disparate_treatment", "McDonnell_Douglas",
            }),
            source="Johnson v. Corp B",
        ),
        LegalArgument(
            name="Disparate Impact (Plaintiff 3)",
            premises=frozenset({
                "facially_neutral_policy",
                "statistical_disparity_shown",
                "policy_caused_disparity",
            }),
            conclusions=frozenset({"discrimination_established"}),
            legal_concepts=frozenset({
                "Title_VII", "disparate_impact", "Griggs_defense",
            }),
            source="Williams v. Corp C",
        ),
        LegalArgument(
            name="Bona Fide Occupational Qualification",
            premises=frozenset({
                "job_requirement_reasonable",
                "qualification_essential_to_business",
                "no_less_discriminatory_alternative",
            }),
            conclusions=frozenset({"no_discrimination_BFOQ"}),
            legal_concepts=frozenset({
                "Title_VII", "BFOQ_defense", "business_necessity",
            }),
            source="Corp D defense brief",
        ),
        LegalArgument(
            name="Legitimate Non-Discriminatory Reason",
            premises=frozenset({
                "legitimate_reason_offered",
                "reason_supported_by_evidence",
                "consistent_application_of_policy",
            }),
            conclusions=frozenset({"no_discrimination_LNDR"}),
            legal_concepts=frozenset({
                "Title_VII", "legitimate_reason", "pretext_analysis",
            }),
            source="Corp E defense brief",
        ),
    ]

    # Print similarity matrix
    print("\n--- Pairwise Similarity Matrix ---")
    import itertools
    header = f"{'':>4}"
    for a in arguments:
        short = a.name[:12]
        header += f" {short:>12}"
    print(header)
    for a in arguments:
        row = f"{a.name[:4]:>4}"
        for b in arguments:
            s = similarity(a, b)
            row += f" {s:>12.4f}"
        print(row)

    # Run clustering with threshold 0.30
    clusters = single_linkage_cluster(arguments, threshold=0.30)

    print(f"\n--- Clustering Result (threshold=0.30) ---")
    print(f"  Number of clusters: {len(clusters)}")
    for cl in clusters:
        print(f"\n  {cl}")
        print(f"    Combined premises    : "
              f"{', '.join(sorted(cl.combined_premises))}")
        print(f"    Combined conclusions : "
              f"{', '.join(sorted(cl.combined_conclusions))}")
        print(f"    Combined concepts    : "
              f"{', '.join(sorted(cl.combined_concepts))}")
        print(f"    Members:")
        for m in cl.members:
            print(f"      - {m.name}  [{m.source}]")

    print()


if __name__ == "__main__":
    demo()
