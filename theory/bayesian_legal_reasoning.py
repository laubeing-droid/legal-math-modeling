"""Bayesian Legal Reasoning: updating legal claim probabilities via Bayes' theorem.

Mathematical Framework
---------------------
Given a legal claim C, we begin with a prior probability P(C) and observe
evidence items E_1, E_2, ..., E_n.  Each evidence item has a likelihood ratio

    L(E_i) = P(E_i | C) / P(E_i | ~C)

The posterior after observing all evidence is obtained by sequential updating:

    P(C | E_1..E_k) = L(E_k) * P(C | E_1..E_{k-1})
                      / [ L(E_k) * P(C | E_1..E_{k-1}) + 1 - P(C | E_1..E_{k-1}) ]

Equivalently, using odds form:

    O(C | E_1..E_k) = O(C) * prod_{i=1}^{k} L(E_i)

    where O(p) = p / (1 - p)  and  p = O / (1 + O).

This module models the progressive strengthening (or weakening) of a legal
claim as evidence accumulates, mirroring how adjudicators weigh proof
under the "preponderance of evidence" or "beyond reasonable doubt" standards.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import Dict, List, Optional, Set, Tuple
from itertools import product


# ---------------------------------------------------------------------------
# Data structures
# ---------------------------------------------------------------------------

@dataclass
class EvidenceItem:
    """A single piece of evidence with a likelihood ratio."""
    name: str
    description: str
    p_if_claim_true: float   # P(E | claim)
    p_if_claim_false: float  # P(E | ~claim)

    @property
    def likelihood_ratio(self) -> float:
        if self.p_if_claim_false == 0:
            raise ZeroDivisionError(
                f"Evidence '{self.name}' has P(E|~C)=0; use a tiny epsilon instead."
            )
        return self.p_if_claim_true / self.p_if_claim_false


@dataclass
class BayesianUpdateRecord:
    """Records one step of the sequential update."""
    step: int
    evidence_name: str
    likelihood_ratio: float
    prior: float
    posterior: float


@dataclass
class BayesianReasoning:
    """Manages sequential Bayesian updating for a legal claim."""
    claim_name: str
    prior: float
    history: List[BayesianUpdateRecord] = field(default_factory=list)

    @property
    def current_posterior(self) -> float:
        return self.history[-1].posterior if self.history else self.prior

    def update(self, evidence: EvidenceItem) -> BayesianUpdateRecord:
        """Apply Bayes' theorem for one evidence item."""
        prior = self.current_posterior
        lr = evidence.likelihood_ratio
        # P(C|E) = LR * P(C) / (LR * P(C) + 1 - P(C))
        numerator = lr * prior
        denominator = numerator + (1 - prior)
        posterior = numerator / denominator

        rec = BayesianUpdateRecord(
            step=len(self.history) + 1,
            evidence_name=evidence.name,
            likelihood_ratio=lr,
            prior=prior,
            posterior=posterior,
        )
        self.history.append(rec)
        return rec

    def apply_all(self, evidence_list: List[EvidenceItem]) -> None:
        for ev in evidence_list:
            self.update(ev)


# ---------------------------------------------------------------------------
# Odds-form utility (alternative formulation)
# ---------------------------------------------------------------------------

def probability_to_odds(p: float) -> float:
    if p >= 1.0:
        return float('inf')
    if p <= 0.0:
        return 0.0
    return p / (1 - p)


def odds_to_probability(o: float) -> float:
    if o <= -1.0:
        raise ValueError(f"Odds must be > -1, got {o}")
    return o / (1 + o)


def odds_form_update(prior: float, likelihood_ratios: List[float]) -> float:
    """Compute posterior from prior and list of LR values using odds form."""
    odds = probability_to_odds(prior)
    for lr in likelihood_ratios:
        odds *= lr
    return odds_to_probability(odds)


# ---------------------------------------------------------------------------
# Standard of proof helpers
# ---------------------------------------------------------------------------

def meets_standard(posterior: float, standard: str = "preponderance") -> bool:
    thresholds = {
        "preponderance": 0.50,           # more likely than not
        "clear_and_convincing": 0.75,     # substantially more likely
        "beyond_reasonable_doubt": 0.95,   # near certainty
    }
    return posterior >= thresholds.get(standard, 0.50)


# ---------------------------------------------------------------------------
# Demo
# ---------------------------------------------------------------------------

# ---------------------------------------------------------------------------
# Bayesian Network for Legal Evidence
# ---------------------------------------------------------------------------

@dataclass
class _BNNode:
    """Internal representation of a node in a Bayesian network."""
    name: str
    prior: float  # P(node=True)


@dataclass
class _BNEdge:
    """Internal representation of a directed edge with conditional probabilities."""
    parent: str
    child: str
    p_true_given_parent_true: float   # P(child=T | parent=T)
    p_true_given_parent_false: float  # P(child=T | parent=F)


class BayesianNetwork:
    """Bayesian network for legal evidence with conditional dependencies.

    Nodes represent evidence items or legal claims with a base prior
    probability.  Edges encode conditional dependencies via a compact
    CPT: for a child node *C* with parents *P_1 .. P_k* the full
    conditional probability table is built from pairwise specifications
    ``P(C=T | P_i=T)`` and ``P(C=T | P_i=F)`` combined with noisy-OR
    (the probability of the child being true increases with more true
    parents, capped at 1.0).

    For networks small enough for full enumeration (up to ~15 free
    variables) ``compute_posterior`` uses exact inference by summing
    over all joint states.
    """

    def __init__(self) -> None:
        self._nodes: Dict[str, _BNNode] = {}
        self._edges: List[_BNEdge] = []
        self._children: Dict[str, List[str]] = {}   # parent -> [child, ...]
        self._parents: Dict[str, List[str]] = {}     # child -> [parent, ...]
        self._edge_map: Dict[Tuple[str, str], _BNEdge] = {}

    # -- construction ---------------------------------------------------------

    def add_node(self, name: str, prior: float) -> None:
        """Add a node with prior probability P(name=True)."""
        if not 0.0 <= prior <= 1.0:
            raise ValueError(f"Prior must be in [0,1], got {prior} for '{name}'")
        self._nodes[name] = _BNNode(name=name, prior=prior)
        self._children.setdefault(name, [])
        self._parents.setdefault(name, [])

    def add_edge(
        self,
        parent: str,
        child: str,
        p_true_given_parent_true: float,
        p_true_given_parent_false: float,
    ) -> None:
        """Add a directed edge from *parent* to *child* with conditional probs."""
        for n in (parent, child):
            if n not in self._nodes:
                raise KeyError(f"Node '{n}' not yet added")
        edge = _BNEdge(
            parent=parent,
            child=child,
            p_true_given_parent_true=p_true_given_parent_true,
            p_true_given_parent_false=p_true_given_parent_false,
        )
        self._edges.append(edge)
        self._edge_map[(parent, child)] = edge
        self._children[parent].append(child)
        self._parents[child].append(parent)

    # -- probability computation ----------------------------------------------

    def _node_prob(self, node_name: str, state: Dict[str, bool]) -> float:
        """Return P(node=True | parent states in *state*).

        If the node has no parents, returns its prior.  If it has parents
        whose states are not yet determined, the prior is returned as a
        fallback (should not happen during proper enumeration).
        """
        parents = self._parents[node_name]
        if not parents:
            return self._nodes[node_name].prior

        # For each parent, retrieve P(child=T | parent=value).
        # Use noisy-OR combination:
        #   P(C=T) = 1 - prod_i (1 - p_i)
        # where p_i = P(C=T | P_i = observed_value_i)  (only the
        # contribution of that parent alone, ignoring others).
        #
        # Because our CPT is specified pairwise (each edge independently
        # gives P(child|parent)), noisy-OR is a natural and commonly used
        # aggregation for multiple independent causes.
        complement = 1.0
        for p in parents:
            edge = self._edge_map[(p, node_name)]
            p_val = edge.p_true_given_parent_true if state.get(p, False) else edge.p_true_given_parent_false
            complement *= (1.0 - p_val)
        return min(1.0, max(0.0, 1.0 - complement))

    def compute_posterior(
        self, target_node: str, observed: Dict[str, bool]
    ) -> float:
        """Compute P(target=T | observed evidence) by exact enumeration.

        For small networks (up to ~15 non-observed nodes) this sums
        over all 2^n joint assignments of the hidden variables.

        Parameters
        ----------
        target_node : str
            The node whose posterior we want.
        observed : dict[str, bool]
            Evidence: nodes whose values are known.

        Returns
        -------
        float
            P(target_node = True | observed evidence).
        """
        if target_node not in self._nodes:
            raise KeyError(f"Unknown node '{target_node}'")
        for n in observed:
            if n not in self._nodes:
                raise KeyError(f"Unknown observed node '{n}'")

        all_nodes = list(self._nodes.keys())
        hidden = [n for n in all_nodes if n not in observed and n != target_node]

        # We need to enumerate assignments to hidden + target.
        query_vars = hidden + [target_node]

        numerator = 0.0   # sum of joint(target=T, observed, hidden) over hidden
        denominator = 0.0  # sum of joint(target=T/F, observed, hidden) over hidden

        for bits in product([False, True], repeat=len(query_vars)):
            assignment = dict(zip(query_vars, bits))
            assignment.update(observed)

            joint = self._joint_probability(assignment)

            if assignment[target_node]:
                numerator += joint
            denominator += joint

        if denominator == 0.0:
            return 0.0
        return numerator / denominator

    def _joint_probability(self, assignment: Dict[str, bool]) -> float:
        """Compute the joint probability P(X_1=x_1, ..., X_n=x_n)."""
        prob = 1.0
        for node_name in self._nodes:
            p_true = self._node_prob(node_name, assignment)
            if assignment[node_name]:
                prob *= p_true
            else:
                prob *= (1.0 - p_true)
            if prob == 0.0:
                return 0.0
        return prob


# ---------------------------------------------------------------------------
# Bayesian Network Demo — Contract Breach Case
# ---------------------------------------------------------------------------

def demo_bayesian_network() -> None:
    print("\n" + "=" * 65)
    print("Bayesian Network — Contract Breach Case Demo")
    print("=" * 65)

    bn = BayesianNetwork()

    # Nodes
    bn.add_node("ContractSigned", prior=0.95)
    bn.add_node("NoticeGiven", prior=0.80)
    bn.add_node("ContributoryNegligence", prior=0.20)
    bn.add_node("BreachOccurred", prior=0.30)
    bn.add_node("Damages", prior=0.70)

    # Edges (conditional dependencies)
    # ContractSigned -> BreachOccurred
    bn.add_edge("ContractSigned", "BreachOccurred",
                p_true_given_parent_true=0.60,
                p_true_given_parent_false=0.10)

    # NoticeGiven -> BreachOccurred
    bn.add_edge("NoticeGiven", "BreachOccurred",
                p_true_given_parent_true=0.55,
                p_true_given_parent_false=0.20)

    # BreachOccurred -> Damages
    bn.add_edge("BreachOccurred", "Damages",
                p_true_given_parent_true=0.85,
                p_true_given_parent_false=0.15)

    # ContributoryNegligence -> Damages (reduces probability)
    bn.add_edge("ContributoryNegligence", "Damages",
                p_true_given_parent_true=0.30,
                p_true_given_parent_false=0.75)

    print("\nNetwork structure:")
    print("  Nodes:", list(bn._nodes.keys()))
    print("  Edges:")
    for e in bn._edges:
        print(f"    {e.parent} -> {e.child}  "
              f"P(C=T|P=T)={e.p_true_given_parent_true:.2f}  "
              f"P(C=T|P=F)={e.p_true_given_parent_false:.2f}")

    # Marginal (no evidence)
    p_damages_marginal = bn.compute_posterior("Damages", {})
    print(f"\nP(Damages) marginal (no evidence): {p_damages_marginal:.4f}")

    # Query: P(Damages | ContractSigned=T, NoticeGiven=T, ContributoryNegligence=F)
    observed = {
        "ContractSigned": True,
        "NoticeGiven": True,
        "ContributoryNegligence": False,
    }
    p_damages_given_evidence = bn.compute_posterior("Damages", observed)
    print(f"\nP(Damages | ContractSigned=T, NoticeGiven=T, ContribNeg=F)")
    print(f"  = {p_damages_given_evidence:.4f}")

    # Also show P(BreachOccurred | same evidence)
    p_breach = bn.compute_posterior("BreachOccurred", observed)
    print(f"\nP(BreachOccurred | ContractSigned=T, NoticeGiven=T)")
    print(f"  = {p_breach:.4f}")

    # Sensitivity: what if contributory negligence is true?
    observed_cn = {
        "ContractSigned": True,
        "NoticeGiven": True,
        "ContributoryNegligence": True,
    }
    p_damages_cn = bn.compute_posterior("Damages", observed_cn)
    print(f"\nP(Damages | ContractSigned=T, NoticeGiven=T, ContribNeg=T)")
    print(f"  = {p_damages_cn:.4f}")
    print(f"  (Effect of contributory negligence: {p_damages_given_evidence:.4f} -> {p_damages_cn:.4f})")

    print("\nDemo completed successfully.")


def demo() -> None:
    print("=" * 65)
    print("Bayesian Legal Reasoning — Demo")
    print("=" * 65)

    # Claim: Defendant breached a contract.  Prior = 0.30
    br = BayesianReasoning(claim_name="breach of contract", prior=0.30)

    evidence_items = [
        EvidenceItem(
            name="Signed contract with deadline",
            description="Written contract showing a clear delivery deadline",
            p_if_claim_true=0.95,
            p_if_claim_false=0.60,
        ),
        EvidenceItem(
            name="Email admitting delay",
            description="Defendant's email acknowledging the delivery was late",
            p_if_claim_true=0.90,
            p_if_claim_false=0.20,
        ),
        EvidenceItem(
            name="Independent witness testimony",
            description="Third-party witness confirms non-delivery on deadline",
            p_if_claim_true=0.85,
            p_if_claim_false=0.15,
        ),
    ]

    print(f"\nClaim: {br.claim_name}")
    print(f"Prior probability: {br.prior:.4f}")
    print("-" * 65)

    for ev in evidence_items:
        rec = br.update(ev)
        print(
            f"Step {rec.step}: {rec.evidence_name}\n"
            f"  LR = {ev.p_if_claim_true:.2f} / {ev.p_if_claim_false:.2f}"
            f" = {rec.likelihood_ratio:.4f}\n"
            f"  Prior {rec.prior:.4f} -> Posterior {rec.posterior:.4f}"
        )

    final = br.current_posterior
    print("-" * 65)
    print(f"Final posterior P(breach | all evidence): {final:.4f}")

    for std in ("preponderance", "clear_and_convincing", "beyond_reasonable_doubt"):
        ok = meets_standard(final, std)
        print(f"  Meets '{std}' standard: {'YES' if ok else 'NO'}")

    # Cross-check with odds form
    lrs = [ev.likelihood_ratio for ev in evidence_items]
    alt = odds_form_update(0.30, lrs)
    assert abs(alt - final) < 1e-12, "Odds-form mismatch"
    print(f"\nOdds-form cross-check: {alt:.4f} (matches)")

    print("\nDemo completed successfully.")


if __name__ == "__main__":
    demo()
    demo_bayesian_network()
