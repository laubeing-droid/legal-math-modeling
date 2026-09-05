"""Evidence dependency DAG manager for the legal-math-modeling claim ledger.

Maintains a directed acyclic graph of claim dependencies so that when one
claim's evidence status changes, all downstream dependents are updated
automatically.

Dependency semantics
--------------------
- If a dependency is REFUTED_BY_COUNTEREXAMPLE, all dependents become
  DATA_INSUFFICIENT_FOR_PROOF (the dependent's proof is no longer valid).
- If a dependency is PROVED_BY_EXHAUSTIVE_ENUMERATION, the manager checks
  whether all of a dependent's dependencies are now satisfied; if so, the
  dependent can be promoted.
- TOY_SYNTHETIC_PROOF_ONLY and DATA_INSUFFICIENT_FOR_PROOF are neutral:
  they neither refute nor confirm downstream claims.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import Dict, List, Set

# Import EvidenceStatus from the canonical ledger
try:
    from .model_status import EvidenceStatus
except ImportError:
    from model_status import EvidenceStatus


# ---------------------------------------------------------------------------
# Claim node in the dependency DAG
# ---------------------------------------------------------------------------

@dataclass
class ClaimNode:
    """A node in the claim dependency DAG."""
    claim_id: str
    status: EvidenceStatus
    dependencies: List[str] = field(default_factory=list)


# ---------------------------------------------------------------------------
# Dependency manager
# ---------------------------------------------------------------------------

class EvidenceDependencyManager:
    """Manages a DAG of claim dependencies with status propagation."""

    def __init__(self) -> None:
        self.nodes: Dict[str, ClaimNode] = {}
        # reverse deps: node -> set of claims that depend on it
        self._dependents: Dict[str, Set[str]] = {}

    def add_node(self, node: ClaimNode) -> None:
        # Clean up stale reverse edges if re-adding a node
        if node.claim_id in self.nodes:
            old_node = self.nodes[node.claim_id]
            for old_dep in old_node.dependencies:
                if old_dep in self._dependents:
                    self._dependents[old_dep].discard(node.claim_id)

        self.nodes[node.claim_id] = node
        if node.claim_id not in self._dependents:
            self._dependents[node.claim_id] = set()
        for dep in node.dependencies:
            self._dependents.setdefault(dep, set()).add(node.claim_id)

    def propagate_status_change(
        self, claim_id: str, new_status: EvidenceStatus
    ) -> Dict[str, EvidenceStatus]:
        """Change a claim's status and propagate to all dependents.

        Returns a dict of {claim_id: new_status} for every node that was
        actually changed by this propagation (including the root).
        """
        changes: Dict[str, EvidenceStatus] = {}

        if claim_id not in self.nodes:
            raise KeyError(f"Unknown claim: {claim_id}")

        # Apply the root change
        self.nodes[claim_id].status = new_status
        changes[claim_id] = new_status

        # BFS propagation
        frontier: List[str] = [claim_id]
        visited: Set[str] = {claim_id}

        while frontier:
            next_frontier: List[str] = []
            for cid in frontier:
                for dependent_id in self._dependents.get(cid, set()):
                    if dependent_id in visited:
                        continue
                    visited.add(dependent_id)
                    dep_node = self.nodes[dependent_id]

                    # Check actual status of all dependencies for this dependent
                    dep_node = self.nodes[dependent_id]
                    any_dep_refuted = any(
                        self.nodes[d].status == EvidenceStatus.REFUTED_BY_COUNTEREXAMPLE
                        for d in dep_node.dependencies
                        if d in self.nodes
                    )
                    all_deps_proved = all(
                        self.nodes[d].status in {
                            EvidenceStatus.PROVED_BY_EXHAUSTIVE_ENUMERATION,
                            EvidenceStatus.TOY_SYNTHETIC_PROOF_ONLY,
                        }
                        for d in dep_node.dependencies
                        if d in self.nodes
                    )

                    # Rule 1: if any dependency is REFUTED, dependent becomes DATA_INSUFFICIENT
                    if any_dep_refuted:
                        if dep_node.status != EvidenceStatus.DATA_INSUFFICIENT_FOR_PROOF:
                            dep_node.status = EvidenceStatus.DATA_INSUFFICIENT_FOR_PROOF
                            changes[dependent_id] = dep_node.status
                            next_frontier.append(dependent_id)

                    # Rule 2: if ALL dependencies are PROVED, promote to PARTIAL_PROVED
                    elif all_deps_proved:
                        if dep_node.status not in {
                            EvidenceStatus.PROVED_BY_EXHAUSTIVE_ENUMERATION,
                            EvidenceStatus.REFUTED_BY_COUNTEREXAMPLE,
                        }:
                            dep_node.status = EvidenceStatus.PARTIAL_PROVED
                            changes[dependent_id] = dep_node.status
                            next_frontier.append(dependent_id)

            frontier = next_frontier

        return changes

    def get_impact_report(self, claim_id: str) -> Dict[str, EvidenceStatus]:
        """Show all claims that would be affected by a hypothetical status change.

        Returns {claim_id: current_status} for the claim and everything
        downstream (without actually changing anything).
        """
        if claim_id not in self.nodes:
            raise KeyError(f"Unknown claim: {claim_id}")

        report: Dict[str, EvidenceStatus] = {}
        frontier = [claim_id]
        visited: Set[str] = set()

        while frontier:
            next_frontier: List[str] = []
            for cid in frontier:
                if cid in visited:
                    continue
                visited.add(cid)
                report[cid] = self.nodes[cid].status
                next_frontier.extend(self._dependents.get(cid, set()))
            frontier = next_frontier

        return report


# ---------------------------------------------------------------------------
# Pre-populate with the actual dependency graph from the paper
# ---------------------------------------------------------------------------

def build_paper_dependency_graph() -> EvidenceDependencyManager:
    """Build the dependency DAG from the paper's claim structure.

    Dependency relationships (from the formalization paper):
      E_AAF_GROUNDED  (E1)  — independent (AAF convergence, n<=4)
      E2              — depends on E1 (stratified evaluator depends on AAF convergence)
      E3              — refutes E_ORIGINAL_EVALUATOR_MONOTONE (standalone counterexample)
      A1_TOY_ROSETTA  (T8.3) — independent (toy model)
      A1_REAL_ROSETTA — depends on A1_TOY_ROSETTA (real data builds on toy scaffolding)
      C_TOY_BANACH    (T9.2) — independent (scalar Banach)
      C_REAL_BANACH   — depends on C_TOY_BANACH (real pricing needs toy baseline)
      D_PRIVILEGE_EPSILON — depends on E_AAF_GROUNDED (privilege lattice uses AAF framework)
    """
    mgr = EvidenceDependencyManager()

    # Independent roots
    mgr.add_node(ClaimNode(
        claim_id="E_AAF_GROUNDED",
        status=EvidenceStatus.PROVED_BY_EXHAUSTIVE_ENUMERATION,
        dependencies=[],
    ))
    mgr.add_node(ClaimNode(
        claim_id="A1_TOY_ROSETTA",
        status=EvidenceStatus.TOY_SYNTHETIC_PROOF_ONLY,
        dependencies=[],
    ))
    mgr.add_node(ClaimNode(
        claim_id="C_TOY_BANACH",
        status=EvidenceStatus.TOY_SYNTHETIC_PROOF_ONLY,
        dependencies=[],
    ))
    mgr.add_node(ClaimNode(
        claim_id="E_ORIGINAL_EVALUATOR_MONOTONE",
        status=EvidenceStatus.REFUTED_BY_COUNTEREXAMPLE,
        dependencies=[],
    ))

    # E2: stratified evaluator depends on AAF convergence
    mgr.add_node(ClaimNode(
        claim_id="E2_STRATIFIED_EVALUATOR",
        status=EvidenceStatus.TOY_SYNTHETIC_PROOF_ONLY,
        dependencies=["E_AAF_GROUNDED"],
    ))

    # E3: original evaluator monotonicity refutation (standalone)
    mgr.add_node(ClaimNode(
        claim_id="E3_EVALUATOR_REFUTATION",
        status=EvidenceStatus.REFUTED_BY_COUNTEREXAMPLE,
        dependencies=[],
    ))

    # A1_REAL_ROSETTA depends on A1_TOY_ROSETTA
    mgr.add_node(ClaimNode(
        claim_id="A1_REAL_ROSETTA",
        status=EvidenceStatus.DATA_INSUFFICIENT_FOR_PROOF,
        dependencies=["A1_TOY_ROSETTA"],
    ))

    # C_REAL_BANACH depends on C_TOY_BANACH
    mgr.add_node(ClaimNode(
        claim_id="C_REAL_BANACH",
        status=EvidenceStatus.DATA_INSUFFICIENT_FOR_PROOF,
        dependencies=["C_TOY_BANACH"],
    ))

    # D_PRIVILEGE_EPSILON depends on E_AAF_GROUNDED
    mgr.add_node(ClaimNode(
        claim_id="D_PRIVILEGE_EPSILON",
        status=EvidenceStatus.REFUTED_BY_COUNTEREXAMPLE,
        dependencies=["E_AAF_GROUNDED"],
    ))

    return mgr


# ---------------------------------------------------------------------------
# Demo
# ---------------------------------------------------------------------------

def demo() -> None:
    print("=" * 72)
    print("Evidence Dependency Manager — Demo")
    print("=" * 72)

    mgr = build_paper_dependency_graph()

    print("\nInitial claim statuses:")
    print("-" * 72)
    for cid, node in mgr.nodes.items():
        deps = node.dependencies if node.dependencies else ["(none)"]
        print(f"  {cid:<35} {node.status.value}")
        print(f"    depends on: {', '.join(deps)}")

    # Show impact report for E_AAF_GROUNDED
    print("\nImpact report — E_AAF_GROUNDED:")
    print("-" * 72)
    report = mgr.get_impact_report("E_AAF_GROUNDED")
    for cid, status in report.items():
        print(f"  {cid:<35} {status.value}")

    # Scenario: E_AAF_GROUNDED gets refuted (e.g., a larger counterexample found)
    print("\n>>> Scenario: E_AAF_GROUNDED is REFUTED_BY_COUNTEREXAMPLE")
    print("-" * 72)
    changes = mgr.propagate_status_change(
        "E_AAF_GROUNDED",
        EvidenceStatus.REFUTED_BY_COUNTEREXAMPLE,
    )
    print("Propagation changes:")
    for cid, new_status in changes.items():
        print(f"  {cid:<35} -> {new_status.value}")

    print("\nUpdated claim statuses after propagation:")
    print("-" * 72)
    for cid, node in mgr.nodes.items():
        print(f"  {cid:<35} {node.status.value}")

    print("\nDemo completed successfully.")


if __name__ == "__main__":
    demo()
