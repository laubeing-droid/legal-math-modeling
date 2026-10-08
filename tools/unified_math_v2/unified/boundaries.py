"""Runtime contracts for the six inexpressibility boundaries (plan §12.6,
J.15).  Each contract is a small explicit operational system with its own
checks; none of them is a generic audit service.

* BND-01  passive pipelines never map a required failure into a normal
          payload (no ``orElse completeDefault`` exists in the grammar).
* BND-02  ``openObligations`` is a bijection with the real work frontier
          W; a COMPLETE claim requires every required root closed and no
          technical failure on this attempt.
* BND-03  profile emptiness is decided by exhaustive powerset/iteration
          semantics; the empty stable family and the {∅} family differ.
* BND-04  a legally-adverse accepted output requires an independent
          licensed derivation; ActualIssued records are separate.
* BND-05  guarantee aggregation meets per-input (never exceeds), rank
          pooling maxes the existing inventory without minting new
          credentials; the two are NOT claimed isomorphic.
* BND-06  taint propagates along actual data/control dependencies through
          cache/retry/log/dedup transfers; repetition never launders.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from enum import Enum
from typing import Dict, FrozenSet, Iterable, List, Mapping, Optional, Sequence, Tuple


# ---------------------------------------------------------------------------
# BND-01: passive pipeline grammar preserves required failures
# ---------------------------------------------------------------------------


class AttemptOutcome(str, Enum):
    COMPLETE = "COMPLETE"
    FAILURE = "FAILURE"


@dataclass(frozen=True)
class Attempt:
    """One run attempt: the failure axis is part of the value — there is
    no constructor that combines a failure with a complete payload."""

    run_key: str
    outcome: AttemptOutcome
    failure_reason: Optional[str] = None
    payload: Optional[str] = None

    def __post_init__(self) -> None:
        if self.outcome is AttemptOutcome.FAILURE and self.payload is not None:
            raise ValueError("a failed attempt carries no normal payload")
        if self.outcome is AttemptOutcome.COMPLETE and self.payload is None:
            raise ValueError("a complete attempt carries its payload")


def passive_map(attempt: Attempt, transform=None) -> Attempt:
    """map preserves the failure axis verbatim; it has no default branch."""

    if attempt.outcome is AttemptOutcome.FAILURE:
        return attempt
    payload = attempt.payload if transform is None else transform(attempt.payload)
    return Attempt(attempt.run_key, AttemptOutcome.COMPLETE, None, payload)


def passive_all_required(attempts: Sequence[Attempt]) -> Attempt:
    """allRequired keeps the FIRST required failure; there is no branch
    that drops it."""

    for attempt in attempts:
        if attempt.outcome is AttemptOutcome.FAILURE:
            return attempt
    return Attempt(
        attempts[0].run_key if attempts else "",
        AttemptOutcome.COMPLETE,
        None,
        "+".join(a.payload or "" for a in attempts),
    )


def passive_bind(attempt: Attempt, follow_up) -> Attempt:
    """bind on a failure returns the failure unchanged."""

    if attempt.outcome is AttemptOutcome.FAILURE:
        return attempt
    return follow_up(attempt)


# ---------------------------------------------------------------------------
# BND-02: open obligations are exactly the work frontier
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class WorkNode:
    node_id: str
    domain: Tuple[str, ...] = ()   # what the node still has to cover


@dataclass
class SolveState:
    """σ=(runKey, T, C, L, W, F): closed roots C, lower bounds L, open
    frontier W, technical failures F.  Moves are explicit; nothing but a
    covering certificate closes a node."""

    run_key: str
    tree: Tuple[WorkNode, ...]
    closed: FrozenSet[str] = field(default_factory=frozenset)
    lower_bounds: FrozenSet[str] = field(default_factory=frozenset)
    frontier: FrozenSet[str] = field(default_factory=frozenset)
    failures: Tuple[str, ...] = ()

    def __post_init__(self) -> None:
        ids = {n.node_id for n in self.tree}
        if not self.frontier <= ids:
            raise ValueError("frontier nodes must belong to the tree")
        if self.closed & self.frontier:
            raise ValueError("a node cannot be closed and open at once")

    def open_obligations(self) -> FrozenSet[str]:
        return self.frontier

    def split(self, node_id: str, children: Sequence[WorkNode]) -> "SolveState":
        if node_id not in self.frontier:
            raise ValueError("only frontier nodes split")
        child_ids = {c.node_id for c in children}
        return SolveState(
            self.run_key,
            self.tree + tuple(children),
            self.closed,
            self.lower_bounds,
            (self.frontier - {node_id}) | child_ids,
            self.failures,
        )

    def close(self, node_id: str, covering: bool) -> "SolveState":
        """Only a covering certificate closes; a member witness alone
        just enters L (never clears W)."""

        if not covering:
            raise ValueError("close requires a covering certificate")
        if node_id not in self.frontier:
            raise ValueError("only frontier nodes close")
        return SolveState(
            self.run_key,
            self.tree,
            self.closed | {node_id},
            self.lower_bounds,
            self.frontier - {node_id},
            self.failures,
        )

    def record_member(self, node_id: str) -> "SolveState":
        if node_id not in self.frontier:
            raise ValueError("witnesses attach to frontier nodes")
        return SolveState(
            self.run_key,
            self.tree,
            self.closed,
            self.lower_bounds | {node_id},
            self.frontier,
            self.failures,
        )

    def record_failure(self, reason: str) -> "SolveState":
        return SolveState(
            self.run_key,
            self.tree,
            self.closed,
            self.lower_bounds,
            self.frontier,
            self.failures + (reason,),
        )

    def run_status(self, required_roots: FrozenSet[str]) -> str:
        if self.failures:
            return "FAILED"
        if not self.frontier:
            return "COMPLETE"
        if self.closed or self.lower_bounds:
            return "SOUND_PARTIAL"
        return "PAUSED"


# ---------------------------------------------------------------------------
# BND-03: profile emptiness by exhaustive semantics
# ---------------------------------------------------------------------------


def _defends(edges: FrozenSet[Tuple[str, str]], subset: FrozenSet[str], a: str) -> bool:
    return all(any((c, b) in edges for c in subset)
               for b in {s for (s, t) in edges if t == a})


def profile_family(nodes: Sequence[str], edges: FrozenSet[Tuple[str, str]],
                   profile: str) -> Tuple[FrozenSet[FrozenSet[str]], ...]:
    """The complete family under exhaustive powerset semantics (or
    iteration for grounded).  A partial scan is never completed here."""

    from itertools import combinations

    if profile == "grounded":
        current = frozenset()
        while True:
            nxt = frozenset(
                a for a in nodes if _defends(edges, current, a)
            )
            if nxt == current:
                return (current,)
            current = nxt
    subsets = [
        frozenset(c)
        for k in range(len(nodes) + 1)
        for c in combinations(sorted(nodes), k)
    ]
    if profile == "stable":
        return tuple(
            s for s in subsets
            if not any((a, b) in edges for a in s for b in s)
            and all(any((a, b) in edges for a in s)
                    for b in set(nodes) - s)
        )
    def _admissible(s):
        return (not any((a, b) in edges for a in s for b in s)
                and all(_defends(edges, s, a) for a in s))
    if profile == "complete":
        return tuple(
            s for s in subsets
            if _admissible(s)
            and frozenset(a for a in nodes if _defends(edges, s, a)) == s
        )
    if profile == "preferred":
        adm = [s for s in subsets if _admissible(s)]
        return tuple(s for s in adm if not any(s < t for t in adm))
    raise ValueError(f"unknown profile: {profile}")


# ---------------------------------------------------------------------------
# BND-04: accepted adverse results need licensed derivations
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class LicensedAdverse:
    """An adverse output the MODEL accepts as legally-correct: it names
    its required roots and each carries a covering certificate id."""

    claim: str
    derivation_id: str
    closed_roots: Tuple[str, ...]
    certificate_ids: Tuple[str, ...]

    def __post_init__(self) -> None:
        if not self.derivation_id:
            raise ValueError("accepted adverse results name their derivation")
        if len(self.closed_roots) != len(self.certificate_ids):
            raise ValueError("one certificate per required root")


@dataclass(frozen=True)
class ActualIssuedRecord:
    """What actually happened, with its provenance — kept regardless of
    legality; never confusable with a LicensedAdverse."""

    document_id: str
    issuer: str
    at_day: int
    authenticity: str  # genuine | forged | unknown


def accept_adverse(state: SolveState, candidate: LicensedAdverse,
                   required: FrozenSet[str]) -> bool:
    """An adverse acceptance requires every required root closed on this
    attempt; open required roots block it (BND-04)."""

    if state.failures:
        return False
    return required <= state.closed and set(candidate.closed_roots) >= required


# ---------------------------------------------------------------------------
# BND-05: guarantee meet vs credential-pool max
# ---------------------------------------------------------------------------


def guarantee_meet(vectors: Sequence[Tuple[int, ...]]) -> Optional[Tuple[int, ...]]:
    """Per-coordinate minimum over the ACTUAL required inputs: the
    aggregate guarantee never exceeds any input's coordinate."""

    if not vectors:
        return None
    width = len(vectors[0])
    if any(len(v) != width for v in vectors):
        raise ValueError("guarantee vectors share a coordinate width")
    return tuple(min(v[i] for v in vectors) for i in range(width))


def credential_pool_max(levels: Sequence[int]) -> Optional[int]:
    """The pool's EXISTING highest rank: repetition cannot mint a higher
    one — max of a constant list stays that constant."""

    return max(levels) if levels else None


# ---------------------------------------------------------------------------
# BND-06: taint along actual dependencies
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class DagNode:
    node_id: str
    parents: Tuple[str, ...] = ()
    source_tainted: bool = False
    payload: str = ""


class TaintLedger:
    """Append-only DAG; taint of a node = whether any tainted SOURCE is
    among its actual ancestors.  Cache reads return the original node
    reference; retries create new attempts that still cite the same
    sources; dedup merges identities without dropping origins."""

    def __init__(self) -> None:
        self._nodes: Dict[str, DagNode] = {}

    def add(self, node: DagNode) -> None:
        for parent in node.parents:
            if parent not in self._nodes:
                raise ValueError(f"parent {parent} must exist before its child")
        if node.node_id in self._nodes:
            raise ValueError(f"duplicate node id {node.node_id}")
        self._nodes[node.node_id] = node

    def derive(self, node_id: str, parents: Sequence[str], payload: str = "") -> str:
        self.add(DagNode(node_id, tuple(parents), False, payload))
        return node_id

    def cache_get(self, node_id: str) -> DagNode:
        """Cache reads return the original reference — taint unchanged."""

        if node_id not in self._nodes:
            raise KeyError(node_id)
        return self._nodes[node_id]

    def retry(self, new_attempt_id: str, original_sources: Sequence[str]) -> None:
        """A retry attempt still depends on the same sources."""

        self.add(DagNode(new_attempt_id, tuple(original_sources), False, "retry"))

    def dedup(self, kept_id: str, duplicate_id: str) -> None:
        """Folding a duplicate JOINS the two source sets: the kept node
        gains the duplicate's parents (12.6.7 transfer table).  A clean
        kept node with a tainted duplicate becomes tainted — identical
        payloads do not launder different ancestries."""

        if kept_id not in self._nodes or duplicate_id not in self._nodes:
            raise KeyError("dedup requires both nodes")
        if kept_id == duplicate_id:
            raise ValueError("a node cannot be deduplicated with itself")
        # folding a DESCENDANT into its own ancestor would create a
        # cycle; the ledger stays a DAG (round-3 N3)
        stack = list(self._nodes[duplicate_id].parents)
        seen_guard = set()
        while stack:
            cur = stack.pop()
            if cur in seen_guard:
                continue
            seen_guard.add(cur)
            if cur == kept_id:
                raise ValueError(
                    "dedup would fold a descendant into its ancestor "
                    "(cycle); fold the ancestor into the descendant instead"
                )
            stack.extend(self._nodes[cur].parents)
        kept = self._nodes[kept_id]
        duplicate = self._nodes[duplicate_id]
        # the duplicate ITSELF joins the kept ancestry: a tainted SOURCE
        # duplicate (no parents, source_tainted) propagates through the
        # parent link (round-2 defect B)
        merged = tuple(
            dict.fromkeys(kept.parents + duplicate.parents + (duplicate_id,))
        )
        self._nodes[kept_id] = DagNode(
            kept.node_id, merged,
            kept.source_tainted or duplicate.source_tainted,
            kept.payload,
        )

    def taint_of(self, node_id: str) -> bool:
        seen = set()
        stack = [node_id]
        while stack:
            current = stack.pop()
            if current in seen:
                continue
            seen.add(current)
            node = self._nodes[current]
            if node.source_tainted:
                return True
            stack.extend(node.parents)
        return False
