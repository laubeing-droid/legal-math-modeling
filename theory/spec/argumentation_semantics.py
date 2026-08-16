#!/usr/bin/env python3
"""P03 argumentation reference semantics (finite enumeration oracle).

Implements the grounded labelling as the protected default semantics and
a finite priority resolver that yields undecided on cycles. The semantics
registry is explicit; switching semantics requires a version-bound
contract and is never silent.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Any, Dict, FrozenSet, Iterable, List, Mapping, Optional, Tuple

SEMANTICS_REGISTRY = ("GROUNDED", "PREFERRED", "STABLE", "COMPLETE")
PROTECTED_DEFAULT_SEMANTICS = "GROUNDED"


@dataclass(frozen=True)
class GroundedLabelling:
    in_nodes: FrozenSet[str]
    out_nodes: FrozenSet[str]
    undecided_nodes: FrozenSet[str]


def grounded_labelling(attacks: Iterable[Tuple[str, str]]) -> GroundedLabelling:
    """Iterative grounded labelling over a finite attack graph."""

    attack_pairs = tuple(attacks)
    nodes = {node for pair in attack_pairs for node in pair}
    attackers: Dict[str, List[str]] = {node: [] for node in nodes}
    for attacker, target in attack_pairs:
        attackers[target].append(attacker)

    in_nodes: set = set()
    out_nodes: set = set()
    changed = True
    while changed:
        changed = False
        for node in nodes - in_nodes - out_nodes:
            if all(attacker in out_nodes for attacker in attackers[node]):
                in_nodes.add(node)
                changed = True
        for node in nodes - in_nodes - out_nodes:
            if any(attacker in in_nodes for attacker in attackers[node]):
                out_nodes.add(node)
                changed = True

    return GroundedLabelling(
        in_nodes=frozenset(in_nodes),
        out_nodes=frozenset(out_nodes),
        undecided_nodes=frozenset(nodes - in_nodes - out_nodes),
    )


def resolve_priority(
    priority_pairs: Iterable[Tuple[str, str]], a: str, b: str
) -> Optional[str]:
    """Priority resolution; mutual priority (cycle) stays undecided."""

    pairs = set(priority_pairs)
    if (a, b) in pairs and (b, a) in pairs:
        return None
    if (a, b) in pairs:
        return a
    if (b, a) in pairs:
        return b
    return None


def check_semantics_switch(
    request: Mapping[str, Any],
) -> Tuple[bool, Tuple[str, ...]]:
    """Semantics switches require a version-bound contract."""

    errors: List[str] = []
    if request.get("from") not in SEMANTICS_REGISTRY:
        errors.append("UNKNOWN_SOURCE_SEMANTICS")
    if request.get("to") not in SEMANTICS_REGISTRY:
        errors.append("UNKNOWN_TARGET_SEMANTICS")
    if request.get("contract_version_bound") is not True:
        errors.append("SEMANTICS_SWITCH_UNBOUND")
    return (not errors, tuple(errors))
