"""Regular tree grammar of legal arguments, finite summaries, the seven
attack kinds, and exact extension pullback (plan §4, J.0 item 1, J.6.3).

Three objects are kept strictly separate:

* ``ArgTree`` — a finite ordered argument tree.  Rules, sources, premise
  order and nesting are part of tree identity; the tree language of the
  grammar is exactly the set of well-formed finite argument trees and it
  may be infinite (fact p plus rule p ⇒ p).
* ``Summary`` — the finite observable ``(head, sites)`` used for
  acceptance computation.  Saturation produces the finite reachable set
  Q with one generating-tree witness per summary.  Equal summaries never
  claim the trees are equal.
* ``typed edges`` — the seven attack kinds compiled on Q × Q with path
  witnesses retained in the generating trees.

Default last-set policy (§4.2): ``Last(leaf)=∅``, ``Last(def(j,…))={j}``,
``Last(strict(…))=⋃Last(children)``.  Only rebut and undermine consult
the preference; the other five kinds never do.
"""

from __future__ import annotations

from dataclasses import dataclass
from enum import Enum
from itertools import product
from typing import Dict, FrozenSet, Iterable, Mapping, Optional, Tuple


class ArgMode(str, Enum):
    STRICT = "STRICT"
    DEFEASIBLE = "DEFEASIBLE"


class AttackKind(str, Enum):
    """The seven named attack kinds (§4.3).  Self-attack and cycles are
    graph properties, not extra kinds."""

    REBUT = "REBUT"
    UNDERMINE = "UNDERMINE"
    UNDERCUT = "UNDERCUT"
    EXCEPTION = "EXCEPTION"
    AUTHORITY = "AUTHORITY"
    SCOPE = "SCOPE"
    PROCEDURE = "PROCEDURE"


# Guard kinds of the four gate attacks (exception/authority/scope/procedure).
GUARD_KINDS = frozenset({"exception", "authority", "scope", "procedure"})


@dataclass(frozen=True)
class GuardSlot:
    """g=(Inst, kind, slot) with its declared scope fields (§4.3 table)."""

    rule_instance: str
    kind: str
    slot: str
    scope: Tuple[str, ...] = ()
    source: str = ""

    def atom(self) -> str:
        return f"gate_blocked:{self.rule_instance}:{self.kind}:{self.slot}"


@dataclass(frozen=True)
class GrammarRule:
    """One grammar production r: p₁…pₖ ⇒ p with mode and guard slots."""

    rule_id: str
    premises: Tuple[str, ...]
    head: str
    mode: ArgMode = ArgMode.DEFEASIBLE
    guard_slots: Tuple[GuardSlot, ...] = ()

    def __post_init__(self) -> None:
        if not self.rule_id or not self.head:
            raise ValueError("rule requires id and head")
        if any(not p for p in self.premises):
            raise ValueError("premise atoms must be nonempty")
        if self.mode is ArgMode.DEFEASIBLE and self.rule_id in self.premises:
            pass  # rooted cycles are legal; they generate nothing alone
        for g in self.guard_slots:
            if g.rule_instance != self.rule_id:
                raise ValueError("guard slot must name its own rule instance")
            if g.kind not in GUARD_KINDS:
                raise ValueError(f"unknown guard kind: {g.kind}")


@dataclass(frozen=True)
class GrammarLeaf:
    """One source production e : p.  ``leaf_kind`` separates ordinary
    attackable premises from axiom/exempt leaves that undermine cannot
    target (§4.3 undermine row)."""

    leaf_id: str
    atom: str
    leaf_kind: str = "ordinary"
    source: str = ""

    def __post_init__(self) -> None:
        if not self.leaf_id or not self.atom:
            raise ValueError("leaf requires id and atom")


@dataclass(frozen=True)
class ArgTree:
    """A finite argument tree: ``leaf(e)`` or ``node(r, a₁,…,aₖ)``.
    Rule instance, source, premise order and nesting are identity."""

    leaf: Optional[GrammarLeaf]
    rule: Optional[GrammarRule]
    children: Tuple["ArgTree", ...]

    def __post_init__(self) -> None:
        if (self.leaf is None) == (self.rule is None):
            raise ValueError("exactly one of leaf/rule must be set")
        if self.leaf is not None:
            if self.children:
                raise ValueError("a leaf has no children")
        else:
            if tuple(c.head for c in self.children) != self.rule.premises:
                raise ValueError("child conclusions must match premise order")
            if self.rule.mode is ArgMode.DEFEASIBLE:
                return  # defeasible rules may use strict or defeasible support

    # -- convenience -----------------------------------------------------
    @property
    def head(self) -> str:
        return self.leaf.atom if self.leaf is not None else self.rule.head

    @property
    def mode(self) -> ArgMode:
        return ArgMode.STRICT if self.leaf is not None else self.rule.mode

    @property
    def depth(self) -> int:
        if self.leaf is not None:
            return 0
        return 1 + max((c.depth for c in self.children), default=0)

    def subtree_id(self) -> tuple:
        return (self.leaf, self.rule, tuple(c.subtree_id() for c in self.children))


def leaf_argument(leaf: GrammarLeaf) -> ArgTree:
    return ArgTree(leaf=leaf, rule=None, children=())


def node_argument(rule: GrammarRule, children: Tuple[ArgTree, ...]) -> ArgTree:
    return ArgTree(leaf=None, rule=rule, children=children)


# ---------------------------------------------------------------------------
# Summaries
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class HeadSummary:
    conc: str
    mode: ArgMode
    root_rule: Optional[str]
    last: FrozenSet[str]
    leaf_sources: FrozenSet[str]
    tags: FrozenSet[str]


@dataclass(frozen=True)
class SiteSummary:
    conc: str
    mode: ArgMode
    leaf_kind: Optional[str]
    inst: Optional[str]
    last: FrozenSet[str]
    guard_slots: Tuple[GuardSlot, ...]
    source: Optional[str]


@dataclass(frozen=True)
class Summary:
    """The finite observable of a tree.  Identity is (head, sites) only."""

    head: HeadSummary
    sites: FrozenSet[SiteSummary]


def blocked_use_atom(instance: str) -> str:
    return f"blocked_use:{instance}"


def last_of(tree: ArgTree) -> FrozenSet[str]:
    """Default last-set policy: leaves ∅, defeasible roots {j}, strict
    roots union of children (§4.2)."""

    if tree.leaf is not None:
        return frozenset()
    if tree.rule.mode is ArgMode.DEFEASIBLE:
        return frozenset({tree.rule.rule_id})
    union: set = set()
    for child in tree.children:
        union |= last_of(child)
    return frozenset(union)


def leaf_sources_of(tree: ArgTree) -> FrozenSet[str]:
    if tree.leaf is not None:
        return frozenset({tree.leaf.leaf_id})
    union: set = set()
    for child in tree.children:
        union |= leaf_sources_of(child)
    return frozenset(union)


def _own_site(tree: ArgTree) -> Optional[SiteSummary]:
    """The attackable-subtree description of the tree root itself, or None
    when the root is not an attackable position."""

    if tree.leaf is not None:
        if tree.leaf.leaf_kind == "ordinary":
            return SiteSummary(
                conc=tree.leaf.atom,
                mode=ArgMode.STRICT,
                leaf_kind=tree.leaf.leaf_kind,
                inst=None,
                last=frozenset(),
                guard_slots=(),
                source=tree.leaf.source or tree.leaf.leaf_id,
            )
        return None  # axiom/exempt leaves are not attackable positions
    return SiteSummary(
        conc=tree.rule.head,
        mode=tree.rule.mode,
        leaf_kind=None,
        inst=tree.rule.rule_id,
        last=last_of(tree),
        guard_slots=tree.rule.guard_slots,
        source=None,
    )


def summarize(tree: ArgTree) -> Summary:
    sites: set = set()
    own = _own_site(tree)
    if own is not None:
        sites.add(own)
    for child in tree.children:
        sites |= summarize(child).sites
    return Summary(
        head=HeadSummary(
            conc=tree.head,
            mode=tree.mode,
            root_rule=None if tree.leaf is not None else tree.rule.rule_id,
            last=last_of(tree),
            leaf_sources=leaf_sources_of(tree),
            tags=frozenset(),
        ),
        sites=frozenset(sites),
    )


# ---------------------------------------------------------------------------
# Grammar and saturation
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class ArgumentGrammar:
    leaves: Tuple[GrammarLeaf, ...]
    rules: Tuple[GrammarRule, ...]

    def __post_init__(self) -> None:
        if len({l.leaf_id for l in self.leaves}) != len(self.leaves):
            raise ValueError("duplicate leaf ids")
        if len({r.rule_id for r in self.rules}) != len(self.rules):
            raise ValueError("duplicate rule ids")


@dataclass(frozen=True)
class SaturatedSummaries:
    """The finite quotient Q with one generating witness per summary."""

    grammar: ArgumentGrammar
    summaries: Tuple[Summary, ...]
    witnesses: Tuple[ArgTree, ...]

    def summary_keys(self) -> FrozenSet[Summary]:
        return frozenset(self.summaries)

    def by_conclusion(self, atom: str) -> Tuple[Summary, ...]:
        return tuple(s for s in self.summaries if s.head.conc == atom)


def _delta(rule: GrammarRule, children: Tuple[Summary, ...]) -> Summary:
    """Summary transfer δ_r(q₁,…,qₖ): root head op, child-sites union,
    plus the new node's own site (§4.2)."""

    last: FrozenSet[str]
    if rule.mode is ArgMode.DEFEASIBLE:
        last = frozenset({rule.rule_id})
    else:
        merged: set = set()
        for child in children:
            merged |= child.head.last
        last = frozenset(merged)
    sources: set = set()
    tags: set = set()
    sites: set = set()
    for child in children:
        sources |= child.head.leaf_sources
        tags |= child.head.tags
        sites |= child.sites
    sites.add(
        SiteSummary(
            conc=rule.head,
            mode=rule.mode,
            leaf_kind=None,
            inst=rule.rule_id,
            last=last,
            guard_slots=rule.guard_slots,
            source=None,
        )
    )
    return Summary(
        head=HeadSummary(
            conc=rule.head,
            mode=rule.mode,
            root_rule=rule.rule_id,
            last=last,
            leaf_sources=frozenset(sources),
            tags=frozenset(tags),
        ),
        sites=frozenset(sites),
    )


def saturate_summaries(grammar: ArgumentGrammar) -> SaturatedSummaries:
    """Least fixed point of δ from the leaf productions.  Every reachable
    summary carries one generating tree witness; termination is by the
    finite summary domain (finite atoms × finite instances × finite
    source sets × finite sites)."""

    seen: Dict[Summary, ArgTree] = {}
    by_atom: Dict[str, list] = {}
    worklist: list = []
    for leaf in grammar.leaves:
        tree = leaf_argument(leaf)
        summary = summarize(tree)
        if summary not in seen:
            seen[summary] = tree
            by_atom.setdefault(leaf.atom, []).append(summary)
            worklist.append(summary)
    # Seed by_atom for every atom mentioned by a rule so empty pools exist.
    for rule in grammar.rules:
        for atom in (*rule.premises, rule.head):
            by_atom.setdefault(atom, [])

    changed = True
    while changed:
        changed = False
        for rule in grammar.rules:
            pools = tuple(by_atom.get(p, []) for p in rule.premises)
            if any(not pool for pool in pools):
                continue  # this production cannot fire yet (or ever)
            for combo in product(*pools):
                new_summary = _delta(rule, combo)
                if new_summary in seen:
                    continue
                child_witnesses = tuple(seen[c] for c in combo)
                tree = node_argument(rule, child_witnesses)
                seen[new_summary] = tree
                by_atom.setdefault(rule.head, []).append(new_summary)
                changed = True
    keys = tuple(sorted(seen.keys(), key=repr))
    return SaturatedSummaries(
        grammar=grammar,
        summaries=keys,
        witnesses=tuple(seen[k] for k in keys),
    )


# ---------------------------------------------------------------------------
# Defeat compilation: the seven kinds on summaries
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class AttackPolicy:
    """Fixed inputs of the defeat relation: contrary pairs (symmetric),
    the last-set priority u ≻ v, and whether the declared profile lets
    undercut read preference (the T05 profile does not)."""

    contraries: FrozenSet[Tuple[str, str]]
    priority: FrozenSet[Tuple[str, str]] = frozenset()
    undercut_reads_preference: bool = False

    def is_contrary(self, a: str, b: str) -> bool:
        return (a, b) in self.contraries or (b, a) in self.contraries

    def stronger(self, u_last: FrozenSet[str], v_last: FrozenSet[str]) -> bool:
        """Stronger(U,V) iff both Last sets nonempty and every v is beaten
        by some u (§4.2)."""

        if not u_last or not v_last:
            return False
        return all(any((u, v) in self.priority for u in u_last) for v in v_last)


def _site_attack_kinds(
    attacker: Summary, site: SiteSummary, policy: AttackPolicy
) -> Iterable[AttackKind]:
    """Which of the seven kinds the attacker's head lands on this site."""

    head = attacker.head
    # rebut: site root is a defeasible conclusion contrary to the attacker's
    # conclusion, and the site is not Stronger than the attacker.
    if (
        site.mode is ArgMode.DEFEASIBLE
        and site.leaf_kind is None
        and policy.is_contrary(head.conc, site.conc)
        and not policy.stronger(site.last, head.last)
    ):
        yield AttackKind.REBUT
    # undermine: an ordinary premise leaf contrary to the attacker's head.
    if (
        site.leaf_kind == "ordinary"
        and policy.is_contrary(head.conc, site.conc)
        and not policy.stronger(site.last, head.last)
    ):
        yield AttackKind.UNDERMINE
    # undercut: attacker concludes BlockedUse(j) for the defeasible
    # instance j the site actually uses; the default profile reads no
    # preference here (§4.3, T05 profile).
    if (
        site.mode is ArgMode.DEFEASIBLE
        and site.inst is not None
        and head.conc == blocked_use_atom(site.inst)
    ):
        if not policy.undercut_reads_preference or not policy.stronger(
            site.last, head.last
        ):
            yield AttackKind.UNDERCUT
    # The four gate attacks: attacker concludes GateBlocked(g) for a guard
    # slot the target actually carries.  GateOK is a premise of the target
    # rule; proving GateBlocked(g) blocks that use.  None of these kinds
    # consult the last-set preference (§4.3).
    if site.guard_slots:
        for guard in site.guard_slots:
            if head.conc == guard.atom():
                kind = {
                    "exception": AttackKind.EXCEPTION,
                    "authority": AttackKind.AUTHORITY,
                    "scope": AttackKind.SCOPE,
                    "procedure": AttackKind.PROCEDURE,
                }[guard.kind]
                yield kind


def summary_defeats(
    attacker: Summary, target: Summary, policy: AttackPolicy
) -> FrozenSet[AttackKind]:
    """D(s,t): the kinds under which s defeats t through one of t's sites."""

    kinds: set = set()
    for site in target.sites:
        kinds.update(_site_attack_kinds(attacker, site, policy))
    return frozenset(kinds)


@dataclass(frozen=True)
class SummaryGraph:
    """Typed attack graph on Q.  ``untyped`` is the existential
    projection of the seven kinds (§4.3) and drives the extension
    semantics; the typed edges retain the kind for consumers."""

    nodes: Tuple[Summary, ...]
    typed_edges: FrozenSet[Tuple[Summary, Summary, AttackKind]]
    untyped: FrozenSet[Tuple[Summary, Summary]] = frozenset()

    def __post_init__(self) -> None:
        if not self.untyped:
            object.__setattr__(
                self,
                "untyped",
                frozenset((s, t) for (s, t, _k) in self.typed_edges),
            )

    def attacks(self, s: Summary, t: Summary) -> bool:
        return (s, t) in self.untyped

    def attackers_of(self, t: Summary) -> FrozenSet[Summary]:
        return frozenset(s for s in self.nodes if (s, t) in self.untyped)


def compile_summary_defeats(
    saturated: SaturatedSummaries, policy: AttackPolicy
) -> SummaryGraph:
    edges: set = set()
    for s in saturated.summaries:
        for t in saturated.summaries:
            for kind in summary_defeats(s, t, policy):
                edges.add((s, t, kind))
    return SummaryGraph(
        nodes=saturated.summaries, typed_edges=frozenset(edges)
    )


# ---------------------------------------------------------------------------
# Extensions on Q with exact pullback
# ---------------------------------------------------------------------------


class ExtensionProfile(str, Enum):
    GROUNDED = "grounded"
    COMPLETE = "complete"
    PREFERRED = "preferred"
    STABLE = "stable"


MAX_EXTENSION_NODES = 16


def _defends(graph: SummaryGraph, s: FrozenSet[Summary], a: Summary) -> bool:
    return all(
        any((c, b) in graph.untyped for c in s) for b in graph.attackers_of(a)
    )


def _conflict_free(graph: SummaryGraph, s: FrozenSet[Summary]) -> bool:
    return not any(
        graph.attacks(a, b) for a in s for b in s
    )


def _admissible(graph: SummaryGraph, s: FrozenSet[Summary]) -> bool:
    return _conflict_free(graph, s) and all(_defends(graph, s, a) for a in s)


def _characteristic(
    graph: SummaryGraph, s: FrozenSet[Summary]
) -> FrozenSet[Summary]:
    return frozenset(a for a in graph.nodes if _defends(graph, s, a))


def grounded_extension(graph: SummaryGraph) -> FrozenSet[Summary]:
    current: FrozenSet[Summary] = frozenset()
    while True:
        nxt = _characteristic(graph, current)
        if nxt == current:
            return current
        current = nxt


def enumerate_extensions(
    graph: SummaryGraph, profile: ExtensionProfile
) -> Tuple[FrozenSet[Summary], ...]:
    """All extensions of the declared profile on the full node set Q.

    complete/stable enumerate the whole powerset; preferred keeps the
    inclusion-maximal admissible sets; grounded iterates F from ∅.  The
    empty-selection family and “only the empty extension” are distinct
    outcomes; a partial scan is never silently completed here."""

    if len(graph.nodes) > MAX_EXTENSION_NODES:
        raise ValueError(
            f"{len(graph.nodes)} summaries exceed the exhaustive extension "
            f"budget ({MAX_EXTENSION_NODES}); refine the profile instead"
        )
    nodes = tuple(graph.nodes)
    all_subsets = [
        frozenset(combo)
        for k in range(len(nodes) + 1)
        for combo in _combinations_sorted(nodes, k)
    ]
    if profile is ExtensionProfile.COMPLETE:
        return tuple(
            s for s in all_subsets if _admissible(graph, s)
            and _characteristic(graph, s) == s
        )
    if profile is ExtensionProfile.STABLE:
        return tuple(
            s for s in all_subsets
            if _conflict_free(graph, s)
            and all(
                any((a, b) in graph.untyped for a in s)
                for b in frozenset(nodes) - s
            )
        )
    if profile is ExtensionProfile.PREFERRED:
        admissible = [s for s in all_subsets if _admissible(graph, s)]
        return tuple(
            s for s in admissible
            if not any(s < t for t in admissible)
        )
    grounded = grounded_extension(graph)
    return (grounded,)


def _combinations_sorted(nodes, k):
    from itertools import combinations

    return combinations(sorted(nodes, key=repr), k)


# ---------------------------------------------------------------------------
# Full-tree level: the identity-preserving check path
# ---------------------------------------------------------------------------


def tree_defeats(
    attacker: ArgTree,
    target: ArgTree,
    policy: AttackPolicy,
) -> FrozenSet[AttackKind]:
    """LegalDefeat on full trees: the attacker's head against every
    attackable subtree (site) of the target, including lifted ancestors'
    sites (§4.3).  Equal summaries give equal kinds — the factorization
    Defeat(a,b) ↔ D(q(a), q(b)) is tested in the suite."""

    return summary_defeats(summarize(attacker), summarize(target), policy)
