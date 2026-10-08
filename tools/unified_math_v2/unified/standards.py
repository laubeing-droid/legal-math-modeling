"""Reason-node standards: certificates, post-extension comparison, and
CivilHigh exclusion (plan §5.3.2–§5.4, J.6.4).

The pipeline order is fixed by §5.3.6 and is NOT a configuration choice:

1. Local material generates reason nodes (warrant templates W-DIRECT …
   W-ANSWER) with roles: a node may carry ``StrongBasis`` for its claim
   and, by the same-identity rule, ``MaterialCounter`` against the
   accurate contrary claim.
2. Answer/Compare certificates are generated BEFORE extensions; each
   must carry a real attack witness of one of the seven kinds — a bare
   "answered" label produces no edge.
3. Extensions E of the resulting graph are solved (WP-3 machinery).
4. Only then: Out/Live, ``Cmp_E``, ``StrictSuperior_E = Cmp_E(r,s) ∧
   ¬Cmp_E(s,r)`` (never written back into the graph), and the standards.
5. Finalization applies Pos/Neg/undetermined over the finished tables.

The general exclusion theorem (no scope holds both CivilHigh(p) and
CivilHigh(¬p) in one conflict-free extension) is data-independent; the
test suite brute-forces small universes to check it, but the module
itself computes the standard per extension, never by averaging.
"""

from __future__ import annotations

from dataclasses import dataclass
from enum import Enum
from typing import FrozenSet, Optional, Tuple

from theory.spec.canonical_v2.case import Polar
from theory.spec.canonical_v2.kernel import Judgment

from .argument_grammar import (
    ArgumentGrammar,
    AttackKind,
    AttackPolicy,
    ExtensionProfile,
    GrammarLeaf,
    SummaryGraph,
    compile_summary_defeats,
    enumerate_extensions,
    saturate_summaries,
)


class WarrantKind(str, Enum):
    """§5.3.2 named warrant templates.  Strength is not a free input:
    W-STRONG produces StrongBasis only when its local conditions hold."""

    W_DIRECT = "W-DIRECT"
    W_INDIRECT = "W-INDIRECT"
    W_CORR = "W-CORR"
    W_STRONG = "W-STRONG"
    W_COUNTER = "W-COUNTER"
    W_MATERIAL = "W-MATERIAL"
    W_ALT = "W-ALT"
    W_ANSWER = "W-ANSWER"


@dataclass(frozen=True)
class ReasonNode:
    """r=(claim, polarity, kind, leaves, warrant, conditions).  The same
    node can carry StrongBasis for its claim and MaterialCounter against
    the contrary claim — its identity never changes."""

    node_id: str
    claim: str
    polar: Polar
    kind: WarrantKind
    leaves: FrozenSet[str] = frozenset()
    warrant_id: str = ""
    conditions: Tuple[str, ...] = ()

    def __post_init__(self) -> None:
        if not self.node_id or not self.claim:
            raise ValueError("reason node requires id and claim")


@dataclass(frozen=True)
class AnswerCertificate:
    """c answers counter s of claim p, via attacker node a with a REAL
    attack witness of the named kind.  Without a witness-valid edge the
    certificate is a proposal only."""

    cert_id: str
    claim: str
    counter_node: str
    attacker_node: str
    kind: AttackKind

    def __post_init__(self) -> None:
        if self.attacker_node == self.counter_node:
            raise ValueError("an answer cannot target itself")


@dataclass(frozen=True)
class CompareCertificate:
    """r is strictly locally superior to s, witnessed by attacker node a
    defeating s.  Both directions may coexist (then neither is strict)."""

    cert_id: str
    stronger_node: str
    weaker_node: str
    attacker_node: str
    kind: AttackKind


@dataclass(frozen=True)
class ReasonUniverse:
    reasons: Tuple[ReasonNode, ...]
    contraries: FrozenSet[Tuple[str, str]]
    priority: FrozenSet[Tuple[str, str]] = frozenset()
    answer_certs: Tuple[AnswerCertificate, ...] = ()
    compare_certs: Tuple[CompareCertificate, ...] = ()

    def __post_init__(self) -> None:
        ids = [r.node_id for r in self.reasons]
        if len(set(ids)) != len(ids):
            raise ValueError("duplicate reason node ids")
        known = set(ids)
        for cert in self.answer_certs:
            if cert.counter_node not in known or cert.attacker_node not in known:
                raise ValueError("answer certificate names unknown nodes")
        for cert in self.compare_certs:
            if cert.stronger_node not in known or cert.weaker_node not in known:
                raise ValueError("compare certificate names unknown nodes")
            if cert.attacker_node not in known:
                raise ValueError("compare certificate names unknown attacker")


@dataclass(frozen=True)
class CounterEvidence:
    """One counter-evidence package against a claim (plan 5.3.2):

    * W-MATERIAL fires when the evidence has verifiable DIRECT support
      and either independent corroboration or a decisive contradiction,
      AND would change the element if it held — only then does it become
      a material counter (a bare denial generates nothing).
    * W-ALT produces an anchored reasonable alternative (harmless to the
      ordinary standard; must be answered under high standards).
    """

    evidence_id: str
    against_claim: str
    direct_support: bool = False
    corroborated: bool = False
    dispositive: bool = False
    decisive_contradiction: bool = False  # 5.3.2: (佐证 OR 决定性矛盾)
    anchor: str = ""            # concrete factual anchor (W-ALT)
    is_alternative: bool = False  # W-ALT package instead of W-MATERIAL

    def __post_init__(self) -> None:
        if not self.evidence_id or not self.against_claim:
            raise ValueError("counter evidence requires id and target claim")


def counter_reason_nodes(evidence: Iterable[CounterEvidence]) -> Tuple[ReasonNode, ...]:
    """Generate W-MATERIAL / W-ALT / W-COUNTER reason nodes from the
    material packages (5.3.2's middle table):

    * a MATERIAL package becomes a strong node for the CONTRARY claim —
      the same-identity bridge then makes it a material counter
      automatically (Strong(not-p, s) doubles as MaterialCounter(p, s));
    * an ALTERNATIVE package becomes a weak W-ALT node carrying its
      anchor in the conditions (an answer certificate must defeat it
      under high standards);
    * bare denials without direct support generate NOTHING.
    """

    def _contrary(claim: str) -> str:
        return "~" + claim[1:] if claim.startswith("~") else "~" + claim

    nodes: list = []
    for ev in evidence:
        if ev.is_alternative:
            if not ev.anchor:
                raise ValueError(
                    f"alternative {ev.evidence_id} needs a concrete anchor"
                )
            nodes.append(
                ReasonNode(
                    node_id=f"alt:{ev.evidence_id}",
                    claim=_contrary(ev.against_claim),
                    polar=Polar.NEG,
                    kind=WarrantKind.W_ALT,
                    leaves=frozenset({ev.evidence_id}),
                    warrant_id=ev.evidence_id,
                    conditions=(ev.anchor,),
                )
            )
            continue
        # 5.3.2 W-MATERIAL: direct support AND dispositive AND
        # (independent corroboration OR decisive contradiction)
        if (
            ev.direct_support
            and ev.dispositive
            and (ev.corroborated or ev.decisive_contradiction)
        ):
            nodes.append(
                ReasonNode(
                    node_id=f"material:{ev.evidence_id}",
                    claim=_contrary(ev.against_claim),
                    polar=Polar.NEG,
                    kind=WarrantKind.W_MATERIAL,
                    leaves=frozenset({ev.evidence_id}),
                    warrant_id=ev.evidence_id,
                    conditions=(ev.evidence_id, "direct", "corroborated",
                                "dispositive"),
                )
            )
        # bare denial or non-dispositive material: generates nothing
    return tuple(nodes)


def strong_roles(universe: ReasonUniverse) -> FrozenSet[Tuple[str, str]]:
    """(claim, node_id) pairs where the node's warrant actually confers
    StrongBasis — W-STRONG (or a named sufficientity template) with its
    local conditions recorded.  Same identity also carries the counter
    role against the accurate contrary claim (§5.3.6 rule 1)."""

    roles: set = set()
    for reason in universe.reasons:
        if reason.kind is WarrantKind.W_STRONG and reason.conditions:
            roles.add((reason.claim, reason.node_id))
        # a W-MATERIAL node carries strong force for its own (contrary)
        # claim: Strong(not-p, s) doubles as MaterialCounter(p, s)
        if reason.kind is WarrantKind.W_MATERIAL and reason.conditions:
            roles.add((reason.claim, reason.node_id))
    return frozenset(roles)


def counter_roles(universe: ReasonUniverse) -> FrozenSet[Tuple[str, str]]:
    """(claim, node_id): the node carries StrongBasis for a claim contrary
    to ``claim`` — the same-identity counter role (§5.3.6 rule 1)."""

    strong_claim_of = {node: claim for (claim, node) in strong_roles(universe)}
    counters: set = set()
    for node, node_claim in strong_claim_of.items():
        for a, b in universe.contraries:
            if b == node_claim:
                counters.add((a, node))
            if a == node_claim:
                counters.add((b, node))
    return frozenset(counters)


def _cert_edge_valid(
    attacker: ReasonNode,
    target: ReasonNode,
    kind: AttackKind,
    policy: AttackPolicy,
) -> bool:
    """The witness condition of the named kind between two reason nodes:
    contrary-and-not-stronger for rebut, blocked-use/gate atom matches
    otherwise.  Preference is read by rebut/undermine only."""

    if kind in (AttackKind.REBUT, AttackKind.UNDERMINE):
        if not policy.is_contrary(attacker.claim, target.claim):
            return False
        target_last = frozenset({target.node_id})
        attacker_last = frozenset({attacker.node_id})
        return not policy.stronger(target_last, attacker_last)
    if kind is AttackKind.UNDERCUT:
        return attacker.claim == f"blocked_use:{target.node_id}"
    # gate kinds: attacker concludes GateBlocked(g) naming the target's
    # rule instance; for reason nodes the instance key is the node id.
    prefix = {"EXCEPTION": "exception", "AUTHORITY": "authority",
              "SCOPE": "scope", "PROCEDURE": "procedure"}[kind.value]
    return attacker.claim == f"gate_blocked:{target.node_id}:{prefix}"


def build_reason_graph(universe: ReasonUniverse) -> SummaryGraph:
    """Reason nodes become grammar leaves; certificate edges are added
    only when their witness condition holds.  Bare labels produce no
    edges and simply drop out."""

    leaves = tuple(
        GrammarLeaf(leaf_id=r.node_id, atom=r.claim) for r in universe.reasons
    )
    policy = AttackPolicy(
        contraries=universe.contraries, priority=universe.priority
    )
    saturated = saturate_summaries(ArgumentGrammar(leaves=leaves, rules=()))
    graph = compile_summary_defeats(saturated, policy)

    by_node = {
        r.node_id: next(
            s for s in saturated.summaries if s.head.root_rule is None
            and s.head.conc == r.claim
            and next(iter(s.sites)).source == r.node_id
        )
        for r in universe.reasons
    }
    reasons_by_id = {r.node_id: r for r in universe.reasons}

    extra: set = set(graph.typed_edges)
    for cert in universe.answer_certs:
        attacker = reasons_by_id[cert.attacker_node]
        target = reasons_by_id[cert.counter_node]
        if _cert_edge_valid(attacker, target, cert.kind, policy):
            extra.add(
                (by_node[cert.attacker_node], by_node[cert.counter_node], cert.kind)
            )
    for cert in universe.compare_certs:
        attacker = reasons_by_id[cert.attacker_node]
        target = reasons_by_id[cert.weaker_node]
        if _cert_edge_valid(attacker, target, cert.kind, policy):
            extra.add(
                (by_node[cert.attacker_node], by_node[cert.weaker_node], cert.kind)
            )
    return SummaryGraph(
        nodes=saturated.summaries, typed_edges=frozenset(extra)
    )


def _node_of(summary) -> str:
    return next(iter(summary.sites)).source


@dataclass(frozen=True)
class ExtensionView:
    """Fixed extension E: In/Out/Live, Cmp and StrictSuperior projections.
    StrictSuperior is asymmetric by construction (A∧¬B vs B∧¬A) and is
    never written back into the graph."""

    extension: FrozenSet[str]  # node ids In
    out: FrozenSet[str]
    cmp_pairs: FrozenSet[Tuple[str, str]]

    def is_in(self, node: str) -> bool:
        return node in self.extension

    def is_live(self, node: str) -> bool:
        return node not in self.out

    def strictly_superior(self, r: str, s: str) -> bool:
        return (r, s) in self.cmp_pairs and (s, r) not in self.cmp_pairs


def extension_view(universe: ReasonUniverse, graph: SummaryGraph) -> Tuple[ExtensionView, ...]:
    """One view per complete extension of the reason graph (§5.3.6)."""

    views: list = []
    for ext in enumerate_extensions(graph, ExtensionProfile.COMPLETE):
        in_nodes = frozenset(_node_of(s) for s in ext)
        out_nodes = frozenset(
            _node_of(t)
            for (s, t, _k) in graph.typed_edges
            if _node_of(s) in in_nodes
        )
        cmp_pairs: set = set()
        for cert in universe.compare_certs:
            attacker = cert.attacker_node
            weaker = cert.weaker_node
            witness = any(
                _node_of(s) == attacker and _node_of(t) == weaker
                for (s, t, _k) in graph.typed_edges
            )
            if witness and attacker in in_nodes:
                cmp_pairs.add((cert.stronger_node, cert.weaker_node))
        views.append(
            ExtensionView(
                extension=in_nodes,
                out=out_nodes,
                cmp_pairs=frozenset(cmp_pairs),
            )
        )
    return tuple(views)


@dataclass(frozen=True)
class StandardOutcome:
    claim: str
    civil_high: bool
    live_counters: Tuple[str, ...]          # unresolved material counters
    strong_in: Tuple[str, ...]              # In strong-basis witnesses
    answered_counters: Tuple[str, ...]      # Out counters with their basis


def civil_high(claim: str, view: ExtensionView, universe: ReasonUniverse) -> StandardOutcome:
    """CivilHigh(p) := ∃ In StrongBasis(p, r) and every Live material
    counter against p has an In answer or a strict superiority — which,
    by the real-defeat lemma, is exactly “no Live material counter”."""

    strong = strong_roles(universe)
    counters = counter_roles(universe)
    strong_in = tuple(
        sorted(node for (c, node) in strong if c == claim and view.is_in(node))
    )
    counter_nodes = {node for (c, node) in counters if c == claim}
    live = tuple(sorted(n for n in counter_nodes if view.is_live(n)))
    answered = tuple(sorted(n for n in counter_nodes if not view.is_live(n)))
    return StandardOutcome(
        claim=claim,
        civil_high=bool(strong_in) and not live,
        live_counters=live,
        strong_in=strong_in,
        answered_counters=answered,
    )


# ---------------------------------------------------------------------------
# §5.4 finalization
# ---------------------------------------------------------------------------


class FinalBasis(str, Enum):
    POS = "POS"                              # Ready ∧ E ∧ ¬B
    NEG_BLOCKED = "NEG_BLOCKED"              # Ready ∧ B
    NEG_BURDEN = "NEG_BURDEN"                # Ready ∧ F ∧ unmet borne element
    LEGALLY_UNDETERMINED = "LEGALLY_UNDETERMINED"
    NOT_READY = "NOT_READY"                  # procedure not ready / suspension
    GAP = "GAP"                              # exhausted but no Need and no proof


@dataclass(frozen=True)
class ElementStatus:
    element: str
    established: Optional[bool]  # None = undecided
    borne_by_claimant: bool = True


@dataclass(frozen=True)
class IssueFinalization:
    claim: str
    judgment: Judgment
    basis: FinalBasis
    witnesses: Tuple[str, ...] = ()


def finalize_issue(
    claim: str,
    ready: bool,
    elements: Tuple[ElementStatus, ...],
    blockers: FrozenSet[str],
    burden_ready: bool,
    exhausted4: bool,
    need: bool,
) -> IssueFinalization:
    """Independent terminal table (§5.4): Pos and Neg are premise-exclusive;
    undetermined requires Exhausted4 ∧ Need ∧ no FinalDerivable±; a missing
    Exhausted4 is not allowed to pose as undetermined (that is a GAP)."""

    if not ready:
        return IssueFinalization(claim, Judgment.PENDING, FinalBasis.NOT_READY)
    if blockers:
        return IssueFinalization(
            claim, Judgment.NOT_ESTABLISHED, FinalBasis.NEG_BLOCKED,
            tuple(sorted(blockers)),
        )
    if elements and all(e.established is True for e in elements):
        return IssueFinalization(claim, Judgment.ESTABLISHED, FinalBasis.POS)
    unmet = tuple(
        e.element for e in elements
        if e.established is not True and e.borne_by_claimant
    )
    if burden_ready and unmet:
        return IssueFinalization(
            claim, Judgment.NOT_ESTABLISHED, FinalBasis.NEG_BURDEN, unmet
        )
    if exhausted4 and need:
        return IssueFinalization(
            claim, Judgment.PENDING, FinalBasis.LEGALLY_UNDETERMINED, unmet
        )
    if exhausted4 and not need and not elements:
        return IssueFinalization(claim, Judgment.PENDING, FinalBasis.GAP)
    return IssueFinalization(claim, Judgment.PENDING, FinalBasis.GAP, unmet)
