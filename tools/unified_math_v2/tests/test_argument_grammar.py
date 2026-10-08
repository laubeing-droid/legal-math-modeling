"""WP-3 tests: grammar saturation, seven attack kinds, exact extensions.

These are finite counterexample checks (J.6.3): rooted-cycle infiniteness
with finite Q, rootless-cycle emptiness, per-kind factorization
Defeat(a,b) ↔ D(q(a),q(b)) on enumerated trees, default last-set policy,
preference blocking only rebut/undermine, and the four extension
families' exact correspondence including the empty-stable case.
"""

from itertools import product
from unittest import TestCase

import pytest

from unified.argument_grammar import (
    ArgMode,
    ArgumentGrammar,
    AttackKind,
    AttackPolicy,
    ExtensionProfile,
    GrammarLeaf,
    GrammarRule,
    GuardSlot,
    SummaryGraph,
    blocked_use_atom,
    compile_summary_defeats,
    enumerate_extensions,
    grounded_extension,
    leaf_argument,
    node_argument,
    saturate_summaries,
    summarize,
    tree_defeats,
)


def _leaf(leaf_id, atom, kind="ordinary"):
    return GrammarLeaf(leaf_id, atom, kind)


def _rule(rule_id, premises, head, mode=ArgMode.DEFEASIBLE, guards=()):
    return GrammarRule(rule_id, tuple(premises), head, mode, guards)


def _contrary_policy(pairs, priority=()):
    return AttackPolicy(contraries=frozenset(pairs), priority=frozenset(priority))


class GrammarSaturationTests(TestCase):
    def test_rooted_cycle_finite_q_infinite_language(self):
        grammar = ArgumentGrammar(
            leaves=(_leaf("e", "p"),),
            rules=(_rule("j", ["p"], "p"),),
        )
        sat = saturate_summaries(grammar)
        # Two summaries: the leaf and the defeasible node.  The tree
        # language is infinite (nesting), Q is finite.
        self.assertEqual(len(sat.summaries), 2)
        node = sat.by_conclusion("p")
        self.assertEqual(len(node), 2)
        # All nestings collapse to the same node summary.
        w0 = sat.witnesss if False else sat.witnesses
        node_witness = next(t for t in w0 if t.leaf is None)
        nested = node_argument(_rule("j", ["p"], "p"), (node_witness,))
        self.assertEqual(summarize(nested), summarize(node_witness))

    def test_rootless_cycle_generates_nothing(self):
        grammar = ArgumentGrammar(
            leaves=(),
            rules=(_rule("j", ["p"], "p"),),
        )
        sat = saturate_summaries(grammar)
        self.assertEqual(sat.summaries, ())

    def test_chain_two_summaries(self):
        grammar = ArgumentGrammar(
            leaves=(_leaf("e", "q"),),
            rules=(_rule("j1", ["q"], "p"),),
        )
        sat = saturate_summaries(grammar)
        self.assertEqual(len(sat.summaries), 2)
        p_summaries = sat.by_conclusion("p")
        self.assertEqual(len(p_summaries), 1)
        self.assertEqual(next(iter(p_summaries)).head.last, frozenset({"j1"}))
        self.assertEqual(
            next(iter(p_summaries)).head.leaf_sources, frozenset({"e"})
        )

    def test_strict_rule_last_is_union(self):
        grammar = ArgumentGrammar(
            leaves=(_leaf("e1", "q1"), _leaf("e2", "q2")),
            rules=(
                _rule("jd1", ["q1"], "m1"),
                _rule("jd2", ["q2"], "m2"),
                _rule("js", ["m1", "m2"], "p", mode=ArgMode.STRICT),
            ),
        )
        sat = saturate_summaries(grammar)
        p = sat.by_conclusion("p")
        self.assertEqual(len(p), 1)
        # Strict root: Last = union of children's Last sets.
        self.assertEqual(next(iter(p)).head.last, frozenset({"jd1", "jd2"}))

    def test_axiom_leaf_has_no_site(self):
        tree = leaf_argument(_leaf("ax", "p", kind="axiom"))
        summary = summarize(tree)
        self.assertEqual(summary.sites, frozenset())

    def test_ordinary_leaf_has_site(self):
        tree = leaf_argument(_leaf("e", "p"))
        summary = summarize(tree)
        self.assertEqual(len(summary.sites), 1)
        site = next(iter(summary.sites))
        self.assertEqual(site.leaf_kind, "ordinary")

    def test_child_must_match_premise_order(self):
        leaf_q = leaf_argument(_leaf("e", "q"))
        with pytest.raises(ValueError, match="premise order"):
            node_argument(_rule("j", ["q", "r"], "p"), (leaf_q,))


class DefeatCompilationTests(TestCase):
    def _sat(self, leaves, rules):
        return saturate_summaries(ArgumentGrammar(tuple(leaves), tuple(rules)))

    def test_remut_contrary_pair(self):
        sat = self._sat(
            [_leaf("e1", "p"), _leaf("e2", "notp")],
            [],
        )
        policy = _contrary_policy({("p", "notp")})
        graph = compile_summary_defeats(sat, policy)
        s_p = next(s for s in sat.summaries if s.head.conc == "p")
        s_n = next(s for s in sat.summaries if s.head.conc == "notp")
        self.assertTrue(graph.attacks(s_p, s_n))
        self.assertTrue(graph.attacks(s_n, s_p))

    def test_rebut_targets_only_defeasible_roots(self):
        # p is derived by a STRICT rule: no rebut site at its root.
        sat = self._sat(
            [_leaf("e1", "q"), _leaf("e2", "notp")],
            [_rule("js", ["q"], "p", mode=ArgMode.STRICT)],
        )
        policy = _contrary_policy({("p", "notp")})
        graph = compile_summary_defeats(sat, policy)
        s_p = next(s for s in sat.summaries if s.head.conc == "p")
        s_n = next(s for s in sat.summaries if s.head.conc == "notp")
        self.assertFalse(graph.attacks(s_n, s_p))

    def test_preference_blocks_rebut(self):
        # Site j1 ≻ attacker's last j2: Stronger(Bp, A) blocks the rebut.
        sat = self._sat(
            [_leaf("e1", "q1"), _leaf("e2", "q2")],
            [
                _rule("j1", ["q1"], "p"),
                _rule("j2", ["q2"], "notp"),
            ],
        )
        policy = _contrary_policy(
            {("p", "notp")}, priority={("j1", "j2")}
        )
        graph = compile_summary_defeats(sat, policy)
        s_p = next(s for s in sat.summaries if s.head.conc == "p" and s.head.root_rule == "j1")
        s_n = next(s for s in sat.summaries if s.head.conc == "notp")
        # notp cannot rebut the stronger p-site…
        self.assertFalse(graph.attacks(s_n, s_p))
        # …but p rebuts notp unblocked.
        self.assertTrue(graph.attacks(s_p, s_n))

    def test_undercut_via_blocked_use(self):
        sat = self._sat(
            [_leaf("eq", "q"), _leaf("eb", blocked_use_atom("j"))],
            [_rule("j", ["q"], "p")],
        )
        policy = _contrary_policy(set())
        graph = compile_summary_defeats(sat, policy)
        blocker = next(s for s in sat.summaries if s.head.conc == blocked_use_atom("j"))
        target = next(s for s in sat.summaries if s.head.root_rule == "j")
        kinds = {k for (s, t, k) in graph.typed_edges if s == blocker and t == target}
        self.assertIn(AttackKind.UNDERCUT, kinds)

    def test_gate_attacks_by_guard_kind(self):
        guard_exc = GuardSlot("jx", "exception", "grace")
        guard_auth = GuardSlot("ja", "authority", "seal")
        guard_scope = GuardSlot("js", "scope", "territory")
        guard_proc = GuardSlot("jp", "procedure", "service")
        leaves = [
            _leaf("e1", "q"),
            _leaf("x1", guard_exc.atom()),
            _leaf("x2", guard_auth.atom()),
            _leaf("x3", guard_scope.atom()),
            _leaf("x4", guard_proc.atom()),
        ]
        rules = [
            _rule("jx", ["q"], "p", guards=(guard_exc,)),
            _rule("ja", ["q"], "r", guards=(guard_auth,)),
            _rule("js", ["q"], "s", guards=(guard_scope,)),
            _rule("jp", ["q"], "t", guards=(guard_proc,)),
        ]
        sat = self._sat(leaves, rules)
        graph = compile_summary_defeats(sat, AttackPolicy(contraries=frozenset()))
        expected = {
            "p": AttackKind.EXCEPTION,
            "r": AttackKind.AUTHORITY,
            "s": AttackKind.SCOPE,
            "t": AttackKind.PROCEDURE,
        }
        for head_atom, kind in expected.items():
            target = next(
                s for s in sat.summaries if s.head.root_rule and s.head.conc == head_atom
            )
            guard = target.head  # locate attacker by GateBlocked conclusion
            guard_atom = next(
                iter(
                    g.atom()
                    for site in target.sites
                    for g in site.guard_slots
                )
            )
            attacker = next(
                s for s in sat.summaries if s.head.conc == guard_atom
            )
            kinds = {k for (s, t, k) in graph.typed_edges if s == attacker and t == target}
            self.assertIn(kind, kinds, f"missing {kind} on {head_atom}")
            del guard

    def test_factorization_defeat_iff_summary_defeat(self):
        """Defeat(a,b) ↔ D(q(a),q(b)) on an enumerated finite tree set."""

        grammar = ArgumentGrammar(
            leaves=(_leaf("e1", "q1"), _leaf("e2", "q2"), _leaf("e3", "notp")),
            rules=(
                _rule("j1", ["q1"], "p"),
                _rule("j2", ["q2", "p"], "p"),
            ),
        )
        policy = _contrary_policy({("p", "notp")}, priority={("j1", "j2")})
        sat = saturate_summaries(grammar)
        graph = compile_summary_defeats(sat, policy)
        # Enumerate all trees up to depth 2 via the summaries' witnesses
        # and direct nesting; identity differs, summaries repeat.
        trees = list(sat.witnesses)
        for _ in range(2):
            for rule in grammar.rules:
                pools = [
                    [t for t in trees if t.head == p] for p in rule.premises
                ]
                if all(pools):
                    for combo in product(*pools):
                        try:
                            trees.append(node_argument(rule, tuple(combo)))
                        except ValueError:
                            pass
        trees = list({t.subtree_id(): t for t in trees}.values())
        for a in trees:
            for b in trees:
                kinds_tree = tree_defeats(a, b, policy)
                sa, sb = summarize(a), summarize(b)
                kinds_summary = {
                    k for (s, t, k) in graph.typed_edges if s == sa and t == sb
                }
                self.assertEqual(kinds_tree, kinds_summary)

    def test_no_preference_in_gate_attacks(self):
        guard = GuardSlot("jx", "exception", "grace")
        sat = self._sat(
            [_leaf("eq", "q"), _leaf("ex", guard.atom())],
            [_rule("jx", ["q"], "p", guards=(guard,))],
        )
        # Give the TARGET strictly stronger last instances; the gate
        # attack must still fire (gate kinds read no preference).
        policy = AttackPolicy(
            contraries=frozenset(),
            priority=frozenset({("jx", "whatever")}),
        )
        graph = compile_summary_defeats(sat, policy)
        target = next(s for s in sat.summaries if s.head.root_rule == "jx")
        attacker = next(s for s in sat.summaries if s.head.conc == guard.atom())
        self.assertTrue(graph.attacks(attacker, target))


class ExtensionTests(TestCase):
    def _graph_from_edges(self, atoms_and_edges):
        """Build a summary graph directly from named nodes and typed
        rebut edges (the summary content is irrelevant to the extension
        algebra being tested)."""

        from unified.argument_grammar import HeadSummary, Summary

        def _summary(name):
            return Summary(
                head=HeadSummary(
                    conc=name, mode=ArgMode.DEFEASIBLE, root_rule=name,
                    last=frozenset({name}), leaf_sources=frozenset(),
                    tags=frozenset(),
                ),
                sites=frozenset(),
            )

        nodes = tuple(_summary(n) for n in atoms_and_edges[0])
        edges = frozenset(
            (_summary(a), _summary(b), AttackKind.REBUT)
            for a, b in atoms_and_edges[1]
        )
        return SummaryGraph(nodes=nodes, typed_edges=edges)

    def test_self_attack_stable_empty_others_empty_extension(self):
        graph = self._graph_from_edges((["a"], [("a", "a")]))
        stable = enumerate_extensions(graph, ExtensionProfile.STABLE)
        self.assertEqual(stable, ())
        grounded = grounded_extension(graph)
        self.assertEqual(grounded, frozenset())
        complete = enumerate_extensions(graph, ExtensionProfile.COMPLETE)
        self.assertEqual(complete, (frozenset(),))
        preferred = enumerate_extensions(graph, ExtensionProfile.PREFERRED)
        self.assertEqual(preferred, (frozenset(),))

    def test_three_cycle_no_stable_empty_preferred(self):
        # a→b→c→a: no subset defends its members (∅ is the only admissible
        # set), so stable is empty AND preferred is exactly {∅} — two
        # distinct family shapes the typing must separate.
        graph = self._graph_from_edges(
            (["a", "b", "c"], [("a", "b"), ("b", "c"), ("c", "a")])
        )
        stable = enumerate_extensions(graph, ExtensionProfile.STABLE)
        self.assertEqual(stable, ())
        preferred = enumerate_extensions(graph, ExtensionProfile.PREFERRED)
        self.assertEqual(preferred, (frozenset(),))
        complete = enumerate_extensions(graph, ExtensionProfile.COMPLETE)
        self.assertEqual(complete, (frozenset(),))

    def test_grounded_recursive_defense(self):
        # c→b, b→a: grounded = {c, a} (a is defended by c).
        graph = self._graph_from_edges(
            (["a", "b", "c"], [("c", "b"), ("b", "a")])
        )
        grounded = grounded_extension(graph)
        names = {s.head.conc for s in grounded}
        self.assertEqual(names, {"a", "c"})

    def test_isolated_node_in_every_extension(self):
        graph = self._graph_from_edges((["a", "i"], []))
        complete = enumerate_extensions(graph, ExtensionProfile.COMPLETE)
        stable = enumerate_extensions(graph, ExtensionProfile.STABLE)
        self.assertEqual(len(complete), 1)
        self.assertEqual(len(stable), 1)
        self.assertEqual({s.head.conc for s in stable[0]}, {"a", "i"})

    def test_extension_budget_guard(self):
        names = [f"n{i}" for i in range(17)]
        graph = self._graph_from_edges((names, []))
        with pytest.raises(ValueError, match="exhaustive extension budget"):
            enumerate_extensions(graph, ExtensionProfile.COMPLETE)
        # grounded iterates without powerset enumeration: still fine.
        self.assertEqual(len(grounded_extension(graph)), 17)

    def test_mutual_rebut_two_stable(self):
        graph = self._graph_from_edges((["a", "b"], [("a", "b"), ("b", "a")]))
        stable = enumerate_extensions(graph, ExtensionProfile.STABLE)
        self.assertEqual(
            frozenset(frozenset(s) for s in stable),
            frozenset({frozenset(n for n in graph.nodes if n.head.conc == "a"),
                       frozenset(n for n in graph.nodes if n.head.conc == "b")}),
        )
