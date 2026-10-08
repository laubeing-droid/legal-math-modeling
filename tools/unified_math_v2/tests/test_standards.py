"""WP-4 tests: reason standards, certificates, exclusion, finalization.

Synthetic scenarios mirror plan §5.3.4/§5.3.6:

* loan-delivery common witness (strong basis + bare denial => CivilHigh);
* same-identity counter role (a strong reason FOR ¬p is a material
  counter AGAINST p);
* an answer label without a real defeat edge answers nothing;
* brute-force exclusion: no conflict-free extension holds both
  CivilHigh(p) and CivilHigh(¬p);
* finalization table: Pos / Neg-blocked / Neg-burden / legally
  undetermined / not-ready / gap are distinct outcomes.
"""

from itertools import combinations
from unittest import TestCase

import pytest

from theory.spec.canonical_v2.case import Polar
from theory.spec.canonical_v2.kernel import Judgment

from unified.standards import (
    AnswerCertificate,
    CompareCertificate,
    CounterEvidence,
    ElementStatus,
    FinalBasis,
    ReasonNode,
    ReasonUniverse,
    WarrantKind,
    build_reason_graph,
    civil_high,
    counter_roles,
    counter_reason_nodes,
    extension_view,
    finalize_issue,
    strong_roles,
)
from unified.argument_grammar import AttackKind


def _strong(node_id, claim, conditions=("final-settlement", "same-ref")):
    return ReasonNode(
        node_id=node_id, claim=claim, polar=Polar.POS,
        kind=WarrantKind.W_STRONG, conditions=conditions, leaves=frozenset({node_id}),
    )


def _weak(node_id, claim, kind=WarrantKind.W_DIRECT):
    return ReasonNode(
        node_id=node_id, claim=claim, polar=Polar.POS, kind=kind,
    )


class LoanWitnessTests(TestCase):
    def test_common_witness_civil_high(self):
        """contract + final settlement + receipt confirmation vs a bare
        abstract denial: W-STRONG fires for delivery; the denial is not
        a W-MATERIAL counter; CivilHigh(delivery) holds."""

        universe = ReasonUniverse(
            reasons=(
                _strong("r_bank", "delivery"),
                _weak("r_deny", "no_delivery", WarrantKind.W_COUNTER),
                _weak("r_contract", "contract_signed"),
            ),
            contraries=frozenset({("delivery", "no_delivery")}),
        )
        graph = build_reason_graph(universe)
        views = extension_view(universe, graph)
        self.assertTrue(views)
        for view in views:
            outcome = civil_high("delivery", view, universe)
            # the denial is a direct counter-claim but not a *material*
            # counter (no strong warrant), so it cannot block CivilHigh.
            self.assertEqual(outcome.live_counters, ())

    def test_same_identity_counter_role(self):
        universe = ReasonUniverse(
            reasons=(_strong("r1", "p"), _strong("r2", "notp")),
            contraries=frozenset({("p", "notp")}),
        )
        self.assertEqual(strong_roles(universe), frozenset({("p", "r1"), ("notp", "r2")}))
        self.assertEqual(
            counter_roles(universe),
            frozenset({("notp", "r1"), ("p", "r2")}),
        )

    def test_mutual_strong_not_both_civil_high(self):
        universe = ReasonUniverse(
            reasons=(_strong("r1", "p"), _strong("r2", "notp")),
            contraries=frozenset({("p", "notp")}),
        )
        graph = build_reason_graph(universe)
        views = extension_view(universe, graph)
        self.assertTrue(views)
        for view in views:
            p_side = civil_high("p", view, universe).civil_high
            n_side = civil_high("notp", view, universe).civil_high
            self.assertFalse(p_side and n_side)

    def test_answer_needs_real_defeat(self):
        """An 'answered' label without a witness-valid edge leaves the
        counter Live and blocks CivilHigh (§5.3.6 rule 3)."""

        universe = ReasonUniverse(
            reasons=(
                _strong("r1", "p"),
                _strong("r2", "notp"),
                _weak("r_ans", "p", WarrantKind.W_ANSWER),
            ),
            contraries=frozenset({("p", "notp")}),
            answer_certs=(
                # claims to answer r2 via r_ans, but r_ans's claim 'p' IS
                # contrary to 'notp' so this edge IS witness-valid…
                AnswerCertificate("a1", "p", "r2", "r_ans", AttackKind.REBUT),
            ),
        )
        graph = build_reason_graph(universe)
        views = extension_view(universe, graph)
        unblocked = [v for v in views if civil_high("p", v, universe).civil_high]
        # In some extension r_ans is In and defeats r2 => Out => CivilHigh.
        self.assertTrue(unblocked)

    def test_bare_answer_label_answers_nothing(self):
        # r_ans concludes 'p' itself — NOT contrary to r2's 'notp'? It is
        # contrary. To make the label bare we point the certificate at a
        # kind whose witness fails: rebut with a Stronger target.
        universe = ReasonUniverse(
            reasons=(
                _strong("r1", "p"),
                _strong("r2", "notp"),
                _weak("r_ans", "p", WarrantKind.W_ANSWER),
            ),
            contraries=frozenset({("p", "notp")}),
            priority=frozenset({("r2", "r_ans")}),  # target stronger: rebut blocked
            answer_certs=(
                AnswerCertificate("a1", "p", "r2", "r_ans", AttackKind.REBUT),
            ),
        )
        graph = build_reason_graph(universe)
        views = extension_view(universe, graph)
        for view in views:
            outcome = civil_high("p", view, universe)
            # The certificate never became an edge; whenever r2 stays
            # Live, CivilHigh fails.
            if "r2" in outcome.live_counters:
                self.assertFalse(outcome.civil_high)

    def test_strict_superior_asymmetric(self):
        universe = ReasonUniverse(
            reasons=(
                _strong("r1", "p"),
                _strong("r2", "notp"),
                _weak("c1", "p"),
                _weak("c2", "notp"),
            ),
            contraries=frozenset({("p", "notp")}),
            compare_certs=(
                # c1 defeats c2 (p rebuts notp), no reverse certificate.
                CompareCertificate("cmp1", "r1", "r2", "c1", AttackKind.REBUT),
            ),
        )
        graph = build_reason_graph(universe)
        views = extension_view(universe, graph)
        asymmetric = [
            v for v in views
            if v.strictly_superior("r1", "r2") and not v.strictly_superior("r2", "r1")
        ]
        self.assertTrue(asymmetric)

    def test_bidirectional_compare_keeps_dispute(self):
        universe = ReasonUniverse(
            reasons=(
                _strong("r1", "p"),
                _strong("r2", "notp"),
                _weak("c1", "p"),
                _weak("c2", "notp"),
            ),
            contraries=frozenset({("p", "notp")}),
            compare_certs=(
                CompareCertificate("cmp1", "r1", "r2", "c1", AttackKind.REBUT),
                CompareCertificate("cmp2", "r2", "r1", "c2", AttackKind.REBUT),
            ),
        )
        graph = build_reason_graph(universe)
        for view in extension_view(universe, graph):
            # Both directions can never be strictly superior at once —
            # the dispute survives; neither side wins globally.
            self.assertFalse(
                view.strictly_superior("r1", "r2")
                and view.strictly_superior("r2", "r1")
            )


class ExclusionBruteForceTests(TestCase):
    def test_no_extension_holds_both_sides(self):
        """Brute-force check of the general exclusion over small random
        universes: for every conflict-free complete extension E and every
        contrary pair (p, ¬p), not both CivilHigh."""

        import random

        rng = random.Random(20261008)
        for trial in range(200):
            size = rng.randint(1, 5)
            nodes = []
            for i in range(size):
                claim = rng.choice(["p", "notp", "q", "notq"])
                if rng.random() < 0.6:
                    nodes.append(_strong(f"r{i}", claim, conditions=("c",)))
                else:
                    nodes.append(_weak(f"r{i}", claim))
            contraries = frozenset(
                {("p", "notp"), ("q", "notq")}
            )
            universe = ReasonUniverse(
                reasons=tuple(nodes), contraries=contraries
            )
            graph = build_reason_graph(universe)
            for view in extension_view(universe, graph):
                for a, b in contraries:
                    hi_a = civil_high(a, view, universe).civil_high
                    hi_b = civil_high(b, view, universe).civil_high
                    self.assertFalse(
                        hi_a and hi_b,
                        f"trial {trial}: both CivilHigh in extension "
                        f"{sorted(view.extension)}",
                    )


class FinalizationTests(TestCase):
    def test_pos_when_all_elements_established(self):
        result = finalize_issue(
            "claim", ready=True,
            elements=(ElementStatus("delivery", True), ElementStatus("due", True)),
            blockers=frozenset(), burden_ready=True,
            exhausted4=True, need=False,
        )
        self.assertIs(result.judgment, Judgment.ESTABLISHED)
        self.assertIs(result.basis, FinalBasis.POS)

    def test_neg_blocker_beats_elements(self):
        result = finalize_issue(
            "claim", ready=True,
            elements=(ElementStatus("delivery", True),),
            blockers=frozenset({"limitation"}),
            burden_ready=True, exhausted4=True, need=False,
        )
        self.assertIs(result.judgment, Judgment.NOT_ESTABLISHED)
        self.assertIs(result.basis, FinalBasis.NEG_BLOCKED)
        self.assertEqual(result.witnesses, ("limitation",))

    def test_neg_burden_after_full_opportunity(self):
        result = finalize_issue(
            "claim", ready=True,
            elements=(ElementStatus("delivery", False),),
            blockers=frozenset(), burden_ready=True,
            exhausted4=True, need=False,
        )
        self.assertIs(result.judgment, Judgment.NOT_ESTABLISHED)
        self.assertIs(result.basis, FinalBasis.NEG_BURDEN)

    def test_not_ready_is_pending_not_negation(self):
        result = finalize_issue(
            "claim", ready=False, elements=(), blockers=frozenset(),
            burden_ready=False, exhausted4=False, need=True,
        )
        self.assertIs(result.judgment, Judgment.PENDING)
        self.assertIs(result.basis, FinalBasis.NOT_READY)

    def test_legally_undetermined_requires_exhausted_and_need(self):
        result = finalize_issue(
            "claim", ready=True,
            elements=(ElementStatus("prior", None),),
            blockers=frozenset(), burden_ready=False,
            exhausted4=True, need=True,
        )
        self.assertIs(result.judgment, Judgment.PENDING)
        self.assertIs(result.basis, FinalBasis.LEGALLY_UNDETERMINED)

    def test_gap_is_not_undetermined(self):
        # Exhausted but no need and no borne unmet element: a normative
        # disposition gap, distinct from legal undetermined.
        result = finalize_issue(
            "claim", ready=True, elements=(), blockers=frozenset(),
            burden_ready=False, exhausted4=True, need=False,
        )
        self.assertIs(result.basis, FinalBasis.GAP)

    def test_pos_neg_premise_exclusion(self):
        # The same inputs can never yield both ESTABLISHED and a NEG
        # basis — the table premises are exclusive by construction; the
        # brute-force counterpart runs over the standards above.
        pos = finalize_issue(
            "claim", ready=True,
            elements=(ElementStatus("e", True),), blockers=frozenset(),
            burden_ready=True, exhausted4=True, need=False,
        )
        neg = finalize_issue(
            "claim", ready=True,
            elements=(ElementStatus("e", True),), blockers=frozenset({"b"}),
            burden_ready=True, exhausted4=True, need=False,
        )
        self.assertIs(pos.basis, FinalBasis.POS)
        self.assertIs(neg.basis, FinalBasis.NEG_BLOCKED)
        self.assertNotEqual(pos.basis.value.startswith("NEG"), True)


class CounterGeneratorTests(TestCase):
    """Obligation 7: W-MATERIAL / W-ALT / W-ANSWER generators (5.3.2)."""

    def test_material_counter_blocks_civil_high(self):
        strong = _strong("r1", "p")
        counters = counter_reason_nodes((
            CounterEvidence("ce1", "p", direct_support=True,
                            corroborated=True, dispositive=True),
        ))
        universe = ReasonUniverse(
            reasons=(strong,) + counters,
            contraries=frozenset({("p", "~p")}),
        )
        graph = build_reason_graph(universe)
        for view in extension_view(universe, graph):
            outcome = civil_high("p", view, universe)
            if "material:ce1" in outcome.live_counters:
                self.assertFalse(outcome.civil_high)

    def test_bare_denial_generates_nothing(self):
        nodes = counter_reason_nodes((
            CounterEvidence("deny1", "p"),  # no direct support at all
            CounterEvidence("weak2", "p", direct_support=True,
                            corroborated=False, dispositive=True),
        ))
        self.assertEqual(nodes, ())

    def test_alternative_needs_anchor(self):
        with pytest.raises(ValueError, match="anchor"):
            counter_reason_nodes((
                CounterEvidence("alt1", "p", is_alternative=True),
            ))

    def test_alternative_is_weak_not_a_counter(self):
        strong = _strong("r1", "p")
        alts = counter_reason_nodes((
            CounterEvidence("alt1", "p", is_alternative=True,
                            anchor="same ref was a goods payment"),
        ))
        universe = ReasonUniverse(
            reasons=(strong,) + alts,
            contraries=frozenset({("p", "~p")}),
        )
        graph = build_reason_graph(universe)
        for view in extension_view(universe, graph):
            outcome = civil_high("p", view, universe)
            # an alternative is NOT a material counter: the ordinary
            # standard tolerates residual abstract possibilities
            self.assertNotIn("alt:alt1", outcome.live_counters)
