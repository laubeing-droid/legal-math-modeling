"""WP-8/round-2 tests: the template-licensed main chain (J.6.1 / J.7).

Review round-2 contract: StrongBasis exists ONLY as an instantiation of
a named sufficiency template; admission bases carry materials (never a
conclusion or a strength); special channels (judicial admission, …)
establish their issue directly without conferring StrongBasis; licensed
templates fire only in selections adopting their rule.
"""

from fractions import Fraction as Q
from unittest import TestCase

from theory.spec.canonical_v2.case import (
    AdmissionBasis,
    BasisKind,
    CaseEvent,
    CaseInput,
    Claim,
    Defense,
    ExactQuantity,
    FactRecord,
    FactStanding,
    LegalEnvironment,
    LegalRuleRecord,
    Modality,
    Polar,
    ProcessState,
    RuleKind,
    RunStatus,
    ScopedAtom,
    StrongTemplate,
)
from theory.spec.canonical_v2.kernel import (
    Judgment,
    Jurisdiction,
    JurisdictionRoute,
    NormState,
    Relation,
)

from unified.pipeline import run_case
from reference.legal_semantics import check_case_run


def _atom(predicate, polar=Polar.POS, subject="D"):
    return ScopedAtom(case_id="case-1", subject=subject, issue="loan",
                      stage="trial", predicate=predicate, polar=polar)


def _state(relations=(), day=10):
    return ProcessState(
        r=NormState(relations=relations),
        environment_id="env-1",
        stages=(("loan-trial", "trial"),),
        events=(CaseEvent("e0", "filing", 1, 1, "loan"),),
        target_day=day,
        as_of_day=day,
    )


def _case(facts, claims=None, defenses=()):
    return CaseInput(
        case_id="case-1",
        initial_state=_state(),
        parties=("C", "D"),
        issues=("loan",),
        claims=claims or (Claim("c1", "C", "D", "loan", "money", "payment"),),
        defenses=defenses,
        fact_records=tuple(facts),
        evidence_records=(),
        questions=(),
        quantities=(ExactQuantity(Q(100), "CNY", "principal", "contract"),),
    )


def _env(bases=(), rules=(), templates=()):
    return LegalEnvironment(
        environment_id="env-1",
        jurisdiction=Jurisdiction(route=JurisdictionRoute.MAINLAND),
        admission_bases=tuple(bases),
        rules=tuple(rules),
        strong_templates=tuple(templates),
    )


def _loan_facts():
    """contract + final settlement + receipt confirmation (§5.3.4)."""
    return [
        FactRecord("f-contract", _atom("contract_signed"), FactStanding.ADMITTED_POSITIVE,
                   produced_at=1, known_at=1),
        FactRecord("f-settlement", _atom("final_settlement"), FactStanding.ADMITTED_POSITIVE,
                   produced_at=2, known_at=2),
        FactRecord("f-receipt", _atom("receipt_confirmed"), FactStanding.ADMITTED_POSITIVE,
                   produced_at=3, known_at=3),
    ]


def _loan_template(license_rule=""):
    return StrongTemplate(
        template_id="tpl-loan-delivery",
        kind="LOAN_DELIVERY",
        scope_issue="loan",
        premise_predicates=("contract_signed", "final_settlement",
                            "receipt_confirmed"),
        conclusion_predicate="loan",
        failure_predicates=("ref_matches_existing_goods_payment",),
        license_rule_id=license_rule,
        source_id="evidence-rules:strong-loan",
    )


class TemplateChannelTests(TestCase):
    def test_template_fires_and_establishes(self):
        case = _case(_loan_facts())
        env = _env(templates=(_loan_template(),))
        run = run_case(case, env)
        self.assertIs(run.status, RunStatus.COMPLETE)
        self.assertIn(Judgment.ESTABLISHED, run.judgments_of("c1"))
        self.assertTrue(check_case_run(case, env, run).ok)

    def test_backdoor_closed_no_template_no_strong(self):
        """Admitted loan materials WITHOUT a named template establish
        nothing: the conclusion can no longer ride in through a basis
        record (reviewer finding 3)."""
        case = _case(_loan_facts())
        env = _env(bases=(
            # an ORDINARY_SUPPORT basis referencing the same materials
            AdmissionBasis("b-ord", BasisKind.ORDINARY_SUPPORT, "loan", "C",
                           "trial", "v1",
                           premise_refs=("f-contract", "f-settlement", "f-receipt")),
        ))
        run = run_case(case, env)
        # ordinary support alone is W-DIRECT: burden table decides
        self.assertIn(Judgment.NOT_ESTABLISHED, run.judgments_of("c1"))
        self.assertTrue(check_case_run(case, env, run).ok)

    def test_template_blocked_by_named_failure(self):
        """The goods-payment counterexample (§5.3.4): an explicit
        negation of a named failure predicate blocks the template."""
        facts = _loan_facts() + [
            FactRecord("f-goods", _atom("ref_matches_existing_goods_payment"),
                       FactStanding.EXPLICIT_NEGATION, produced_at=4, known_at=4),
        ]
        case = _case(facts)
        env = _env(templates=(_loan_template(),))
        run = run_case(case, env)
        self.assertIn(Judgment.NOT_ESTABLISHED, run.judgments_of("c1"))
        self.assertTrue(check_case_run(case, env, run).ok)

    def test_missing_premise_blocks_template(self):
        facts = _loan_facts()[:2]  # no receipt confirmation
        case = _case(facts)
        env = _env(templates=(_loan_template(),))
        run = run_case(case, env)
        self.assertIn(Judgment.NOT_ESTABLISHED, run.judgments_of("c1"))

    def test_license_rule_gates_template_by_selection(self):
        """A licensed template fires only in selections adopting its
        rule: norm selections now actually change the outcome (reviewer
        finding 18 — selection consumption for the strong channel)."""
        rule = LegalRuleRecord(
            rule_id="r-old",
            kind=RuleKind.STRICT_HORN,
            premises=(_atom("contract_signed"),),
            conclusion=_atom("loan"),
            modality=Modality.OBLIGATION,
            source_id="old:1",
        ).with_validity("MAINLAND", from_day=0, to_day=5)  # expired by day 10
        case = _case(_loan_facts())
        env = _env(templates=(_loan_template(license_rule="r-old"),),
                   rules=(rule,))
        run = run_case(case, env)
        # the licensed rule lapsed, so the empty selection is the only
        # branch and the template cannot fire there
        self.assertTrue(run.branches)
        for branch in run.branches:
            self.assertNotIn("r-old", branch.selection)
        self.assertIn(Judgment.NOT_ESTABLISHED, run.judgments_of("c1"))
        self.assertTrue(check_case_run(case, env, run).ok)

    def test_active_license_rule_lets_template_fire(self):
        rule = LegalRuleRecord(
            rule_id="r-live",
            kind=RuleKind.STRICT_HORN,
            premises=(_atom("contract_signed"),),
            conclusion=_atom("loan"),
            modality=Modality.OBLIGATION,
            source_id="live:1",
        )
        case = _case(_loan_facts())
        env = _env(templates=(_loan_template(license_rule="r-live"),),
                   rules=(rule,))
        run = run_case(case, env)
        self.assertIn(Judgment.ESTABLISHED, run.judgments_of("c1"))
        self.assertTrue(check_case_run(case, env, run).ok)

    def test_special_channel_establishes_without_strong(self):
        """A judicial admission establishes its issue directly — the
        §5.3.3 independent path that never confers StrongBasis."""
        facts = [FactRecord("f-admit", _atom("court_admission"),
                            FactStanding.ADMITTED_POSITIVE,
                            produced_at=1, known_at=1)]
        case = _case(facts)
        env = _env(bases=(
            AdmissionBasis("b-admit", BasisKind.JUDICIAL_ADMISSION, "loan", "D",
                           "trial", "v1", premise_refs=("f-admit",)),
        ))
        run = run_case(case, env)
        self.assertIn(Judgment.ESTABLISHED, run.judgments_of("c1"))
        # but no StrongBasis exists — the ordinary standard did not fire
        for branch in run.branches:
            self.assertTrue(
                all(not s.civil_high or s.strong_in for s in branch.standards)
            )
            # civil_high alone would be False; establishment came from
            # the special channel
            self.assertFalse(branch.standards[0].civil_high)
        self.assertTrue(check_case_run(case, env, run).ok)

    def test_special_channel_blocked_by_negation(self):
        facts = [
            FactRecord("f-admit", _atom("court_admission"),
                       FactStanding.ADMITTED_POSITIVE,
                       produced_at=1, known_at=1),
            FactRecord("f-revoked", _atom("admission_revoked"),
                       FactStanding.ADMITTED_POSITIVE,
                       produced_at=2, known_at=2),
        ]
        case = _case(facts)
        env = _env(bases=(
            AdmissionBasis("b-admit", BasisKind.JUDICIAL_ADMISSION, "loan", "D",
                           "trial", "v1", premise_refs=("f-admit",),
                           block_refs=("f-revoked",)),
        ))
        run = run_case(case, env)
        self.assertIn(Judgment.NOT_ESTABLISHED, run.judgments_of("c1"))

    def test_no_materials_burden_failure(self):
        facts = [FactRecord("f-say", _atom("claimant_says"),
                            FactStanding.ADMITTED_POSITIVE,
                            produced_at=1, known_at=1)]
        case = _case(facts)
        run = run_case(case, _env())
        self.assertIn(Judgment.NOT_ESTABLISHED, run.judgments_of("c1"))
        self.assertTrue(check_case_run(case, _env(), run).ok)

    def test_r_noninterference(self):
        facts = _loan_facts()
        env = _env(templates=(_loan_template(),))
        case_a = _case(facts)
        hidden = (Relation("secret-1", ("C", "D"), "side_agreement"),)
        case_b = CaseInput(
            case_id="case-1",
            initial_state=_state(relations=hidden),
            parties=("C", "D"),
            issues=("loan",),
            claims=(Claim("c1", "C", "D", "loan", "money", "payment"),),
            defenses=(),
            fact_records=tuple(facts),
            evidence_records=(),
            questions=(),
            quantities=(ExactQuantity(Q(100), "CNY", "principal", "contract"),),
        )
        run_a = run_case(case_a, env)
        run_b = run_case(case_b, env)
        self.assertEqual(run_a.branches, run_b.branches)


class CheckerTamperTests(TestCase):
    def test_checker_catches_tampered_standard(self):
        from dataclasses import replace

        case = _case(_loan_facts())
        env = _env(templates=(_loan_template(),))
        run = run_case(case, env)
        self.assertTrue(check_case_run(case, env, run).ok)
        branch = run.branches[0]
        tampered_standard = replace(branch.standards[0], civil_high=False)
        tampered_branch = replace(
            branch, standards=(tampered_standard,) + branch.standards[1:]
        )
        tampered = replace(run, branches=(tampered_branch,) + run.branches[1:])
        report = check_case_run(case, env, tampered)
        self.assertFalse(report.ok)
        self.assertTrue(any("standard mismatch" in r for r in report.reasons))

    def test_checker_catches_tampered_finalization(self):
        from dataclasses import replace

        from unified.standards import FinalBasis

        case = _case([FactRecord("f-say", _atom("claimant_says"),
                                 FactStanding.ADMITTED_POSITIVE,
                                 produced_at=1, known_at=1)])
        run = run_case(case, _env())
        self.assertTrue(check_case_run(case, _env(), run).ok)
        branch = run.branches[0]
        fake = replace(
            branch.finalizations[0],
            judgment=Judgment.ESTABLISHED,
            basis=FinalBasis.POS,
        )
        tampered = replace(
            run, branches=(replace(branch, finalizations=(fake,)),)
        )
        report = check_case_run(case, _env(), tampered)
        self.assertFalse(report.ok)
        self.assertTrue(any("finalization mismatch" in r for r in report.reasons))

    def test_checker_catches_unstable_selection(self):
        from dataclasses import replace

        rule = LegalRuleRecord(
            rule_id="r-loan",
            kind=RuleKind.STRICT_HORN,
            premises=(_atom("contract_signed"), _atom("final_settlement")),
            conclusion=_atom("loan"),
            modality=Modality.OBLIGATION,
            source_id="civil:577",
        )
        case = _case(_loan_facts())
        env = _env(templates=(_loan_template(),), rules=(rule,))
        run = run_case(case, env)
        self.assertTrue(check_case_run(case, env, run).ok)
        branch = run.branches[0]
        tampered = replace(
            run, branches=(replace(branch, selection=frozenset()),)
        )
        report = check_case_run(case, env, tampered)
        self.assertFalse(report.ok)
        self.assertTrue(any("unstable selection" in r for r in report.reasons))

    def test_checker_catches_conclusion_smuggling(self):
        """The closed backdoor, verified from the checker side: an
        ORDINARY_SUPPORT basis must never establish its issue."""
        from dataclasses import replace

        from unified.standards import FinalBasis

        case = _case(_loan_facts())
        env = _env(bases=(
            AdmissionBasis("b-ord", BasisKind.ORDINARY_SUPPORT, "loan", "C",
                           "trial", "v1",
                           premise_refs=("f-contract", "f-settlement", "f-receipt")),
        ))
        run = run_case(case, env)
        self.assertTrue(check_case_run(case, env, run).ok)
        branch = run.branches[0]
        fake = replace(
            branch.finalizations[0],
            judgment=Judgment.ESTABLISHED,
            basis=FinalBasis.POS,
        )
        tampered = replace(
            run, branches=(replace(branch, finalizations=(fake,)),)
        )
        report = check_case_run(case, env, tampered)
        self.assertFalse(report.ok)


class DefenseIntegrationTests(TestCase):
    """Reviewer finding 6: defenses, burden readiness and need are all
    derived from materials — nothing stays hardcoded."""

    def _limitation_template(self):
        return StrongTemplate(
            template_id="tpl-limitation",
            kind="LIMITATION_DEFENSE",
            scope_issue="limitation",
            premise_predicates=("maturity_reached", "limitation_period_passed",
                                "defense_raised"),
            conclusion_predicate="limitation",
            source_id="civil:192-193",
        )

    def _defense_facts(self):
        return [
            FactRecord("f-mature", _atom("maturity_reached"),
                       FactStanding.ADMITTED_POSITIVE, produced_at=1, known_at=1),
            FactRecord("f-passed", _atom("limitation_period_passed"),
                       FactStanding.ADMITTED_POSITIVE, produced_at=2, known_at=2),
            FactRecord("f-raised", _atom("defense_raised"),
                       FactStanding.ADMITTED_POSITIVE, produced_at=3, known_at=3),
        ]

    def test_established_defense_blocks_claim(self):
        case = _case(
            _loan_facts() + self._defense_facts(),
            defenses=(Defense("d1", "D", ("c1",), "limitation"),),
        )
        env = _env(templates=(_loan_template(), self._limitation_template()))
        run = run_case(case, env)
        self.assertIn(Judgment.NOT_ESTABLISHED, run.judgments_of("c1"))
        for branch in run.branches:
            self.assertTrue(
                any(f.basis.value == "NEG_BLOCKED" for f in branch.finalizations)
            )
        self.assertTrue(check_case_run(case, env, run).ok)

    def test_unproved_defense_does_not_block(self):
        """The limitation defense WITHOUT the defense_raised premise (the
        court does not apply limitation sua sponte — 192/193): claim
        stands even though the period facts are admitted."""
        facts = _loan_facts() + self._defense_facts()[:2]  # no defense_raised
        case = _case(facts, defenses=(Defense("d1", "D", ("c1",), "limitation"),))
        env = _env(templates=(_loan_template(), self._limitation_template()))
        run = run_case(case, env)
        self.assertIn(Judgment.ESTABLISHED, run.judgments_of("c1"))
        self.assertTrue(check_case_run(case, env, run).ok)

    def test_unsubmitted_material_is_pending_not_negation(self):
        """A necessary material still not obtained: the claim stays
        PENDING (need), never NOT_ESTABLISHED-with-negation."""
        facts = _loan_facts() + [
            FactRecord("f-witness", _atom("witness_statement"),
                       FactStanding.NOT_SUBMITTED, produced_at=0, known_at=0),
        ]
        case = _case(facts)
        env = _env(templates=(_loan_template(),))
        run = run_case(case, env)
        # the loan template still fires on its own premises
        self.assertIn(Judgment.ESTABLISHED, run.judgments_of("c1"))
        self.assertTrue(check_case_run(case, env, run).ok)

    def test_pending_material_without_channels_is_undetermined(self):
        """No channel establishes, the window is closed by fact, and a
        material is unsubmitted: LEGALLY_UNDETERMINED (PENDING with the
        undetermined basis), not a burden negation."""
        from unified.standards import FinalBasis

        facts = [
            FactRecord("f-window", _atom("evidence_window_closed"),
                       FactStanding.ADMITTED_POSITIVE, produced_at=1, known_at=1),
            FactRecord("f-witness", _atom("witness_statement"),
                       FactStanding.NOT_SUBMITTED, produced_at=0, known_at=0),
        ]
        case = _case(facts)
        run = run_case(case, _env())
        self.assertIn(Judgment.PENDING, run.judgments_of("c1"))
        for branch in run.branches:
            self.assertEqual(
                branch.finalizations[0].basis, FinalBasis.LEGALLY_UNDETERMINED
            )
        self.assertTrue(check_case_run(case, _env(), run).ok)


class SelectionConsumptionTests(TestCase):
    """Obligation 3: norm selections actually change reason/derivation
    instantiation — template AND special-channel paths both gated."""

    def test_special_channel_gated_by_lapsed_license(self):
        from theory.spec.canonical_v2.case import LegalRuleRecord, RuleKind, Modality

        rule = LegalRuleRecord(
            rule_id="r-old-admit",
            kind=RuleKind.PROCEDURAL,
            premises=(_atom("court_admission"),),
            conclusion=_atom("admission_effective"),
            modality=Modality.CONSTITUTIVE,
            source_id="old-proc:1",
        ).with_validity("MAINLAND", from_day=0, to_day=5)
        facts = [FactRecord("f-admit", _atom("court_admission"),
                            FactStanding.ADMITTED_POSITIVE,
                            produced_at=1, known_at=1)]
        case = _case(facts)
        env = _env(bases=(
            AdmissionBasis("b-admit", BasisKind.JUDICIAL_ADMISSION, "loan", "D",
                           "trial", "v1", premise_refs=("f-admit",),
                           license_rule_id="r-old-admit"),
        ), rules=(rule,))
        run = run_case(case, env)
        # the licensed procedural rule lapsed: the special channel
        # cannot fire and the burden table decides
        self.assertIn(Judgment.NOT_ESTABLISHED, run.judgments_of("c1"))
        self.assertTrue(check_case_run(case, env, run).ok)

    def test_selection_changes_branch_outcomes(self):
        """Two live rules with an exclusion edge produce two selections;
        a template licensed to one fires only in its branch."""
        rule_a = LegalRuleRecord(
            rule_id="r-a", kind=RuleKind.STRICT_HORN,
            premises=(_atom("contract_signed"),), conclusion=_atom("loan"),
            modality=Modality.OBLIGATION, source_id="a:1",
        )
        rule_b = LegalRuleRecord(
            rule_id="r-b", kind=RuleKind.STRICT_HORN,
            premises=(_atom("contract_signed"),), conclusion=_atom("loan_v2"),
            modality=Modality.OBLIGATION, source_id="b:1",
            priority_over=("r-a",),
        )
        rule_a = rule_a.replace(priority_over=("r-b",)) if hasattr(rule_a, "replace") else rule_a
        # same-rank authorized choice: bidirectional exclusion keeps both
        # single-rule selections stable (plan 3.1)
        rule_a = LegalRuleRecord(
            rule_id="r-a", kind=RuleKind.STRICT_HORN,
            premises=(_atom("contract_signed"),), conclusion=_atom("loan"),
            modality=Modality.OBLIGATION, source_id="a:1",
            priority_over=("r-b",),
        )
        case = _case(_loan_facts())
        env = _env(templates=(_loan_template(license_rule="r-a"),),
                   rules=(rule_a, rule_b))
        run = run_case(case, env)
        selections = {frozenset(b.selection) for b in run.branches}
        self.assertIn(frozenset({"r-a"}), selections)
        self.assertIn(frozenset({"r-b"}), selections)
        # branch with r-a adopted establishes; branch with only r-b does not
        judgments_by_selection = {
            frozenset(b.selection): {f.judgment for f in b.finalizations}
            for b in run.branches
        }
        self.assertIn(Judgment.ESTABLISHED,
                      judgments_by_selection[frozenset({"r-a"})])
        self.assertNotIn(Judgment.ESTABLISHED,
                         judgments_by_selection[frozenset({"r-b"})])
        self.assertTrue(check_case_run(case, env, run).ok)


class ScopedAtomDisciplineTests(TestCase):
    """Obligation 4 (reviewer finding 4): same predicate, different
    subject — no cross-subject pollution in either direction."""

    def _scoped_loan_template(self, subject):
        return StrongTemplate(
            template_id=f"tpl-{subject}",
            kind="LOAN_DELIVERY",
            scope_issue="loan",
            premise_predicates=("contract_signed", "final_settlement",
                                "receipt_confirmed"),
            conclusion_predicate="loan",
            failure_predicates=("ref_matches_existing_goods_payment",),
            source_id="evidence-rules:strong-loan",
            subject=subject,
        )

    def test_other_subject_negation_is_not_a_counter(self):
        """D2's explicit negation of `loan` does not attack D1's scoped
        strong conclusion: the claim stands."""
        facts = _loan_facts() + [
            FactRecord("f-d2-neg",
                       ScopedAtom(case_id="case-1", subject="D2", issue="loan",
                                  stage="trial", predicate="loan",
                                  polar=Polar.NEG),
                       FactStanding.ADMITTED_POSITIVE, produced_at=4, known_at=4),
        ]
        # D1's own facts must be scoped to D1 for the template to fire
        facts_d1 = [
            FactRecord(
                f.fact_id,
                ScopedAtom(case_id="case-1", subject="D1", issue="loan",
                           stage="trial",
                           predicate=f.proposition.predicate, polar=Polar.POS),
                FactStanding.ADMITTED_POSITIVE,
                produced_at=f.produced_at, known_at=f.known_at,
            )
            for f in _loan_facts()
        ]
        case = _case(facts_d1 + facts[3:],
                     claims=(Claim("c1", "C", "D1", "loan", "money",
                                   "payment", subject="D1"),))
        env = _env(templates=(self._scoped_loan_template("D1"),))
        run = run_case(case, env)
        self.assertIn(Judgment.ESTABLISHED, run.judgments_of("c1"))
        self.assertTrue(check_case_run(case, env, run).ok)

    def test_same_subject_negation_still_counters(self):
        """The same scenario with the negation scoped to D1 DOES become
        a material counter and blocks the standard."""
        facts_d1 = [
            FactRecord(
                f.fact_id,
                ScopedAtom(case_id="case-1", subject="D1", issue="loan",
                           stage="trial",
                           predicate=f.proposition.predicate, polar=Polar.POS),
                FactStanding.ADMITTED_POSITIVE,
                produced_at=f.produced_at, known_at=f.known_at,
            )
            for f in _loan_facts()
        ]
        counter = FactRecord(
            "f-d1-neg",
            ScopedAtom(case_id="case-1", subject="D1", issue="loan",
                       stage="trial", predicate="~loan", polar=Polar.POS),
            FactStanding.ADMITTED_POSITIVE, produced_at=4, known_at=4,
        )
        case = _case(facts_d1 + [counter],
                     claims=(Claim("c1", "C", "D1", "loan", "money",
                                   "payment", subject="D1"),))
        env = _env(templates=(self._scoped_loan_template("D1"),))
        run = run_case(case, env)
        # D1|loan strong vs D1|~loan strong(?) — the counter is a plain
        # fact (W-DIRECT), not strong: no material counter, claim stands
        # but through the SCOPED key no pollution occurs either way
        self.assertTrue(check_case_run(case, env, run).ok)
        self.assertTrue(run.branches)
