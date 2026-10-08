"""Integrated reference: findings -> rules -> arguments -> extensions -> amounts,
scenario probability -> success event -> constrained settlement strategy.
Not the production JC Application; integration is a separately tracked task.

The v3 public entry points (run_case / step_event / run_trace) compose the
unified-construction modules per plan J.6.1: knowledge view -> norm
selection branches -> reason standards per extension -> finalization ->
quantities.  They never accept precomputed verdicts.
"""
from dataclasses import replace as _replace
from fractions import Fraction as Q
from typing import Mapping, Optional, Tuple

from theory.spec.canonical_v2.case import (
    AdmissionBasis,
    BasisKind,
    CaseInput,
    ExecutionLimits,
    FactStanding,
    LegalEnvironment,
    Polar,
    RunStatus,
    knowledge_view,
)
from .arguments import Rule,Leaf,generate,valid_argument
from .contract import Subject,search,check_finite,Envelope,relation_join
from reference.unified_reference import powerset,dung_member
from reference.core import PMF,scenario_event_bounds,settlement_bounds

from .norm_selection import (
    NormCandidate,
    SelectionStatus,
    enumerate_stable_selections,
)
from .standards import (
    ReasonNode,
    ReasonUniverse,
    WarrantKind,
    build_reason_graph,
    civil_high,
    extension_view,
    finalize_issue,
    ElementStatus,
)
from .process import ProcessEvent as _ProcessEvent, run_trace as _run_trace, step_event as _step_event  # noqa: F401  (re-export)


# ---------------------------------------------------------------------------
# v3 main chain (J.6.1)
# ---------------------------------------------------------------------------


def _claim_key(predicate: str, polar: Polar) -> str:
    return predicate if polar is Polar.POS else "~" + predicate


def enumerate_norm_selections(
    case: CaseInput, env: LegalEnvironment, limits: Optional[ExecutionLimits] = None
):
    """Stable selections over the validity-passing candidates; exclusion
    edges come from ``priority_over`` declarations (plan 3.1)."""

    day = case.initial_state.as_of_day
    stages = {s for _p, s in case.initial_state.stages}
    stage = next(iter(stages)) if len(stages) == 1 else ""
    candidates = frozenset(
        rule.rule_id
        for rule in env.rules
        if rule.applicable_at(env.jurisdiction.route.value, day, stage)
    )
    cand_objs = tuple(
        NormCandidate(rule.rule_id, env.jurisdiction.route.value)
        for rule in env.rules
        if rule.rule_id in candidates
    )
    # Edges naming non-candidates (e.g. superseded norms kept for
    # priority records) lapse with them instead of crashing the run.
    exclusions = frozenset(
        (rule.rule_id, other)
        for rule in env.rules
        if rule.rule_id in candidates
        for other in rule.priority_over
        if other in candidates
    )
    return enumerate_stable_selections(cand_objs, exclusions)


def build_reason_universe(
    case: CaseInput, env: LegalEnvironment, selection: frozenset
) -> ReasonUniverse:
    """Reason nodes from the case's own materials under one norm
    selection (reviewer findings 2/3/18 fixed):

    * admitted positive facts are W-DIRECT reasons — nothing more;
    * an admission basis NEVER carries a conclusion or a strength: it
      only references materials, and creates no reason node at all
      (special channels are consumed in finalization instead);
    * StrongBasis exists ONLY as an instantiation of a NAMED
      sufficiency template from the environment: the template declares
      which premise predicates license strong support for which
      conclusion, plus its named failure predicates; a licensed rule
      binds the template to the norm selection, so selections now
      actually change the reason universe."""

    facts = case.fact_records
    reasons = [
        ReasonNode(
            node_id=f"fact:{f.fact_id}",
            claim=_claim_key(f.proposition.predicate, f.proposition.polar),
            polar=f.proposition.polar,
            kind=WarrantKind.W_DIRECT,
            leaves=frozenset({f.fact_id}),
        )
        for f in facts
        if f.standing is FactStanding.ADMITTED_POSITIVE
    ]
    admitted_predicates = {
        f.proposition.predicate for f in facts
        if f.standing is FactStanding.ADMITTED_POSITIVE
    }
    negated_predicates = {
        f.proposition.predicate for f in facts
        if f.standing is FactStanding.EXPLICIT_NEGATION
    }
    admitted_ids = {
        f.fact_id for f in facts
        if f.standing is FactStanding.ADMITTED_POSITIVE
    }
    for template in env.strong_templates:
        # selection consumption: a licensed template fires only when its
        # rule is among the adopted candidates
        if template.license_rule_id and template.license_rule_id not in selection:
            continue
        # every premise predicate must be admitted positively
        if not all(p in admitted_predicates for p in template.premise_predicates):
            continue
        # a named failure predicate explicitly negated blocks the template
        if any(p in negated_predicates for p in template.failure_predicates):
            continue
        matched = tuple(
            f.fact_id for f in facts
            if f.standing is FactStanding.ADMITTED_POSITIVE
            and f.proposition.predicate in template.premise_predicates
        )
        reasons.append(
            ReasonNode(
                node_id=f"template:{template.template_id}",
                claim=_claim_key(template.conclusion_predicate, Polar.POS),
                polar=Polar.POS,
                kind=WarrantKind.W_STRONG,
                leaves=frozenset(matched),
                warrant_id=template.template_id,
                conditions=matched + (template.template_id,),
            )
        )
    del admitted_ids
    # Contrary closure over ALL reason claims (facts AND template
    # conclusions): a strong reason for x is a material counter against
    # ~x whenever both claim keys occur in the universe.
    claim_keys = {r.claim for r in reasons}
    contraries = frozenset(
        (c, "~" + c[1:] if c.startswith("~") else "~" + c)
        for c in claim_keys
        if ("~" + c[1:] if c.startswith("~") else "~" + c) in claim_keys
    )
    return ReasonUniverse(reasons=tuple(reasons), contraries=contraries)


SPECIAL_ESTABLISHMENT_KINDS = frozenset({
    BasisKind.JUDICIAL_ADMISSION,
    BasisKind.FORENSIC_EXEMPT,
    BasisKind.FINAL_BINDING,
    BasisKind.EVIDENCE_OBSTRUCTION,
})


def active_special_establishments(
    case: CaseInput, env: LegalEnvironment, selection: frozenset
) -> frozenset:
    """Issues established by SPECIAL channels (§5.3.3: 自认、免证等走
    独立特别路径): an admission basis of a special kind whose premises
    are all admitted and whose blocks are unmet establishes its issue
    directly — it never passes through the ordinary-support standard
    and never confers StrongBasis."""

    facts = case.fact_records
    admitted_ids = {
        f.fact_id for f in facts
        if f.standing is FactStanding.ADMITTED_POSITIVE
    }
    established: set = set()
    for basis in env.admission_bases:
        if basis.kind not in SPECIAL_ESTABLISHMENT_KINDS:
            continue
        if basis.license_rule_id and basis.license_rule_id not in selection:
            continue
        if not basis.premise_refs or not all(
            r in admitted_ids for r in basis.premise_refs
        ):
            continue
        # a block reference names an ADMITTED revocation/defeat EVENT
        # (11.1: 依法裁定撤销则撤去该依据) — a positive fact, not a
        # negation of the premise
        if any(b in admitted_ids for b in basis.block_refs):
            continue
        established.add(basis.issue_id)
    return frozenset(established)


def run_case(
    case: CaseInput,
    env: LegalEnvironment,
    *,
    limits: Optional[ExecutionLimits] = None,
) -> "CaseRun":
    """The composed main chain for the declared fragment: every branch
    keeps its own selection/extension/standards/finalization witnesses;
    no averaging, no hidden default choice."""

    from theory.spec.canonical_v2.kernel import Judgment

    try:
        selection_result = enumerate_norm_selections(case, env, limits)
        branches = []
        pending_notes = []
        if selection_result.status is SelectionStatus.ESCALATE:
            pending_notes.append(
                "norm conflict requires referral: "
                + ", ".join(sorted("/".join(sorted(p)) for p in selection_result.refer_pairs))
            )
        if selection_result.status is SelectionStatus.NORM_CONFLICT:
            pending_notes.append("norm conflict: no stable selection")
        if selection_result.status is SelectionStatus.EMPTY_CANDIDATES:
            # No applicable candidates at all: the empty selection is the
            # unique branch — a diagnosis, not an impossibility.
            selections = (frozenset(),)
        else:
            selections = selection_result.selections
        for selection in selections:
            universe = build_reason_universe(case, env, selection)
            special = active_special_establishments(case, env, selection)
            graph = build_reason_graph(universe)
            for view in extension_view(universe, graph):
                standards = tuple(
                    civil_high(_claim_key(claim.basis, Polar.POS), view, universe)
                    for claim in case.claims
                )
                # defense evaluation (reviewer finding 6): each defense
                # blocks when its own basis issue is established by the
                # SAME channels — a strong template conclusion or an
                # active special establishment
                defense_blockers = frozenset(
                    defense.defense_id
                    for defense in case.defenses
                    if civil_high(
                        _claim_key(defense.basis, Polar.POS), view, universe
                    ).civil_high
                    or defense.basis in special
                )
                # burden readiness from procedure state, not a constant:
                # the window closes at a decision-ready stage or by an
                # admitted evidence_window_closed fact
                stages = {s for _p, s in case.initial_state.stages}
                window_closed_fact = any(
                    f.proposition.predicate == "evidence_window_closed"
                    and f.standing is FactStanding.ADMITTED_POSITIVE
                    for f in case.fact_records
                )
                burden_ready = bool(stages) and stages <= {
                    "ready_for_decision", "decided", "trial"
                } or window_closed_fact
                # Need: a necessary material still not obtained
                need = any(
                    f.standing in (
                        FactStanding.NOT_SUBMITTED,
                        FactStanding.AWAITING_ADMISSION,
                    )
                    for f in case.fact_records
                )
                # Exhausted4: every declared basis has been evaluated
                # (its issue resolved one way or the other through the
                # channels above); it is INDEPENDENT of need — an
                # unsubmitted material does not un-exhaust the rules,
                # it defers the burden instead (5.4: 阶段未到不启动终局负担)
                exhausted4 = True
                # the burden opportunity is not complete while a
                # necessary material is still outstanding
                burden_ready_effective = burden_ready and not need
                finalizations = []
                for claim, outcome in zip(case.claims, standards):
                    elements = (
                        # E(q): ordinary standard OR an active special
                        # channel (self-admission, exemption, final
                        # binding, obstruction) — separate paths that
                        # never confer StrongBasis.
                        ElementStatus(
                            claim.basis,
                            outcome.civil_high or claim.basis in special,
                        ),
                    )
                    finalizations.append(
                        finalize_issue(
                            claim.claim_id,
                            ready=True,  # ready-ness per branch: the
                            # fragment reached the evaluating stage
                            elements=elements,
                            blockers=defense_blockers,
                            burden_ready=burden_ready_effective,
                            exhausted4=exhausted4,
                            need=need,
                        )
                    )
                branches.append(
                    CaseRunBranch(
                        selection=selection,
                        extension=view.extension,
                        standards=standards,
                        finalizations=tuple(finalizations),
                    )
                )
        status = RunStatus.COMPLETE if branches else RunStatus.PAUSED
        return CaseRun(
            case_id=case.case_id,
            status=status,
            branches=tuple(branches),
            pending=tuple(pending_notes),
            failures=(),
        )
    except Exception as exc:  # technical failure is FAILED, never a verdict
        return CaseRun(
            case_id=case.case_id,
            status=RunStatus.FAILED,
            branches=(),
            pending=(),
            failures=(f"{type(exc).__name__}: {exc}",),
        )


def step_event(state, event, env=None, limits=None):
    """Public re-export of the §9 step relation (J.3 entry points)."""

    return _step_event(state, event, env, limits)


def run_trace(initial, events, env=None):
    """Public re-export of the §9 finite-trace fold (J.3 entry points)."""

    return _run_trace(initial, events, env)


from dataclasses import dataclass  # noqa: E402  (kept near its users)


@dataclass(frozen=True)
class CaseRunBranch:
    selection: frozenset
    extension: frozenset
    standards: tuple
    finalizations: tuple


@dataclass(frozen=True)
class CaseRun:
    case_id: str
    status: RunStatus
    branches: Tuple[CaseRunBranch, ...]
    pending: Tuple[str, ...]
    failures: Tuple[str, ...]

    def judgments_of(self, claim_id: str):
        return tuple(
            f.judgment for b in self.branches for f in b.finalizations
            if f.claim == claim_id
        )



def scenario_outcomes(subject, scenario, *, base: Q, paid: Q, profile='grounded',budget=None):
    if base<0 or paid<0:
        raise ValueError('Nonnegative monetary inputs required')
    # These are labelled scenario assumptions, NEVER official admitted facts.
    leaves=(Leaf('relationship','relationship',True),Leaf('due','due',True))
    if scenario=='payment_established':
        leaves += (Leaf('payment','payment',True),)
    elif scenario!='payment_not_established':
        raise ValueError('Unsupported declared scenario')
    rules=(Rule('claim_rule',('relationship','due'),'payment_claim'),)
    args=generate(repr((subject.request,subject.scenario)),leaves,rules,2)
    assert all(valid_argument(a,repr((subject.request,subject.scenario)),leaves,rules,2) for a in args)
    ordered=sorted(args,key=lambda a:repr(a.identity))
    names=tuple(str(i) for i in range(len(ordered)))
    # No conflict is manufactured for a partial-payment defence: it changes
    # amount rather than erasing the existence of the entire payment claim.
    edges=frozenset()
    universe=powerset(names)
    predicate=lambda s:dung_member(profile,names,edges,s)
    cert=search(subject,'normative_extensions',universe,predicate,budget)
    # Legacy pedagogical double invocation, NOT an independent-checker claim.
    # The V2.1 acceptance runner uses v21.checker instead.
    if not check_finite(subject,'normative_extensions',universe,predicate,cert):
        raise AssertionError('Reference certificate rejected')
    outcomes=[]
    for ext in cert.classification.found:
        if any(ordered[int(i)].head=='payment_claim' for i in ext):
            # Signed residual is retained; excess payment is separately visible.
            residual=base-(paid if scenario=='payment_established' else Q(0))
            outcomes.append(residual)
    return cert,tuple(outcomes)


def combined_demo(base=Q(100000),paid=Q(40000),prob_paid=Q(3,5)):
    scenarios=('payment_established','payment_not_established')
    outputs={}
    for scenario in scenarios:
        subject=Subject('demo','CN_fixed_sources','payment_reference',scenario,'depth<=2','elicited_example')
        cert,amounts=scenario_outcomes(subject,scenario,base=base,paid=paid)
        outputs[scenario]=frozenset(amounts)
    weights=PMF({scenarios[0]:prob_paid,scenarios[1]:1-prob_paid})
    # Success event defined before analysis: award at least 80,000, first instance.
    low,high=scenario_event_bounds(weights,outputs,lambda amount:amount>=Q(80000))
    expect=sum((weights.mass[s]*next(iter(outputs[s])) for s in scenarios),Q(0))
    interval=settlement_bounds(expect,expect,Q(5000),Q(4000),Q(500),Q(500))["interval"]
    amount=interval.lo+(interval.hi-interval.lo)/2
    return {'status':'SYNTHETIC_CONDITIONAL_ANALYSIS',
            'success_event':'claimant_first_instance_award_at_least_80000',
            'conditional_win_probability_bounds':[str(low),str(high)],
            'expected_award':str(expect),'scenario_amounts':{s:[str(x) for x in outputs[s]] for s in scenarios},
            'settlement_interval':[str(interval.lo),str(interval.hi)],
            'strategy_amount':str(amount),'empirical_validation':'NOT_ESTABLISHED',
            'formal_fact_promotions':0,'jc_public_application_integration':'NOT_PERFORMED'}


def all_fields_demo():
    """One conditional burden/probability chain for EACH named issue template.

    These are symbolic policy consequences, not completed doctrinal rule packs.
    Criminal/state/public-law remedies are kept as symbolic consequences; no
    arbitrary conversion of them to money or civil claimant success occurs.
    """
    from pathlib import Path
    import json
    from .burdens import BurdenPolicy,ScenarioAssessment,resolve_scenario
    profiles=json.loads((Path(__file__).parents[1]/'fixtures/burden_profiles.json').read_text())
    rows=[]
    for d in profiles:
        subject=Subject('synthetic:'+d['id'],'source_versions_as_declared',d['id'],
                        'finding_scenarios','two_declared_findings','elicited_demo')
        p=BurdenPolicy(d['id'],d['field'],d['issue'],d['bearer'],d['standard'],tuple(d['sources']),
                       frozenset({'ready_for_decision'}),d['success'],d['failure'],frozenset({'lawyer'}))
        established=resolve_scenario(subject,d['issue'],p,ScenarioAssessment(d['id']+':yes','established'))
        unproved=resolve_scenario(subject,d['issue'],p,ScenarioAssessment(d['id']+':unknown','undetermined'))
        rows.append({'profile':d['id'],'field':d['field'],'issue':d['issue'],
          'alternatives':[established,unproved],
          'conditional_probability_of_declared_success':'2/3',
          'parameter_origin':'SYNTHETIC_ELICITED_TEST_ONLY','fact_promotions':0,
          'whole_field_semantics':'NOT_IMPLEMENTED_BY_THIS_TEMPLATE',
          'historical_win_accuracy':'NOT_MEASURED'})
    return rows
