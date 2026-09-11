"""Integrated reference: findings -> rules -> arguments -> extensions -> amounts,
scenario probability -> success event -> constrained settlement strategy.
Not the production JC Application; integration is a separately tracked task.
"""
from fractions import Fraction as Q
from .arguments import Rule,Leaf,generate,valid_argument
from .contract import Subject,search,check_finite,Envelope,relation_join
from reference.unified_reference import powerset,dung_member
from reference.core import PMF,scenario_event_bounds,settlement_bounds


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
