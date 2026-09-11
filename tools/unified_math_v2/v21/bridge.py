"""A concrete shared-input probability -> amount -> IR -> lawful selection chain."""
from dataclasses import dataclass
from fractions import Fraction as Q
from reference.core import rational, probability
from .context import ContextKey, require_same_context


@dataclass(frozen=True)
class SettlementInput:
    context: ContextKey
    due: Q
    paid: Q
    probability_recognized: Q
    defendant_probability_recognized: Q
    claimant_litigation_cost: Q
    defendant_litigation_cost: Q
    claimant_settlement_cost: Q
    defendant_settlement_cost: Q
    lawful_candidates: tuple[Q,...]
    lawful_basis: str
    threshold: Q
    def __post_init__(self):
        for n in ('due','paid','claimant_litigation_cost','defendant_litigation_cost',
                  'claimant_settlement_cost','defendant_settlement_cost','threshold'):
            object.__setattr__(self,n,rational(getattr(self,n)))
        for n in ('probability_recognized','defendant_probability_recognized'):
            object.__setattr__(self,n,probability(getattr(self,n)))
        if min(self.due,self.paid,self.claimant_litigation_cost,self.defendant_litigation_cost,
               self.claimant_settlement_cost,self.defendant_settlement_cost)<0:
            raise ValueError('Negative cost or original amount')
        vals=tuple(rational(x) for x in self.lawful_candidates)
        if len(set(vals))!=len(vals) or not self.lawful_basis:raise ValueError('Lawful candidate basis required')
        object.__setattr__(self,'lawful_candidates',tuple(sorted(vals)))


def solve_settlement(inputs: SettlementInput):
    # Probability is for recognition in the declared scenario model, NOT a
    # raw historical fact probability or a threshold used to admit that fact.
    recognized=inputs.due-inputs.paid
    unrecognized=inputs.due
    p=inputs.probability_recognized; q=inputs.defendant_probability_recognized
    mp=p*recognized+(1-p)*unrecognized
    md=q*recognized+(1-q)*unrecognized
    lo=mp-inputs.claimant_litigation_cost+inputs.claimant_settlement_cost
    hi=md+inputs.defendant_litigation_cost-inputs.defendant_settlement_cost
    admissible=tuple(x for x in inputs.lawful_candidates if lo<=x<=hi)
    # Never invent a midpoint outside a non-convex lawful set.
    selected=admissible[0] if admissible else None  # same first-feasible selector as the Lean seed; not a recommendation
    win=p*int(recognized>=inputs.threshold)+(1-p)*int(unrecognized>=inputs.threshold)
    return {'context':inputs.context.canonical_json(),
            'branches':((True,recognized),(False,unrecognized)),
            'claimant_expectation':mp,'defendant_expectation':md,
            'win_probability':win,'ir_lower':lo,'ir_upper':hi,
            'feasible_set':admissible,'selected':selected,
            'status':'conditional_choice' if selected is not None else 'no_mutually_acceptable_lawful_candidate',
            'meaning':'finite_lawful_carrier_only','lawful_basis':inputs.lawful_basis,
            'empirical_status':'NOT_EXTERNALLY_VALIDATED','fact_promotions':0}


def check_settlement(expected_context, inputs, output):
    """Independent algebraic check, no call to solve_settlement."""
    require_same_context(expected_context,inputs.context)
    if type(output) is not dict:return False
    if any(type(output.get(k)) is not Q for k in
           ('claimant_expectation','defendant_expectation','win_probability','ir_lower','ir_upper')):
        return False
    if type(output.get('fact_promotions')) is not int:return False
    if output.get('selected') is not None and type(output.get('selected')) is not Q:return False
    if output.get('context')!=expected_context.canonical_json():return False
    p=inputs.probability_recognized;q=inputs.defendant_probability_recognized
    mp=inputs.due-p*inputs.paid;md=inputs.due-q*inputs.paid
    lo=mp-inputs.claimant_litigation_cost+inputs.claimant_settlement_cost
    hi=md+inputs.defendant_litigation_cost-inputs.defendant_settlement_cost
    feasible=tuple(x for x in inputs.lawful_candidates if lo<=x and x<=hi)
    event=(p if inputs.due-inputs.paid>=inputs.threshold else Q(0))+(1-p if inputs.due>=inputs.threshold else Q(0))
    if (output.get('branches')!=((True,inputs.due-inputs.paid),(False,inputs.due))
        or output.get('claimant_expectation')!=mp or output.get('defendant_expectation')!=md
        or output.get('win_probability')!=event or output.get('ir_lower')!=lo
        or output.get('ir_upper')!=hi or output.get('feasible_set')!=feasible
        or output.get('fact_promotions')!=0 or output.get('lawful_basis')!=inputs.lawful_basis
        or output.get('meaning')!='finite_lawful_carrier_only'
        or output.get('empirical_status')!='NOT_EXTERNALLY_VALIDATED'):
        return False
    selected=output.get('selected')
    if not feasible:
        return selected is None and output.get('status')=='no_mutually_acceptable_lawful_candidate'
    return selected==feasible[0] and selected in feasible and output.get('status')=='conditional_choice'
