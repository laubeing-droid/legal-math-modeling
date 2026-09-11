from fractions import Fraction as Q
from .context import synthetic_context
from .model_binding import bind_synthetic_model, BoundObservation, outcome_forecast
from .bridge import SettlementInput, solve_settlement, check_settlement
from .law_slices import SLICES,evaluate_slice
from reference.core import Node


def main_demo():
    c=synthetic_context(target='claimant_award_ge_80_given_model')
    # Recognized is an explicit future recognition scenario variable, not an
    # assertion that evidence truth and judicial recognition are identical.
    nodes=(Node('Recognized',('yes','no'),(),{(): (Q(1,2),Q(1,2))}),
           Node('BankRecord',('yes','no'),('Recognized',),
                {('yes',):(Q(4,5),Q(1,5)),('no',):(Q(1,5),Q(4,5))}))
    model=bind_synthetic_model(c,nodes)
    observed=(BoundObservation(c,'obs1','bank-record-family','snapshot1','BankRecord','yes'),)
    posterior=outcome_forecast(model,'Recognized',observed)
    p=posterior['probabilities']['yes']
    data=SettlementInput(c,Q(100),Q(40),p,p,Q(5),Q(4),Q(1,2),Q(1,2),
                         tuple(Q(x) for x in (60,64,66,68,70,72,75)),'stipulated-test-lawful-grid',Q(80))
    result=solve_settlement(data)
    if not check_settlement(c,data,result):raise AssertionError('Concrete bridge failed')
    return {'probability':posterior,'bridge':result,'status':'SYNTHETIC_CONDITIONAL_REFERENCE',
            'jc_integration':'NOT_PERFORMED','lean':'NOT_EXECUTED_BY_PYTHON'}


def law_slice_demos():
    return [evaluate_slice(synthetic_context(issue=s.identity),s.identity,
                           {k:'true' for k in s.required}) for s in SLICES]
