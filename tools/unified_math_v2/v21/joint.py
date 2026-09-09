"""One concrete accepted reference pipeline, with a non-callback final checker.

Scope: source-stipulated debt entitlement graph + recognized-payment model +
finite lawful settlement carrier. Not the general C07 runtime refinement.
"""
from dataclasses import dataclass
from fractions import Fraction as Q
from .context import ContextKey,require_same_context
from .checker import DungProblem,solve,check_partition,checked_query
from .model_binding import BoundModel,validate_observations
from .bridge import SettlementInput,solve_settlement,check_settlement

@dataclass(frozen=True)
class JointInput:
    context: ContextKey
    normative: DungProblem
    entitlement_arguments: frozenset[str]
    model: BoundModel
    observations: tuple
    recognized_node: str
    recognized_state: str
    amounts_and_costs: tuple[Q,...]  # due,paid,cP,cD,sP,sD,threshold
    lawful_candidates: tuple[Q,...]
    lawful_basis: str
    def __post_init__(self):
        require_same_context(self.context,self.model.context)
        if self.normative.profile!=self.context.profile:raise ValueError('Profile binding mismatch')
        if len(self.amounts_and_costs)!=7:raise ValueError('Explicit monetary inputs required')
        if not self.entitlement_arguments or not self.entitlement_arguments<=set(self.normative.arguments):
            raise ValueError('Entitlement argument projection missing')


def _settlement_input(data,p):
    due,paid,cp,cd,sp,sd,threshold=data.amounts_and_costs
    return SettlementInput(data.context,due,paid,p,p,cp,cd,sp,sd,
                           data.lawful_candidates,data.lawful_basis,threshold)


def evaluate_joint(data: JointInput):
    cert=solve(data.context,data.normative)
    query=checked_query(data.context,data.normative,cert,data.entitlement_arguments)
    if query['common'] is not True:
        return {'status':'normative_unresolved','normative':cert,'fact_promotions':0}
    observations=validate_observations(data.model,data.observations)
    posterior=data.model.network().eliminate_query(data.recognized_node,observations)
    p=posterior.distribution.mass[data.recognized_state]
    return {'status':'conditional_joint_result','normative':cert,'recognition_probability':p,
            'settlement':solve_settlement(_settlement_input(data,p)),
            'fact_promotions':0,'assurance':'REFERENCE_CROSS_CHECK_ONLY',
            'empirical':'NOT_EXTERNALLY_VALIDATED'}


def check_joint(expected: JointInput, report):
    """Verifies every connective; no free lo/hi or unchecked probability port."""
    if type(report) is not dict:return False
    cert=report.get('normative')
    if not check_partition(expected.context,expected.normative,cert):return False
    query=checked_query(expected.context,expected.normative,cert,expected.entitlement_arguments)
    if query['common'] is not True:
        return (report.get('status')=='normative_unresolved'
                and report.get('fact_promotions')==0 and 'settlement' not in report)
    observations=validate_observations(expected.model,expected.observations)
    # Independent enumeration, not the variable-elimination solver.
    posterior=expected.model.network().enumerate_query(expected.recognized_node,observations)
    p=posterior.distribution.mass[expected.recognized_state]
    return (report.get('status')=='conditional_joint_result'
            and type(report.get('recognition_probability')) is Q
            and report.get('recognition_probability')==p
            and check_settlement(expected.context,_settlement_input(expected,p),report.get('settlement',{}))
            and report.get('fact_promotions')==0
            and report.get('assurance')=='REFERENCE_CROSS_CHECK_ONLY'
            and report.get('empirical')=='NOT_EXTERNALLY_VALIDATED')
