"""CPT-to-source binding and material-sensitive conditional outcome forecasting."""
from dataclasses import dataclass
from fractions import Fraction as Q
from reference.core import BayesNet, Node, Observation, rational, PMF
from .context import ContextKey, require_same_context


@dataclass(frozen=True)
class ParameterCell:
    model_version: str
    node: str
    parent_values: tuple[str,...]
    state: str
    value: Q
    source_id: str
    source_snapshot: str
    basis: str
    def __post_init__(self):
        object.__setattr__(self,'parent_values',tuple(self.parent_values))
        object.__setattr__(self,'value',rational(self.value))
        if not 0<=self.value<=1 or not self.source_id or not self.source_snapshot:
            raise ValueError('Source-bound probability required')
        if self.basis not in {'observed_count','learned','expert_assumption','synthetic'}:
            raise ValueError('Unspecified parameter origin')


@dataclass(frozen=True)
class BoundModel:
    context: ContextKey
    nodes: tuple[Node,...]
    parameters: tuple[ParameterCell,...]
    hypothesis_author: str
    alternatives: tuple[str,...]
    dependence_basis: str
    unmodelled_risk: str

    def __post_init__(self):
        if type(self.context) is not ContextKey:raise TypeError('Closed context type required')
        if any(type(n) is not Node for n in self.nodes):raise TypeError('Closed node type required')
        # Snapshot nested sequence containers, not only the outer dataclass.
        object.__setattr__(self,'nodes',tuple(Node(n.name,tuple(n.states),tuple(n.parents),n.cpt) for n in self.nodes))
        if any(type(c) is not ParameterCell for c in self.parameters):raise TypeError('Closed parameter cell required')
        object.__setattr__(self,'parameters',tuple(self.parameters))
        object.__setattr__(self,'alternatives',tuple(self.alternatives))
        if not self.hypothesis_author or not self.alternatives or not self.dependence_basis or not self.unmodelled_risk:
            raise ValueError('Modeling choices and residual uncertainty required')
        BayesNet(self.context.model_version,self.nodes)  # structural/CPT validation
        expected={}
        for node in self.nodes:
            for parents,row in node.cpt.items():
                for state,value in zip(node.states,row): expected[node.name,parents,state]=value
        actual={}
        for cell in self.parameters:
            key=cell.node,cell.parent_values,cell.state
            if key in actual or cell.model_version!=self.context.model_version:
                raise ValueError('Duplicate or foreign-model parameter binding')
            actual[key]=cell.value
        if actual!=expected:
            raise ValueError('Declared sources do not bind the ACTUALLY consumed CPT values')

    def network(self):
        return BayesNet(self.context.model_version,self.nodes)


@dataclass(frozen=True)
class BoundObservation:
    context: ContextKey
    observation_id: str
    source_family: str
    source_snapshot: str
    variable: str
    value: str


def validate_observations(model, observations):
    """Copies of the same event do not become independent evidence nodes.

    Multi-feature extraction from one source requires an explicitly modeled
    joint/latent-source representation; this conservative reference rejects it.
    It does not discover real-world dependence automatically.
    """
    families={}; ids={}; result=[]
    for o in observations:
        require_same_context(model.context,o.context)
        if not o.observation_id or not o.source_family or not o.source_snapshot:
            raise ValueError('Evidence provenance required')
        content=(o.variable,o.value,o.source_family,o.source_snapshot)
        if o.observation_id in ids and ids[o.observation_id]!=content: raise ValueError('Conflicting observation identity')
        if o.source_family in families and families[o.source_family]!=(o.variable,o.value,o.source_snapshot):
            raise ValueError('Same source modeled as multiple independent observations')
        ids[o.observation_id]=content;families[o.source_family]=(o.variable,o.value,o.source_snapshot)
        result.append(Observation(o.observation_id,o.variable,o.value))
    return tuple(result)


def outcome_forecast(model: BoundModel, target_node: str, observations):
    obs=validate_observations(model,observations)
    net=model.network()
    answer=net.eliminate_query(target_node,obs)
    oracle=net.enumerate_query(target_node,obs)
    if answer.distribution.mass!=oracle.distribution.mass or answer.evidence_mass!=oracle.evidence_mass:
        raise ValueError('Bayesian algorithm mismatch')
    return {'kind':'MODEL_CONDITIONAL_FORECAST', 'target':model.context.target,
            'model':model.context.model_version, 'probabilities':dict(answer.distribution.mass),
            'evidence_mass':answer.evidence_mass,'empirical_status':'NOT_EXTERNALLY_VALIDATED',
            'fact_promotions':0}


def bind_synthetic_model(context,nodes):
    cells=tuple(ParameterCell(context.model_version,n.name,k,state,value,
                'synthetic-fixture','synthetic-v1','synthetic')
                for n in nodes for k,row in n.cpt.items() for state,value in zip(n.states,row))
    return BoundModel(context,tuple(nodes),cells,'fixture_author',('H','not-H'),
                      'explicit finite DAG; illustrative only','not exhaustive real-world alternatives')
