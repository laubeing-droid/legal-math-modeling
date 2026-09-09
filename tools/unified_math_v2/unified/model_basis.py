"""Minimal provenance contract for empirical hypotheses; no automatic legal admission."""
from dataclasses import dataclass
from .contract import Subject

@dataclass(frozen=True)
class ParameterBasis:
    name: str
    origin: str
    references: tuple[str,...]
    assumption_scope: str
    def __post_init__(self):
        if self.origin not in {'observed_frequency','elicited','learned','synthetic'}:
            raise ValueError('Unknown parameter origin')
        if not self.name or not self.references or not self.assumption_scope:
            raise ValueError('Parameter provenance/scope missing')

@dataclass(frozen=True)
class ModelBasis:
    subject: Subject
    hypothesis_space: tuple[str,...]
    defined_by: str
    alternatives_considered: tuple[str,...]
    residual_alternative: str
    dependence_review: str
    parameters: tuple[ParameterBasis,...]
    task: str
    def __post_init__(self):
        if not self.hypothesis_space or len(set(self.hypothesis_space))!=len(self.hypothesis_space):
            raise ValueError('Invalid hypothesis space')
        if not all((self.defined_by,self.residual_alternative,self.dependence_review,self.task)):
            raise ValueError('Missing modeling decision or limitation')
        if not self.parameters:
            raise ValueError('No prior/likelihood basis')
        if self.task not in {'evidence_analysis','observed_outcome_prediction','strategic_scenario'}:
            raise ValueError('Not a defined empirical task')


def require_compatible_evidence_models(model_masses):
    """Never silently discard a named model assigning zero evidence mass.

    A finite model-average update can assign such a model zero posterior weight
    under a fixed prior; a robust-all-models assertion cannot do so silently.
    The caller must decide which of these claims is requested.
    """
    if not model_masses or any(mass<0 for mass in model_masses.values()):
        raise ValueError('Invalid evidence masses')
    incompatible=tuple(k for k,v in model_masses.items() if v==0)
    return {'incompatible':incompatible,'robust_all_models_available':not incompatible}
