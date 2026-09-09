"""Issue-scoped burden engine shared by all registered procedural profiles.

The engine consumes explicit assessments; it does not determine their legal
correctness. A profile is not a full implementation of its entire field of law.
"""
from dataclasses import dataclass
from .contract import Subject

STATES = frozenset({'established','not_established','undetermined'})

@dataclass(frozen=True)
class BurdenPolicy:
    identity: str
    field: str
    issue_kind: str
    bearer: str
    standard: str
    source_ids: tuple[str,...]
    ready_stages: frozenset[str]
    success: str
    failure: str
    allowed_reviewers: frozenset[str]

@dataclass(frozen=True)
class Assessment:
    subject: Subject
    issue: str
    policy_id: str
    standard: str
    state: str
    completed: bool
    review_role: str
    reviewer_id: str
    basis_refs: tuple[str,...]
    origin: str = 'legal_assessment'

    def __post_init__(self):
        if self.state not in STATES:
            raise ValueError('Invalid fact assessment')

@dataclass(frozen=True)
class IssueDecision:
    issue: str
    status: str
    consequence: str | None
    bearer: str
    meaning: str


def resolve(subject: Subject, issue: str, stage: str, policy: BurdenPolicy,
            assessment: Assessment | None, *, analyst_mode: bool = True):
    if not policy.source_ids:
        raise ValueError('No legal source basis')
    pending=lambda: IssueDecision(issue,'pending',None,policy.bearer,'no_final_finding')
    if assessment is None:
        return pending()
    if (assessment.subject != subject or assessment.issue!=issue
        or assessment.policy_id!=policy.identity or assessment.standard!=policy.standard):
        raise ValueError('Assessment subject/issue/policy mismatch')
    if (not assessment.completed or stage not in policy.ready_stages
        or not assessment.reviewer_id or not assessment.basis_refs
        or assessment.review_role not in policy.allowed_reviewers
        or assessment.origin!='legal_assessment'):
        return pending()
    # A lawyer's analysis does not impersonate a court's institutional act.
    if not analyst_mode:
        # V2.1: this legacy function has no trusted institution resolver.
        # Institutional projection is only supported by v21.authority.
        return pending()
    consequence=policy.success if assessment.state=='established' else policy.failure
    return IssueDecision(issue,'resolved',consequence,policy.bearer,
                         'conditional_legal_analysis' if analyst_mode else 'recorded_institutional_finding')


def transition(stage: str, event: str):
    table={('initial','file'): 'filed',('filed','serve'): 'served',
           ('served','hear'): 'heard',('heard','close'): 'ready_for_decision',
           ('ready_for_decision','decide'): 'decided',('decided','appeal'): 'appeal_pending'}
    if (stage,event) not in table:
        raise ValueError('Not a permitted procedural transition')
    return table[stage,event]

@dataclass(frozen=True)
class ScenarioAssessment:
    assumption_id: str
    hypothetical_finding: str
    def __post_init__(self):
        if not self.assumption_id or self.hypothetical_finding not in STATES:
            raise ValueError('Explicit hypothetical finding required')


def resolve_scenario(subject: Subject, issue: str, policy: BurdenPolicy,
                     assumption: ScenarioAssessment):
    """The same declared consequence map under an EXPLICIT assumption.

    This does not fabricate an Assessment/authority receipt. It cannot promote
    a fact or be consumed as an unconditional legal finding.
    """
    if not policy.source_ids:
        raise ValueError('Scenario still requires a named legal policy')
    effect=policy.success if assumption.hypothetical_finding=='established' else policy.failure
    return {'subject':subject,'issue':issue,'consequence':effect,
            'assumptions':(assumption.assumption_id,),
            'finding':assumption.hypothetical_finding,'meaning':'hypothetical_legal_consequence',
            'formal_admission':False}
