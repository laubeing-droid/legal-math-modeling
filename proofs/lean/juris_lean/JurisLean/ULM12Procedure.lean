import JurisLean.ULM11BranchQuery

/-! Burden/procedure adjudication and non-conversion of incomplete results. -/

namespace JurisLean.ULM

structure ProofStandard where
  standardId : String
  domain : String
  version : JurisLean.SchemaVersion
deriving DecidableEq, Repr

inductive LegalStatusKind where
  | claimSupported
  | claimNotSupported
  | procedureMoved
  | procedureDismissed
  | undecided
deriving DecidableEq, Repr

structure LegalStatus where
  kind : LegalStatusKind
  proposition : String
  request : RequestKey
deriving DecidableEq, Repr

def LegalStatus.isProcedural (s : LegalStatus) : Bool :=
  match s.kind with
  | .procedureMoved => true
  | .procedureDismissed => true
  | _ => false

structure BurdenRule where
  issue : JurisLean.LegalId .claim
  standard : ProofStandard
  successConsequence : LegalStatus
  failureConsequence : LegalStatus
deriving DecidableEq, Repr

inductive ProcedureStage where
  | initial
  | filed
  | served
  | heard
  | expired
  | institutionallyDecided
deriving DecidableEq, Repr

structure ProcedureState where
  request : RequestKey
  stage : ProcedureStage
  normativeMarker : String
deriving DecidableEq, Repr

inductive ProcedureCause where
  | filing
  | service
  | hearing
  | expiry
  | institutionalDecision
deriving DecidableEq, Repr

def ProcedureCause.targetStage : ProcedureCause → ProcedureStage
  | .filing => .filed
  | .service => .served
  | .hearing => .heard
  | .expiry => .expired
  | .institutionalDecision => .institutionallyDecided

/-- Procedure transitions change procedure stage but do not manufacture a new
normative marker. -/
def applyProcedureCause (cause : ProcedureCause)
    (s : ProcedureState) : ProcedureState :=
  { s with stage := cause.targetStage }

@[simp] theorem procedure_transition_preserves_normative_marker
    (cause : ProcedureCause) (s : ProcedureState) :
    (applyProcedureCause cause s).normativeMarker = s.normativeMarker := rfl

inductive ProofFinding where
  | satisfied
  | unmet
deriving DecidableEq, Repr

structure AdjudicationAuthority where
  rule : BurdenRule
  finding : ProofFinding
  reviewer : String
deriving DecidableEq, Repr

/-- Authority is valid only for the exact request being adjudicated. Burden
success/failure consequences are entity/non-procedural outputs; procedure-only
outcomes use the separate typed channel below. -/
structure AdjudicationAuthority.ValidFor
    (a : AdjudicationAuthority) (request : RequestKey) : Prop where
  issueMatches : a.rule.issue = request.query
  successRequest : a.rule.successConsequence.request = request
  failureRequest : a.rule.failureConsequence.request = request
  reviewerNonempty : a.reviewer ≠ ""
  successNonprocedural : a.rule.successConsequence.isProcedural = false
  failureNonprocedural : a.rule.failureConsequence.isProcedural = false

abbrev ValidatedAdjudicationAuthority (request : RequestKey) :=
  {a : AdjudicationAuthority // a.ValidFor request}

abbrev ProceduralStatusFor (request : RequestKey) :=
  {s : LegalStatus // s.request = request ∧ s.isProcedural = true}

/-- An adjudicated status set is request-bound and excludes procedural statuses
by construction. -/
structure AdjudicatedStatusesFor (request : RequestKey) where
  statuses : Finset LegalStatus
  allBound : ∀ s ∈ statuses,
    s.request = request ∧ s.isProcedural = false

inductive ProcedureAdjudicateResult (request : RequestKey) where
  | adjudicatedStatus (statuses : AdjudicatedStatusesFor request)
  | proceduralDisposition (status : ProceduralStatusFor request)
  | pendingLegalJudgment (missing : Finset String)
  | solverIncomplete (open : Finset OpenObligation)

structure AdjudicationInput (af : DefeatAF) where
  evaluation : EvalResult af
  authority : Option (ValidatedAdjudicationAuthority af.request)
  proceduralOnly : Option (ProceduralStatusFor af.request)

def successStatuses
    {request : RequestKey}
    (a : ValidatedAdjudicationAuthority request) :
    AdjudicatedStatusesFor request where
  statuses := {a.1.rule.successConsequence}
  allBound := by
    intro s hs
    have hEq : s = a.1.rule.successConsequence := by
      simpa using hs
    subst s
    exact ⟨a.2.successRequest, a.2.successNonprocedural⟩

def failureStatuses
    {request : RequestKey}
    (a : ValidatedAdjudicationAuthority request) :
    AdjudicatedStatusesFor request where
  statuses := {a.1.rule.failureConsequence}
  allBound := by
    intro s hs
    have hEq : s = a.1.rule.failureConsequence := by
      simpa using hs
    subst s
    exact ⟨a.2.failureRequest, a.2.failureNonprocedural⟩

/-- Total four-way adjudication normal form. Extension existence does not by
itself determine proof satisfaction. A request-bound authority finding is
required. -/
def adjudicate {af : DefeatAF}
    (input : AdjudicationInput af) : ProcedureAdjudicateResult af.request :=
  match input.evaluation with
  | .incomplete _ partial => .solverIncomplete partial.open
  | .noExtension _ _ =>
      match input.proceduralOnly, input.authority with
      | some status, _ => .proceduralDisposition status
      | none, none => .pendingLegalJudgment {"burden-rule-or-finding"}
      | none, some a =>
          match a.1.finding with
          | .satisfied => .adjudicatedStatus (successStatuses a)
          | .unmet => .adjudicatedStatus (failureStatuses a)
  | .extensions _ _ _ =>
      match input.proceduralOnly, input.authority with
      | some status, _ => .proceduralDisposition status
      | none, none => .pendingLegalJudgment {"burden-rule-or-finding"}
      | none, some a =>
          match a.1.finding with
          | .satisfied => .adjudicatedStatus (successStatuses a)
          | .unmet => .adjudicatedStatus (failureStatuses a)

@[simp] theorem adjudicate_incomplete
    (af : DefeatAF) (profile : SemanticProfile)
    (partial : IncompleteEvaluation af profile)
    (authority : Option (ValidatedAdjudicationAuthority af.request))
    (proceduralOnly : Option (ProceduralStatusFor af.request)) :
    adjudicate
      { evaluation := EvalResult.incomplete profile partial
        authority := authority
        proceduralOnly := proceduralOnly } =
      .solverIncomplete partial.open := rfl

@[simp] theorem noExtension_without_authority_is_pending
    (af : DefeatAF) (profile : SemanticProfile)
    (hEmpty : extensionsForProfile profile af = ∅) :
    adjudicate
      { evaluation := EvalResult.noExtension profile hEmpty
        authority := none
        proceduralOnly := none } =
      .pendingLegalJudgment {"burden-rule-or-finding"} := rfl

def ValidatedAdjudicationAuthority.withFinding
    {request : RequestKey}
    (a : ValidatedAdjudicationAuthority request)
    (finding : ProofFinding) : ValidatedAdjudicationAuthority request :=
  ⟨{ a.1 with finding := finding },
    { issueMatches := a.2.issueMatches
      successRequest := a.2.successRequest
      failureRequest := a.2.failureRequest
      reviewerNonempty := a.2.reviewerNonempty
      successNonprocedural := a.2.successNonprocedural
      failureNonprocedural := a.2.failureNonprocedural }⟩

@[simp] theorem unmet_finding_uses_declared_failure
    (af : DefeatAF) (profile : SemanticProfile)
    (hEmpty : extensionsForProfile profile af = ∅)
    (a : ValidatedAdjudicationAuthority af.request) :
    adjudicate
      { evaluation := EvalResult.noExtension profile hEmpty
        authority := some (a.withFinding .unmet)
        proceduralOnly := none } =
      .adjudicatedStatus (failureStatuses (a.withFinding .unmet)) := rfl

@[simp] theorem procedural_disposition_precedes_entity_finding
    (af : DefeatAF) (profile : SemanticProfile)
    (hEmpty : extensionsForProfile profile af = ∅)
    (status : ProceduralStatusFor af.request)
    (authority : Option (ValidatedAdjudicationAuthority af.request)) :
    adjudicate
      { evaluation := EvalResult.noExtension profile hEmpty
        authority := authority
        proceduralOnly := some status } =
      .proceduralDisposition status := rfl

theorem procedural_input_is_procedural
    {request : RequestKey} (status : ProceduralStatusFor request) :
    status.1.isProcedural = true := status.2.2

theorem burden_success_is_nonprocedural
    {request : RequestKey} (a : ValidatedAdjudicationAuthority request) :
    a.1.rule.successConsequence.isProcedural = false :=
  a.2.successNonprocedural

theorem burden_failure_is_nonprocedural
    {request : RequestKey} (a : ValidatedAdjudicationAuthority request) :
    a.1.rule.failureConsequence.isProcedural = false :=
  a.2.failureNonprocedural

theorem adjudicated_statuses_are_nonprocedural
    {request : RequestKey} (statuses : AdjudicatedStatusesFor request)
    {s : LegalStatus} (h : s ∈ statuses.statuses) :
    s.isProcedural = false :=
  (statuses.allBound s h).2

theorem pending_ne_adjudicated
    {request : RequestKey} (m : Finset String)
    (s : AdjudicatedStatusesFor request) :
    ProcedureAdjudicateResult.pendingLegalJudgment m ≠
      ProcedureAdjudicateResult.adjudicatedStatus s := by
  intro h
  cases h

theorem solverIncomplete_ne_adjudicated
    {request : RequestKey} (o : Finset OpenObligation)
    (s : AdjudicatedStatusesFor request) :
    ProcedureAdjudicateResult.solverIncomplete o ≠
      ProcedureAdjudicateResult.adjudicatedStatus s := by
  intro h
  cases h

end JurisLean.ULM
