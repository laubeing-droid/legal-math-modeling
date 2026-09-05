import JurisLean.ULM13DomainCompositionExact

/-! Coverage layers, five-coordinate trust, and field-specific assurance aggregation. -/

namespace JurisLean.ULM

structure NotApplicableEvidence where
  obligation : String
  reason : String
deriving DecidableEq

/-- Coverage is represented by its still-open obligations and its explicit
not-applicability evidence. Aggregation never discards either carrier. -/
structure CoverageStatus where
  openObligations : Finset OpenObligation
  notApplicable : Finset NotApplicableEvidence
deriving DecidableEq

namespace CoverageStatus

def complete : CoverageStatus :=
  { openObligations := ∅, notApplicable := ∅ }

def incomplete (openObligations : Finset OpenObligation) : CoverageStatus :=
  { openObligations := openObligations, notApplicable := ∅ }

def exempt (evidence : NotApplicableEvidence) : CoverageStatus :=
  { openObligations := ∅, notApplicable := {evidence} }

def IsComplete (status : CoverageStatus) : Prop :=
  status.openObligations = ∅

end CoverageStatus

structure SemanticCoverage where
  expected : Finset (Finset ArgId)
  actual : Finset (Finset ArgId)
  exact : actual = expected

/-- Runtime status is derived from the actual result constructor. -/
def coverageStatusOf {af : DefeatAF} : EvalResult af → CoverageStatus
  | .noExtension _ _ => .complete
  | .extensions _ _ _ => .complete
  | .incomplete _ partialResult => .incomplete partialResult.openObligations

structure ExecutionReturnCorrectness (af : DefeatAF) where
  result : EvalResult af
  status : CoverageStatus
  statusExact : status = coverageStatusOf result

structure AuditLifecycleCoverage where
  ledgerComplete : Bool
  occurrenceComplete : Bool
  successorComplete : Bool
deriving DecidableEq

theorem incomplete_not_complete
    {openObligations : Finset OpenObligation} (h : openObligations.Nonempty) :
    ¬ (CoverageStatus.incomplete openObligations).IsComplete := by
  simpa [CoverageStatus.IsComplete, CoverageStatus.incomplete] using
    (Finset.nonempty_iff_ne_empty.mp h)

@[simp] theorem exemption_records_evidence (w : NotApplicableEvidence) :
    w ∈ (CoverageStatus.exempt w).notApplicable := by
  simp [CoverageStatus.exempt]

/-- Three levels per coordinate; the five fields remain non-interchangeable. -/
abbrev TrustLevel := Fin 3

structure TrustVector where
  source : TrustLevel
  text : TrustLevel
  fact : TrustLevel
  proof : TrustLevel
  authority : TrustLevel
deriving DecidableEq

def TrustVector.meet (a b : TrustVector) : TrustVector :=
  { source := min a.source b.source
    text := min a.text b.text
    fact := min a.fact b.fact
    proof := min a.proof b.proof
    authority := min a.authority b.authority }

def TrustLE (a b : TrustVector) : Prop :=
  a.source ≤ b.source ∧
    a.text ≤ b.text ∧
    a.fact ≤ b.fact ∧
    a.proof ≤ b.proof ∧
    a.authority ≤ b.authority

theorem trust_meet_le_left (a b : TrustVector) :
    TrustLE (a.meet b) a := by
  exact ⟨min_le_left _ _, min_le_left _ _, min_le_left _ _,
    min_le_left _ _, min_le_left _ _⟩

theorem trust_meet_le_right (a b : TrustVector) :
    TrustLE (a.meet b) b := by
  exact ⟨min_le_right _ _, min_le_right _ _, min_le_right _ _,
    min_le_right _ _, min_le_right _ _⟩

inductive SpecStatus where
  | proved
  | assumed
  | openObligations
deriving DecidableEq

inductive ImplementationAssurance where
  | crossCheckOnly
  | tcbSpecified
  | kernelVerified
deriving DecidableEq

inductive RunCheckStatus where
  | checked
  | unchecked
  | checkFailed
deriving DecidableEq

/-- Pending and assumed legal-input references are independent carriers. This
prevents a pending status from silently dropping assumptions already used. -/
structure LegalInputStatus where
  pendingRefs : Finset String
  assumedRefs : Finset String
deriving DecidableEq

namespace LegalInputStatus

def complete : LegalInputStatus :=
  { pendingRefs := ∅, assumedRefs := ∅ }

def assumed (refs : Finset String) : LegalInputStatus :=
  { pendingRefs := ∅, assumedRefs := refs }

def pending (refs : Finset String) : LegalInputStatus :=
  { pendingRefs := refs, assumedRefs := ∅ }

def IsComplete (status : LegalInputStatus) : Prop :=
  status.pendingRefs = ∅ ∧ status.assumedRefs = ∅

end LegalInputStatus

structure AssuranceScope where
  request : RequestKey
  profile : SemanticProfile
deriving DecidableEq

structure AssuranceEnvelope where
  spec : SpecStatus
  implementation : ImplementationAssurance
  runCheck : RunCheckStatus
  coverage : CoverageStatus
  legalInput : LegalInputStatus
  scope : AssuranceScope
  openSpecRefs : Finset String
  formalAssumptionRefs : Finset String
  tcbRefs : Finset String
  notices : Finset OpenObligation
deriving DecidableEq

def combineSpec : SpecStatus → SpecStatus → SpecStatus
  | .openObligations, _ => .openObligations
  | _, .openObligations => .openObligations
  | .assumed, _ => .assumed
  | _, .assumed => .assumed
  | .proved, .proved => .proved

def combineImplementation :
    ImplementationAssurance → ImplementationAssurance → ImplementationAssurance
  | .crossCheckOnly, _ => .crossCheckOnly
  | _, .crossCheckOnly => .crossCheckOnly
  | .tcbSpecified, _ => .tcbSpecified
  | _, .tcbSpecified => .tcbSpecified
  | .kernelVerified, .kernelVerified => .kernelVerified

def combineRunCheck : RunCheckStatus → RunCheckStatus → RunCheckStatus
  | .checkFailed, _ => .checkFailed
  | _, .checkFailed => .checkFailed
  | .unchecked, _ => .unchecked
  | _, .unchecked => .unchecked
  | .checked, .checked => .checked

def combineCoverage (a b : CoverageStatus) : CoverageStatus :=
  { openObligations := a.openObligations ∪ b.openObligations
    notApplicable := a.notApplicable ∪ b.notApplicable }

def combineLegalInput (a b : LegalInputStatus) : LegalInputStatus :=
  { pendingRefs := a.pendingRefs ∪ b.pendingRefs
    assumedRefs := a.assumedRefs ∪ b.assumedRefs }

def combineAssurance (a b : AssuranceEnvelope) : Option AssuranceEnvelope :=
  if h : a.scope = b.scope then
    some
      { spec := combineSpec a.spec b.spec
        implementation := combineImplementation a.implementation b.implementation
        runCheck := combineRunCheck a.runCheck b.runCheck
        coverage := combineCoverage a.coverage b.coverage
        legalInput := combineLegalInput a.legalInput b.legalInput
        scope := a.scope
        openSpecRefs := a.openSpecRefs ∪ b.openSpecRefs
        formalAssumptionRefs :=
          a.formalAssumptionRefs ∪ b.formalAssumptionRefs
        tcbRefs := a.tcbRefs ∪ b.tcbRefs
        notices := a.notices ∪ b.notices }
  else
    none

@[simp] theorem combineSpec_open_left (b : SpecStatus) :
    combineSpec .openObligations b = .openObligations := by
  cases b <;> rfl

@[simp] theorem combineRunCheck_failed_left (b : RunCheckStatus) :
    combineRunCheck .checkFailed b = .checkFailed := by
  cases b <;> rfl

@[simp] theorem combineCoverage_open (a b : CoverageStatus) :
    (combineCoverage a b).openObligations = a.openObligations ∪ b.openObligations := rfl

@[simp] theorem combineCoverage_notApplicable (a b : CoverageStatus) :
    (combineCoverage a b).notApplicable =
      a.notApplicable ∪ b.notApplicable := rfl

@[simp] theorem combineLegalInput_pendingRefs
    (a b : LegalInputStatus) :
    (combineLegalInput a b).pendingRefs =
      a.pendingRefs ∪ b.pendingRefs := rfl

@[simp] theorem combineLegalInput_assumedRefs
    (a b : LegalInputStatus) :
    (combineLegalInput a b).assumedRefs =
      a.assumedRefs ∪ b.assumedRefs := rfl

theorem incompatible_assurance_scope_rejected
    {a b : AssuranceEnvelope} (h : a.scope ≠ b.scope) :
    combineAssurance a b = none := by
  simp [combineAssurance, h]

theorem combined_assurance_preserves_scope
    {a b c : AssuranceEnvelope}
    (h : combineAssurance a b = some c) : c.scope = a.scope := by
  unfold combineAssurance at h
  split at h
  · cases h
    rfl
  · simp at h

theorem combined_open_spec_cannot_be_proved
    {a b c : AssuranceEnvelope}
    (ha : a.spec = .openObligations)
    (h : combineAssurance a b = some c) : c.spec = .openObligations := by
  unfold combineAssurance at h
  split at h
  · cases h
    simp [ha, combineSpec]
  · simp at h

theorem combined_coverage_retains_left_open
    {a b c : AssuranceEnvelope}
    (h : combineAssurance a b = some c) :
    a.coverage.openObligations ⊆ c.coverage.openObligations := by
  unfold combineAssurance at h
  split at h
  · cases h
    intro x hx
    exact Finset.mem_union_left _ hx
  · simp at h

theorem combined_coverage_retains_left_exemptions
    {a b c : AssuranceEnvelope}
    (h : combineAssurance a b = some c) :
    a.coverage.notApplicable ⊆ c.coverage.notApplicable := by
  unfold combineAssurance at h
  split at h
  · cases h
    intro x hx
    exact Finset.mem_union_left _ hx
  · simp at h

theorem combined_legal_input_retains_left_pending
    {a b c : AssuranceEnvelope}
    (h : combineAssurance a b = some c) :
    a.legalInput.pendingRefs ⊆ c.legalInput.pendingRefs := by
  unfold combineAssurance at h
  split at h
  · cases h
    intro x hx
    exact Finset.mem_union_left _ hx
  · simp at h

theorem combined_assurance_retains_left_open_spec_refs
    {a b c : AssuranceEnvelope}
    (h : combineAssurance a b = some c) :
    a.openSpecRefs ⊆ c.openSpecRefs := by
  unfold combineAssurance at h
  split at h
  · cases h
    intro x hx
    exact Finset.mem_union_left _ hx
  · simp at h

theorem combined_assurance_retains_left_notices
    {a b c : AssuranceEnvelope}
    (h : combineAssurance a b = some c) :
    a.notices ⊆ c.notices := by
  unfold combineAssurance at h
  split at h
  · cases h
    intro x hx
    exact Finset.mem_union_left _ hx
  · simp at h

end JurisLean.ULM
