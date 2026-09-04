import JurisLean.ULM01NormalForm
import JurisLean.ULM02Outcome
import JurisLean.ULM03TypedGraph
import JurisLean.ULM04Obligations
import JurisLean.ULM05Machine
import JurisLean.ULM06FactEvidence
import JurisLean.ULM07HornSupport
import JurisLean.ULM08ArgumentConstruction
import JurisLean.ULM09AttackDefeat
import JurisLean.ULM10DungProfiles
import JurisLean.ULM11BranchQuery
import JurisLean.ULM12Procedure
import JurisLean.ULM13DomainCompositionExact
import JurisLean.ULM14CoverageTrust
import JurisLean.ULM15IncrementalEmpiricalBanach

/-! Umbrella module and stable CORE/COMP ownership identifiers.

The named theorems below are concrete normal-form instances. They do not claim
that every theorem family in the full TheorySpec or every Python implementation
refinement has already been closed. -/

namespace JurisLean.ULM

inductive CoreId where
  | core01 | core02 | core03 | core04 | core05
  | core06 | core07 | core08 | core09 | core10
  | core11 | core12 | core13 | core14 | core15
  | core16 | core17 | core18 | core19 | core20
  | core21 | core22 | core23 | core24 | core25
  deriving DecidableEq

inductive CompId where
  | c01 | c02 | c03 | c04
  deriving DecidableEq

/-- Ownership is an index, not evidence that the whole family has been proved. -/
def coreOwner : CoreId → String
  | .core01 => "ULM03TypedGraph"
  | .core02 => "ULM06FactEvidence/ULM07HornSupport"
  | .core03 => "ULM07HornSupport"
  | .core04 => "ULM07HornSupport"
  | .core05 => "ULM09AttackDefeat"
  | .core06 => "ULM12Procedure/ULM13DomainCompositionExact"
  | .core07 => "ULM09AttackDefeat/ULM10DungProfiles"
  | .core08 => "ULM11BranchQuery"
  | .core09 => "ULM11BranchQuery"
  | .core10 => "ULM12Procedure"
  | .core11 => "ULM12Procedure"
  | .core12 => "ULM05Machine"
  | .core13 => "ULM13DomainCompositionExact"
  | .core14 => "ULM13DomainCompositionExact"
  | .core15 => "ULM15IncrementalEmpiricalBanach"
  | .core16 => "ULM15IncrementalEmpiricalBanach"
  | .core17 => "ULM15IncrementalEmpiricalBanach"
  | .core18 => "ULM01NormalForm"
  | .core19 => "ULM08ArgumentConstruction"
  | .core20 => "ULM10DungProfiles"
  | .core21 => "ULM11BranchQuery/ULM13DomainCompositionExact"
  | .core22 => "ULM05Machine"
  | .core23 => "ULM04Obligations"
  | .core24 => "ULM04Obligations"
  | .core25 => "ULM12Procedure"

def compOwner : CompId → String
  | .c01 => "ULM14CoverageTrust"
  | .c02 => "ULM01NormalForm/ULM09AttackDefeat"
  | .c03 => "ULM15IncrementalEmpiricalBanach"
  | .c04 => "ULM02Outcome/ULM06FactEvidence/ULM12Procedure"

/-- COMP-C01 instance: coordinatewise meet cannot exceed either input. -/
theorem COMP_C01_trust_nonupgrade_left (a b : TrustVector) :
    TrustLE (a.meet b) a := trust_meet_le_left a b

theorem COMP_C01_trust_nonupgrade_right (a b : TrustVector) :
    TrustLE (a.meet b) b := trust_meet_le_right a b

/-- COMP-C02 instance: observation preservation composes. -/
theorem COMP_C02_observation_preservation
    {α β γ δ : Type*}
    (obsA : α → δ) (obsB : β → δ) (obsC : γ → δ)
    (f : α → β) (g : β → γ)
    (hf : Preserves obsA obsB f) (hg : Preserves obsB obsC g) :
    Preserves obsA obsC (g ∘ f) :=
  preserves_comp obsA obsB obsC f g hf hg

/-- COMP-C03 instance: a concrete implementation satisfying the refinement
relation returns the exact child full recomputation. -/
theorem COMP_C03_add_only_refinement
    {α : Type} [DecidableEq α]
    {sys : HornSystem α}
    {implementation : HornAddDelta sys → Finset α}
    (h : IncrementalImplementationCorrect (sys := sys) implementation)
    (delta : HornAddDelta sys) :
    implementation delta = childFullRecompute sys delta :=
  incremental_correct_returns_full_recompute h delta

/-- The independent child recomputation is a fixed point of the extended Horn
operator. -/
theorem COMP_C03_child_reference_fixed
    {α : Type} [DecidableEq α]
    (sys : HornSystem α) (delta : HornAddDelta sys) :
    HornSystem.TH (extendHorn sys delta) (childFullRecompute sys delta) =
      childFullRecompute sys delta :=
  childFullRecompute_fixed sys delta

/-- COMP-C04 instance: mapping preserves the exact failure object. -/
theorem COMP_C04_failure_nonconversion
    {α β : Type*} (f : α → β) (e : FailureCore) :
    Outcome.map f (.failure e) = (.failure e : Outcome β) :=
  Outcome.map_never_upgrades_failure f e

/-- CORE-01 instance: an executable local graph transition keeps request identity. -/
theorem CORE_01_typed_transition_request
    {g : TypedGraph} {s t : LocalState}
    (h : LocalTransition g s t) : t.request = s.request :=
  localTransition_preserves_request h

/-- CORE-02 instance: an admitted strict-premise token really carries admitted
status in the repository fact-attestation type. -/
theorem CORE_02_admitted_premise_status
    (a : JurisLean.FactAdmissionAttestation)
    (f : JurisLean.LegalId .fact) (r : RequestKey)
    (h : PremiseToken.WF
      { fact := f, request := r, origin := .admitted a }) :
    a.status = .admitted :=
  admitted_wf_has_admitted_status a f r h

/-- CORE-03 instance: support closure is an actual Horn fixed point. -/
theorem CORE_03_support_fixed (sys : TaggedHornSystem) :
    HornSystem.TH sys (supportClosure sys) = supportClosure sys :=
  supportClosure_fixed sys

/-- CORE-04 instance: every generated candidate satisfies the declared support
predicate. -/
theorem CORE_04_generated_candidate_sound
    {sys : TaggedHornSystem} {pool : Finset PositionCandidate}
    {c : PositionCandidate} (h : c ∈ generateCandidates sys pool) :
    CandidateWF sys c :=
  generated_candidate_sound h

/-- CORE-05 instance: a resolved defeat has an actual well-formed typed source. -/
theorem CORE_05_resolved_defeat_has_source
    {input : ValidatedAttackSet} {policy : DefeatPolicy}
    {x y : CanonicalArgument} (h : (x, y) ∈ resolveDefeat input policy) :
    ∃ a ∈ input.attacks,
      AttackWF a ∧ policy.succeeds a = true ∧
      a.attacker = x ∧ a.target = y :=
  resolved_defeat_has_wf_source h

/-- CORE-07 instance: the first structured-to-Dung bridge yields a request-bound
well-formed resolved defeat AF. -/
theorem CORE_07_resolved_bridge_wellFormed
    (input : StructuredArgumentation) (policy : DefeatPolicy) :
    (resolveToDefeatAF input policy).WellFormed :=
  resolveToDefeatAF_wellFormed input policy

/-- CORE-08 instance: different semantic branches cannot be one legal outcome. -/
theorem CORE_08_branch_nonmixing
    {x y : BranchArtifact} (h : x.branch ≠ y.branch) :
    ¬ ComposableAsOneLegalOutcome x y :=
  different_branches_not_composable h

/-- CORE-09 instance: an undecided witness must come from an enterable branch. -/
theorem CORE_09_undecided_requires_enterable
    {env : QueryEnvironment} {f : ExtensionFamily}
    {q : JurisLean.LegalId .claim}
    (h : UndecidedSome env f q) :
    ∃ e ∈ f.carrier, GateEnterable env e q :=
  undecided_requires_enterable h

/-- CORE-10 normal-form instance: procedure movement does not manufacture a
new normative marker. -/
theorem CORE_10_procedure_transition_nonmanufacture
    (cause : ProcedureCause) (s : ProcedureState) :
    (applyProcedureCause cause s).normativeMarker = s.normativeMarker :=
  procedure_transition_preserves_normative_marker cause s

/-- CORE-11 instance: burden failure cannot be smuggled into the procedural
channel; procedural dismissal requires the separate typed input. -/
theorem CORE_11_burden_failure_nonprocedural
    {request : RequestKey} (a : ValidatedAdjudicationAuthority request) :
    a.1.rule.failureConsequence.isProcedural = false :=
  burden_failure_is_nonprocedural a

/-- CORE-13 instance: an accepted composition choice is selected from its actual
bundle and is bound to its actual policy. -/
theorem CORE_13_choice_membership
    {bundle : DomainBundle} {policy : CompositionPolicy}
    {choice : CompositionChoice}
    (h : ChoiceWF bundle policy choice) :
    choice.selected ⊆ bundle.candidates :=
  choice_wf_selected_subset h

/-- CORE-14 instance: exact evaluator equals its recursive denotation. -/
theorem CORE_14_exact_denotation
    {d : Dimension} (e : ExactExpr d) :
    executeExact e = .complete e.denote :=
  exact_execution_matches_denotation e

/-- CORE-15 instance: empirical scoring does not rewrite normative solutions. -/
theorem CORE_15_empirical_read_only
    {α : Type*} (solutions : Finset α) (score : ℚ) :
    (attachEmpirical solutions score).normativeSolutions = solutions := rfl

/-- CORE-16 instance: deviation score is the declared finite weighted sum. -/
theorem CORE_16_deviation_decomposition
    {n : Nat} (weight feature : Fin n → ℚ) :
    deviationScore weight feature = ∑ i, weight i * feature i :=
  deviationScore_decomposes weight feature

/-- CORE-17 instance: a genuine contracting map on a complete nonempty metric
space has a fixed point. -/
theorem CORE_17_banach_exists
    {β : Type*} [MetricSpace β] [CompleteSpace β] [Nonempty β]
    {K : ℝ≥0} {f : β → β} (hf : ContractingWith K f) :
    ∃ y, Function.IsFixedPt f y :=
  banach_exists_fixedPoint hf

/-- CORE-19 instance: equality with a frozen expected carrier plus expected
well-formedness transfers well-formedness to every actual argument. -/
theorem CORE_19_argument_coverage_sound
    {expected actual : Finset CanonicalArgument}
    (hCoverage : ArgumentCoverage expected actual)
    (hExpectedWF : ∀ a ∈ expected, ArgumentWF a)
    {a : CanonicalArgument} (hActual : a ∈ actual) :
    ArgumentWF a :=
  covered_argument_is_well_formed hCoverage hExpectedWF hActual

/-- CORE-20 instance: the finite preferred reference family is complete. -/
theorem CORE_20_preferred_complete
    {af : DefeatAF} {s : Finset ArgId} (h : Preferred af s) :
    s ∈ preferredExtensions af :=
  preferredExtensions_complete h

/-- CORE-22 instance: finite machine runs preserve request identity. -/
theorem CORE_22_run_subject_preserved
    {g : TypedGraph} {x y : Machine} (h : Run g x y) :
    x.request = y.request :=
  run_preserves_request h

/-- CORE-23 instance: no edge can erase the mandatory obligation baseline. -/
theorem CORE_23_required_nonempty (e : NFEdge) :
    (requiredObligations e).Nonempty :=
  requiredObligations_nonempty e

/-- CORE-24 instance: a sound verifier that accepts exact required evidence
establishes the independently stated goal. -/
theorem CORE_24_sat_sound
    {goal : ProofSubject → Prop} {v : VerifierEntry}
    (hv : VerifierSound goal v)
    {subject : ProofSubject} (hs : Sat v subject) :
    subject.obligation ∈ requiredObligations subject.edge ∧
      subject.obligation ∈ v.supported ∧ goal subject :=
  sat_sound hv hs

/-- CORE-25 instance: incomplete solving stays in the solver-incomplete
constructor. -/
theorem CORE_25_incomplete_not_adjudicated
    (af : DefeatAF) (profile : SemanticProfile)
    (partialResult : IncompleteEvaluation af profile)
    (authority : Option (ValidatedAdjudicationAuthority af.request))
    (proceduralOnly : Option (ProceduralStatusFor af.request)) :
    adjudicate
      { evaluation := EvalResult.incomplete profile partialResult
        authority := authority
        proceduralOnly := proceduralOnly } =
      .solverIncomplete partialResult.openObligations :=
  adjudicate_incomplete af profile partialResult authority proceduralOnly

end JurisLean.ULM
