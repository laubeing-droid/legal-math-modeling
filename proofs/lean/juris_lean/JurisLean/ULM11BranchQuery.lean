import JurisLean.ULM10DungProfiles

/-! Scenario/branch identities, semantic extension binding, and query reports. -/

namespace JurisLean.ULM

structure ExtensionFamily where
  carrier : Finset (Finset ArgId)
  nonempty : carrier.Nonempty

noncomputable def extensionsForProfile
    (profile : SemanticProfile) (af : DefeatAF) : Finset (Finset ArgId) :=
  match profile with
  | .grounded => {groundedExtension af}
  | .preferred => preferredExtensions af
  | .stable => stableExtensions af
  | .complete => completeExtensions af

/-- An incomplete result carries at least one open obligation and every reported
extension is already sound for the selected profile. It does not claim that all
extensions were found. -/
structure IncompleteEvaluation (af : DefeatAF) (profile : SemanticProfile) where
  discovered : Finset (Finset ArgId)
  open : Finset OpenObligation
  openNonempty : open.Nonempty
  discoveredSound : ∀ e ∈ discovered, SatisfiesProfile af profile e

/-- Complete constructors carry equality with the selected profile's actual
semantic extension family. `NoExtension` carries an emptiness proof. -/
inductive EvalResult (af : DefeatAF) where
  | noExtension (profile : SemanticProfile)
      (emptyProof : extensionsForProfile profile af = ∅)
  | extensions (profile : SemanticProfile) (family : ExtensionFamily)
      (exact : family.carrier = extensionsForProfile profile af)
  | incomplete (profile : SemanticProfile)
      (partial : IncompleteEvaluation af profile)

namespace EvalResult

def profile {af : DefeatAF} : EvalResult af → SemanticProfile
  | .noExtension p _ => p
  | .extensions p _ _ => p
  | .incomplete p _ => p

end EvalResult

/-- Generic exact reference evaluator. It returns `NoExtension` only when the
selected semantic family is actually empty. -/
noncomputable def evaluateProfile
    (profile : SemanticProfile) (af : DefeatAF) : EvalResult af := by
  classical
  by_cases h : extensionsForProfile profile af = ∅
  · exact .noExtension profile h
  · exact .extensions profile
      { carrier := extensionsForProfile profile af
        nonempty := Finset.nonempty_iff_ne_empty.mpr h }
      rfl

noncomputable def evaluateGrounded (af : DefeatAF) : EvalResult af :=
  .extensions .grounded
    { carrier := {groundedExtension af}, nonempty := ⟨groundedExtension af, by simp⟩ }
    rfl

noncomputable def evaluatePreferred (af : DefeatAF) : EvalResult af :=
  .extensions .preferred
    { carrier := preferredExtensions af
      nonempty := preferredExtensions_nonempty af }
    rfl

@[simp] theorem evaluateProfile_profile
    (profile : SemanticProfile) (af : DefeatAF) :
    (evaluateProfile profile af).profile = profile := by
  unfold evaluateProfile
  split <;> rfl

theorem grounded_extension_family_nonempty (af : DefeatAF) :
    (extensionsForProfile .grounded af).Nonempty := by
  refine ⟨groundedExtension af, ?_⟩
  simp [extensionsForProfile]

theorem preferred_extension_family_nonempty (af : DefeatAF) :
    (extensionsForProfile .preferred af).Nonempty := by
  simpa [extensionsForProfile] using preferredExtensions_nonempty af

@[simp] theorem evaluateGrounded_profile (af : DefeatAF) :
    (evaluateGrounded af).profile = .grounded := rfl

@[simp] theorem evaluatePreferred_profile (af : DefeatAF) :
    (evaluatePreferred af).profile = .preferred := rfl

/-- `{∅}` is a nonempty extension family. -/
def singletonEmptyFamily : ExtensionFamily :=
  { carrier := {∅}, nonempty := ⟨∅, by simp⟩ }

@[simp] theorem singleton_empty_family_nonempty :
    singletonEmptyFamily.carrier.Nonempty :=
  singletonEmptyFamily.nonempty

structure ScenarioKey where
  request : RequestKey
  assumptions : Finset String
deriving DecidableEq, Repr

structure SemanticBranchKey where
  scenario : ScenarioKey
  profile : SemanticProfile
  extension : Finset ArgId
deriving DecidableEq, Repr

structure BranchArtifact where
  branch : SemanticBranchKey
  claims : Finset (JurisLean.LegalId .claim)
deriving DecidableEq, Repr

def ComposableAsOneLegalOutcome (x y : BranchArtifact) : Prop :=
  x.branch = y.branch

theorem different_branches_not_composable
    {x y : BranchArtifact} (h : x.branch ≠ y.branch) :
    ¬ ComposableAsOneLegalOutcome x y := by
  simpa [ComposableAsOneLegalOutcome] using h

/-- Positive enterability and exclusion are proof-bearing. An incomplete gate
cannot be used as a witness for any query-status report. -/
structure QueryEnterabilityWitness
    (request : RequestKey) (extension : Finset ArgId)
    (query : JurisLean.LegalId .claim) where
  basis : String
  basisNonempty : basis ≠ ""

structure QueryExclusionWitness
    (request : RequestKey) (extension : Finset ArgId)
    (query : JurisLean.LegalId .claim) where
  reason : String
  reasonNonempty : reason ≠ ""

inductive QueryGateState
    (request : RequestKey) (extension : Finset ArgId)
    (query : JurisLean.LegalId .claim) where
  | enterable (witness : QueryEnterabilityWitness request extension query)
  | excluded (witness : QueryExclusionWitness request extension query)
  | incomplete (open : Finset OpenObligation) (openNonempty : open.Nonempty)

structure QueryEnvironment where
  request : RequestKey
  conclusion : ArgId → JurisLean.LegalId .claim
  refutations : Finset QueryRefutation
  gate : (extension : Finset ArgId) → (query : JurisLean.LegalId .claim) →
    QueryGateState request extension query

def GateEnterable (env : QueryEnvironment) (e : Finset ArgId)
    (q : JurisLean.LegalId .claim) : Prop :=
  ∃ witness, env.gate e q = .enterable witness

def GateExcluded (env : QueryEnvironment) (e : Finset ArgId)
    (q : JurisLean.LegalId .claim) : Prop :=
  ∃ witness, env.gate e q = .excluded witness

def GateIncomplete (env : QueryEnvironment) (e : Finset ArgId)
    (q : JurisLean.LegalId .claim) : Prop :=
  ∃ open openNonempty, env.gate e q = .incomplete open openNonempty

def AcceptedIn (env : QueryEnvironment) (e : Finset ArgId)
    (q : JurisLean.LegalId .claim) : Prop :=
  ∃ a ∈ e, env.conclusion a = q

def RefutedIn (env : QueryEnvironment) (e : Finset ArgId)
    (q : JurisLean.LegalId .claim) : Prop :=
  ∃ a ∈ e,
    QueryRefutes env.refutations env.request (env.conclusion a) q

def Common (env : QueryEnvironment) (f : ExtensionFamily)
    (q : JurisLean.LegalId .claim) : Prop :=
  ∀ e ∈ f.carrier, AcceptedIn env e q

def Possible (env : QueryEnvironment) (f : ExtensionFamily)
    (q : JurisLean.LegalId .claim) : Prop :=
  ∃ e ∈ f.carrier, AcceptedIn env e q

def CommonRefuted (env : QueryEnvironment) (f : ExtensionFamily)
    (q : JurisLean.LegalId .claim) : Prop :=
  ∀ e ∈ f.carrier, RefutedIn env e q

def PossiblyRefuted (env : QueryEnvironment) (f : ExtensionFamily)
    (q : JurisLean.LegalId .claim) : Prop :=
  ∃ e ∈ f.carrier, RefutedIn env e q

def UndecidedSome (env : QueryEnvironment) (f : ExtensionFamily)
    (q : JurisLean.LegalId .claim) : Prop :=
  ∃ e ∈ f.carrier,
    GateEnterable env e q ∧
    ¬ AcceptedIn env e q ∧ ¬ RefutedIn env e q

def InconsistentSome (env : QueryEnvironment) (f : ExtensionFamily)
    (q : JurisLean.LegalId .claim) : Prop :=
  ∃ e ∈ f.carrier,
    GateEnterable env e q ∧
    AcceptedIn env e q ∧ RefutedIn env e q

def Excluded (env : QueryEnvironment) (f : ExtensionFamily)
    (q : JurisLean.LegalId .claim) : Prop :=
  ∀ e ∈ f.carrier, GateExcluded env e q

theorem undecided_requires_enterable
    {env : QueryEnvironment} {f : ExtensionFamily}
    {q : JurisLean.LegalId .claim}
    (h : UndecidedSome env f q) :
    ∃ e ∈ f.carrier, GateEnterable env e q := by
  rcases h with ⟨e, he, hgate, _, _⟩
  exact ⟨e, he, hgate⟩

theorem inconsistent_requires_acceptance_and_refutation
    {env : QueryEnvironment} {f : ExtensionFamily}
    {q : JurisLean.LegalId .claim}
    (h : InconsistentSome env f q) :
    ∃ e ∈ f.carrier, AcceptedIn env e q ∧ RefutedIn env e q := by
  rcases h with ⟨e, he, _, ha, hr⟩
  exact ⟨e, he, ha, hr⟩

theorem enterability_has_positive_witness
    {env : QueryEnvironment} {e : Finset ArgId}
    {q : JurisLean.LegalId .claim}
    (h : GateEnterable env e q) :
    ∃ witness : QueryEnterabilityWitness env.request e q,
      witness.basis ≠ "" := by
  rcases h with ⟨witness, _⟩
  exact ⟨witness, witness.basisNonempty⟩

end JurisLean.ULM
