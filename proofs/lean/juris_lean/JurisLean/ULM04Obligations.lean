import JurisLean.ULM03TypedGraph

/-! Kind-indexed mandatory claims, non-empty obligations, and TCB soundness. -/

namespace JurisLean.ULM

inductive ObligationKind where
  | typeSafety
  | semanticSoundness
  | failurePreservation
  | completeness
  | observationPreservation
  | observationReflection
  | trustNonUpgrade
  | updateSafety
  | identityPreservation
  | branchNonMixing
  | authorityBinding
  | dimensionalCorrectness
  | termination
  | confluence
  | observationDeclaration
  deriving DecidableEq

/-- Every executable kind has an irreducible baseline; specialised kinds add
obligations rather than deleting the baseline. -/
def baselineClaims (k : EdgeKind) : List ClaimKind :=
  [.typeSafety, .soundness, .failure] ++
  match k with
  | .stateTransition => [.update, .identity, .branch]
  | .abstraction => [.preserve]
  | .probabilityKernel => [.observe]
  | .ranker => [.observe]
  | .exactCalculation => [.dimension]
  | _ => []

def obligationsForClaim : ClaimKind → List ObligationKind
  | .typeSafety => [.typeSafety]
  | .soundness => [.semanticSoundness]
  | .failure => [.failurePreservation]
  | .completeness => [.completeness]
  | .preserve => [.observationPreservation]
  | .reflect => [.observationReflection]
  | .observe => [.observationDeclaration]
  | .trust => [.trustNonUpgrade]
  | .update => [.updateSafety]
  | .identity => [.identityPreservation]
  | .branch => [.branchNonMixing]
  | .authority => [.authorityBinding]
  | .dimension => [.dimensionalCorrectness]
  | .termination => [.termination]
  | .confluence => [.confluence]

/-- Required obligations are derived from the frozen baseline plus declared
claims.  The explicit insertion prevents an empty-obligation escape. -/
noncomputable def requiredObligations (e : NFEdge) : Finset ObligationKind :=
  insert .typeSafety
    ((baselineClaims e.kind ++ e.claims.toList).flatMap obligationsForClaim).toFinset

theorem typeSafety_mem_required (e : NFEdge) :
    .typeSafety ∈ requiredObligations e := by
  exact Finset.mem_insert_self _ _

theorem requiredObligations_nonempty (e : NFEdge) :
    (requiredObligations e).Nonempty :=
  ⟨.typeSafety, typeSafety_mem_required e⟩

structure ProofSubject where
  edge : NFEdge
  obligation : ObligationKind
  registryVersion : JurisLean.SchemaVersion
deriving DecidableEq

structure ProofEvidence where
  subject : ProofSubject
  evidenceKind : ObligationKind
  payload : String
deriving DecidableEq

structure VerifierEntry where
  verifierId : String
  supported : Finset ObligationKind
  verify : ProofEvidence → Bool

/-- `goal` is the independently stated obligation semantics. -/
def VerifierSound (goal : ProofSubject → Prop) (v : VerifierEntry) : Prop :=
  ∀ ev, v.verify ev = true →
    ev.evidenceKind ∈ v.supported ∧ goal ev.subject

/-- Evidence must bind the exact structured subject and an actually required
obligation. -/
def Sat (v : VerifierEntry) (subject : ProofSubject) : Prop :=
  subject.obligation ∈ requiredObligations subject.edge ∧
  ∃ ev : ProofEvidence,
    ev.subject = subject ∧
    ev.evidenceKind = subject.obligation ∧
    v.verify ev = true

theorem sat_sound
    {goal : ProofSubject → Prop} {v : VerifierEntry}
    (hv : VerifierSound goal v)
    {subject : ProofSubject} (hs : Sat v subject) :
    subject.obligation ∈ requiredObligations subject.edge ∧
    subject.obligation ∈ v.supported ∧
    goal subject := by
  rcases hs with ⟨hrequired, ev, hsubject, hkind, hverify⟩
  have hsound := hv ev hverify
  refine ⟨hrequired, ?_, ?_⟩
  · simpa [hkind] using hsound.1
  · simpa [hsubject] using hsound.2

end JurisLean.ULM
