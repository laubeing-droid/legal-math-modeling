import JurisLean.RemainingClosure.CNSemanticConnection

set_option autoImplicit false

/-!
F14: a tuple of unrelated query fields does not establish a common legal
interpretation. Actual selection and source identities are checked below;
same-world refinement is then proved, not included as a query field.
Source only; CI_NOT_RUN until subject-bound evidence exists.
-/
namespace LegalMath.RemainingClosure.EntitySemantics

open JurisLean.KernelV3
open JurisLean.CN.Revision20261101
open JurisLean.CN.Completion20261105
open LegalMath.RemainingClosure.CNSemanticConnection

noncomputable section

/-- These are source/selection conditions on the given legal question, not
soundness, truth, correctness, or success assumptions. -/
structure CoherentQuery (s : Situation) (q : EntityQuery) : Prop where
  ruleSelection : selectedRules s.core q.call.request = [q.law]
  methodSelection : selectedTemplates s q.law = [q.method]
  policyIdentity : (q.call.policy.scope != q.law.scope ||
    q.call.policy.source.id != q.law.source.id ||
    q.call.policy.source.version != q.law.source.version) = false
  scopeIdentity : q.scope = q.call.request.scope
  lawScope : q.law.scope = q.scope
  atomScope : q.atom.scope = q.scope
  natureIdentity : q.call.world = q.world.nature
  compatible : semanticCompatible s q.world
  decisionIdentity : ∀ d, recordedDecision s q = some d →
    d.request.rule = q.call.request.rule ∧ d.request.version = q.call.request.version

theorem selected_law_is_actual (s : Situation) (q : EntityQuery) (h : CoherentQuery s q) :
    q.law ∈ s.core.state.N.rules := by
  have member : q.law ∈ selectedRules s.core q.call.request := by
    rw [h.ruleSelection]
    exact List.mem_singleton_self _
  exact (List.mem_filter.mp member).1

theorem selected_method_is_actual (s : Situation) (q : EntityQuery) (h : CoherentQuery s q) :
    q.method ∈ selectedTemplates s q.law := by
  rw [h.methodSelection]
  exact List.mem_singleton_self _

/-- The actual proofAt checker uses the same selected rule and approved
template as the semantic assessment, including its source identity guard. -/
theorem proofAt_known_assessment (s : Situation) (q : EntityQuery) (h : CoherentQuery s q)
    (j : Judgment) (known : proofAt s q.call (.atom q.atom) = .known j) :
    atomAssessment s q.law q.method q.atom = j := by
  unfold proofAt at known
  rw [h.ruleSelection] at known
  simp only [h.policyIdentity, Bool.false_eq_true, if_false] at known
  rw [h.methodSelection] at known
  cases evaluated : evalProofFormula q.method.body
      (admittedView s.core.state.E q.law.materials) (.atom q.atom) with
  | unknown reason => simp [evaluated] at known
  | known actual =>
    simp only [evaluated] at known
    have same : actual = j := by
      split at known
      · exact Check.known.inj known
      · cases known
    have templateValue : templateAtom q.method.body
        (admittedView s.core.state.E q.law.materials) q.atom = .known j := by
      simpa only [evalProofFormula, same] using evaluated
    simp only [atomAssessment, templateValue, collapse]

/-- Reuses the original semantic compatibility relation for precisely the
actual selected rule/method; it does not equate natural truth with support. -/
theorem actual_judgment_refines_same_world (s : Situation) (q : EntityQuery)
    (h : CoherentQuery s q) (j : Judgment)
    (known : proofAt s q.call (.atom q.atom) = .known j) :
    Refines j (q.world.assessment q.law q.method q.atom) := by
  rw [← proofAt_known_assessment s q h j known]
  exact h.compatible.2 q.law (selected_law_is_actual s q h)
    q.method (selected_method_is_actual s q h) q.atom

theorem determinate_assessment_eq (s : Situation) (q : EntityQuery)
    (h : CoherentQuery s q) (j : Judgment) (determinate : j ≠ .undetermined)
    (known : proofAt s q.call (.atom q.atom) = .known j) :
    q.world.assessment q.law q.method q.atom = j := by
  rcases actual_judgment_refines_same_world s q h j known with unknown | equal
  · exact False.elim (determinate unknown)
  · exact equal.symm

/-- Correctness is computed against that SAME world's assessment and actual
stored decision. It may be false; validity and performance remain separate. -/
theorem correctness_uses_same_assessment (s : Situation) (q : EntityQuery)
    (h : CoherentQuery s q) (j : Judgment) (determinate : j ≠ .undetermined)
    (known : proofAt s q.call (.atom q.atom) = .known j) :
    (fourEffects s q).correctness =
      (recordedDecision s q).map (fun d => d.judgment == j) := by
  have assessment := determinate_assessment_eq s q h j determinate known
  cases decision : recordedDecision s q with
  | none => simp [fourEffects, decision]
  | some d =>
    cases j <;> simp_all [fourEffects, evalFormula]

/-- The original private write leaves the selected legal question intact. -/
theorem private_table_preserves_coherence (s : Situation) (q : EntityQuery)
    (h : CoherentQuery s q) (table : List Rat) :
    CoherentQuery (s.withCore (s.core.putState
      {s.core.state with A := {s.core.state.A with theta := table}} rfl)) q := by
  exact ⟨h.ruleSelection, h.methodSelection, h.policyIdentity, h.scopeIdentity,
    h.lawScope, h.atomScope, h.natureIdentity, h.compatible, h.decisionIdentity⟩

/-- Consumes the actual retained-report learning command, including all
failure branches. Private learning cannot change the legal interpretation. -/
theorem learnReport_preserves_coherent_query (s : Situation) (q : EntityQuery)
    (h : CoherentQuery s q) (r : Request) (id : Ref .material) :
    CoherentQuery (learnReport s r id).after q := by
  unfold learnReport
  split
  · exact h
  · split
    · exact h
    · split
      · split
        · exact h
        · exact private_table_preserves_coherence s q h _
      · exact h

theorem learnReport_legal_readouts (s : Situation) (q : EntityQuery)
    (r : Request) (id : Ref .material) :
    sixJudgments (learnReport s r id).after q = sixJudgments s q ∧
      fourEffects (learnReport s r id).after q = fourEffects s q := by
  unfold learnReport
  split
  · exact ⟨rfl,rfl⟩
  · split
    · exact ⟨rfl,rfl⟩
    · split
      · split <;> exact ⟨rfl,rfl⟩
      · exact ⟨rfl,rfl⟩

namespace Actual
open Examples

def query : EntityQuery where
  call := Examples.call .decide
  atom := toyAtom
  document := ⟨70⟩
  person := ⟨12⟩
  scope := toyScope
  time := 5
  bindingKind := .resJudicata
  law := confirmation
  method := CompilerBridge.Actual.method
  world := canonicalWorld bound toyWorld

/-- The witness is a real stored decision/binding post, not a handwritten
assessment made equal to the desired conclusion. -/
theorem query_is_coherent : CoherentQuery bound query := by
  constructor
  · rfl
  · rfl
  · decide
  · rfl
  · rfl
  · rfl
  · rfl
  · exact canonicalWorld_compatible bound toyWorld
      (legalWorldCheck_sound bound toyWorld (by decide))
  · intro d found
    have stored : recordedDecision bound query = some decisionRecord := by decide
    rw [stored] at found
    cases found
    constructor <;> rfl

theorem actual_proof_and_world_agree :
    proofAt bound query.call (.atom query.atom) = .known .established ∧
    query.world.assessment query.law query.method query.atom = .established := by
  have checked : proofAt bound query.call (.atom query.atom) = .known .established := by decide
  exact ⟨checked, determinate_assessment_eq bound query query_is_coherent
    .established (by decide) checked⟩

def mismatched : EntityQuery :=
  {query with world := ⟨toyWorld, fun _ _ _ => .notEstablished⟩}

/-- An unvalidated tuple really can disagree: the actual proof is established
while its independently supplied assessment is notEstablished. -/
theorem bare_query_counterexample :
    proofAt bound mismatched.call (.atom mismatched.atom) = .known .established ∧
    mismatched.world.assessment mismatched.law mismatched.method mismatched.atom = .notEstablished ∧
    ¬ CoherentQuery bound mismatched := by
  have checked : proofAt bound mismatched.call (.atom mismatched.atom) = .known .established :=
    actual_proof_and_world_agree.1
  refine ⟨checked, rfl, ?_⟩
  intro coherent
  have impossible := actual_judgment_refines_same_world bound mismatched coherent .established checked
  simp [Refines, mismatched] at impossible

end Actual

#print axioms selected_law_is_actual
#print axioms selected_method_is_actual
#print axioms proofAt_known_assessment
#print axioms actual_judgment_refines_same_world
#print axioms determinate_assessment_eq
#print axioms correctness_uses_same_assessment
#print axioms private_table_preserves_coherence
#print axioms learnReport_preserves_coherent_query
#print axioms learnReport_legal_readouts
#print axioms Actual.query_is_coherent
#print axioms Actual.actual_proof_and_world_agree
#print axioms Actual.bare_query_counterexample

end
end LegalMath.RemainingClosure.EntitySemantics
