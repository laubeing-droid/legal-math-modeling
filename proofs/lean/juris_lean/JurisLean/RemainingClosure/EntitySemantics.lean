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

/-- Source/selection conditions and the original semantic model class.
The latter is reused as defined in WorldSemantics; it is not a new derivation
of world soundness. This atomic specialization identifies the actual question. -/
structure CoherentQuery (s : Situation) (q : EntityQuery) : Prop where
  ruleSelection : selectedRules s.core q.call.request = [q.law]
  methodSelection : selectedTemplates s q.law = [q.method]
  policyIdentity : (q.call.policy.scope != q.law.scope ||
    q.call.policy.source.id != q.law.source.id ||
    q.call.policy.source.version != q.law.source.version) = false
  scopeIdentity : q.scope = q.call.request.scope
  lawScope : q.law.scope = q.scope
  atomScope : q.atom.scope = q.scope
  questionIdentity : q.law.guard = .atom q.atom
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
    h.lawScope, h.atomScope, h.questionIdentity, h.natureIdentity, h.compatible, h.decisionIdentity⟩

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

/- General formulas use the actual selected rule's guard. They do not infer
question identity from scope, and are not restricted to single-atom rules. -/
def naturalFormula (w : PossibleWorld) : Formula → Bool
  | .atom a => w.fact a
  | .both a b => naturalFormula w a && naturalFormula w b
  | .either a b => naturalFormula w a || naturalFormula w b
  | .neg a => !naturalFormula w a

/-- A document/scope match alone must not compare decisions about a different
norm or version. Inconsistent source identities keep the unknown exit. -/
def matchedDecision (s : Situation) (q : EntityQuery) : Option DecisionRecord :=
  (recordedDecision s q).filter (fun d => d.request.rule == q.call.request.rule &&
    d.request.version == q.call.request.version && d.request.scope == q.scope &&
    d.request.scope == q.call.request.scope)

theorem matched_decision_has_same_source (s : Situation) (q : EntityQuery) (d : DecisionRecord)
    (found : matchedDecision s q = some d) :
    d.request.rule = q.call.request.rule ∧ d.request.version = q.call.request.version ∧
      d.request.scope = q.scope ∧ d.request.scope = q.call.request.scope := by
  cases recorded : recordedDecision s q with
  | none => simp [matchedDecision, recorded] at found
  | some row =>
    simp only [matchedDecision, recorded] at found
    change (if row.request.rule == q.call.request.rule &&
      row.request.version == q.call.request.version && row.request.scope == q.scope &&
      row.request.scope == q.call.request.scope then some row else none) = some d at found
    split at found
    · rename_i accepted
      have same : row = d := Option.some.inj found
      subst d
      simpa only [Bool.and_eq_true, beq_iff_eq, and_assoc] using accepted
    · cases found

def formulaBindingReadout (s : Situation) (q : EntityQuery) : Answer Bool :=
  match s.core.state.bindings.filterMap (fun b => match b with
    | .decide d => if d.decision.document == q.document && d.kind == q.bindingKind &&
        d.decision.request.rule == q.call.request.rule &&
        d.decision.request.version == q.call.request.version &&
        d.decision.request.scope == q.scope &&
        d.decision.request.scope == q.call.request.scope then some d.index else none
    | .other _ => none) with
  | [] => .unknown .inputUnchecked
  | indices => .success (indices.any (fun i => withinBinding i q.person q.scope q.time))

def formulaSixJudgments (s : Situation) (q : EntityQuery) : SixJudgments :=
  ⟨naturalFormula q.world.nature q.law.guard,
    evalFormula (support (admittedView s.core.state.E q.law.materials)) q.law.guard,
    proofAt s q.call q.law.guard,
    (matchedDecision s q).map (fun d => d.judgment),
    (matchedDecision s q).map (fun d => d.valid), formulaBindingReadout s q⟩

def formulaFourEffects (s : Situation) (q : EntityQuery) : FourEffects :=
  ⟨(matchedDecision s q).map (fun d => d.valid),
    formulaBindingReadout s {q with bindingKind := .resJudicata},
    (matchedDecision s q).bind (fun d =>
      match evalFormula (q.world.assessment q.law q.method) q.law.guard with
      | .undetermined => none
      | expected => some (d.judgment == expected)),
    s.core.state.ledger.filter (fun entry => entry.request.scope == q.scope)⟩

theorem formula_learnReport_legal_readouts (s : Situation) (q : EntityQuery)
    (r : Request) (id : Ref .material) :
    formulaSixJudgments (learnReport s r id).after q = formulaSixJudgments s q ∧
      formulaFourEffects (learnReport s r id).after q = formulaFourEffects s q := by
  unfold learnReport
  split
  · exact ⟨rfl,rfl⟩
  · split
    · exact ⟨rfl,rfl⟩
    · split
      · split <;> exact ⟨rfl,rfl⟩
      · exact ⟨rfl,rfl⟩

/-- The new bridge proves actual checker/selected-template agreement. It
requires no supported-world refinement or semanticCompatible premise. -/
theorem actual_formula_checker_assessment (s : Situation) (q : EntityQuery)
    (ruleSelection : selectedRules s.core q.call.request = [q.law])
    (methodSelection : selectedTemplates s q.law = [q.method])
    (policyIdentity : (q.call.policy.scope != q.law.scope ||
      q.call.policy.source.id != q.law.source.id ||
      q.call.policy.source.version != q.law.source.version) = false)
    (j : Judgment) (known : proofAt s q.call q.law.guard = .known j) :
    evalFormula (atomAssessment s q.law q.method) q.law.guard = j := by
  unfold proofAt at known
  rw [ruleSelection] at known
  simp only [policyIdentity, Bool.false_eq_true, if_false] at known
  rw [methodSelection] at known
  cases evaluated : evalProofFormula q.method.body
      (admittedView s.core.state.E q.law.materials) q.law.guard with
  | unknown reason => simp [evaluated] at known
  | known actual =>
    simp only [evaluated] at known
    have same : actual = j := by
      split at known
      · exact Check.known.inj known
      · cases known
    unfold atomAssessment
    rw [← collapse_formula, evaluated, same]
    rfl

/-- The old semantic model class is explicit and separate from the proved
checker bridge. Formula refinement is reused on the SAME selected question. -/
theorem selected_formula_refines_supported_world (s : Situation) (q : EntityQuery)
    (ruleSelection : selectedRules s.core q.call.request = [q.law])
    (methodSelection : selectedTemplates s q.law = [q.method])
    (policyIdentity : (q.call.policy.scope != q.law.scope ||
      q.call.policy.source.id != q.law.source.id ||
      q.call.policy.source.version != q.law.source.version) = false)
    (compatible : semanticCompatible s q.world)
    (j : Judgment) (known : proofAt s q.call q.law.guard = .known j) :
    Refines j (evalFormula (q.world.assessment q.law q.method) q.law.guard) := by
  have lawIn : q.law ∈ s.core.state.N.rules := by
    have member : q.law ∈ selectedRules s.core q.call.request := by simp [ruleSelection]
    exact (List.mem_filter.mp member).1
  have methodIn : q.method ∈ selectedTemplates s q.law := by simp [methodSelection]
  have transported := formula_refines (atomAssessment s q.law q.method)
    (q.world.assessment q.law q.method) q.law.guard
    (compatible.2 q.law lawIn q.method methodIn)
  rw [actual_formula_checker_assessment s q ruleSelection methodSelection policyIdentity j known]
    at transported
  exact transported

local instance {k : Nat} : MeasurableSpace (Fin k) := ⊤
local instance {k : Nat} : MeasurableSpace (List (Fin k)) := ⊤
local instance : MeasurableSpace Private := ⊤

/-- The whole formula's legal readouts and actual learned table are a joint
readout of the SAME original CN next-state kernel. -/
theorem formula_entity_feedback_law {k : Nat}
    [MeasurableSpace SixJudgments] [MeasurableSpace FourEffects]
    (initial : Situation) (catalog : Fin k → PackedCommand) (q : EntityQuery)
    (policy : ProbabilityTheory.Kernel (List (Fin k) × Private) (Fin k))
    [ProbabilityTheory.IsMarkovKernel policy] (h : List (Fin k)) :
    (LegalMath20261108.ClosedLoop.step (model initial catalog policy) (encode initial catalog h)).map
      (fun z => (formulaSixJudgments (replay initial catalog z.1) q,
        formulaFourEffects (replay initial catalog z.1) q,
        (replay initial catalog z.1).core.state.A.theta)) =
      (policy (encode initial catalog h)).map (fun a =>
        let post := (executeCommand (replay initial catalog h) (catalog a).2).after
        (formulaSixJudgments post q, formulaFourEffects post q, post.core.state.A.theta)) :=
  readout_kernel_transport initial catalog policy
    (fun post => (formulaSixJudgments post q, formulaFourEffects post q, post.core.state.A.theta)) h

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

/-- A real stored decision/binding post realizes the original canonical
semantic model, with actual rule/method/source selection. -/
theorem query_is_coherent : CoherentQuery bound query := by
  constructor
  · rfl
  · rfl
  · decide
  · rfl
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

theorem same_scope_is_not_same_question :
    faithAtom.scope = query.scope ∧ ¬ CoherentQuery bound {query with atom := faithAtom} := by
  refine ⟨rfl, ?_⟩
  intro coherent
  have different : confirmation.guard ≠ .atom faithAtom := by decide
  exact different coherent.questionIdentity

/-- The actual stored decision is matched to its complete rule question;
validity, binding, correctness and performance are distinct actual readouts. -/
theorem actual_stored_decision_formula :
    (formulaSixJudgments bound query).recognized = some .established ∧
    (formulaFourEffects bound query).validity = some true ∧
    (formulaFourEffects bound query).finality = .success true ∧
    (formulaFourEffects bound query).correctness = some true ∧
    (formulaFourEffects bound query).performance = [] := by decide

def compoundMethod : IssuedTemplate :=
  ⟨Examples.request .addTemplate, {Examples.template with clauses := (Examples.template.clauses.filter (fun clause => containsAtom clause.1 compensationLaw.guard))}⟩

def compoundQuery : EntityQuery where
  call := Examples.call .decide
  atom := toyAtom
  document := query.document
  person := query.person
  scope := toyScope
  time := query.time
  bindingKind := query.bindingKind
  law := compensationLaw
  method := compoundMethod
  world := canonicalWorld compensated.after toyWorld

/-- A real compound institutional question (including negation) consumes the
general bridge. Its formula is derived from the actual selected rule. -/
theorem compound_institution_same_question :
    selectedRules compensated.after.core compoundQuery.call.request = [compoundQuery.law] ∧
    selectedTemplates compensated.after compoundQuery.law = [compoundQuery.method] ∧
    (formulaSixJudgments compensated.after compoundQuery).justified = .known .established ∧
    evalFormula (compoundQuery.world.assessment compoundQuery.law compoundQuery.method)
      compoundQuery.law.guard = .established := by
  have laws : selectedRules compensated.after.core compoundQuery.call.request = [compoundQuery.law] := by rfl
  have methods : selectedTemplates compensated.after compoundQuery.law = [compoundQuery.method] := by rfl
  have identity : (compoundQuery.call.policy.scope != compoundQuery.law.scope ||
      compoundQuery.call.policy.source.id != compoundQuery.law.source.id ||
      compoundQuery.call.policy.source.version != compoundQuery.law.source.version) = false := by decide
  have checked : proofAt compensated.after compoundQuery.call compoundQuery.law.guard = .known .established := by decide
  have compatible : semanticCompatible compensated.after compoundQuery.world :=
    canonicalWorld_compatible compensated.after toyWorld
      (legalWorldCheck_sound compensated.after toyWorld (by decide))
  have semantic := selected_formula_refines_supported_world compensated.after compoundQuery
    laws methods identity compatible .established checked
  refine ⟨laws, methods, checked, ?_⟩
  rcases semantic with unknown | same
  · cases unknown
  · exact same.symm

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
#print axioms matched_decision_has_same_source
#print axioms formula_learnReport_legal_readouts
#print axioms actual_formula_checker_assessment
#print axioms selected_formula_refines_supported_world
#print axioms formula_entity_feedback_law
#print axioms Actual.query_is_coherent
#print axioms Actual.actual_proof_and_world_agree
#print axioms Actual.bare_query_counterexample
#print axioms Actual.same_scope_is_not_same_question
#print axioms Actual.actual_stored_decision_formula
#print axioms Actual.compound_institution_same_question

end
end LegalMath.RemainingClosure.EntitySemantics
