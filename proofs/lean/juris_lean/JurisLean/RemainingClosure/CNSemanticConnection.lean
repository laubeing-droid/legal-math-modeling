import JurisLean.RemainingClosure.FullEventLog
import JurisLean.RemainingClosure.ProcessTransport
import JurisLean.CN.Completion20261105.WorldSemantics
import JurisLean.CN.Completion20261105.Examples
import JurisLean.CN.Completion20261105.EngineExamples
import JurisLean.Candidates.CompilerProvenance20261027
import JurisLean.Candidates.CompilerOriginalBoundaries20261031

set_option autoImplicit false

/-!
Actual CN commands realize the existing ClosedLoop.Dynamics on their complete
ordered histories. The policy is any declared measurable kernel and reads the
actual updated private table. All legal, quantity and learning readouts use the
same replay. Source only; CI_NOT_RUN until subject-bound evidence exists.
-/
namespace LegalMath.RemainingClosure.CNSemanticConnection

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open LegalMath20261108.ClosedLoop
open JurisLean.KernelV3
open JurisLean.CN.Revision20261101
open JurisLean.CN.Completion20261105

noncomputable section

abbrev PackedCommand := FullEventLog.CN.PackedCommand
abbrev Private := List Rat

variable {k : Nat}
local instance : MeasurableSpace (Fin k) := ⊤
local instance : MeasurableSpace (List (Fin k)) := ⊤
local instance : MeasurableSpace Private := ⊤

def replay (initial : Situation) (catalog : Fin k → PackedCommand)
    (h : List (Fin k)) : Situation :=
  h.foldl (fun s a => FullEventLog.CN.advance s (catalog a)) initial

theorem replay_append (initial : Situation) (catalog : Fin k → PackedCommand)
    (h : List (Fin k)) (a : Fin k) :
    replay initial catalog (h ++ [a]) =
      (executeCommand (replay initial catalog h) (catalog a).2).after := by
  simp [replay, List.foldl_append, FullEventLog.CN.advance]

def encode (initial : Situation) (catalog : Fin k → PackedCommand)
    (h : List (Fin k)) : List (Fin k) × Private :=
  (h,(replay initial catalog h).core.state.A.theta)

/-- No legal meaning or arbitrary command payload is erased by a catalog.
The quantifier ranges over every finite actual command sequence. -/
theorem finite_sequence_catalog (commands : List PackedCommand) (initial : Situation) :
    replay initial (fun i : Fin commands.length => commands.get i)
      (List.finRange commands.length) = FullEventLog.CN.replay initial commands := by
  simp [replay, FullEventLog.CN.replay, ← List.foldl_map]

/-- The outcome is the completed command; its complete deterministic response
is reconstructed from the full payload and the current replay, never guessed
from a numeric summary. Randomness of the next command remains in policy. -/
def model (initial : Situation) (catalog : Fin k → PackedCommand)
    (policy : Kernel (List (Fin k) × Private) (Fin k)) :
    Dynamics (List (Fin k)) Private (Fin k) Unit Private where
  policy := policy
  outcome := Kernel.const _ (Measure.dirac ())
  append := fun h a _ => h ++ [a]
  measure := fun h _ _ => (replay initial catalog h).core.state.A.theta
  learn := fun _ actual => actual
  measurable_append :=
    (Measurable.of_discrete (f := fun z : List (Fin k) × Fin k => z.1 ++ [z.2])).comp
      (measurable_fst.prodMk measurable_snd.fst)
  measurable_measure :=
    (Measurable.of_discrete (f := fun h : List (Fin k) =>
      (replay initial catalog h).core.state.A.theta)).comp measurable_fst
  measurable_learn := measurable_snd

instance model_policy_markov (initial : Situation) (catalog : Fin k → PackedCommand)
    (policy : Kernel (List (Fin k) × Private) (Fin k)) [IsMarkovKernel policy] :
    IsMarkovKernel (model initial catalog policy).policy := by
  change IsMarkovKernel policy
  infer_instance

instance model_outcome_markov (initial : Situation) (catalog : Fin k → PackedCommand)
    (policy : Kernel (List (Fin k) × Private) (Fin k)) :
    IsMarkovKernel (model initial catalog policy).outcome := by
  dsimp [model]
  infer_instance

/-- One actual source post produces both the legal history and private table. -/
theorem actual_post_commutes (initial : Situation) (catalog : Fin k → PackedCommand)
    (policy : Kernel (List (Fin k) × Private) (Fin k)) (h : List (Fin k)) (a : Fin k) :
    update (model initial catalog policy) (encode initial catalog h,(a,())) =
      encode initial catalog (h ++ [a]) := by
  rfl

theorem actual_step_lintegral (initial : Situation) (catalog : Fin k → PackedCommand)
    (policy : Kernel (List (Fin k) × Private) (Fin k)) [IsMarkovKernel policy]
    (h : List (Fin k)) (f : (List (Fin k) × Private) → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ s, f s ∂step (model initial catalog policy) (encode initial catalog h) =
      ∫⁻ a, f (encode initial catalog (h ++ [a])) ∂policy (encode initial catalog h) := by
  rw [LegalMath20261108.ClosedLoop.step_lintegral _ _ _ hf]
  simp [model, Kernel.const_apply, update, historyOut, parameterOut, feedback, encode]

/-- The actual transition law is the pushforward of the SAME policy, including
nonconstant policies that depend on the current private table. -/
theorem actual_step_law (initial : Situation) (catalog : Fin k → PackedCommand)
    (policy : Kernel (List (Fin k) × Private) (Fin k)) [IsMarkovKernel policy]
    (h : List (Fin k)) :
    step (model initial catalog policy) (encode initial catalog h) =
      (policy (encode initial catalog h)).map (fun a => encode initial catalog (h ++ [a])) := by
  ext B hB
  have indicator : Measurable (B.indicator (1 : (List (Fin k) × Private) → ℝ≥0∞)) :=
    (measurable_const : Measurable (fun _ : List (Fin k) × Private => (1 : ℝ≥0∞))).indicator hB
  have transported := actual_step_lintegral initial catalog policy h (B.indicator 1) indicator
  calc
    step (model initial catalog policy) (encode initial catalog h) B =
        ∫⁻ s, B.indicator 1 s ∂step (model initial catalog policy) (encode initial catalog h) :=
      (lintegral_indicator_one hB).symm
    _ = ∫⁻ a, B.indicator 1 (encode initial catalog (h ++ [a]))
        ∂policy (encode initial catalog h) := transported
    _ = (policy (encode initial catalog h)).map
        (fun a => encode initial catalog (h ++ [a])) B := by
      rw [Measure.map_apply Measurable.of_discrete hB]
      simpa only [Set.indicator_apply] using
        (lintegral_indicator_one
          ((Measurable.of_discrete : Measurable (fun a : Fin k => encode initial catalog (h ++ [a]))) hB)
          (μ := policy (encode initial catalog h)))

/-- The next command law reads the actual post-history AND actual learned table. -/
theorem next_action_reads_actual_post (initial : Situation) (catalog : Fin k → PackedCommand)
    (policy : Kernel (List (Fin k) × Private) (Fin k)) [IsMarkovKernel policy]
    (h : List (Fin k)) {B : Set (Fin k)} (hB : MeasurableSet B) :
    nextAction (model initial catalog policy) (encode initial catalog h) B =
      ∫⁻ a, policy (h ++ [a],
        (executeCommand (replay initial catalog h) (catalog a).2).after.core.state.A.theta) B
        ∂policy (encode initial catalog h) := by
  rw [nextAction, Kernel.comp_apply' _ _ _ hB]
  change (∫⁻ s, policy s B ∂step (model initial catalog policy) (encode initial catalog h)) = _
  rw [actual_step_lintegral initial catalog policy h _ (Kernel.measurable_coe policy hB)]
  simp only [encode, replay_append]

/-- Every legal/quantity/learning readout is transported from the SAME actual
post. No readout is resampled independently from its marginal. -/
theorem readout_kernel_transport {V : Type*} [MeasurableSpace V]
    (initial : Situation) (catalog : Fin k → PackedCommand)
    (policy : Kernel (List (Fin k) × Private) (Fin k)) [IsMarkovKernel policy]
    (read : Situation → V) (h : List (Fin k)) :
    (step (model initial catalog policy) (encode initial catalog h)).map
      (fun s => read (replay initial catalog s.1)) =
    (policy (encode initial catalog h)).map
      (fun a => read (executeCommand (replay initial catalog h) (catalog a).2).after) := by
  rw [actual_step_law]
  have outer : Measurable (fun s : List (Fin k) × Private => read (replay initial catalog s.1)) :=
    (Measurable.of_discrete (f := fun h : List (Fin k) => read (replay initial catalog h))).comp measurable_fst
  rw [Measure.map_map (g := fun s : List (Fin k) × Private => read (replay initial catalog s.1))
    (f := fun a : Fin k => encode initial catalog (h ++ [a])) outer Measurable.of_discrete]
  congr 1
  funext a
  simp [encode, replay_append]

/-- The encoded history is faithful even when two histories have equal money. -/
theorem encode_injective (initial : Situation) (catalog : Fin k → PackedCommand) :
    Function.Injective (encode initial catalog) := by
  intro a b h
  exact congrArg Prod.fst h

/-- An actual legal success reuses the approved-method/all-supported-worlds
proof at the very same state used by the feedback process. -/
theorem actual_legal_step_worlds (initial : Situation) (catalog : Fin k → PackedCommand)
    (h : List (Fin k)) (c : Law.Call)
    (success : (executeCommand (replay initial catalog h) (.legal c)).answer = .success ()) :
    ∃ law t, law ∈ (replay initial catalog h).core.state.N.rules ∧
      WorldReady (replay initial catalog h) law t :=
  actual_legal_step_semantic_ready _ c.request c.policy c.mode c.world success

/-- Legal rules, facts and relations are framed by the actual retained-report
learning consumer, rather than by an unrelated private-parameter update. -/
theorem actual_learning_frame (initial : Situation) (catalog : Fin k → PackedCommand)
    (h : List (Fin k)) (request : Request) (material : Ref .material) :
    (executeCommand (replay initial catalog h) (.learnReport request material)).after.core.state.N =
      (replay initial catalog h).core.state.N ∧
    (executeCommand (replay initial catalog h) (.learnReport request material)).after.core.state.F =
      (replay initial catalog h).core.state.F ∧
    (executeCommand (replay initial catalog h) (.learnReport request material)).after.core.state.L =
      (replay initial catalog h).core.state.L :=
  learnReport_frame _ request material

/-- Reading a retained report is a real definition, not a fit-risk conclusion
smuggled into a transport premise. The fit/RSI instances below compute it. -/
theorem learn_retained_actual_table (s : Situation) (r : Request) (id : Ref .material)
    (report : EngineReport) (table : List Rat)
    (fresh : freshRequest s r = true) (kind : r.act = .learnModel)
    (found : s.engineResults.find? (fun row => row.material.id == id) = some report)
    (allowed : engineMaterialAllowed s ⟨r.scope,report.material.target⟩ report.material = true)
    (decoded : learnedTable report = some table) :
    (learnReport s r id).after.core.state.A.theta = table := by
  simp [learnReport, fresh, kind, found, allowed, decoded, Situation.withCore, CaseState.putState]


/-- Parameters choose the legally supplied question and interpretation, never
an empirical score in place of the approved legal method. -/
structure EntityQuery where
  call : Law.Call
  atom : Atom
  document : Ref .document
  person : Ref .actor
  scope : Scope
  time : Nat
  bindingKind : DecideKind
  law : Rule
  method : IssuedTemplate
  world : SemanticWorld

def recordedDecision (s : Situation) (q : EntityQuery) : Option DecisionRecord :=
  s.core.state.decisions.find? (fun d =>
    d.document == q.document && d.request.scope == q.scope)

def bindingReadout (s : Situation) (q : EntityQuery) : Answer Bool :=
  match s.core.state.bindings.filterMap (fun b => match b with
    | .decide d => if d.decision.document == q.document && d.kind == q.bindingKind then
        some d.index else none
    | .other _ => none) with
  | [] => .unknown .inputUnchecked
  | indices => .success (indices.any (fun i => withinBinding i q.person q.scope q.time))

/-- Different value types preserve the six distinctions of v4 section 2.3. -/
structure SixJudgments where
  truth : Bool
  support : Judgment
  justified : Check Judgment
  recognized : Option Judgment
  valid : Option Bool
  binding : Answer Bool

def sixJudgments (s : Situation) (q : EntityQuery) : SixJudgments :=
  ⟨q.world.nature.fact q.atom,
   support (admittedView s.core.state.E q.law.materials) q.atom,
   proofAt s q.call (.atom q.atom),
   (recordedDecision s q).map (fun d => d.judgment),
   (recordedDecision s q).map (fun d => d.valid),
   bindingReadout s q⟩

/-- Validity, finality, correctness and actual performance are separate
coordinates, computed from the same source object and legal-world reading. -/
structure FourEffects where
  validity : Option Bool
  finality : Answer Bool
  correctness : Option Bool
  performance : List Performance

def fourEffects (s : Situation) (q : EntityQuery) : FourEffects :=
  ⟨(recordedDecision s q).map (fun d => d.valid),
   bindingReadout s {q with bindingKind := .resJudicata},
   (recordedDecision s q).bind (fun d =>
     match evalFormula (q.world.assessment q.law q.method) (.atom q.atom) with
     | .undetermined => none
     | expected => some (d.judgment == expected)),
   s.core.state.ledger.filter (fun entry => entry.request.scope == q.scope)⟩

def legalPermission (s : Situation) (q : EntityQuery) : Prop :=
  (permissionDispatch s q.call.request q.call.policy q.call.mode q.call.world).answer = .success ()

/-- This joint readout preserves correlations of entity, operation, quantity
and learning. It is one map, not a product of separately chosen marginal laws. -/
def jointLegalReadout (initial : Situation) (catalog : Fin k → PackedCommand)
    (q : EntityQuery) (s : List (Fin k) × Private) :
    SixJudgments × FourEffects × Private :=
  (sixJudgments (replay initial catalog s.1) q,
   fourEffects (replay initial catalog s.1) q,
   (replay initial catalog s.1).core.state.A.theta)

/-- Every entity coordinate uses the same h, N and supplied legal interpretation.
The measurable statement is derived from the countable complete-history carrier. -/
theorem measurable_joint_legal_readout (initial : Situation)
    (catalog : Fin k → PackedCommand) (q : EntityQuery)
    [MeasurableSpace SixJudgments] [MeasurableSpace FourEffects] :
    Measurable (jointLegalReadout initial catalog q) :=
  (Measurable.of_discrete (f := fun h : List (Fin k) =>
    (sixJudgments (replay initial catalog h) q,
     fourEffects (replay initial catalog h) q,
     (replay initial catalog h).core.state.A.theta))).comp measurable_fst

/-- The full joint legal readout consumes the already proved actual kernel
transport, so separate legal and numerical proof islands are not substituted. -/
theorem legal_entity_feedback_law (initial : Situation)
    (catalog : Fin k → PackedCommand) (q : EntityQuery)
    [MeasurableSpace SixJudgments] [MeasurableSpace FourEffects]
    (policy : Kernel (List (Fin k) × Private) (Fin k)) [IsMarkovKernel policy]
    (h : List (Fin k)) :
    (step (model initial catalog policy) (encode initial catalog h)).map
      (jointLegalReadout initial catalog q) =
    (policy (encode initial catalog h)).map (fun a =>
      let post := (executeCommand (replay initial catalog h) (catalog a).2).after
      (sixJudgments post q, fourEffects post q, post.core.state.A.theta)) :=
  readout_kernel_transport initial catalog policy
    (fun post => (sixJudgments post q,fourEffects post q,post.core.state.A.theta)) h

/-- Authoritative norm/fact/relation/decision/binding coordinates are framed by
private learning; the current table changes, and the following policy may change. -/
theorem learnReport_entity_frame (s : Situation) (r : Request) (id : Ref .material) :
    (learnReport s r id).after.core.state.N = s.core.state.N ∧
    (learnReport s r id).after.core.state.F = s.core.state.F ∧
    (learnReport s r id).after.core.state.L = s.core.state.L ∧
    (learnReport s r id).after.core.state.E = s.core.state.E ∧
    (learnReport s r id).after.core.state.decisions = s.core.state.decisions ∧
    (learnReport s r id).after.core.state.bindings = s.core.state.bindings ∧
    (learnReport s r id).after.core.state.ledger = s.core.state.ledger := by
  unfold learnReport
  split
  · exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩
  · split
    · exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩
    · split
      · split <;> exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩
      · exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩


/-- A one-command instance is a projection of the very same Dynamics.update.
The generic model above also admits arbitrary nonconstant random policies. -/
def representedReply {α : Type} (initial : Situation) (command : Command α) : Reply α :=
  let catalog : Fin 1 → PackedCommand := fun _ => ⟨α,command⟩
  let policy : Kernel (List (Fin 1) × Private) (Fin 1) := Kernel.const _ (Measure.dirac 0)
  let actual := update (model initial catalog policy) (encode initial catalog [],(0,()))
  ⟨replay initial catalog actual.1,(executeCommand initial command).answer⟩

theorem representedReply_eq {α : Type} (initial : Situation) (command : Command α) :
    representedReply initial command = executeCommand initial command := by
  rfl

namespace Institutions
open InstitutionRules Examples

/-- Existing nonjudicial formation is consumed by the common feedback post. -/
theorem formation_feedback :
    (representedReply (readyCase toyRule .lifecycle) (.legal (call .constitute))).after.core.state.L = [toyRelation] ∧
    (representedReply (readyCase toyRule .lifecycle) (.legal (call .constitute))).after.core.state.decisions = [] ∧
    (representedReply (readyCase toyRule .lifecycle) (.legal (call .constitute))).after.core.state.bindings.isEmpty = true := by
  simpa only [representedReply_eq, formedCase, Examples.advance] using actual_nonjudicial_formation

theorem lifecycle_feedback :
    (representedReply revokeStart (.institution (.revoke (call .constitute) (.atom toyAtom)
      toyScope.object revokeGuard))).after.core.state.L = [] ∧
    (representedReply revokeStart (.institution (.revoke (call .constitute) (.atom toyAtom)
      toyScope.object revokeGuard))).after.core.state.F = revokeStart.core.state.F ∧
    (representedReply revokeStart (.institution (.revoke (call .constitute) (.atom toyAtom)
      toyScope.object {revokeGuard with atTime := 100}))).after.core.state.L = revokeStart.core.state.L := by
  simp only [representedReply_eq]
  exact ⟨lifecycle_actual.2.2.2.2.1,lifecycle_actual.2.2.2.2.2,lifecycle_failure_preserves_effect⟩

theorem agency_feedback :
    (representedReply agencyStart (.institution (.delegate (call .constitute) (.atom toyAtom)
      toyScope.object child))).after.core.state.N.grants.contains child = true ∧
    ((representedReply agencyStart (.institution (.delegate (call .constitute) (.atom toyAtom)
      toyScope.object child))).after.agencies toyScope.object).map Agency.principalCapacity = some true ∧
    (representedReply agencyStart (.institution (.delegate (call .constitute) (.atom toyAtom)
      toyScope.object {child with stop := 100}))).after.core.state.N.grants = agencyStart.core.state.N.grants := by
  simp only [representedReply_eq]
  exact ⟨agency_actual.1,agency_actual.2,agency_over_scope_rejected⟩

theorem jurisdiction_feedback :
    (representedReply normal (.institution (.jurisdiction true
      ⟨true,false,false,false,false,false,false,true⟩))).answer = .success (some .ordinary) ∧
    (representedReply normal (.institution (.jurisdiction true
      ⟨true,true,false,false,false,false,true,true⟩))).answer = .success none := by
  simpa only [representedReply_eq] using jurisdiction_actual

theorem evidence_feedback :
    (representedReply (recordedCase confirmation .evidence)
      (.burdenEvidence (call .decide) (.atom toyAtom))).answer = .unknown .inputUnchecked ∧
    (representedReply normal (.burdenEvidence (call .decide) (.atom toyAtom))).answer = .success .established ∧
    (representedReply withdrawnCase (.burdenEvidence (call .decide) (.atom toyAtom))).answer = .unknown .inputUnchecked ∧
    rawOf (withdrawnCase.core.state.E ⟨9⟩) = some toyRaw := by
  simpa only [representedReply_eq] using
    And.intro evidence_actual.1 (And.intro evidence_actual.2.1
      (And.intro evidence_actual.2.2.1 evidence_actual.2.2.2.1))

theorem acquisition_feedback :
    (representedReply acquisitionStart (.acquisitionEvidence (call .decide) parties .ordinary311
      faithAtom priceAtom publicityAtom)).answer = .success .established ∧
    (representedReply badFaithStart (.acquisitionEvidence (call .decide) parties .ordinary311
      faithAtom priceAtom publicityAtom)).answer = .success .notEstablished ∧
    (representedReply acquisitionStart (.acquisitionEvidence (call .decide) parties .lost312
      faithAtom priceAtom publicityAtom)).answer = .unknown .systemNotJudge := by
  simpa only [representedReply_eq] using acquisition_actual

theorem offense_feedback :
    (representedReply (offenseStart aYi) (.offenseEvidence (call .decide) aYi ev1 q1
      toyAtom toyAtom)).answer = .success toyScope.question ∧
    (representedReply (offenseStart aYi) (.offenseEvidence (call .decide) aYi ev2 q1
      toyAtom toyAtom)).answer = .unknown .inputUnchecked := by
  simpa only [representedReply_eq] using offense_actual

def feedbackAccepted : Situation :=
  (representedReply bankruptcyStart
    (.institution (.bankruptcy (call .decide) (.atom toyAtom) ⟨0,some 0⟩ aD))).after

theorem bankruptcy_feedback :
    feedbackAccepted.stayed = [procD.id] ∧
    feedbackAccepted.bankruptcyCases aD = some 0 ∧
    feedbackAccepted.bankruptcyCases aO = none ∧
    (representedReply feedbackAccepted
      (.institution (.interest (call .decide) (.atom toyAtom) interestClaim 20))).answer = .success 0 := by
  simpa only [feedbackAccepted,representedReply_eq,accepted,interestResult,Examples.advance] using
    And.intro bankruptcy_actual.1 (And.intro bankruptcy_actual.2.1
      (And.intro bankruptcy_actual.2.2.1 bankruptcy_actual.2.2.2.1))

theorem compensation_feedback :
    (representedReply compensationStart (.institution (.compensation (call .decide)
      compensationLaw.guard .criminal ⟨62⟩))).after.tracks.stateCompensation = [(.criminal,⟨62⟩)] ∧
    (representedReply compensationStart (.institution (.compensation (call .decide)
      compensationLaw.guard .criminal ⟨62⟩))).after.tracks.civil = [] ∧
    (representedReply noTermination (.institution (.compensation (call .decide)
      compensationLaw.guard .criminal ⟨62⟩))).answer = .unknown .inputUnchecked := by
  simp only [representedReply_eq]
  exact ⟨compensation_actual.1,compensation_actual.2.1,compensation_missing_prerequisite_not_automatic⟩

theorem rights_feedback :
    (representedReply normal (.institution .rightsConflict)).answer = .conflict .competentReview ∧
    (representedReply normal (.institution .rightsConflict)).after.core.state.L = normal.core.state.L := by
  simpa only [representedReply_eq] using rights_actual

def feedbackInterpreted : Situation :=
  (representedReply (readyCase confirmation .interpretation)
    (.institution (.interpret (call .decide) (.atom toyAtom) toyScope.object (.known (.atom toyAtom))))).after

theorem interpretation_feedback :
    (representedReply feedbackInterpreted (.contractQuery (call .decide) toyScope.object)).answer =
      .success .established ∧
    feedbackInterpreted.core.state.N.version = 1 ∧ feedbackInterpreted.meanings ⟨999⟩ = none := by
  simpa only [feedbackInterpreted,representedReply_eq,interpreted,Examples.advance] using interpretation_actual

def feedbackBound : Situation :=
  (representedReply decisionCase (.bindDecided decisionBinding .human)).after

theorem resJudicata_feedback :
    (representedReply feedbackBound (.storedResJudicata ⟨70⟩ ⟨12⟩ toyScope 5)).answer = .success true ∧
    (representedReply feedbackBound (.storedResJudicata ⟨70⟩ ⟨99⟩ toyScope 5)).answer = .success false ∧
    (representedReply feedbackBound (.storedResJudicata ⟨70⟩ ⟨12⟩ toyScope 11)).answer = .success false ∧
    (representedReply feedbackBound
      (.storedResJudicata ⟨70⟩ ⟨12⟩ {toyScope with question := ⟨999⟩} 5)).answer = .success false := by
  simpa only [feedbackBound,representedReply_eq,bound,Examples.advance] using resJudicata_actual

theorem proposal_feedback :
    (representedReply normal (.institution (.propose fitOut))).after.core.state.candidates.length = 1 ∧
    (representedReply normal (.institution (.propose fitOut))).after.core.state.decisions = [] ∧
    (representedReply normal (.institution (.propose fitOut))).after.core.state.bindings.isEmpty = true := by
  simpa only [representedReply_eq] using proposal_actual

end Institutions


namespace Engines

def material (s : Situation) (c : EngineContext) (id : Ref .material)
    (source : Ref .document) (call : EngineCall) : EngineMaterial :=
  ⟨id,c.scope,c.target,source,s.core.state.N.version,call⟩

/-- The stored native report is read from the same post that the feedback
kernel transports. It is not a numerical calculation performed beside it. -/
theorem retained_call (s : Situation) (c : EngineContext) (id : Ref .material)
    (input : EngineMaterial)
    (lookup : s.engineInputs.filter (fun row => row.id == id) = [input])
    (allowed : engineMaterialAllowed s c input = true) :
    (representedReply s (.engine c id)).after.engineResults.head? =
      some ⟨input,(callEngine s c input.input).native⟩ := by
  simpa only [representedReply_eq,executeCommand] using
    (bound_engine_calls_stored_input s c id input lookup allowed).2.2

theorem fit_feedback {m n : Nat} (s : Situation) (c : EngineContext)
    (id : Ref .material) (source : Ref .document)
    (protocol : Native.Fit.LearningProtocol) (loss : ℚ → Bool → ℚ)
    (models : List (List ℚ)) (data : Fin n → Fin m × Bool) (out : Native.Fit.FittedTable)
    (lookup : s.engineInputs.filter (fun row => row.id == id) =
      [material s c id source (.fit m n protocol loss models data)])
    (allowed : engineMaterialAllowed s c (material s c id source (.fit m n protocol loss models data)) = true)
    (actual : Native.Fit.fitTable protocol loss models data = .known out) :
    (representedReply s (.engine c id)).after.engineResults.head? =
      some ⟨material s c id source (.fit m n protocol loss models data),.known out⟩ ∧
    out.protocol = protocol ∧ out.sampleSize = n ∧ out.table ∈ models ∧
    ∀ table ∈ models,
      JurisLean.Candidates.LearningERM20261027.empiricalScore (Native.Fit.tableLoss loss) data out.table ≤
      JurisLean.Candidates.LearningERM20261027.empiricalScore (Native.Fit.tableLoss loss) data table := by
  have keep := retained_call s c id _ lookup allowed
  have evaluated : (callEngine s c (.fit m n protocol loss models data)).native = .known out := actual
  have head : (representedReply s (.engine c id)).after.engineResults.head? =
      some ⟨material s c id source (.fit m n protocol loss models data),.known out⟩ := by
    change (representedReply s (.engine c id)).after.engineResults.head? =
      some ⟨material s c id source (.fit m n protocol loss models data),.known out⟩
    simpa only [material,evaluated] using keep
  have fitted := fit_uses_actual_sample s c protocol loss models data out actual
  exact ⟨head,fitted.1,fitted.2.1,fitted.2.2.2.1,fitted.2.2.2.2.2⟩

theorem probability_feedback {n : Nat} (s : Situation) (c : EngineContext)
    (id : Ref .material) (source : Ref .document)
    (prior : Native.Prob.FiniteLaw (Fin n)) (likelihood : Fin n → ℚ)
    (event : Fin n → Ref .event) (post : Native.Prob.FiniteLaw (Fin n))
    (lookup : s.engineInputs.filter (fun row => row.id == id) =
      [material s c id source (.prob n prior likelihood event)])
    (allowed : engineMaterialAllowed s c (material s c id source (.prob n prior likelihood event)) = true)
    (actual : (consumeProb s c prior likelihood event).native = .known post) :
    (representedReply s (.engine c id)).after.engineResults.head? =
      some ⟨material s c id source (.prob n prior likelihood event),.known post⟩ ∧
    ∀ w, post.mass w = prior.mass w * likelihood w / Native.Prob.expectation prior likelihood := by
  have keep := retained_call s c id _ lookup allowed
  have evaluated : (callEngine s c (.prob n prior likelihood event)).native = .known post := actual
  refine ⟨?_,probability_uses_actual_posterior s c prior likelihood event post actual⟩
  simpa only [material,evaluated] using keep

theorem causal_feedback {n l : Nat} (s : Situation) (c : EngineContext)
    (id : Ref .material) (source : Ref .document) (x : CausalInput n l) (permit : Option CausalPermit)
    (lookup : s.engineInputs.filter (fun row => row.id == id) =
      [material s c id source (.causal n l x permit)])
    (allowed : engineMaterialAllowed s c (material s c id source (.causal n l x permit)) = true)
    (support : x.supported = true) :
    (representedReply s (.engine c id)).after.engineResults.head? =
      some ⟨material s c id source (.causal n l x permit),(consumeCausal s c x permit).native⟩ ∧
    x.recovered true - x.recovered false =
      Native.Causal.interventionValue x.mass.mass (fun i => (x.latent i).mass) x.response true -
      Native.Causal.interventionValue x.mass.mass (fun i => (x.latent i).mass) x.response false := by
  refine ⟨retained_call s c id _ lookup allowed,causal_actual_identified_value x support⟩

theorem bargain_feedback {n : Nat} (s : Situation) (c : EngineContext)
    (id : Ref .material) (source : Ref .document)
    (score : Fin n → ℚ) (permitted : Fin n → Bool) (options : List (Fin n))
    (offer : Fin n → List (Ref .actor × Quantity .money)) (out : Fin n)
    (lookup : s.engineInputs.filter (fun row => row.id == id) =
      [material s c id source (.bargain n score permitted options offer)])
    (allowed : engineMaterialAllowed s c (material s c id source (.bargain n score permitted options offer)) = true)
    (actual : (consumeBargain s c score permitted options offer).native = .known out) :
    (representedReply s (.engine c id)).after.engineResults.head? =
      some ⟨material s c id source (.bargain n score permitted options offer),.known out⟩ ∧
    out ∈ options ∧ permitted out = true ∧
      ∀ other ∈ options, permitted other = true → score other ≤ score out := by
  have keep := retained_call s c id _ lookup allowed
  have evaluated : (callEngine s c (.bargain n score permitted options offer)).native = .known out := actual
  refine ⟨?_,bargain_actual_allowed_maximum s c score permitted options offer out actual⟩
  simpa only [material,evaluated] using keep

theorem cash_feedback (s : Situation) (c : EngineContext) (id : Ref .material)
    (source : Ref .document) (before : Native.Cash.State) (payment : Native.PaymentPayload)
    (out : Native.Cash.State)
    (lookup : s.engineInputs.filter (fun row => row.id == id) =
      [material s c id source (.cash before payment)])
    (allowed : engineMaterialAllowed s c (material s c id source (.cash before payment)) = true)
    (actual : (consumeCash s c before payment).native = .known out) :
    (representedReply s (.engine c id)).after.engineResults.head? =
      some ⟨material s c id source (.cash before payment),.known out⟩ ∧
    Native.Cash.Conserves out ∧ Native.Cash.CashConsistent out := by
  have keep := retained_call s c id _ lookup allowed
  have evaluated : (callEngine s c (.cash before payment)).native = .known out := actual
  refine ⟨?_,cash_actual_post_conserves s c before payment out actual⟩
  simpa only [material,evaluated] using keep

theorem exact_feedback (s : Situation) (c : EngineContext) (id : Ref .material)
    (source : Ref .document) (unit : UnitKind) (left right out : Native.Decision.TypedValue)
    (lookup : s.engineInputs.filter (fun row => row.id == id) =
      [material s c id source (.exact unit left right)])
    (allowed : engineMaterialAllowed s c (material s c id source (.exact unit left right)) = true)
    (actual : (consumeExact s c unit left right).native = .known out) :
    (representedReply s (.engine c id)).after.engineResults.head? =
      some ⟨material s c id source (.exact unit left right),.known out⟩ ∧
    Native.Decision.Evaluates out.expr (Native.Decision.evalExact out.expr) := by
  have keep := retained_call s c id _ lookup allowed
  have evaluated : (callEngine s c (.exact unit left right)).native = .known out := actual
  refine ⟨?_,exact_native_meaning out⟩
  simpa only [material,evaluated] using keep

/-- The behavioral optimizer can prefer a prohibited action; this is a
computed behavioral consequence and is never turned into legal permission. -/
theorem behavior_actual_selected (s : Situation) (c : EngineContext) (threshold : ℚ)
    (actor : Ref .actor) (action : Fin 3 → Ref .query) (out : Fin 3)
    (h0 : 0 < threshold) (h1 : threshold ≤ 1)
    (actual : (consumeBehavior s c threshold actor action).native = .known out) : out = 2 := by
  change behaviorSource threshold = .known out at actual
  unfold behaviorSource at actual
  rw [if_pos ⟨h0,h1⟩] at actual
  cases selected : Native.Decision.best (Native.Response.preparationUtility threshold) [0,1,2] with
  | none => simp [selected] at actual
  | some best =>
      simp only [selected] at actual
      have equal : best = out := by injection actual
      subst out
      by_contra different
      have strictly := behavior_model_does_not_filter_illegal_action threshold h0 h1 best different
      have maximal := Native.Decision.best_dominates
        (Native.Response.preparationUtility threshold) selected 2 (by simp)
      exact (not_lt_of_ge maximal) strictly

theorem behavior_feedback (s : Situation) (c : EngineContext) (id : Ref .material)
    (source : Ref .document) (threshold : ℚ) (actor : Ref .actor)
    (action : Fin 3 → Ref .query) (out : Fin 3)
    (lookup : s.engineInputs.filter (fun row => row.id == id) =
      [material s c id source (.behavior threshold actor action)])
    (allowed : engineMaterialAllowed s c (material s c id source (.behavior threshold actor action)) = true)
    (h0 : 0 < threshold) (h1 : threshold ≤ 1)
    (actual : (consumeBehavior s c threshold actor action).native = .known out) :
    (representedReply s (.engine c id)).after.engineResults.head? =
      some ⟨material s c id source (.behavior threshold actor action),.known out⟩ ∧ out = 2 := by
  have keep := retained_call s c id _ lookup allowed
  have evaluated : (callEngine s c (.behavior threshold actor action)).native = .known out := actual
  refine ⟨?_,behavior_actual_selected s c threshold actor action out h0 h1 actual⟩
  simpa only [material,evaluated] using keep

theorem rsi_feedback {m : Nat} (s : Situation) (c : EngineContext)
    (id : Ref .material) (source : Ref .document) (before : Native.RSI.RoundState m)
    (request : Native.RSI.RoundRequest m) (samples : List (Native.RSI.SamplingReceipt m))
    (permits : List (Native.RSI.LoadPermit m)) (proposal : Ref .model)
    (lookup : s.engineInputs.filter (fun row => row.id == id) =
      [material s c id source (.rsi m before request samples permits proposal)])
    (allowed : engineMaterialAllowed s c (material s c id source (.rsi m before request samples permits proposal)) = true)
    (budget : Native.RSI.roundSpent before ≤ before.limit) :
    (representedReply s (.engine c id)).after.engineResults.head? =
      some ⟨material s c id source (.rsi m before request samples permits proposal),
        (consumeRSI s c before request samples permits proposal).native⟩ ∧
    Native.RSI.roundSpent (consumeRSI s c before request samples permits proposal).native.post ≤ before.limit :=
  ⟨retained_call s c id _ lookup allowed,
    rsi_actual_post_budget s c before request samples permits proposal budget⟩


lemma actual_head_is_found (s : Situation) (id : Ref .material) (report : EngineReport)
    (head : s.engineResults.head? = some report) (key : report.material.id = id) :
    s.engineResults.find? (fun row => row.material.id == id) = some report := by
  cases entries : s.engineResults with
  | nil => simp [entries] at head
  | cons first rest =>
      simp only [entries,List.head?_cons,Option.some.injEq] at head
      subst first
      simp [entries,key]

/-- The actual native ERM table is retained, read under the existing legal
consumer guards, loaded into the same private coordinate and framed from law.
The request guards below are exactly those in learnReport, not a risk bound or
an assumed commutation equation. -/
theorem fit_to_private_feedback {m n : Nat} (s : Situation) (c : EngineContext)
    (id : Ref .material) (source : Ref .document)
    (protocol : Native.Fit.LearningProtocol) (loss : ℚ → Bool → ℚ)
    (models : List (List ℚ)) (data : Fin n → Fin m × Bool) (out : Native.Fit.FittedTable)
    (r : Request)
    (lookup : s.engineInputs.filter (fun row => row.id == id) =
      [material s c id source (.fit m n protocol loss models data)])
    (allowed : engineMaterialAllowed s c (material s c id source (.fit m n protocol loss models data)) = true)
    (actual : Native.Fit.fitTable protocol loss models data = .known out)
    (fresh : freshRequest (representedReply s (.engine c id)).after r = true)
    (kind : r.act = .learnModel)
    (sourceBound : engineMaterialAllowed (representedReply s (.engine c id)).after
      ⟨r.scope,c.target⟩ (material s c id source (.fit m n protocol loss models data)) = true) :
    (representedReply (representedReply s (.engine c id)).after
      (.learnReport r id)).after.core.state.A.theta = out.table ∧
    (representedReply (representedReply s (.engine c id)).after
      (.learnReport r id)).after.core.state.N = (representedReply s (.engine c id)).after.core.state.N ∧
    (representedReply (representedReply s (.engine c id)).after
      (.learnReport r id)).after.core.state.F = (representedReply s (.engine c id)).after.core.state.F ∧
    (representedReply (representedReply s (.engine c id)).after
      (.learnReport r id)).after.core.state.L = (representedReply s (.engine c id)).after.core.state.L ∧
    ∀ table ∈ models,
      JurisLean.Candidates.LearningERM20261027.empiricalScore (Native.Fit.tableLoss loss) data out.table ≤
      JurisLean.Candidates.LearningERM20261027.empiricalScore (Native.Fit.tableLoss loss) data table := by
  have fit := fit_feedback s c id source protocol loss models data out lookup allowed actual
  have found := actual_head_is_found (representedReply s (.engine c id)).after id
    ⟨material s c id source (.fit m n protocol loss models data),.known out⟩ fit.1 rfl
  have learned := learn_retained_actual_table (representedReply s (.engine c id)).after r id
    ⟨material s c id source (.fit m n protocol loss models data),.known out⟩ out.table
    fresh kind found sourceBound rfl
  have frames := learnReport_frame (representedReply s (.engine c id)).after r id
  simp only [representedReply_eq,executeCommand] at learned frames ⊢
  exact ⟨learned,frames.1,frames.2.1,frames.2.2,fit.2.2.2.2⟩

/-- Successful RSI feedback reads the actual Loaded object's table. Rejected,
unevaluated, key-conflicting and not-loaded branches do not supply this table. -/
theorem rsi_loaded_report_table {m : Nat} (s : Situation) (c : EngineContext)
    (id : Ref .material) (source : Ref .document) (before : Native.RSI.RoundState m)
    (request : Native.RSI.RoundRequest m) (samples : List (Native.RSI.SamplingReceipt m))
    (permits : List (Native.RSI.LoadPermit m)) (proposal : Ref .model)
    (evaluated : (consumeRSI s c before request samples permits proposal).native.status = .evaluated)
    (loaded : ((consumeRSI s c before request samples permits proposal).native.receipt.bind
      (fun record => record.load)).any (fun load => load.status == .loaded) = true) :
    learnedTable ⟨material s c id source (.rsi m before request samples permits proposal),
      (consumeRSI s c before request samples permits proposal).native⟩ =
      some (consumeRSI s c before request samples permits proposal).native.post.service.loaded.fitted.table := by
  simp [learnedTable,material,evaluated,loaded]

end Engines


namespace CompilerBridge
open JurisLean.Candidates.Final20261021.Compiler

/-- Negative literals are explicit values, never failure to derive a positive. -/
abbrev SignedFormula := Formula × Bool
abbrev CRule := JurisLean.Candidates.Final20261021.Compiler.Rule Nat

def signedHolds (v : Atom → Judgment) (literal : SignedFormula) : Prop :=
  evalFormula v literal.1 = if literal.2 then .established else .notEstablished

theorem explicit_negative_iff (v : Atom → Judgment) (f : Formula) :
    signedHolds v (f,false) ↔ evalFormula v (.neg f) = .established := by
  cases h : evalFormula v f <;> simp [signedHolds,evalFormula,h,notJ]

theorem missing_support_is_not_negation (a : Atom) :
    ¬ signedHolds (fun _ => .undetermined) (.atom a,true) ∧
    ¬ signedHolds (fun _ => .undetermined) (.atom a,false) := by
  simp [signedHolds,evalFormula]

lemma signed_refines (v z : Atom → Judgment) (literal : SignedFormula)
    (refines : ∀ a, Refines (v a) (z a)) (seed : signedHolds v literal) :
    signedHolds z literal := by
  rcases literal with ⟨f,polarity⟩
  have formula := formula_refines v z f refines
  cases polarity <;> dsimp [signedHolds] at seed ⊢
  all_goals
    rw [seed] at formula
    rcases formula with impossible | equal
    · cases impossible
    · exact equal.symm

/-- Original question 03.3 supplies valid rules and supported initial facts as
separate semantic premises. The existing finite compiler establishes its own
closed/least derivation result, then the SAME CN assessments interpret it. -/
theorem finite_closure_same_cn_world
    (s : Situation) (law : JurisLean.CN.Revision20261101.Rule) (method : IssuedTemplate)
    (lawIn : law ∈ s.core.state.N.rules) (methodIn : method ∈ selectedTemplates s law)
    (decode : Nat → SignedFormula) (rules : List CRule) (facts : List Nat) (fuel : Nat)
    (enough : (finiteCarrier rules facts).card ≤ fuel)
    (initialSupport : ∀ a ∈ facts, signedHolds (atomAssessment s law method) (decode a))
    (rulesValid : ∀ world, semanticCompatible s world → ∀ r ∈ rules,
      (∀ a ∈ r.premises, signedHolds (world.assessment law method) (decode a)) →
      signedHolds (world.assessment law method) (decode r.conclusion)) :
    ∃ known, proposed_checked_rule_input rules fuel facts = .known known ∧
      (∀ q, q ∈ known ↔ ∀ truth, Models (· ∈ facts) (· ∈ rules) truth → truth q) ∧
      ∀ world, semanticCompatible s world → ∀ q ∈ known,
        signedHolds (world.assessment law method) (decode q) := by
  obtain ⟨known,run,complete⟩ := u03_2_bounded_executable_closure_complete rules facts fuel enough
  refine ⟨known,run,?_,?_⟩
  · intro q
    exact (complete q).trans (u03_2_relative_completeness (· ∈ facts) (· ∈ rules) q)
  · intro world compatible q member
    apply u03_1_relative_soundness (truth := fun a =>
      signedHolds (world.assessment law method) (decode a)) _ ((complete q).mp member)
    refine ⟨?_,rulesValid world compatible⟩
    intro a ha
    exact signed_refines _ _ (decode a)
      (fun atom => compatible.2 law lawIn method methodIn atom) (initialSupport a ha)

/-- The existing checked DAG is also consumed with the same CN interpretation.
Its leaf/source and rule obligations are the original 03.5 obligations; the
accepted checker supplies the actual leaves, derivation and acyclic order. -/
theorem provenance_same_cn_world
    (s : Situation) (law : JurisLean.CN.Revision20261101.Rule) (method : IssuedTemplate)
    (lawIn : law ∈ s.core.state.N.rules) (methodIn : method ∈ selectedTemplates s law)
    (decode : Nat → SignedFormula)
    (ctx : JurisLean.Candidates.Final20261021.Gamma)
    (catalog : List JurisLean.Candidates.CompilerProvenance20261027.RuleUse)
    (leafCheck : JurisLean.Candidates.Final20261021.Gamma →
      JurisLean.Candidates.CompilerProvenance20261027.Leaf → Bool)
    (ruleGate : JurisLean.Candidates.Final20261021.Gamma →
      JurisLean.Candidates.CompilerProvenance20261027.RuleUse → Bool)
    (nodes : List JurisLean.Candidates.CompilerProvenance20261027.Node) (root query : Nat)
    (out : JurisLean.Candidates.CompilerProvenance20261027.Evidence)
    (sourceSupport : ∀ leaf, leaf.interpretationVersion = ctx.interpretation →
      leafCheck ctx leaf = true → signedHolds (atomAssessment s law method) (decode leaf.atom))
    (rulesValid : ∀ world, semanticCompatible s world →
      ∀ r ∈ JurisLean.Candidates.CompilerProvenance20261027.activeRules ctx catalog ruleGate,
      (∀ a ∈ r.premises, signedHolds (world.assessment law method) (decode a)) →
      signedHolds (world.assessment law method) (decode r.conclusion))
    (accepted : JurisLean.Candidates.CompilerProvenance20261027.proposed_provenance_input
      ctx catalog leafCheck ruleGate nodes root query = .known out) :
    (∀ i, ¬ Relation.TransGen (JurisLean.Candidates.CompilerProvenance20261027.Edge nodes) i i) ∧
    (query ∈ JurisLean.Candidates.CompilerProvenance20261027.closureFromEvidence ctx catalog ruleGate out) ∧
    ∀ world, semanticCompatible s world →
      signedHolds (world.assessment law method) (decode query) := by
  refine ⟨JurisLean.Candidates.CompilerProvenance20261027.u03_1_checked_provenance_acyclic
    ctx catalog leafCheck ruleGate nodes root query out accepted,
    JurisLean.Candidates.CompilerProvenance20261027.u03_1_provenance_consumed_by_finite_closure
      ctx catalog leafCheck ruleGate nodes root query out accepted,?_⟩
  intro world compatible
  apply JurisLean.Candidates.CompilerProvenance20261027.u03_1_provenance_semantic_composition
    ctx catalog leafCheck ruleGate nodes root query out
    (fun a => signedHolds (world.assessment law method) (decode a)) _
    (rulesValid world compatible) accepted
  intro leaf version checked
  exact signed_refines _ _ (decode leaf.atom)
    (fun atom => compatible.2 law lawIn method methodIn atom)
    (sourceSupport leaf version checked)

/-- The strict MustFacts counterexample already used the actual old finite
closure evaluator. It is reused with its exact statement, not reproved. -/
theorem must_facts_strict_counterexample :
    let rules : List CRule := [⟨[1],3⟩,⟨[2],3⟩]
    proposed_robust_queries rules [[1],[2]] [3] = .known [3] ∧
      3 ∉ proposed_rule_input rules (finiteCarrier rules []).card [] :=
  u03_1_robust_query_strictly_beyond_common_facts

namespace Actual
open Examples

def method : IssuedTemplate :=
  ⟨request .addTemplate,{template with clauses := [(toyAtom,.support toyAtom)]}⟩

def queryFormula : Formula := .both (.atom toyAtom) (.atom toyAtom)

def decode (n : Nat) : SignedFormula :=
  if n = 0 then (.atom toyAtom,true)
  else if n = 1 then (queryFormula,true)
  else (.atom toyAtom,false)

def rules : List CRule := [⟨[0],1⟩]

theorem current_law : confirmation ∈ normal.core.state.N.rules := by
  change confirmation ∈ [confirmation]
  exact List.mem_singleton_self _

theorem current_method : method ∈ selectedTemplates normal confirmation := by
  change method ∈ [method]
  exact List.mem_singleton_self _

theorem current_admitted_seed : signedHolds (atomAssessment normal confirmation method) (decode 0) := by
  change atomAssessment normal confirmation method toyAtom = .established
  rfl

theorem current_rule_valid (world : SemanticWorld) :
    ∀ r ∈ rules,
      (∀ a ∈ r.premises, signedHolds (world.assessment confirmation method) (decode a)) →
      signedHolds (world.assessment confirmation method) (decode r.conclusion) := by
  intro r member premises
  have ruleEq : r = ⟨[0],1⟩ := List.mem_singleton.mp member
  subst r
  have seed := premises 0 (by simp)
  change world.assessment confirmation method toyAtom = .established at seed
  change evalFormula (world.assessment confirmation method) queryFormula = .established
  simp [queryFormula,evalFormula,seed,andJ]

theorem current_nonempty : ∃ world, semanticCompatible normal world := by
  have successful : (executeCommand normal (.legal (call .decide))).answer = .success () := by decide
  obtain ⟨law,t,member,ready⟩ := actual_legal_step_semantic_ready normal
    (call .decide).request (call .decide).policy (call .decide).mode (call .decide).world successful
  exact ready.1

/-- A real current CN admitted view consumes the old finite closure and returns
the matching source query answer through the common feedback realization. -/
theorem admitted_closure_feedback :
    (representedReply normal (.burdenEvidence (call .decide) queryFormula)).answer = .success .established ∧
    (∃ world, semanticCompatible normal world) ∧
    ∃ known, proposed_checked_rule_input rules (finiteCarrier rules [0]).card [0] = .known known ∧
      (∀ q, q ∈ known ↔ ∀ truth, Models (· ∈ ([0] : List Nat)) (· ∈ rules) truth → truth q) ∧
      1 ∈ known ∧
      ∀ world, semanticCompatible normal world →
        evalFormula (world.assessment confirmation method) queryFormula = .established := by
  constructor
  · decide
  · refine ⟨current_nonempty,?_⟩
    obtain ⟨known,run,least,sound⟩ := finite_closure_same_cn_world normal confirmation method
      current_law current_method decode rules [0] (finiteCarrier rules [0]).card le_rfl
      (by intro a ha; have eq : a = 0 := List.mem_singleton.mp ha; subst a; exact current_admitted_seed)
      (fun world _ => current_rule_valid world)
    have derived : Derives (· ∈ ([0] : List Nat)) (· ∈ rules) 1 := by
      apply Derives.fire (⟨[0],1⟩ : CRule) (by simp [rules])
      intro a member
      have eq : a = 0 := List.mem_singleton.mp member
      subst a
      exact Derives.fact 0 (by simp)
    have inKnown : 1 ∈ known := (least 1).mpr
      ((u03_2_relative_completeness (· ∈ ([0] : List Nat)) (· ∈ rules) 1).mp derived)
    refine ⟨known,run,least,inKnown,?_⟩
    intro world compatible
    exact sound world compatible 1 inKnown

end Actual
end CompilerBridge


namespace Numeric
open JurisLean.Candidates.LearningERM20261027
open LegalMath20261109.PosteriorLaw

/-- The projection reads the ACTUALLY loaded native table. -/
def read (s : Situation) : ℚ × ℚ :=
  (s.core.state.A.theta.getD 0 0,s.core.state.A.theta.getD 1 0)

def candidate (s : ℚ × ℚ) (y : Bool) : List ℚ :=
  [(afterQ s y).1,(afterQ s y).2]

def models (s : ℚ × ℚ) : List (List ℚ) := [candidate s false,candidate s true]

def labelLoss (q : ℚ) (y : Bool) : ℚ := (q - if y then 1 else 0)^2

def sample (y : Bool) : Fin 1 → Fin 2 × Bool := fun _ => (0,y)

def fitted (s : ℚ × ℚ) (y : Bool) : Native.Fit.FittedTable :=
  ⟨EngineExamples.protocol,candidate s y,1,0⟩

def fitInput (s : ℚ × ℚ) (y : Bool) : EngineCall :=
  .fit 2 1 EngineExamples.protocol labelLoss (models s) (sample y)

/-- Two candidates are supplied BEFORE seeing Y. Their first coordinates are
0 and 1; the actual Brier sample selects the matching zero-risk candidate. The
second coordinate is the original update, not an assumed fitted-table result. -/
theorem native_fit_output (s : ℚ × ℚ) (y : Bool) :
    Native.Fit.fitTable EngineExamples.protocol labelLoss (models s) (sample y) =
      .known (fitted s y) := by
  cases y <;> norm_num [Native.Fit.fitTable,models,candidate,afterQ,sample,labelLoss,
    EngineExamples.protocol,Native.Fit.tableLoss,proposed_empirical_fit,fitNonempty,
    selectMinimum,empiricalScore,fitted,Fin.sum_univ_succ]

theorem fitted_numeric_projection (s : ℚ × ℚ) (y : Bool) :
    ((fitted s y).table.getD 0 0,(fitted s y).table.getD 1 0) = afterQ s y := by
  simp [fitted,candidate]

/-- Old semantic identities are consumed at the actual learned-table readout. -/
theorem fitted_original_after (s : ℚ × ℚ) (y : Bool) :
    embed ((fitted s y).table.getD 0 0,(fitted s y).table.getD 1 0) =
      LegalMath20261108.UnifiedFeedbackBridge.after (embed s) y := by
  rw [fitted_numeric_projection,afterQ_embed]

private def identityRegistry (keys : List Nat) :
    LegalMath20261110.OccurrenceHistory.History Unit Unit :=
  keys.map (fun id => ⟨id,(),()⟩)

def freshId (keys : List Nat) : Nat :=
  LegalMath20261110.OccurrenceHistory.fresh (identityRegistry keys)

lemma freshId_not_mem (keys : List Nat) : freshId keys ∉ keys := by
  have fresh := LegalMath20261110.OccurrenceHistory.fresh_not_mem (identityRegistry keys)
  simpa [freshId,identityRegistry,List.map_map] using fresh

def materialId (s : Situation) : Ref .material :=
  ⟨freshId (s.core.keys.map (fun id => id.value) ++ s.engineInputs.map (fun input => input.id.value))⟩

def cashId (s : Situation) : JurisLean.Candidates.Final20261021.EventId :=
  ⟨freshId (s.core.state.F.map (fun event => event.id.value) ++
    s.core.state.ledger.map (fun entry => entry.event.value))⟩

lemma new_material_not_key (s : Situation) : materialId s ∉ s.core.keys := by
  intro member
  apply freshId_not_mem (s.core.keys.map (fun id => id.value) ++
    s.engineInputs.map (fun input => input.id.value))
  exact List.mem_append_left _ (List.mem_map.mpr ⟨materialId s,member,rfl⟩)

lemma new_material_absent (s : Situation) : s.core.state.E (materialId s) = .absent :=
  s.core.closed (materialId s) (new_material_not_key s)

lemma new_material_not_registered (s : Situation) :
    s.engineInputs.any (fun input => input.id == materialId s) = false := by
  apply Bool.eq_false_iff.mpr
  intro found
  obtain ⟨input,member,equal⟩ := List.any_eq_true.mp found
  have h : input.id = materialId s := by simpa using equal
  apply freshId_not_mem (s.core.keys.map (fun id => id.value) ++
    s.engineInputs.map (fun input => input.id.value))
  apply List.mem_append_right
  exact List.mem_map.mpr ⟨input,member,congrArg Ref.value h⟩


private lemma event_find_none (events : List Occurrence) (id : Ref .event)
    (fresh : id.value ∉ events.map (fun event => event.id.value)) :
    events.find? (fun event => event.id == id) = none := by
  induction events with
  | nil => rfl
  | cons event rest ih =>
      have different : event.id ≠ id := by
        intro equal
        apply fresh
        simp [equal]
      have remaining : id.value ∉ rest.map (fun item => item.id.value) := by
        intro member
        apply fresh
        exact List.mem_cons_of_mem _ member
      simp [different,ih remaining]

lemma new_cash_not_event (s : Situation) :
    s.core.state.F.find? (fun event => event.id == (⟨(cashId s).value⟩ : Ref .event)) = none := by
  apply event_find_none
  intro member
  apply freshId_not_mem (s.core.state.F.map (fun event => event.id.value) ++
    s.core.state.ledger.map (fun entry => entry.event.value))
  exact List.mem_append_left _ member

lemma new_material_filter_empty (s : Situation) :
    s.engineInputs.filter (fun input => input.id == materialId s) = [] := by
  apply List.filter_eq_nil_iff.mpr
  intro input member equal
  have found : s.engineInputs.any (fun input => input.id == materialId s) = true :=
    List.any_eq_true.mpr ⟨input,member,equal⟩
  rw [new_material_not_registered] at found
  cases found

/-- Only the fixed declared authorization context is needed for the fit/learn
part. Preservation below proves it for every reachable prefix. -/
def ModelReady (s : Situation) : Prop := s.core.state.N = EngineExamples.cashStart.core.state.N

/-- Exactly the native preparation guards. Neither the rule list, the rest
of the grants, legal relations nor any institution state is fixed here. -/
def FitReady (s : Situation) : Prop :=
  s.core.state.N.version = 1 ∧
  authorized s.core.state.N (Examples.request .admitEvidence) = true ∧
  authorized s.core.state.N (Examples.request .learnModel) = true

instance fitReady_decidable (s : Situation) : Decidable (FitReady s) := by
  unfold FitReady
  infer_instance

lemma fitReady_of_modelReady {s : Situation} (ready : ModelReady s) : FitReady s := by
  unfold FitReady
  rw [ready]
  decide

lemma fit_fresh_admit (s : Situation) (ready : FitReady s) :
    freshRequest s (Examples.request .admitEvidence) = true := by
  unfold freshRequest
  rw [ready.2.1,ready.1]
  rfl

lemma fit_fresh_learn (s : Situation) (ready : FitReady s) :
    freshRequest s (Examples.request .learnModel) = true := by
  unfold freshRequest
  rw [ready.2.2,ready.1]
  rfl

lemma fresh_request (s : Situation) (ready : ModelReady s) (act : Act) :
    freshRequest s (Examples.request act) = true := by
  unfold freshRequest
  rw [ready]
  cases act <;> decide

def observedAtom (s : Situation) : Atom :=
  ⟨toyScope,⟨2*(cashId s).value⟩⟩

def event (s : Situation) (y : Bool) : Occurrence :=
  ⟨⟨(cashId s).value⟩,⟨8⟩,
    if y then observedAtom s else ⟨toyScope,⟨2*(cashId s).value+1⟩⟩,0⟩

def raw (s : Situation) (y : Bool) : Raw (materialId s) :=
  ⟨observedAtom s,y,⟨(materialId s).value⟩,0⟩

def receipt (s : Situation) (y : Bool) : Receipt (raw s y) :=
  ⟨⟨(materialId s).value⟩,⟨12⟩,toyNorm,true,true,true,by decide⟩

def input (s : Situation) (y : Bool) : EngineMaterial :=
  Engines.material s EngineExamples.context (materialId s) ⟨(materialId s).value⟩ (fitInput (read s) y)

def physical (s : Situation) (y : Bool) : Situation :=
  {s with core := {s.core with state := {s.core.state with F := s.core.state.F ++ [event s y]}}}

def recorded (s : Situation) (y : Bool) : Situation :=
  (physical s y).withCore ((physical s y).core.setCell (materialId s) (.pending (raw s y)))

def admitted (s : Situation) (y : Bool) : Situation :=
  (recorded s y).withCore ((recorded s y).core.setCell (materialId s) (.accepted (raw s y) (receipt s y)))

def prepared (s : Situation) (y : Bool) : Situation :=
  {admitted s y with engineInputs := input s y :: s.engineInputs}

lemma physical_actual (s : Situation) (y : Bool) :
    (executeCommand s (.occur (event s y))).after = physical s y := by
  simp [executeCommand,occurrence,event,new_cash_not_event,physical,EffectIR.adjust,EffectIR.write]

lemma recorded_actual (s : Situation) (y : Bool) :
    (executeCommand (physical s y) (.record (materialId s) (raw s y))).after = recorded s y := by
  simp [executeCommand,recordMaterial,physical,new_material_absent,recorded,rawOf]

lemma admitted_actual (s : Situation) (ready : FitReady s) (y : Bool) :
    (executeCommand (recorded s y) (.admitEvidence (Examples.request .admitEvidence)
      .human (materialId s) (raw s y) (receipt s y))).after = admitted s y := by
  have fresh : freshRequest (recorded s y) (Examples.request .admitEvidence) = true :=
    fit_fresh_admit s ready
  have pending : (recorded s y).core.state.E (materialId s) = .pending (raw s y) := by
    simp [recorded,CaseState.setCell,Situation.withCore,setEvidence]
  change (admission (recorded s y) (Examples.request .admitEvidence)
    .human (materialId s) (raw s y) (receipt s y)).after = _
  unfold admission
  rw [fresh,pending]
  norm_num [automationAllowed,raw,observedAtom,receipt,Examples.request,toyRequest,toyNorm,
    EffectIR.adjust,EffectIR.admission,EffectIR.write,admitted]

lemma prepared_actual (s : Situation) (ready : FitReady s) (y : Bool) :
    (executeCommand (admitted s y) (.registerEngine (Examples.request .learnModel) (input s y))).after =
      prepared s y := by
  have fresh : freshRequest (admitted s y) (Examples.request .learnModel) = true :=
    fit_fresh_learn s ready
  have version : s.core.state.N.version = 1 := ready.1
  have cell : (admitted s y).core.state.E (materialId s) = .accepted (raw s y) (receipt s y) := by
    simp [admitted,CaseState.setCell,Situation.withCore,setEvidence]
  have unused : (admitted s y).engineInputs.any (fun old => old.id == (input s y).id) = false :=
    new_material_not_registered s
  change (registerEngineMaterial (admitted s y) (Examples.request .learnModel) (input s y)).after = _
  unfold registerEngineMaterial
  rw [fresh,unused]
  have fetched : rawOf ((admitted s y).core.state.E (input s y).id) = some (raw s y) := by
    change rawOf ((admitted s y).core.state.E (materialId s)) = _
    rw [cell]
    rfl
  rw [fetched]
  norm_num [prepared,input,Engines.material,EngineExamples.context,raw,observedAtom,receipt,
    Examples.request,toyRequest,version]
  rfl

lemma prepared_lookup (s : Situation) (y : Bool) :
    (prepared s y).engineInputs.filter (fun item => item.id == materialId s) = [input s y] := by
  simp [prepared,input,Engines.material,new_material_filter_empty]

lemma prepared_allowed (s : Situation) (ready : FitReady s) (y : Bool) :
    engineMaterialAllowed (prepared s y) EngineExamples.context (input s y) = true := by
  have version : s.core.state.N.version = 1 := ready.1
  simp [engineMaterialAllowed,prepared,admitted,recorded,physical,input,Engines.material,
    EngineExamples.context,CaseState.setCell,Situation.withCore,setEvidence,raw,observedAtom,receipt,toyNorm,version]

def fitPost (s : Situation) (y : Bool) : Situation :=
  (executeCommand (prepared s y) (.engine EngineExamples.context (materialId s))).after

def learned (s : Situation) (y : Bool) : Situation :=
  (executeCommand (fitPost s y) (.learnReport (Examples.request .learnModel) (materialId s))).after

lemma fitPost_formula (s : Situation) (ready : FitReady s) (y : Bool) :
    fitPost s y =
      { (Law.proposeEngine (prepared s y)
          (engineOutput (prepared s y) EngineExamples.context .fit
            "JurisLean.Candidates.LearningConsumer20261027.u01_6_fit_card_minimizes_actual_sample"
            (⟨0⟩,⟨EngineExamples.protocol.failureBudget⟩))).after with
        engineResults := ⟨input s y,.known (fitted (read s) y)⟩ :: (prepared s y).engineResults} := by
  change (runBoundEngine (prepared s y) EngineExamples.context (materialId s)).legal.after = _
  unfold runBoundEngine
  rw [prepared_lookup s y]
  dsimp only
  rw [prepared_allowed s ready y]
  simp [callEngine,input,Engines.material,fitInput,consumeFit,relayNative,native_fit_output,fitted]
  rfl

lemma fitPost_norm (s : Situation) (ready : FitReady s) (y : Bool) :
    (fitPost s y).core.state.N = s.core.state.N := by
  rw [fitPost_formula s ready y]
  rfl

lemma fitPost_cell (s : Situation) (ready : FitReady s) (y : Bool) :
    (fitPost s y).core.state.E (materialId s) = .accepted (raw s y) (receipt s y) := by
  rw [fitPost_formula s ready y]
  simp [Law.proposeEngine,EffectIR.adjust,EffectIR.proposal,EffectIR.write,
    prepared,admitted,recorded,physical,CaseState.setCell,Situation.withCore,setEvidence]

lemma learned_formula (s : Situation) (ready : FitReady s) (y : Bool) :
    learned s y = (fitPost s y).withCore ((fitPost s y).core.putState
      {(fitPost s y).core.state with
        A := {(fitPost s y).core.state.A with theta := candidate (read s) y}} rfl) := by
  have norm := fitPost_norm s ready y
  have fresh : freshRequest (fitPost s y) (Examples.request .learnModel) = true := by
    simpa only [freshRequest,norm] using fit_fresh_learn s ready
  have head : (fitPost s y).engineResults.head? = some ⟨input s y,.known (fitted (read s) y)⟩ := by
    rw [fitPost_formula s ready y]
    rfl
  have found := Engines.actual_head_is_found (fitPost s y) (materialId s)
    ⟨input s y,.known (fitted (read s) y)⟩ head rfl
  have version : s.core.state.N.version = 1 := ready.1
  have allowed : engineMaterialAllowed (fitPost s y)
      ⟨(Examples.request .learnModel).scope,(input s y).target⟩ (input s y) = true := by
    simp [engineMaterialAllowed,input,Engines.material,EngineExamples.context,
      Examples.request,toyRequest,raw,observedAtom,receipt,toyNorm,norm,fitPost_cell s ready y,version]
  change (learnReport (fitPost s y) (Examples.request .learnModel) (materialId s)).after = _
  unfold learnReport
  rw [fresh,found]
  have act : (Act.learnModel != Act.learnModel) = false := by decide
  change engineMaterialAllowed (fitPost s y) ⟨toyScope,(input s y).target⟩ (input s y) = true at allowed
  simp only [Examples.request,toyRequest,act,beq_self_eq_true,Bool.not_true,Bool.false_or,
    Bool.false_eq_true,↓reduceIte]
  rw [allowed]
  norm_num [learnedTable,input,Engines.material,fitInput,fitted,Examples.request,toyRequest]
  rfl

/-- The actual public native-fit/report/learn episode updates the projection
by the original afterQ. The fitted-table equality was proved by the ERM, not
assumed as an input. -/
theorem learned_read (s : Situation) (ready : FitReady s) (y : Bool) :
    read (learned s y) = afterQ (read s) y := by
  rw [learned_formula s ready y]
  simp [read,candidate,Situation.withCore,CaseState.putState]

theorem learned_ready (s : Situation) (ready : FitReady s) (y : Bool) : FitReady (learned s y) := by
  change (learned s y).core.state.N = _
  rw [learned_formula s ready y]
  change (fitPost s y).core.state.N = _
  rw [fitPost_norm s ready y]
  exact ready

/-- All six source commands, including the actual observed Y, are retained. -/
def preparationCommands (s : Situation) (y : Bool) : List PackedCommand :=
  [⟨_,.occur (event s y)⟩,
   ⟨_,.record (materialId s) (raw s y)⟩,
   ⟨_,.admitEvidence (Examples.request .admitEvidence) .human (materialId s) (raw s y) (receipt s y)⟩,
   ⟨_,.registerEngine (Examples.request .learnModel) (input s y)⟩,
   ⟨_,.engine EngineExamples.context (materialId s)⟩,
   ⟨_,.learnReport (Examples.request .learnModel) (materialId s)⟩]

theorem preparation_replay (s : Situation) (ready : FitReady s) (y : Bool) :
    FullEventLog.CN.replay s (preparationCommands s y) = learned s y := by
  simp only [FullEventLog.CN.replay,preparationCommands,List.foldl_cons,List.foldl_nil,
    FullEventLog.CN.advance]
  rw [physical_actual,recorded_actual,admitted_actual s ready y,prepared_actual s ready y]
  rfl

/-- No occurrence, ledger entry, or previous source report is reset. -/
theorem learned_events (s : Situation) (ready : FitReady s) (y : Bool) :
    (learned s y).core.state.F = s.core.state.F ++ [event s y] := by
  rw [learned_formula s ready y]
  change (fitPost s y).core.state.F = _
  rw [fitPost_formula s ready y]
  rfl

theorem learned_ledger (s : Situation) (ready : FitReady s) (y : Bool) :
    (learned s y).core.state.ledger = s.core.state.ledger := by
  rw [learned_formula s ready y]
  change (fitPost s y).core.state.ledger = _
  rw [fitPost_formula s ready y]
  rfl


/-- One fixed legal context, with the ACTUAL changing account. Its debt value
is not frozen: the accepted native account can allocate and retain surplus. -/
structure LegalReady (s : Situation) : Prop where
  norms : ModelReady s
  relations : s.core.state.L = [toyRelation]
  constraints : s.core.state.constraints = []
  templates : s.templates = EngineExamples.cashStart.templates
  disputes : s.disputes = []
  source : s.core.state.E ⟨9⟩ = .accepted toyRaw toyReceipt
  sourceKey : (⟨9⟩ : Ref .material) ∈ s.core.keys
  account : ∃ account, s.accounts ⟨6⟩ = some account ∧
    account.debt.relation = ⟨6⟩ ∧ account.debt.obligor = ⟨8⟩ ∧ account.debt.creditor = ⟨7⟩ ∧
    account.debt.amount.tag = EngineExamples.amountTag ∧
    Native.Cash.Conserves account ∧ Native.Cash.CashConsistent account

lemma LegalReady.fit {s : Situation} (ready : LegalReady s) : FitReady s :=
  fitReady_of_modelReady ready.norms

def initial (state : ℚ × ℚ) : Situation :=
  let base := EngineExamples.cashStart
  base.withCore (base.core.putState {base.core.state with
    A := {base.core.state.A with theta := [state.1,state.2]}} rfl)

theorem initial_read (state : ℚ × ℚ) : read (initial state) = state := by
  simp [initial,read,Situation.withCore,CaseState.putState]

theorem initial_ready (state : ℚ × ℚ) : LegalReady (initial state) := by
  refine ⟨rfl,rfl,rfl,rfl,rfl,rfl,?_,?_⟩
  · change (⟨9⟩ : Ref .material) ∈ EngineExamples.cashStart.core.keys
    decide
  · refine ⟨EngineExamples.cashBefore,rfl,rfl,rfl,rfl,rfl,?_,?_⟩
    · norm_num [JurisLean.Candidates.Final20261021.Ledger.Conserves,
        JurisLean.Candidates.Final20261021.Ledger.balance,EngineExamples.cashBefore]
    · rfl

theorem learned_legal_ready (s : Situation) (ready : LegalReady s) (y : Bool) :
    LegalReady (learned s y) := by
  have different : materialId s ≠ (⟨9⟩ : Ref .material) := by
    intro equal
    apply new_material_not_key s
    rw [equal]
    exact ready.sourceKey
  have norm : (learned s y).core.state.N = s.core.state.N := by
    rw [learned_formula s ready.fit y,fitPost_formula s ready.fit y]
    rfl
  refine ⟨norm.trans ready.norms,?_,?_,?_,?_,?_,?_,?_⟩
  · rw [learned_formula s ready.fit y,fitPost_formula s ready.fit y]
    exact ready.relations
  · rw [learned_formula s ready.fit y,fitPost_formula s ready.fit y]
    exact ready.constraints
  · rw [learned_formula s ready.fit y,fitPost_formula s ready.fit y]
    exact ready.templates
  · rw [learned_formula s ready.fit y,fitPost_formula s ready.fit y]
    exact ready.disputes
  · rw [learned_formula s ready.fit y,fitPost_formula s ready.fit y]
    simpa [Law.proposeEngine,EffectIR.adjust,EffectIR.proposal,EffectIR.write,
      prepared,admitted,recorded,physical,Situation.withCore,CaseState.putState,
      CaseState.setCell,setEvidence,Ne.symm different] using ready.source
  · rw [learned_formula s ready.fit y,fitPost_formula s ready.fit y]
    change (⟨9⟩ : Ref .material) ∈ materialId s :: materialId s :: s.core.keys
    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ ready.sourceKey)
  · rw [learned_formula s ready.fit y,fitPost_formula s ready.fit y]
    exact ready.account

/-- F and the primary ledger remain actual historical fields. The world used
by the existing legal checker reads those facts and actual account reductions. -/
def actualWorld (s : Situation) : PossibleWorld :=
  rebasedWorld s {toyWorld with
    fact := fun atom => s.core.state.F.any (fun event => event.atom == atom)
    active := fun _ => true}

lemma actualWorld_facts (s : Situation) (event : Occurrence) (member : event ∈ s.core.state.F) :
    (actualWorld s).fact event.atom = true := by
  apply List.any_eq_true.mpr
  exact ⟨event,member,by simp⟩

lemma world_check (s : Situation) (ready : LegalReady s) :
    legalWorldCheck s (actualWorld s) = true := by
  have facts : s.core.state.F.all (fun event => (actualWorld s).fact event.atom) = true :=
    List.all_eq_true.mpr (fun event member => actualWorld_facts s event member)
  simp only [legalWorldCheck,facts,ready.constraints,List.all_nil,Bool.true_and,
    ready.relations,List.all_cons,List.all_nil,Bool.and_true]
  cases quantity : knownReduction s toyRelation with
  | none => simp [actualWorld,rebasedWorld,ready.relations,quantity]
  | some q => simp [actualWorld,rebasedWorld,ready.relations,quantity]

lemma source_admitted (s : Situation) (ready : LegalReady s) :
    admittedSource s ⟨EngineExamples.payment.source.value⟩ toyScope = true := by
  apply List.any_eq_true.mpr
  refine ⟨⟨9⟩,ready.sourceKey,?_⟩
  rw [ready.source]
  rfl


def performanceLaw : JurisLean.CN.Revision20261101.Rule :=
  {Examples.confirmation with effect := .performance}

def performanceMethod : IssuedTemplate := CompilerBridge.Actual.method

lemma performance_selected_rule (s : Situation) (ready : LegalReady s) :
    selectedRules s.core (Examples.request .perform) = [performanceLaw] := by
  unfold selectedRules
  rw [ready.norms]
  rfl

lemma performance_selected_template (s : Situation) (ready : LegalReady s) :
    selectedTemplates s performanceLaw = [performanceMethod] := by
  have norms : s.core.state.N = EngineExamples.cashStart.core.state.N := ready.norms
  simpa only [selectedTemplates,templateMatches,templateGate,selectedRules,ready.templates,norms] using
    (show selectedTemplates EngineExamples.cashStart performanceLaw = [performanceMethod] from rfl)

lemma current_admitted_view (s : Situation) (ready : LegalReady s) :
    admittedView s.core.state.E performanceLaw.materials = [⟨⟨9⟩,toyRaw,toyReceipt⟩] := by
  simp [performanceLaw,Examples.confirmation,toyRule,admittedView,admittedAt,ready.source]

lemma performance_assessed (s : Situation) (ready : LegalReady s) :
    assessed s performanceLaw performanceMethod.body = .known .established := by
  unfold assessed
  rw [current_admitted_view s ready]
  rfl

lemma performance_agreement (s : Situation) (ready : LegalReady s) :
    policyAgreement s performanceLaw Examples.policy .established = true := by
  unfold policyAgreement
  rw [current_admitted_view s ready]
  rfl

/-- Permission is derived from the actual unchanged norm and admitted source;
no Ready or successful-Permission ticket is assumed. -/
lemma actual_permission (s : Situation) (ready : LegalReady s) :
    permissionDispatch s (Examples.request .perform) Examples.policy .human (actualWorld s) =
      quiet s (.success ()) := by
  have auth : authorized s.core.state.N (Examples.request .perform) = true := by
    rw [ready.norms]
    decide
  have request : permissionRequestGate s (Examples.request .perform) performanceLaw Examples.policy = true := by
    unfold permissionRequestGate
    rw [ready.norms]
    rfl
  simp [permissionDispatch,automationAllowed,auth,activeConflict,ready.disputes,
    performance_selected_rule s ready,performance_selected_template s ready,
    permissionLaw,request,world_check s ready,performance_assessed s ready,
    performance_agreement s ready]

def payment (s : Situation) : Native.PaymentPayload :=
  {EngineExamples.payment with cashId := cashId s}

lemma cash_source_known (source : Situation) (account : Native.Cash.State)
    (conservation : Native.Cash.Conserves account) (consistent : Native.Cash.CashConsistent account)
    (tag : account.debt.amount.tag = EngineExamples.amountTag) :
    cashSource account (payment source) = .known (Native.Cash.performance account (payment source)) := by
  unfold cashSource
  have amount : 0 ≤ (payment source).amount.value := by norm_num [payment,EngineExamples.payment]
  have same : (payment source).amount.tag = account.debt.amount.tag := by rw [tag]; rfl
  rw [if_pos ⟨conservation,consistent,amount,same⟩]

lemma new_cash_not_ledger (s : Situation) :
    s.core.state.ledger.any (fun entry => entry.event.value == (cashId s).value) = false := by
  apply Bool.eq_false_iff.mpr
  intro found
  obtain ⟨entry,member,equal⟩ := List.any_eq_true.mp found
  have same : entry.event.value = (cashId s).value := by simpa using equal
  apply freshId_not_mem (s.core.state.F.map (fun event => event.id.value) ++
    s.core.state.ledger.map (fun entry => entry.event.value))
  exact List.mem_append_right _ (List.mem_map.mpr ⟨entry,member,same⟩)

lemma learned_payment_event (s : Situation) (ready : FitReady s) :
    (learned s true).core.state.F.any (fun event =>
      event.id.value == (payment s).cashId.value && event.atom.scope == toyScope &&
      event.actor.value == (payment s).payer.value) = true := by
  rw [learned_events s ready true]
  apply List.any_eq_true.mpr
  exact ⟨event s true,List.mem_append_right _ (by simp),by simp [event,observedAtom,payment,EngineExamples.payment]⟩

def cashPost (s : Situation) (source : Situation) (account : Native.Cash.State) : Situation :=
  let after := Native.Cash.performance account (payment source)
  let entry : Performance :=
    ⟨⟨(payment source).cashId.value⟩,⟨6⟩,⟨after.allocated-account.allocated⟩,Examples.request .perform⟩
  EffectIR.adjust (EffectIR.payment entry ⟨6⟩ after) s

/-- The actual Perform edge commits the same source cash once, under its
existing guards, using the original conserved account and current event. -/
lemma performPayment_actual (source : Situation) (ready : LegalReady source)
    (account : Native.Cash.State) (accountAt : source.accounts ⟨6⟩ = some account)
    (relation : account.debt.relation = ⟨6⟩) (payer : account.debt.obligor = ⟨8⟩)
    (payee : account.debt.creditor = ⟨7⟩) (tag : account.debt.amount.tag = EngineExamples.amountTag)
    (conservation : Native.Cash.Conserves account) (consistent : Native.Cash.CashConsistent account) :
    performPayment (learned source true) (Examples.request .perform) .human ⟨6⟩ (payment source) =
      ⟨cashPost (learned source true) source account,.success ()⟩ := by
  have sameAccount : (learned source true).accounts ⟨6⟩ = some account := by
    rw [learned_formula source ready.fit true,fitPost_formula source ready.fit true]
    exact accountAt
  have current := learned_legal_ready source ready true
  have fresh := fresh_request (learned source true) current.norms .perform
  have admittedSource : admittedSource (learned source true) ⟨(payment source).source.value⟩ toyScope = true :=
    source_admitted (learned source true) current
  have event := learned_payment_event source ready.fit
  have unused : (learned source true).core.state.ledger.any (fun entry =>
      entry.event.value == (payment source).cashId.value) = false := by
    simpa only [learned_ledger source ready.fit true,payment] using new_cash_not_ledger source
  have native := cash_source_known source account conservation consistent tag
  simp only [payment,EngineExamples.payment,Examples.request,toyRequest,toyScope]
    at fresh admittedSource event unused native
  simp [performPayment,automationAllowed,fresh,sameAccount,relation,payer,payee,
    current.relations,admittedSource,event,unused,native,
    payment,EngineExamples.payment,Examples.request,toyRequest,toyScope,toyRelation,cashPost]


lemma cashPost_ready (s : Situation) (ready : LegalReady s) (source : Situation)
    (account : Native.Cash.State)
    (relation : account.debt.relation = ⟨6⟩) (payer : account.debt.obligor = ⟨8⟩)
    (payee : account.debt.creditor = ⟨7⟩) (tag : account.debt.amount.tag = EngineExamples.amountTag)
    (conservation : Native.Cash.Conserves account) (consistent : Native.Cash.CashConsistent account) :
    LegalReady (cashPost s source account) := by
  refine ⟨ready.norms,ready.relations,ready.constraints,ready.templates,ready.disputes,
    ready.source,ready.sourceKey,?_⟩
  refine ⟨Native.Cash.performance account (payment source),?_,relation,payer,payee,tag,?_,?_⟩
  · simp [cashPost,EffectIR.adjust,EffectIR.payment,EffectIR.write]
  · exact Native.Cash.u09_1_quantity_conservation account (payment source) conservation
      (by norm_num [payment,EngineExamples.payment])
  · exact Native.Cash.performance_cash_consistent account (payment source) consistent

lemma cashPost_world_check (s : Situation) (ready : LegalReady s)
    (source : Situation) (account : Native.Cash.State) :
    legalWorldCheck (cashPost s source account)
      (rebasedWorld (cashPost s source account) (actualWorld s)) = true := by
  have facts : (cashPost s source account).core.state.F.all (fun event =>
      (rebasedWorld (cashPost s source account) (actualWorld s)).fact event.atom) = true := by
    apply List.all_eq_true.mpr
    intro event member
    exact actualWorld_facts s event member
  have relations : (cashPost s source account).core.state.L = [toyRelation] := ready.relations
  have constraints : (cashPost s source account).core.state.constraints = [] := ready.constraints
  simp only [legalWorldCheck,facts,constraints,List.all_nil,Bool.true_and,
    relations,List.all_cons,List.all_nil,Bool.and_true]
  cases quantity : knownReduction (cashPost s source account) toyRelation with
  | none => simp [rebasedWorld,actualWorld,ready.relations,relations,quantity]
  | some q => simp [rebasedWorld,actualWorld,ready.relations,relations,quantity]

lemma performPaired_actual (source : Situation) (ready : LegalReady source)
    (account : Native.Cash.State) (accountAt : source.accounts ⟨6⟩ = some account)
    (relation : account.debt.relation = ⟨6⟩) (payer : account.debt.obligor = ⟨8⟩)
    (payee : account.debt.creditor = ⟨7⟩) (tag : account.debt.amount.tag = EngineExamples.amountTag)
    (conservation : Native.Cash.Conserves account) (consistent : Native.Cash.CashConsistent account) :
    performPaired (learned source true) (Examples.request .perform) .human ⟨6⟩ (payment source) =
      ⟨cashPost (learned source true) source account,.success ()⟩ := by
  have current := learned_legal_ready source ready true
  have group : reductionGroup (learned source true) (Examples.request .perform) ⟨6⟩ = .success [] := by
    simp [reductionGroup,current.constraints]
  have sameAccount : (learned source true).accounts ⟨6⟩ = some account := by
    rw [learned_formula source ready.fit true,fitPost_formula source ready.fit true]
    exact accountAt
  unfold performPaired
  rw [group,sameAccount,performPayment_actual source ready account accountAt relation payer payee tag conservation consistent]
  simp [Law.continueWith,cashPost,EffectIR.adjust,EffectIR.payment,EffectIR.write,reduceTargets,quiet]

def paymentCall (s : Situation) : Law.Call :=
  {Examples.call .perform with world := actualWorld (learned s true)}

/-- Success of the existing public Perform wrapper is a conclusion. Its
source-world, source-bound permission and cash guards were all derived above. -/
theorem actual_payment (source : Situation) (ready : LegalReady source) :
    ∃ account, source.accounts ⟨6⟩ = some account ∧
      (executeCommand (learned source true) (.perform (paymentCall source) ⟨6⟩ (payment source))) =
        ⟨cashPost (learned source true) source account,.success ()⟩ ∧
      LegalReady (cashPost (learned source true) source account) := by
  obtain ⟨account,atAccount,relation,payer,payee,tag,conservation,consistent⟩ := ready.account
  have current := learned_legal_ready source ready true
  refine ⟨account,atAccount,?_,cashPost_ready _ current source account relation payer payee tag conservation consistent⟩
  change performCall (learned source true) (paymentCall source) ⟨6⟩ (payment source) = _
  unfold performCall
  simp only [paymentCall,Examples.call]
  rw [actual_permission (learned source true) current]
  simp only [Law.continueWith,quiet]
  rw [performPaired_actual source ready account atAccount relation payer payee tag conservation consistent]
  simp only [Law.atomic,checkPost]
  rw [cashPost_world_check (learned source true) current source account]
  rfl

/-- This is a compositional episode over the previous full CN post, never a
reset to a fixture. Only initialization below starts from cashStart. -/
def episode (s : Situation) (y : Bool) : Situation :=
  if y then
    (executeCommand (learned s true) (.perform (paymentCall s) ⟨6⟩ (payment s))).after
  else learned s false

def episodeCommands (s : Situation) (y : Bool) : List PackedCommand :=
  preparationCommands s y ++ if y then ([⟨Unit,.perform (paymentCall s) ⟨6⟩ (payment s)⟩] : List PackedCommand) else []

theorem episode_replay (s : Situation) (ready : LegalReady s) (y : Bool) :
    FullEventLog.CN.replay s (episodeCommands s y) = episode s y := by
  change (preparationCommands s y ++
    if y then ([⟨Unit,.perform (paymentCall s) ⟨6⟩ (payment s)⟩] : List PackedCommand) else []).foldl
      FullEventLog.CN.advance s = _
  rw [List.foldl_append]
  change (if y then ([⟨Unit,.perform (paymentCall s) ⟨6⟩ (payment s)⟩] : List PackedCommand) else []).foldl
    FullEventLog.CN.advance (FullEventLog.CN.replay s (preparationCommands s y)) = _
  rw [preparation_replay s ready.fit y]
  cases y <;> rfl

theorem episode_read (s : Situation) (ready : LegalReady s) (y : Bool) :
    read (episode s y) = afterQ (read s) y := by
  cases y with
  | false => exact learned_read s ready.fit false
  | true =>
      obtain ⟨account,atAccount,actual,closed⟩ := actual_payment s ready
      change read (executeCommand (learned s true) (.perform (paymentCall s) ⟨6⟩ (payment s))).after = _
      rw [actual]
      change read (learned s true) = _
      exact learned_read s ready.fit true

theorem episode_ready (s : Situation) (ready : LegalReady s) (y : Bool) : LegalReady (episode s y) := by
  cases y with
  | false => exact learned_legal_ready s ready false
  | true =>
      obtain ⟨account,atAccount,actual,closed⟩ := actual_payment s ready
      change LegalReady (executeCommand (learned s true) (.perform (paymentCall s) ⟨6⟩ (payment s))).after
      rw [actual]
      exact closed

theorem episode_keeps_events (s : Situation) (ready : LegalReady s) (y : Bool) :
    (episode s y).core.state.F = s.core.state.F ++ [event s y] := by
  cases y with
  | false => exact learned_events s ready.fit false
  | true =>
      obtain ⟨account,atAccount,actual,closed⟩ := actual_payment s ready
      change (executeCommand (learned s true) (.perform (paymentCall s) ⟨6⟩ (payment s))).after.core.state.F = _
      rw [actual]
      change (learned s true).core.state.F = _
      exact learned_events s ready.fit true

def run (s : Situation) (outcomes : List Bool) : Situation := outcomes.foldl episode s

def rationalRun (state : ℚ × ℚ) (outcomes : List Bool) : ℚ × ℚ := outcomes.foldl afterQ state

theorem run_ready (s : Situation) (ready : LegalReady s) (outcomes : List Bool) :
    LegalReady (run s outcomes) := by
  induction outcomes generalizing s with
  | nil => exact ready
  | cons y rest ih => exact ih (episode s y) (episode_ready s ready y)

/-- Arbitrary finite prefixes inherit the same actual private update. All
source states, reports, F and ledger data remain in the threaded source run. -/
theorem run_read (s : Situation) (ready : LegalReady s) (outcomes : List Bool) :
    read (run s outcomes) = rationalRun (read s) outcomes := by
  induction outcomes generalizing s with
  | nil => rfl
  | cons y rest ih =>
      change read (run (episode s y) rest) = rationalRun (afterQ (read s) y) rest
      rw [ih (episode s y) (episode_ready s ready y),episode_read s ready y]

theorem every_finite_prefix (state : ℚ × ℚ) (outcomes : List Bool) (n : Nat) :
    LegalReady (run (initial state) (outcomes.take n)) ∧
    embed (read (run (initial state) (outcomes.take n))) =
      embed (rationalRun state (outcomes.take n)) := by
  refine ⟨run_ready _ (initial_ready state) _,?_⟩
  rw [run_read _ (initial_ready state),initial_read]

/- This menu changes the ACTUAL original Perform payload. The fixed legal
context already permits nonnegative same-tag performance; the utility below is
its actual transferred cash (including the original surplus semantics). -/
namespace Menu

def amount (action outcome : Bool) : ℚ :=
  if action then if outcome then 2 else 0 else 1

lemma amount_nonnegative (action outcome : Bool) : 0 ≤ amount action outcome := by
  cases action <;> cases outcome <;> norm_num [amount]

def payload (source : Situation) (quantity : ℚ) : Native.PaymentPayload :=
  {payment source with amount := {(payment source).amount with value := quantity}}

def post (s source : Situation) (quantity : ℚ) (account : Native.Cash.State) : Situation :=
  let after := Native.Cash.performance account (payload source quantity)
  let entry : Performance :=
    ⟨⟨(payload source quantity).cashId.value⟩,⟨6⟩,⟨after.allocated-account.allocated⟩,Examples.request .perform⟩
  EffectIR.adjust (EffectIR.payment entry ⟨6⟩ after) s

lemma native_source (source : Situation) (quantity : ℚ) (nonnegative : 0 ≤ quantity)
    (account : Native.Cash.State) (conservation : Native.Cash.Conserves account)
    (consistent : Native.Cash.CashConsistent account)
    (tag : account.debt.amount.tag = EngineExamples.amountTag) :
    cashSource account (payload source quantity) =
      .known (Native.Cash.performance account (payload source quantity)) := by
  unfold cashSource
  have value : 0 ≤ (payload source quantity).amount.value := nonnegative
  have same : (payload source quantity).amount.tag = account.debt.amount.tag := by rw [tag]; rfl
  rw [if_pos ⟨conservation,consistent,value,same⟩]

lemma event_present (s : Situation) (ready : FitReady s) (y : Bool) (quantity : ℚ) :
    (learned s y).core.state.F.any (fun event =>
      event.id.value == (payload s quantity).cashId.value && event.atom.scope == toyScope &&
      event.actor.value == (payload s quantity).payer.value) = true := by
  rw [learned_events s ready y]
  apply List.any_eq_true.mpr
  refine ⟨event s y,List.mem_append_right _ (by simp),?_⟩
  cases y <;> simp [event,observedAtom,payload,payment,EngineExamples.payment]

lemma post_ready (s : Situation) (ready : LegalReady s) (source : Situation)
    (quantity : ℚ) (nonnegative : 0 ≤ quantity) (account : Native.Cash.State)
    (relation : account.debt.relation = ⟨6⟩) (payer : account.debt.obligor = ⟨8⟩)
    (payee : account.debt.creditor = ⟨7⟩) (tag : account.debt.amount.tag = EngineExamples.amountTag)
    (conservation : Native.Cash.Conserves account) (consistent : Native.Cash.CashConsistent account) :
    LegalReady (post s source quantity account) := by
  refine ⟨ready.norms,ready.relations,ready.constraints,ready.templates,ready.disputes,
    ready.source,ready.sourceKey,?_⟩
  refine ⟨Native.Cash.performance account (payload source quantity),?_,relation,payer,payee,tag,?_,?_⟩
  · simp [post,EffectIR.adjust,EffectIR.payment,EffectIR.write]
  · exact Native.Cash.u09_1_quantity_conservation account (payload source quantity) conservation nonnegative
  · exact Native.Cash.performance_cash_consistent account (payload source quantity) consistent

lemma post_world (s : Situation) (ready : LegalReady s) (source : Situation)
    (quantity : ℚ) (account : Native.Cash.State) :
    legalWorldCheck (post s source quantity account)
      (rebasedWorld (post s source quantity account) (actualWorld s)) = true := by
  have facts : (post s source quantity account).core.state.F.all (fun event =>
      (rebasedWorld (post s source quantity account) (actualWorld s)).fact event.atom) = true := by
    apply List.all_eq_true.mpr
    intro event member
    exact actualWorld_facts s event member
  have relations : (post s source quantity account).core.state.L = [toyRelation] := ready.relations
  have constraints : (post s source quantity account).core.state.constraints = [] := ready.constraints
  simp only [legalWorldCheck,facts,constraints,List.all_nil,Bool.true_and,
    relations,List.all_cons,List.all_nil,Bool.and_true]
  cases reduction : knownReduction (post s source quantity account) toyRelation with
  | none => simp [rebasedWorld,actualWorld,ready.relations,relations,reduction]
  | some q => simp [rebasedWorld,actualWorld,ready.relations,relations,reduction]

lemma raw_performance (source : Situation) (ready : LegalReady source) (y : Bool)
    (quantity : ℚ) (nonnegative : 0 ≤ quantity) (account : Native.Cash.State)
    (accountAt : source.accounts ⟨6⟩ = some account)
    (relation : account.debt.relation = ⟨6⟩) (payer : account.debt.obligor = ⟨8⟩)
    (payee : account.debt.creditor = ⟨7⟩) (tag : account.debt.amount.tag = EngineExamples.amountTag)
    (conservation : Native.Cash.Conserves account) (consistent : Native.Cash.CashConsistent account) :
    performPayment (learned source y) (Examples.request .perform) .human ⟨6⟩ (payload source quantity) =
      ⟨post (learned source y) source quantity account,.success ()⟩ := by
  have sameAccount : (learned source y).accounts ⟨6⟩ = some account := by
    rw [learned_formula source ready.fit y,fitPost_formula source ready.fit y]
    exact accountAt
  have current := learned_legal_ready source ready y
  have fresh := fresh_request (learned source y) current.norms .perform
  have admitted : admittedSource (learned source y) ⟨(payload source quantity).source.value⟩ toyScope = true :=
    source_admitted (learned source y) current
  have event := event_present source ready.fit y quantity
  have unused : (learned source y).core.state.ledger.any (fun entry =>
      entry.event.value == (payload source quantity).cashId.value) = false := by
    simpa only [learned_ledger source ready.fit y,payload,payment] using new_cash_not_ledger source
  have native := native_source source quantity nonnegative account conservation consistent tag
  simp only [payload,payment,EngineExamples.payment,Examples.request,toyRequest,toyScope]
    at fresh admitted event unused native
  simp [performPayment,automationAllowed,fresh,sameAccount,relation,payer,payee,
    current.relations,admitted,event,unused,native,
    payload,payment,EngineExamples.payment,Examples.request,toyRequest,toyScope,toyRelation,post]

lemma paired_performance (source : Situation) (ready : LegalReady source) (y : Bool)
    (quantity : ℚ) (nonnegative : 0 ≤ quantity) (account : Native.Cash.State)
    (accountAt : source.accounts ⟨6⟩ = some account)
    (relation : account.debt.relation = ⟨6⟩) (payer : account.debt.obligor = ⟨8⟩)
    (payee : account.debt.creditor = ⟨7⟩) (tag : account.debt.amount.tag = EngineExamples.amountTag)
    (conservation : Native.Cash.Conserves account) (consistent : Native.Cash.CashConsistent account) :
    performPaired (learned source y) (Examples.request .perform) .human ⟨6⟩ (payload source quantity) =
      ⟨post (learned source y) source quantity account,.success ()⟩ := by
  have current := learned_legal_ready source ready y
  have group : reductionGroup (learned source y) (Examples.request .perform) ⟨6⟩ = .success [] := by
    simp [reductionGroup,current.constraints]
  have sameAccount : (learned source y).accounts ⟨6⟩ = some account := by
    rw [learned_formula source ready.fit y,fitPost_formula source ready.fit y]
    exact accountAt
  unfold performPaired
  rw [group,sameAccount,raw_performance source ready y quantity nonnegative account accountAt
    relation payer payee tag conservation consistent]
  simp [Law.continueWith,post,EffectIR.adjust,EffectIR.payment,EffectIR.write,reduceTargets,quiet]

def context (s : Situation) (y : Bool) : Law.Call :=
  {Examples.call .perform with world := actualWorld (learned s y)}

/-- Nonnegative amounts are not a success assumption. All public permission,
source, version, physical-event, freshness and conservation guards are derived. -/
theorem public_performance (source : Situation) (ready : LegalReady source)
    (y : Bool) (quantity : ℚ) (nonnegative : 0 ≤ quantity) :
    ∃ account, source.accounts ⟨6⟩ = some account ∧
      executeCommand (learned source y) (.perform (context source y) ⟨6⟩ (payload source quantity)) =
        ⟨post (learned source y) source quantity account,.success ()⟩ ∧
      LegalReady (post (learned source y) source quantity account) := by
  obtain ⟨account,atAccount,relation,payer,payee,tag,conservation,consistent⟩ := ready.account
  have current := learned_legal_ready source ready y
  refine ⟨account,atAccount,?_,post_ready _ current source quantity nonnegative account
    relation payer payee tag conservation consistent⟩
  change performCall (learned source y) (context source y) ⟨6⟩ (payload source quantity) = _
  unfold performCall
  simp only [context,Examples.call]
  rw [actual_permission (learned source y) current]
  simp only [Law.continueWith,quiet]
  rw [paired_performance source ready y quantity nonnegative account atAccount
    relation payer payee tag conservation consistent]
  simp only [Law.atomic,checkPost]
  rw [post_world (learned source y) current source quantity account]
  rfl

def episode (s : Situation) (action y : Bool) : Situation :=
  (executeCommand (learned s y)
    (.perform (context s y) ⟨6⟩ (payload s (amount action y)))).after

def commands (s : Situation) (action y : Bool) : List PackedCommand :=
  preparationCommands s y ++
    [⟨_,.perform (context s y) ⟨6⟩ (payload s (amount action y))⟩]

theorem actual_episode (s : Situation) (ready : LegalReady s) (a y : Bool) :
    ∃ account, s.accounts ⟨6⟩ = some account ∧
      episode s a y = post (learned s y) s (amount a y) account ∧
      LegalReady (episode s a y) := by
  obtain ⟨account,atAccount,actual,closed⟩ :=
    public_performance s ready y (amount a y) (amount_nonnegative a y)
  refine ⟨account,atAccount,?_,?_⟩ <;> simp only [episode,actual]
  exact closed

theorem episode_replay (s : Situation) (ready : LegalReady s) (a y : Bool) :
    FullEventLog.CN.replay s (commands s a y) = episode s a y := by
  change (preparationCommands s y ++
    ([⟨Unit,.perform (context s y) ⟨6⟩ (payload s (amount a y))⟩] : List PackedCommand)).foldl FullEventLog.CN.advance s = _
  rw [List.foldl_append]
  change FullEventLog.CN.advance (FullEventLog.CN.replay s (preparationCommands s y))
    (⟨Unit,.perform (context s y) ⟨6⟩ (payload s (amount a y))⟩ : PackedCommand) = _
  rw [preparation_replay s ready.fit y]
  rfl

theorem episode_read (s : Situation) (ready : LegalReady s) (a y : Bool) :
    read (episode s a y) = afterQ (read s) y := by
  obtain ⟨account,atAccount,actual,closed⟩ := actual_episode s ready a y
  rw [actual]
  change read (learned s y) = _
  exact learned_read s ready.fit y

theorem episode_ready (s : Situation) (ready : LegalReady s) (a y : Bool) :
    LegalReady (episode s a y) := by
  obtain ⟨account,atAccount,actual,closed⟩ := actual_episode s ready a y
  exact closed

theorem episode_events (s : Situation) (ready : LegalReady s) (a y : Bool) :
    (episode s a y).core.state.F = s.core.state.F ++ [event s y] := by
  obtain ⟨account,atAccount,actual,closed⟩ := actual_episode s ready a y
  rw [actual]
  change (learned s y).core.state.F = _
  exact learned_events s ready.fit y

/-- The same actual source transfer supplies the utility. Allocated debt and
surplus remain separate; this is NOT the allocation quantity after saturation. -/
theorem actual_cash_payoff (s : Situation) (ready : LegalReady s) (a y : Bool) :
    ∃ before after, s.accounts ⟨6⟩ = some before ∧
      (episode s a y).accounts ⟨6⟩ = some after ∧
      after = Native.Cash.performance before (payload s (amount a y)) ∧
      after.paid-before.paid = amount a y ∧
      Native.Cash.Conserves after ∧ Native.Cash.CashConsistent after := by
  obtain ⟨account,atAccount,actual,closed⟩ := actual_episode s ready a y
  refine ⟨account,Native.Cash.performance account (payload s (amount a y)),atAccount,?_,rfl,?_,?_,?_⟩
  · rw [actual]
    simp [post,EffectIR.adjust,EffectIR.payment,EffectIR.write]
  · change (account.paid + amount a y)-account.paid = amount a y
    ring
  · obtain ⟨after,atAfter,rest⟩ := closed.account
    have eq : after = Native.Cash.performance account (payload s (amount a y)) := by
      apply Option.some.inj
      rw [←atAfter,actual]
      simp [post,EffectIR.adjust,EffectIR.payment,EffectIR.write]
    simpa [eq] using rest.2.2.2.2.1
  · obtain ⟨after,atAfter,rest⟩ := closed.account
    have eq : after = Native.Cash.performance account (payload s (amount a y)) := by
      apply Option.some.inj
      rw [←atAfter,actual]
      simp [post,EffectIR.adjust,EffectIR.payment,EffectIR.write]
    simpa [eq] using rest.2.2.2.2.2

/-- Expected cash uses the very same Xi marginal as the physical response and
private update; there is no independently selected utility distribution. -/
def score (s : Situation) (action : Bool) : ℚ :=
  (1-probabilityQ (read s))*amount action false + probabilityQ (read s)*amount action true

def choose (s : Situation) : Bool := if score s false ≤ score s true then true else false

theorem score_formula (s : Situation) : score s false = 1 ∧ score s true = 2*probabilityQ (read s) := by
  constructor <;> simp [score,amount] <;> ring

theorem actual_native_choice (s : Situation) :
    Native.Decision.legalBest (score s) (fun _ => true) [false,true] = some (choose s) := by
  by_cases selected : score s false ≤ score s true <;>
    simp [Native.Decision.legalBest,Native.Decision.best,choose,selected]

theorem chosen_maximizes_actual_cash (s : Situation) :
    ∀ action : Bool, score s action ≤ score s (choose s) := by
  have old := Native.Decision.legal_best_sound (score s) (fun _ => true) [false,true]
    (choose s) (actual_native_choice s)
  intro action
  exact old.2.2 action (by cases action <;> simp) rfl

theorem score_from_same_xi (s : Situation) (a : Bool) :
    score s a = ∑ y : Bool, amount a y *
      (∑ world, ∑ material, LegalMath20261109.PosteriorLaw.xi (read s) (world,material,y)) := by
  simp_rw [LegalMath20261109.PosteriorLaw.xi_outcome_marginal]
  simp [score,Fintype.univ_bool] <;> ring

theorem learning_changes_actual_choice :
    choose (initial (0,0)) = false ∧ choose (initial (1,1)) = true := by
  norm_num [choose,score,amount,initial_read,probabilityQ,responseQ]

/-- Two-point expansion of the original same-world response law. -/
theorem expected_amount (s : Situation) (a : Bool) :
    (score s a : ℝ) = ∫ y, (amount a y : ℝ)
      ∂LegalMath20261108.UnifiedFeedbackBridge.model.outcome (embed (read s),a) := by
  change (score s a : ℝ) = ∫ y, (amount a y : ℝ)
    ∂LegalMath20261108.UnifiedFeedbackBridge.coin (embed (read s))
  rw [LegalMath20261109.PosteriorLaw.integral_coin]
  simp only [score,Rat.cast_add,Rat.cast_mul,Rat.cast_sub,Rat.cast_one,probabilityQ_embed]
  rfl

def paidRead (s : Situation) : ℚ := ((s.accounts ⟨6⟩).map (fun account => account.paid)).getD 0

def realizedPayoff (s : Situation) (a y : Bool) : ℚ := paidRead (episode s a y)-paidRead s

/-- The payoff is decoded from the actual CN post account. The original
performance theorem derives its value; it is not defined to equal the menu. -/
theorem realizedPayoff_eq_amount (s : Situation) (ready : LegalReady s) (a y : Bool) :
    realizedPayoff s a y = amount a y := by
  obtain ⟨before,after,atBefore,atAfter,source,delta,conservation,consistent⟩ := actual_cash_payoff s ready a y
  simpa [realizedPayoff,paidRead,atBefore,atAfter] using delta

/-- Score is exactly the expected cash change decoded from the same ACTUAL
CN command post, with its same-world outcome distribution. -/
theorem expected_actual_cash (s : Situation) (ready : LegalReady s) (a : Bool) :
    (score s a : ℝ) = ∫ y, (realizedPayoff s a y : ℝ)
      ∂LegalMath20261108.UnifiedFeedbackBridge.model.outcome (embed (read s),a) := by
  rw [expected_amount s a]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun y => by
    change (amount a y : ℝ) = (realizedPayoff s a y : ℝ)
    rw [realizedPayoff_eq_amount s ready a y])

/-- The original best theorem therefore compares actual command post cash,
not arbitrary surrogate numbers. Both source commands succeed by the already
proved public guard/permission/conservation construction. -/
theorem native_choice_maximizes_actual_expected_cash (s : Situation) (ready : LegalReady s) (a : Bool) :
    (∫ y, (realizedPayoff s a y : ℝ)
      ∂LegalMath20261108.UnifiedFeedbackBridge.model.outcome (embed (read s),a)) ≤
    ∫ y, (realizedPayoff s (choose s) y : ℝ)
      ∂LegalMath20261108.UnifiedFeedbackBridge.model.outcome (embed (read s),choose s) := by
  rw [←expected_actual_cash s ready a,←expected_actual_cash s ready (choose s)]
  exact_mod_cast chosen_maximizes_actual_cash s a

/-- A reachable, non-reset episode changes the next actual payment command:
Y=true is retained, natively fitted, learned and paid under action false. -/
theorem actual_reachable_learning_changes_choice :
    choose (initial (0,0)) = false ∧
    read (episode (initial (0,0)) false true) = (1,5/8) ∧
    LegalReady (episode (initial (0,0)) false true) ∧
    choose (episode (initial (0,0)) false true) = true := by
  have reading : read (episode (initial (0,0)) false true) = (1,5/8) := by
    rw [episode_read _ (initial_ready (0,0)) false true,initial_read]
    norm_num [afterQ]
  refine ⟨?_,reading,episode_ready _ (initial_ready (0,0)) false true,?_⟩
  · norm_num [choose,score,amount,initial_read,probabilityQ,responseQ]
  · norm_num [choose,score,amount,reading,probabilityQ,responseQ]

/-- Finite full logs replay the previous COMPLETE actual CN post. -/
def run (s : Situation) (log : List (Bool × Bool)) : Situation :=
  log.foldl (fun current entry => episode current entry.1 entry.2) s

lemma run_ready (s : Situation) (ready : LegalReady s) (log : List (Bool × Bool)) :
    LegalReady (run s log) := by
  induction log generalizing s with
  | nil => exact ready
  | cons entry rest ih => exact ih _ (episode_ready s ready entry.1 entry.2)

lemma run_append (s : Situation) (log : List (Bool × Bool)) (a y : Bool) :
    run s (log ++ [(a,y)]) = episode (run s log) a y := by
  simp [run,List.foldl_append]

/-- This is the full operation list, not only a final numeric summary. -/
def fullCommands (s : Situation) : List (Bool × Bool) → List PackedCommand
  | [] => []
  | entry :: rest => commands s entry.1 entry.2 ++ fullCommands (episode s entry.1 entry.2) rest

lemma full_replay (s : Situation) (ready : LegalReady s) (log : List (Bool × Bool)) :
    FullEventLog.CN.replay s (fullCommands s log) = run s log := by
  induction log generalizing s with
  | nil => rfl
  | cons entry rest ih =>
      change (commands s entry.1 entry.2 ++ fullCommands (episode s entry.1 entry.2) rest).foldl
        FullEventLog.CN.advance s = run (episode s entry.1 entry.2) rest
      rw [List.foldl_append]
      change FullEventLog.CN.replay (FullEventLog.CN.replay s (commands s entry.1 entry.2))
        (fullCommands (episode s entry.1 entry.2) rest) = _
      rw [episode_replay s ready entry.1 entry.2]
      exact ih _ (episode_ready s ready entry.1 entry.2)

/-- All final fields and the dependent History itself are retained through the
already proved fresh-operation-token code. -/
theorem full_history_decoded (s : Situation) (log : List (Bool × Bool)) :
    FullEventLog.CN.runHistory s
      (FullEventLog.Tokens.forget (FullEventLog.Tokens.encode (fullCommands s log))) =
      FullEventLog.CN.runHistory s (fullCommands s log) := by
  rw [FullEventLog.Tokens.decode_encode]

abbrev Log := List (Bool × Bool)
abbrev RealState := LegalMath20261108.UnifiedFeedbackBridge.State
local instance : MeasurableSpace Log := ⊤

def actual (state : ℚ × ℚ) (log : Log) : Situation := run (initial state) log

def projection (state : ℚ × ℚ) (source : Log × RealState) : RealState :=
  embed (read (actual state source.1))

lemma measurable_projection (state : ℚ × ℚ) : Measurable (projection state) :=
  (Measurable.of_discrete (f := fun log : Log => embed (read (actual state log)))).comp measurable_fst

lemma actual_ready (state : ℚ × ℚ) (log : Log) : LegalReady (actual state log) :=
  run_ready _ (initial_ready state) log

lemma projection_append (state : ℚ × ℚ) (log : Log) (shadow : RealState) (a y : Bool) :
    projection state (log ++ [(a,y)],shadow) =
      LegalMath20261108.UnifiedFeedbackBridge.after (projection state (log,shadow)) y := by
  change embed (read (run (initial state) (log ++ [(a,y)]))) = _
  rw [run_append]
  change embed (read (episode (actual state log) a y)) =
    LegalMath20261108.UnifiedFeedbackBridge.after (embed (read (actual state log))) y
  rw [episode_read _ (actual_ready state log) a y,afterQ_embed]

def responseKernel (state : ℚ × ℚ) : Kernel ((Log × RealState) × Bool) Bool where
  toFun := fun z => LegalMath20261108.UnifiedFeedbackBridge.coin (projection state z.1)
  measurable' := LegalMath20261108.UnifiedFeedbackBridge.measurable_coin.comp
    ((measurable_projection state).comp measurable_fst)

instance responseKernel_markov (state : ℚ × ℚ) : IsMarkovKernel (responseKernel state) where
  isProbabilityMeasure z := LegalMath20261108.UnifiedFeedbackBridge.coin_probability _

/-- In this actual parameter instance, the full log determines the entire legal
post. The real shadow is written from the ACTUALLY learned table and is proved
consistent along the reachable path below; it is not an independent learner. -/
def sourceModel (state : ℚ × ℚ) : Dynamics Log RealState Bool Bool RealState where
  policy := Kernel.deterministic (fun z => choose (actual state z.1))
    ((Measurable.of_discrete (f := fun log : Log => choose (actual state log))).comp measurable_fst)
  outcome := responseKernel state
  append := fun log a y => log ++ [(a,y)]
  measure := fun log _ _ => embed (read (actual state log))
  learn := fun _ table => table
  measurable_append := Measurable.of_discrete
  measurable_measure :=
    (Measurable.of_discrete (f := fun log : Log => embed (read (actual state log)))).comp measurable_fst
  measurable_learn := measurable_snd

instance sourceModel_policy_markov (state : ℚ × ℚ) : IsMarkovKernel (sourceModel state).policy where
  isProbabilityMeasure s := by
    change IsProbabilityMeasure (Measure.dirac (choose (actual state s.1)))
    infer_instance

instance sourceModel_outcome_markov (state : ℚ × ℚ) : IsMarkovKernel (sourceModel state).outcome := by
  change IsMarkovKernel (responseKernel state)
  infer_instance

/-- The actual sampled action changes the original command and cash, while
exactly the SAME Y is learned by the retained native Brier minimizer. -/
theorem source_update_commutes (state : ℚ × ℚ) (s : Log × RealState) (a y : Bool) :
    projection state (update (sourceModel state) (s,(a,y))) =
      LegalMath20261108.UnifiedFeedbackBridge.after (projection state s) y := by
  exact projection_append state s.1 s.2 a y

theorem source_private_is_actual (state : ℚ × ℚ) (s : Log × RealState) (a y : Bool) :
    (update (sourceModel state) (s,(a,y))).2 =
      projection state (update (sourceModel state) (s,(a,y))) := rfl

/-- Concrete next choice reads the new retained/loaded table; the old native
legalBest theorem is applied to the very cash score used by the next command. -/
theorem next_choice_reads_loaded_table (state : ℚ × ℚ) (s : Log × RealState) (a y : Bool) :
    (sourceModel state).policy (update (sourceModel state) (s,(a,y))) =
      Measure.dirac (choose (episode (actual state s.1) a y)) ∧
    Native.Decision.legalBest (score (episode (actual state s.1) a y))
      (fun _ => true) [false,true] = some (choose (episode (actual state s.1) a y)) := by
  have replayed : actual state (s.1 ++ [(a,y)]) = episode (actual state s.1) a y :=
    run_append _ s.1 a y
  constructor
  · change Measure.dirac (choose (actual state (s.1 ++ [(a,y)]))) = _
    rw [replayed]
  · exact actual_native_choice _

/-- This transports the actual CN transition, not a declared TransportData
commutation field. It holds on every log, with every rational initial table. -/
theorem source_kernel_projection (state : ℚ × ℚ) (s : Log × RealState) :
    (step (sourceModel state) s).map (projection state) =
      step LegalMath20261108.UnifiedFeedbackBridge.model (projection state s) := by
  classical
  ext B hB
  rw [Measure.map_apply (measurable_projection state) hB,
    step_apply (sourceModel state) s ((measurable_projection state) hB),joint,Kernel.compProd_apply]
  · change (∫⁻ action : Bool,
      LegalMath20261108.UnifiedFeedbackBridge.coin (projection state s)
        ((fun y => projection state (update (sourceModel state) (s,(action,y)))) ⁻¹' B)
        ∂(sourceModel state).policy s) = _
    simp_rw [source_update_commutes]
    rw [lintegral_const,measure_univ,mul_one,
      LegalMath20261108.UnifiedFeedbackBridge.step_two_atoms]
    simp [LegalMath20261108.UnifiedFeedbackBridge.coin,Measure.add_apply,smul_eq_mul,Set.indicator_apply]
  · exact ((measurable_update (sourceModel state)).comp
      (measurable_const.prodMk measurable_id)) ((measurable_projection state) hB)

/-- All time correlations, not just each time marginal, use the original
numeric process. The source action log retains its actual adaptive choices;
it is not relabelled as the original independent fair-action log. -/
theorem complete_source_path_projection (state : ℚ × ℚ)
    (μ : Measure (Log × RealState)) [IsProbabilityMeasure μ] :
    (pathLaw (sourceModel state) μ).map
      (LegalMath20261110.RemainingClosure.ProcessTransport.mapPath (projection state)) =
      pathLaw LegalMath20261108.UnifiedFeedbackBridge.model (μ.map (projection state)) :=
  LegalMath20261110.RemainingClosure.ProcessTransport.pathLaw_transport (sourceModel state)
    LegalMath20261108.UnifiedFeedbackBridge.model (projection state)
    (measurable_projection state) (source_kernel_projection state) μ

/-- Each complete finite prefix is transported jointly, with all preceding
actual commands/cash/source states replayed rather than reset. -/
theorem complete_source_prefix_projection (state : ℚ × ℚ)
    (μ : Measure (Log × RealState)) [IsProbabilityMeasure μ] (n : Nat) :
    (LegalMath20261110.RemainingClosure.ProcessTransport.prefixLaw (sourceModel state) μ n).map
      (LegalMath20261110.RemainingClosure.ProcessTransport.mapPrefix (projection state) n) =
      LegalMath20261110.RemainingClosure.ProcessTransport.prefixLaw
        LegalMath20261108.UnifiedFeedbackBridge.model (μ.map (projection state)) n :=
  LegalMath20261110.RemainingClosure.ProcessTransport.complete_prefix_transport (sourceModel state)
    LegalMath20261108.UnifiedFeedbackBridge.model (projection state)
    (measurable_projection state) (source_kernel_projection state) μ n

/-- The actual physical law is exactly the old Xi marginal, now at the actual
current CN replay and its loaded table. External A-IDENT is not inferred. -/
theorem source_response_from_same_xi (state : ℚ × ℚ) (s : Log × RealState) (a : Bool) :
    (sourceModel state).outcome (s,a) =
      ENNReal.ofReal ((∑ world, ∑ material,
        LegalMath20261109.PosteriorLaw.xi (read (actual state s.1)) (world,material,false) : ℚ) : ℝ) •
        Measure.dirac false +
      ENNReal.ofReal ((∑ world, ∑ material,
        LegalMath20261109.PosteriorLaw.xi (read (actual state s.1)) (world,material,true) : ℚ) : ℝ) •
        Measure.dirac true := by
  exact LegalMath20261109.PosteriorLaw.actual_Q_from_xi (read (actual state s.1)) a

/-- A declared matching statistical certificate remains conditional. This
consumer binds it to this same actual ERM-selected/retained/loaded CN table;
no sample risk or in-distribution claim is fabricated by fitting one label. -/
theorem calibrated_actual_table (s : Situation) (ready : FitReady s) (y : Bool)
    (query : Fin 2) (certificate : JurisLean.Candidates.LearningConsumer20261027.TableCalibration)
    (riskLimit : ℚ)
    (scope : certificate.protocol = EngineExamples.protocol)
    (table : certificate.table = (fitted (read s) y).table)
    (boundScope : certificate.bounds.contract = EngineExamples.protocol.fit)
    (coverage : 0 < certificate.bounds.lowerCoverage)
    (nonnegative : 0 ≤ certificate.bounds.upperRisk)
    (acceptable : certificate.bounds.upperRisk ≤ riskLimit) :
    JurisLean.Candidates.LearningConsumer20261027.fitThenCalibrationGate
      EngineExamples.protocol EngineExamples.protocol labelLoss (models (read s)) (sample y)
      query certificate riskLimit true =
      .known ⟨EngineExamples.protocol,(learned s y).core.state.A.theta.getD query.val 0,certificate.bounds⟩ ∧
    ∀ model ∈ models (read s),
      empiricalScore (JurisLean.Candidates.LearningConsumer20261027.tableLoss labelLoss) (sample y)
        (fitted (read s) y).table ≤
      empiricalScore (JurisLean.Candidates.LearningConsumer20261027.tableLoss labelLoss) (sample y) model := by
  have old := JurisLean.Candidates.LearningConsumer20261027.u01_6_successful_pipeline_uses_actual_empirical_minimizer
    EngineExamples.protocol labelLoss (models (read s)) (sample y) query certificate riskLimit
    (fitted (read s) y) (native_fit_output (read s) y) scope table boundScope coverage nonnegative acceptable
  constructor
  · convert old.1 using 1
    rw [learned_formula s ready y]
    rfl
  · exact old.2.2

end Menu

end Numeric

namespace InstitutionalContinuation
open Numeric
open InstitutionRules Examples

/-- The structural institution state is preserved by this actual observation,
preparation and private-learning continuation. New F/E/candidates/reports are
retained separately; old evidence cells are proved below, not globally erased. -/
structure InstitutionFrame (before after : Situation) : Prop where
  norms : after.core.state.N = before.core.state.N
  relations : after.core.state.L = before.core.state.L
  life : after.life = before.life
  agencies : after.agencies = before.agencies
  stayed : after.stayed = before.stayed
  bankruptcy : after.bankruptcyCases = before.bankruptcyCases
  tracks : after.tracks = before.tracks
  meanings : after.meanings = before.meanings
  decisions : after.core.state.decisions = before.core.state.decisions
  bindings : after.core.state.bindings = before.core.state.bindings
  ledger : after.core.state.ledger = before.core.state.ledger
  accounts : after.accounts = before.accounts
  templates : after.templates = before.templates
  executions : after.executions = before.executions
  interest : after.interest = before.interest
  cutoffs : after.cutoffs = before.cutoffs
  paused : after.paused = before.paused
  actRelations : after.actRelations = before.actRelations
  choices : after.choices = before.choices
  uses : after.uses = before.uses
  disputes : after.disputes = before.disputes
  participations : after.participations = before.participations
  causalClauses : after.causalClauses = before.causalClauses
  offenseSlots : after.offenseSlots = before.offenseSlots
  decisionSources : after.decisionSources = before.decisionSources
  equalReductionRules : after.equalReductionRules = before.equalReductionRules
  constraints : after.core.state.constraints = before.core.state.constraints
  clocks : after.core.state.clocks = before.core.state.clocks
  proceedings : after.core.state.proceedings = before.core.state.proceedings
  interpretations : after.core.state.interpretations = before.core.state.interpretations
  refusals : after.core.state.refusals = before.core.state.refusals

lemma actual_institution_frame (s : Situation) (ready : FitReady s) (y : Bool) :
    InstitutionFrame s (learned s y) := by
  constructor <;> rw [learned_formula s ready y,fitPost_formula s ready y] <;> rfl

lemma old_evidence_preserved (s : Situation) (ready : FitReady s) (y : Bool)
    (i : Ref .material) (old : i ∈ s.core.keys) :
    (learned s y).core.state.E i = s.core.state.E i := by
  have distinct : i ≠ materialId s := by
    intro equal
    apply new_material_not_key s
    simpa [equal] using old
  rw [learned_formula s ready y,fitPost_formula s ready y]
  simp [Law.proposeEngine,EffectIR.adjust,EffectIR.proposal,EffectIR.write,
    prepared,admitted,recorded,physical,CaseState.setCell,CaseState.putState,
    Situation.withCore,setEvidence,distinct,Ne.symm distinct]

lemma actual_retained_report (s : Situation) (ready : FitReady s) (y : Bool) :
    (learned s y).engineResults.head? = some ⟨input s y,.known (fitted (read s) y)⟩ := by
  rw [learned_formula s ready y,fitPost_formula s ready y]
  rfl

local instance : MeasurableSpace Situation := ⊤

def reading (s : Situation) : LegalMath20261108.UnifiedFeedbackBridge.State := embed (read s)

lemma measurable_reading : Measurable reading := by
  intro target measurable
  trivial

/-- A genuine common-response kernel on full CN states. Every outcome is
observed, admitted, fitted, retained and learned in that SAME old state. -/
def learningKernel : Kernel Situation Situation where
  toFun s := (LegalMath20261108.UnifiedFeedbackBridge.coin (reading s)).map (learned s)
  measurable' := by
    intro target measurable
    trivial

instance learningKernel_markov : IsMarkovKernel learningKernel where
  isProbabilityMeasure s := by
    change IsProbabilityMeasure
      ((LegalMath20261108.UnifiedFeedbackBridge.coin (reading s)).map (learned s))
    exact Measure.isProbabilityMeasure_map (Measurable.of_discrete : Measurable (learned s)).aemeasurable

/-- The commuting equation is calculated from the old native minimizer and
actual source commands, under only their checked permissions/version guards. -/
theorem actual_kernel_projection (s : Situation) (ready : FitReady s) :
    (learningKernel s).map reading =
      step LegalMath20261108.UnifiedFeedbackBridge.model (reading s) := by
  change ((LegalMath20261108.UnifiedFeedbackBridge.coin (reading s)).map (learned s)).map reading = _
  rw [Measure.map_map measurable_reading (Measurable.of_discrete : Measurable (learned s))]
  have functions : reading ∘ learned s = LegalMath20261108.UnifiedFeedbackBridge.after (reading s) := by
    funext y
    change embed (read (learned s y)) = _
    rw [learned_read s ready y,afterQ_embed]
    rfl
  rw [functions]
  ext B hB
  rw [Measure.map_apply Measurable.of_discrete hB,LegalMath20261108.UnifiedFeedbackBridge.step_two_atoms]
  simp [LegalMath20261108.UnifiedFeedbackBridge.coin,Measure.add_apply,smul_eq_mul,Set.indicator_apply]

/-- The following supplied legal policy receives the ACTUAL learned CN post,
including unchanged institution state and the loaded new private table. Its
own permission support and observation factorization remain its original
conditions; a numerical menu does not authorize unrelated institutions. -/
theorem following_policy_reads_actual_post {A : Type*} [MeasurableSpace A]
    (policy : Kernel Situation A) [IsMarkovKernel policy] (s : Situation)
    {B : Set A} (hB : MeasurableSet B) :
    (policy ∘ₖ learningKernel) s B =
      ∫⁻ y, policy (learned s y) B
        ∂LegalMath20261108.UnifiedFeedbackBridge.coin (reading s) := by
  rw [Kernel.comp_apply' policy learningKernel s hB]
  change (∫⁻ post, policy post B
    ∂(LegalMath20261108.UnifiedFeedbackBridge.coin (reading s)).map (learned s)) = _
  rw [lintegral_map (Kernel.measurable_coe policy hB) Measurable.of_discrete]

def afterCommand {α : Type} (s : Situation) (c : Command α) : Situation := (executeCommand s c).after

def completeCommands {α : Type} (s : Situation) (c : Command α) (y : Bool) : List PackedCommand :=
  ⟨α,c⟩ :: preparationCommands (afterCommand s c) y

lemma complete_replay {α : Type} (s : Situation) (c : Command α)
    (ready : FitReady (afterCommand s c)) (y : Bool) :
    FullEventLog.CN.replay s (completeCommands s c y) = learned (afterCommand s c) y := by
  change FullEventLog.CN.replay (afterCommand s c) (preparationCommands (afterCommand s c) y) = _
  exact preparation_replay _ ready y

/-- The same complete original command list is a genuine old CN.model history;
its private coordinate is the actual post-institution native learned table. -/
theorem common_model_realization {α : Type} (s : Situation) (c : Command α)
    (ready : FitReady (afterCommand s c)) (y : Bool) :
    encode s (fun i : Fin (completeCommands s c y).length => (completeCommands s c y).get i)
      (List.finRange (completeCommands s c y).length) =
    (List.finRange (completeCommands s c y).length,(learned (afterCommand s c) y).core.state.A.theta) := by
  unfold encode
  rw [finite_sequence_catalog,complete_replay s c ready y]

/-- All concrete branches below derive their guard witnesses. Failed or
conflicting original legal results remain part of the same completed history. -/
def Connected (s : Situation) : Prop :=
  FitReady s ∧
  (∀ y, InstitutionFrame s (learned s y) ∧ FitReady (learned s y) ∧
    (learned s y).engineResults.head? = some ⟨input s y,.known (fitted (read s) y)⟩ ∧
    reading (learned s y) = LegalMath20261108.UnifiedFeedbackBridge.after (reading s) y) ∧
  (learningKernel s).map reading = step LegalMath20261108.UnifiedFeedbackBridge.model (reading s)

lemma connected (s : Situation) (ready : FitReady s) : Connected s := by
  refine ⟨ready,?_,actual_kernel_projection s ready⟩
  intro y
  refine ⟨actual_institution_frame s ready y,learned_ready s ready y,actual_retained_report s ready y,?_⟩
  change embed (read (learned s y)) = _
  rw [learned_read s ready y,afterQ_embed]
  rfl

/-- Lifecycle uses its real formation and revoked posts, including empty L. -/
theorem lifecycle_continuation (y : Bool) :
    Connected formedCase ∧ Connected revokedCase.after ∧
    (learned formedCase y).core.state.L = [toyRelation] ∧
    (learned revokedCase.after y).core.state.L = [] ∧
    (learned revokedCase.after y).core.state.F = revokedCase.after.core.state.F ++ [event revokedCase.after y] := by
  have formedReady : FitReady formedCase := by decide
  have revokedReady : FitReady revokedCase.after := by decide
  refine ⟨connected _ formedReady,connected _ revokedReady,?_,?_,learned_events _ revokedReady y⟩
  · rw [(actual_institution_frame _ formedReady y).relations]
    exact actual_nonjudicial_formation.1
  · rw [(actual_institution_frame _ revokedReady y).relations]
    exact lifecycle_actual.2.2.2.2.1

theorem agency_continuation (y : Bool) :
    Connected delegated.after ∧
    (learned delegated.after y).core.state.N.grants.contains child = true ∧
    ((learned delegated.after y).agencies toyScope.object).map Agency.principalCapacity = some true := by
  have ready : FitReady delegated.after := by decide
  refine ⟨connected _ ready,?_,?_⟩
  · rw [(actual_institution_frame _ ready y).norms]
    exact agency_actual.1
  · rw [(actual_institution_frame _ ready y).agencies]
    exact agency_actual.2

def jurisdictionPost : Situation := afterCommand normal
  (.institution (.jurisdiction true ⟨true,false,false,false,false,false,false,true⟩))

theorem jurisdiction_continuation :
    (executeCommand normal (.institution (.jurisdiction true
      ⟨true,false,false,false,false,false,false,true⟩))).answer = .success (some .ordinary) ∧
    Connected jurisdictionPost := by
  exact ⟨jurisdiction_actual.1,connected _ (by decide)⟩

theorem evidence_continuation : Connected normal ∧ Connected (recordedCase confirmation .evidence) ∧
    Connected withdrawnCase ∧ rawOf (withdrawnCase.core.state.E ⟨9⟩) = some toyRaw := by
  exact ⟨connected _ (by decide),connected _ (by decide),connected _ (by decide),evidence_actual.2.2.2.1⟩

def acquisitionPost : Situation := afterCommand acquisitionStart
  (.acquisitionEvidence (call .decide) parties .ordinary311 faithAtom priceAtom publicityAtom)
def badFaithPost : Situation := afterCommand badFaithStart
  (.acquisitionEvidence (call .decide) parties .ordinary311 faithAtom priceAtom publicityAtom)

theorem acquisition_continuation :
    (executeCommand acquisitionStart (.acquisitionEvidence (call .decide) parties .ordinary311
      faithAtom priceAtom publicityAtom)).answer = .success .established ∧
    Connected acquisitionPost ∧ Connected badFaithPost := by
  exact ⟨acquisition_actual.1,connected _ (by decide),connected _ (by decide)⟩

def offensePost : Situation := afterCommand (offenseStart aYi)
  (.offenseEvidence (call .decide) aYi ev1 q1 toyAtom toyAtom)
def missingOffensePost : Situation := afterCommand (offenseStart aYi)
  (.offenseEvidence (call .decide) aYi ev2 q1 toyAtom toyAtom)

theorem offense_continuation :
    (executeCommand (offenseStart aYi) (.offenseEvidence (call .decide) aYi ev1 q1
      toyAtom toyAtom)).answer = .success toyScope.question ∧
    Connected offensePost ∧ Connected missingOffensePost := by
  exact ⟨offense_actual.1,connected _ (by decide),connected _ (by decide)⟩

theorem bankruptcy_continuation (y : Bool) :
    Connected accepted ∧ (learned accepted y).stayed = [procD.id] ∧
    (learned accepted y).bankruptcyCases aD = some 0 ∧
    (learned accepted y).bankruptcyCases aO = none := by
  have ready : FitReady accepted := by decide
  refine ⟨connected _ ready,?_,?_,?_⟩
  · rw [(actual_institution_frame _ ready y).stayed]; exact bankruptcy_actual.1
  · rw [(actual_institution_frame _ ready y).bankruptcy]; exact bankruptcy_actual.2.1
  · rw [(actual_institution_frame _ ready y).bankruptcy]; exact bankruptcy_actual.2.2.1

def missingCompensationPost : Situation := afterCommand noTermination
  (.institution (.compensation (call .decide) compensationLaw.guard .criminal ⟨62⟩))

theorem compensation_continuation (y : Bool) :
    Connected compensated.after ∧ Connected missingCompensationPost ∧
    (learned compensated.after y).tracks.stateCompensation = [(.criminal,⟨62⟩)] ∧
    (learned compensated.after y).tracks.civil = [] := by
  have ready : FitReady compensated.after := by decide
  refine ⟨connected _ ready,connected _ (by decide),?_,?_⟩
  · rw [(actual_institution_frame _ ready y).tracks]; exact compensation_actual.1
  · rw [(actual_institution_frame _ ready y).tracks]; exact compensation_actual.2.1

def rightsPost : Situation := afterCommand normal (.institution .rightsConflict)

theorem rights_continuation (y : Bool) :
    (executeCommand normal (.institution .rightsConflict)).answer = .conflict .competentReview ∧
    Connected rightsPost ∧ (learned rightsPost y).core.state.L = normal.core.state.L := by
  have ready : FitReady rightsPost := by decide
  refine ⟨rights_actual.1,connected _ ready,?_⟩
  rw [(actual_institution_frame _ ready y).relations]
  exact rights_actual.2

theorem interpretation_continuation (y : Bool) :
    Connected interpreted ∧ (learned interpreted y).meanings = interpreted.meanings ∧
    (executeCommand interpreted (.contractQuery (call .decide) toyScope.object)).answer = .success .established := by
  have ready : FitReady interpreted := by decide
  exact ⟨connected _ ready,(actual_institution_frame _ ready y).meanings,interpretation_actual.1⟩

theorem resJudicata_continuation (y : Bool) :
    Connected bound ∧ (learned bound y).core.state.bindings = bound.core.state.bindings ∧
    (executeCommand bound (.storedResJudicata ⟨70⟩ ⟨12⟩ toyScope 5)).answer = .success true ∧
    (executeCommand bound (.storedResJudicata ⟨70⟩ ⟨99⟩ toyScope 5)).answer = .success false := by
  have ready : FitReady bound := by decide
  exact ⟨connected _ ready,(actual_institution_frame _ ready y).bindings,
    resJudicata_actual.1,resJudicata_actual.2.1⟩

def proposalPost : Situation := afterCommand normal (.institution (.propose fitOut))

theorem proposal_continuation (y : Bool) :
    Connected proposalPost ∧ (learned proposalPost y).core.state.decisions = [] ∧
    (learned proposalPost y).core.state.bindings.isEmpty = true := by
  have ready : FitReady proposalPost := by decide
  refine ⟨connected _ ready,?_,?_⟩
  · rw [(actual_institution_frame _ ready y).decisions]; exact proposal_actual.2.1
  · rw [(actual_institution_frame _ ready y).bindings]; exact proposal_actual.2.2

def lateLifecyclePost : Situation := afterCommand revokeStart
  (.institution (.revoke (call .constitute) (.atom toyAtom) toyScope.object {revokeGuard with atTime := 100}))
def overScopeAgencyPost : Situation := afterCommand agencyStart
  (.institution (.delegate (call .constitute) (.atom toyAtom) toyScope.object {child with stop := 100}))
def exclusiveJurisdictionPost : Situation := afterCommand normal
  (.institution (.jurisdiction true ⟨true,true,false,false,false,false,true,true⟩))
def lostAcquisitionPost : Situation := afterCommand acquisitionStart
  (.acquisitionEvidence (call .decide) parties .lost312 faithAtom priceAtom publicityAtom)

/-- The old failure/conflict cases also continue from their ACTUAL posts.
Continuing private learning never retroactively changes their original answer. -/
theorem failure_exits_continue :
    Connected lateLifecyclePost ∧ Connected overScopeAgencyPost ∧
    Connected exclusiveJurisdictionPost ∧ Connected lostAcquisitionPost ∧
    (executeCommand revokeStart (.institution (.revoke (call .constitute) (.atom toyAtom)
      toyScope.object {revokeGuard with atTime := 100}))).after.core.state.L = revokeStart.core.state.L ∧
    (executeCommand agencyStart (.institution (.delegate (call .constitute) (.atom toyAtom)
      toyScope.object {child with stop := 100}))).after.core.state.N.grants = agencyStart.core.state.N.grants ∧
    (executeCommand normal (.institution (.jurisdiction true
      ⟨true,true,false,false,false,false,true,true⟩))).answer = .success none ∧
    (executeCommand acquisitionStart (.acquisitionEvidence (call .decide) parties .lost312
      faithAtom priceAtom publicityAtom)).answer = .unknown .systemNotJudge ∧
    (executeCommand noTermination (.institution (.compensation (call .decide)
      compensationLaw.guard .criminal ⟨62⟩))).answer = .unknown .inputUnchecked := by
  exact ⟨connected _ (by decide),connected _ (by decide),connected _ (by decide),connected _ (by decide),
    lifecycle_failure_preserves_effect,agency_over_scope_rejected,jurisdiction_actual.2,
    acquisition_actual.2.2,compensation_missing_prerequisite_not_automatic⟩

end InstitutionalContinuation

#print axioms replay_append
#print axioms finite_sequence_catalog
#print axioms actual_post_commutes
#print axioms actual_step_lintegral
#print axioms actual_step_law
#print axioms next_action_reads_actual_post
#print axioms readout_kernel_transport
#print axioms encode_injective
#print axioms actual_legal_step_worlds
#print axioms actual_learning_frame
#print axioms learn_retained_actual_table
#print axioms measurable_joint_legal_readout
#print axioms legal_entity_feedback_law
#print axioms learnReport_entity_frame

#print axioms representedReply_eq
#print axioms Institutions.formation_feedback
#print axioms Institutions.lifecycle_feedback
#print axioms Institutions.agency_feedback
#print axioms Institutions.jurisdiction_feedback
#print axioms Institutions.evidence_feedback
#print axioms Institutions.acquisition_feedback
#print axioms Institutions.offense_feedback
#print axioms Institutions.bankruptcy_feedback
#print axioms Institutions.compensation_feedback
#print axioms Institutions.rights_feedback
#print axioms Institutions.interpretation_feedback
#print axioms Institutions.resJudicata_feedback
#print axioms Institutions.proposal_feedback
#print axioms Engines.retained_call
#print axioms Engines.fit_feedback
#print axioms Engines.probability_feedback
#print axioms Engines.causal_feedback
#print axioms Engines.bargain_feedback
#print axioms Engines.cash_feedback
#print axioms Engines.exact_feedback
#print axioms Engines.behavior_actual_selected
#print axioms Engines.behavior_feedback
#print axioms Engines.rsi_feedback
#print axioms Engines.fit_to_private_feedback
#print axioms Engines.rsi_loaded_report_table

#print axioms CompilerBridge.explicit_negative_iff
#print axioms CompilerBridge.missing_support_is_not_negation
#print axioms CompilerBridge.finite_closure_same_cn_world
#print axioms CompilerBridge.provenance_same_cn_world
#print axioms CompilerBridge.must_facts_strict_counterexample
#print axioms CompilerBridge.Actual.current_admitted_seed
#print axioms CompilerBridge.Actual.current_nonempty
#print axioms CompilerBridge.Actual.admitted_closure_feedback

#print axioms Numeric.native_fit_output
#print axioms Numeric.fitted_numeric_projection
#print axioms Numeric.fitted_original_after
#print axioms Numeric.new_material_absent

#print axioms Numeric.physical_actual
#print axioms Numeric.recorded_actual
#print axioms Numeric.admitted_actual
#print axioms Numeric.prepared_actual
#print axioms Numeric.prepared_lookup
#print axioms Numeric.prepared_allowed
#print axioms Numeric.fitPost_formula
#print axioms Numeric.learned_formula
#print axioms Numeric.learned_read
#print axioms Numeric.learned_ready
#print axioms Numeric.preparation_replay
#print axioms Numeric.learned_events
#print axioms Numeric.learned_ledger

#print axioms Numeric.initial_read
#print axioms Numeric.initial_ready
#print axioms Numeric.learned_legal_ready
#print axioms Numeric.world_check
#print axioms Numeric.source_admitted

#print axioms Numeric.performance_selected_rule
#print axioms Numeric.performance_selected_template
#print axioms Numeric.performance_assessed
#print axioms Numeric.actual_permission
#print axioms Numeric.cash_source_known
#print axioms Numeric.learned_payment_event
#print axioms Numeric.performPayment_actual

#print axioms Numeric.cashPost_ready
#print axioms Numeric.performPaired_actual
#print axioms Numeric.actual_payment
#print axioms Numeric.episode_replay
#print axioms Numeric.episode_read
#print axioms Numeric.episode_ready
#print axioms Numeric.episode_keeps_events
#print axioms Numeric.run_ready
#print axioms Numeric.run_read
#print axioms Numeric.every_finite_prefix
#print axioms Numeric.Menu.native_source
#print axioms Numeric.Menu.event_present
#print axioms Numeric.Menu.post_ready
#print axioms Numeric.Menu.raw_performance
#print axioms Numeric.Menu.public_performance
#print axioms Numeric.Menu.actual_episode
#print axioms Numeric.Menu.episode_replay
#print axioms Numeric.Menu.episode_read
#print axioms Numeric.Menu.episode_ready
#print axioms Numeric.Menu.episode_events
#print axioms Numeric.Menu.actual_cash_payoff
#print axioms Numeric.Menu.actual_native_choice
#print axioms Numeric.Menu.chosen_maximizes_actual_cash
#print axioms Numeric.Menu.score_from_same_xi
#print axioms Numeric.Menu.learning_changes_actual_choice
#print axioms Numeric.Menu.expected_actual_cash
#print axioms Numeric.Menu.expected_amount
#print axioms Numeric.Menu.realizedPayoff_eq_amount
#print axioms Numeric.Menu.native_choice_maximizes_actual_expected_cash
#print axioms Numeric.Menu.actual_reachable_learning_changes_choice
#print axioms Numeric.Menu.run_ready
#print axioms Numeric.Menu.run_append
#print axioms Numeric.Menu.full_replay
#print axioms Numeric.Menu.full_history_decoded
#print axioms Numeric.Menu.projection_append
#print axioms Numeric.Menu.source_update_commutes
#print axioms Numeric.Menu.source_private_is_actual
#print axioms Numeric.Menu.next_choice_reads_loaded_table
#print axioms Numeric.Menu.source_kernel_projection
#print axioms Numeric.Menu.complete_source_path_projection
#print axioms Numeric.Menu.complete_source_prefix_projection
#print axioms Numeric.Menu.source_response_from_same_xi
#print axioms Numeric.Menu.calibrated_actual_table
#print axioms InstitutionalContinuation.actual_institution_frame
#print axioms InstitutionalContinuation.old_evidence_preserved
#print axioms InstitutionalContinuation.actual_retained_report
#print axioms InstitutionalContinuation.actual_kernel_projection
#print axioms InstitutionalContinuation.following_policy_reads_actual_post
#print axioms InstitutionalContinuation.complete_replay
#print axioms InstitutionalContinuation.common_model_realization
#print axioms InstitutionalContinuation.connected
#print axioms InstitutionalContinuation.lifecycle_continuation
#print axioms InstitutionalContinuation.agency_continuation
#print axioms InstitutionalContinuation.jurisdiction_continuation
#print axioms InstitutionalContinuation.evidence_continuation
#print axioms InstitutionalContinuation.acquisition_continuation
#print axioms InstitutionalContinuation.offense_continuation
#print axioms InstitutionalContinuation.bankruptcy_continuation
#print axioms InstitutionalContinuation.compensation_continuation
#print axioms InstitutionalContinuation.rights_continuation
#print axioms InstitutionalContinuation.interpretation_continuation
#print axioms InstitutionalContinuation.resJudicata_continuation
#print axioms InstitutionalContinuation.proposal_continuation
#print axioms InstitutionalContinuation.failure_exits_continue

end
end LegalMath.RemainingClosure.CNSemanticConnection
