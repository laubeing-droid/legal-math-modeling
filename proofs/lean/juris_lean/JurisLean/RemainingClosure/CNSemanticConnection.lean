import JurisLean.RemainingClosure.FullEventLog
import JurisLean.CN.Completion20261105.WorldSemantics
import JurisLean.CN.Completion20261105.Examples
import JurisLean.CN.Completion20261105.EngineExamples

/-!
Actual CN commands realize the existing ClosedLoop.Dynamics on their complete
ordered histories. The policy is any declared measurable kernel and reads the
actual updated private table. All legal, quantity and learning readouts use the
same replay. Source only; CI_NOT_RUN until subject-bound evidence exists.
-/
namespace LegalMath.RemainingClosure.CNSemanticConnection

open MeasureTheory ProbabilityTheory
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
  rw [← lintegral_indicator_one hB,
    actual_step_lintegral initial catalog policy h _ (measurable_const.indicator hB),
    Measure.map_apply Measurable.of_discrete hB]
  simpa [Set.indicator_apply] using
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
  rw [nextAction, Kernel.comp_apply' _ _ _ hB,
    actual_step_lintegral initial catalog policy h _ (Kernel.measurable_coe policy hB)]
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
  rw [actual_step_law, Measure.map_map
    ((Measurable.of_discrete (f := fun h : List (Fin k) => read (replay initial catalog h))).comp measurable_fst)
    Measurable.of_discrete]
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

def bindingReadout (s : Situation) (q : EntityQuery) : Bool :=
  s.core.state.bindings.any (fun b => match b with
    | .decide d => d.decision.document == q.document && d.kind == q.bindingKind &&
        withinBinding d.index q.person q.scope q.time
    | .other _ => false)

/-- Different value types preserve the six distinctions of v4 section 2.3. -/
structure SixJudgments where
  truth : Bool
  support : Judgment
  justified : Check Judgment
  recognized : Option Judgment
  valid : Option Bool
  binding : Bool

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
  finality : Bool
  correctness : Option Bool
  performance : List Performance

def fourEffects (s : Situation) (q : EntityQuery) : FourEffects :=
  ⟨(recordedDecision s q).map (fun d => d.valid),
   bindingReadout s {q with bindingKind := .resJudicata},
   (recordedDecision s q).map (fun d =>
     d.judgment == evalFormula (q.world.assessment q.law q.method) (.atom q.atom)),
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

end
end LegalMath.RemainingClosure.CNSemanticConnection
