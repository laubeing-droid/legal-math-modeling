import JurisLean.Candidates.BusinessFeedbackLoop20261027
import JurisLean.FeedbackHistoryBridge

/-! Actual business histories realize the joint feedback dynamics.  A finite
command catalog retains the full original inputs, including measurement data.
Every finite command sequence admits such a catalog; no numeric replacement of
business outcomes or of the original learner is used. -/

namespace LegalMath20261109.BusinessProcess

open MeasureTheory ProbabilityTheory
open LegalMath20261108.ClosedLoop
open JurisLean.Candidates.Final20261021
open JurisLean.Candidates.AdaptiveRoundLedger20261027
open JurisLean.Candidates.MeasuredPolicy20261027
open JurisLean.Candidates.BusinessMeasurement20261027

noncomputable section

variable {W : Type} {m k : Nat}

local instance : MeasurableSpace (JurisLean.Candidates.BusinessFeedbackLoop20261027.State m) := ⊤
local instance : MeasurableSpace (RoundState m) := ⊤
local instance : MeasurableSpace (Fin k) := ⊤
local instance : MeasurableSpace (List (Fin k)) := ⊤

def replay (initial : JurisLean.Candidates.BusinessFeedbackLoop20261027.State m) (catalog : Fin k → JurisLean.Candidates.BusinessFeedbackLoop20261027.Command W m)
    (history : List (Fin k)) : JurisLean.Candidates.BusinessFeedbackLoop20261027.State m :=
  history.foldl (fun s a => JurisLean.Candidates.BusinessFeedbackLoop20261027.step s (catalog a)) initial

theorem replay_append (initial : JurisLean.Candidates.BusinessFeedbackLoop20261027.State m) (catalog : Fin k → JurisLean.Candidates.BusinessFeedbackLoop20261027.Command W m)
    (h : List (Fin k)) (a : Fin k) :
    replay initial catalog (h ++ [a]) = JurisLean.Candidates.BusinessFeedbackLoop20261027.step (replay initial catalog h) (catalog a) := by
  simp [replay, List.foldl_append]

def encode (initial : JurisLean.Candidates.BusinessFeedbackLoop20261027.State m) (catalog : Fin k → JurisLean.Candidates.BusinessFeedbackLoop20261027.Command W m)
    (h : List (Fin k)) : List (Fin k) × RoundState m :=
  (h, (replay initial catalog h).learning)

def response (initial : JurisLean.Candidates.BusinessFeedbackLoop20261027.State m) (catalog : Fin k → JurisLean.Candidates.BusinessFeedbackLoop20261027.Command W m)
    (z : (List (Fin k) × RoundState m) × Fin k) : JurisLean.Candidates.BusinessFeedbackLoop20261027.State m :=
  JurisLean.Candidates.BusinessFeedbackLoop20261027.step (replay initial catalog z.1.1) (catalog z.2)

lemma measurable_response (initial : JurisLean.Candidates.BusinessFeedbackLoop20261027.State m) (catalog : Fin k → JurisLean.Candidates.BusinessFeedbackLoop20261027.Command W m) :
    Measurable (response initial catalog) :=
  (Measurable.of_discrete (f := fun z : List (Fin k) × Fin k =>
    JurisLean.Candidates.BusinessFeedbackLoop20261027.step (replay initial catalog z.1) (catalog z.2))).comp
      (measurable_fst.fst.prodMk measurable_snd)

def model (initial : JurisLean.Candidates.BusinessFeedbackLoop20261027.State m) (catalog : Fin k → JurisLean.Candidates.BusinessFeedbackLoop20261027.Command W m)
    (pick : List (Fin k) → Fin k) :
    Dynamics (List (Fin k)) (RoundState m) (Fin k) (JurisLean.Candidates.BusinessFeedbackLoop20261027.State m) (RoundState m) where
  policy := Kernel.deterministic (fun s => pick s.1)
    (Measurable.of_discrete.comp measurable_fst)
  outcome := Kernel.deterministic (response initial catalog) (measurable_response initial catalog)
  append := fun h a _ => h ++ [a]
  measure := fun _ _ actual => actual.learning
  learn := fun _ actual => actual
  measurable_append :=
    (Measurable.of_discrete (f := fun z : List (Fin k) × Fin k => z.1 ++ [z.2])).comp
      (measurable_fst.prodMk measurable_snd.fst)
  measurable_measure :=
    (Measurable.of_discrete (f := fun s : JurisLean.Candidates.BusinessFeedbackLoop20261027.State m => s.learning)).comp measurable_snd.snd
  measurable_learn := measurable_snd

instance model_policy_markov (initial : JurisLean.Candidates.BusinessFeedbackLoop20261027.State m) (catalog : Fin k → JurisLean.Candidates.BusinessFeedbackLoop20261027.Command W m)
    (pick : List (Fin k) → Fin k) : IsMarkovKernel (model initial catalog pick).policy := by
  dsimp [model]
  infer_instance

instance model_outcome_markov (initial : JurisLean.Candidates.BusinessFeedbackLoop20261027.State m) (catalog : Fin k → JurisLean.Candidates.BusinessFeedbackLoop20261027.Command W m)
    (pick : List (Fin k) → Fin k) : IsMarkovKernel (model initial catalog pick).outcome := by
  dsimp [model]
  infer_instance

/-- The old actual poststate, including its actual learner, is the new update. -/
theorem actual_post_commutes (initial : JurisLean.Candidates.BusinessFeedbackLoop20261027.State m) (catalog : Fin k → JurisLean.Candidates.BusinessFeedbackLoop20261027.Command W m)
    (pick : List (Fin k) → Fin k) (h : List (Fin k)) (a : Fin k) :
    update (model initial catalog pick)
      (encode initial catalog h, (a, JurisLean.Candidates.BusinessFeedbackLoop20261027.step (replay initial catalog h) (catalog a))) =
        encode initial catalog (h ++ [a]) := by
  simp [update, historyOut, parameterOut, feedback, model, encode, replay_append]

theorem actual_step_law (initial : JurisLean.Candidates.BusinessFeedbackLoop20261027.State m) (catalog : Fin k → JurisLean.Candidates.BusinessFeedbackLoop20261027.Command W m)
    (pick : List (Fin k) → Fin k) (h : List (Fin k)) :
    step (model initial catalog pick) (encode initial catalog h) =
      Measure.dirac (encode initial catalog (h ++ [pick h])) := by
  ext s hs
  rw [step_apply _ _ hs, joint, Kernel.compProd_apply]
  · simp [model, Kernel.deterministic_apply, response, encode,
      update, historyOut, parameterOut, feedback, replay_append,
      Set.indicator_apply, Measure.dirac_apply' _ hs]
  · exact ((measurable_update (model initial catalog pick)).comp
      (measurable_const.prodMk measurable_id)) hs

def legalInvariant (initial : JurisLean.Candidates.BusinessFeedbackLoop20261027.State m) (catalog : Fin k → JurisLean.Candidates.BusinessFeedbackLoop20261027.Command W m)
    (s : List (Fin k) × RoundState m) : Prop :=
  JurisLean.Candidates.BusinessFeedbackLoop20261027.KnownBusinessInvariant (replay initial catalog s.1) ∧
    s.2 = (replay initial catalog s.1).learning ∧
    s.2.limit = initial.learning.limit ∧ roundSpent s.2 ≤ initial.learning.limit

/-- The invariant is transported from the original finite-command theorem. -/
theorem replay_invariant (initial : JurisLean.Candidates.BusinessFeedbackLoop20261027.State m) (catalog : Fin k → JurisLean.Candidates.BusinessFeedbackLoop20261027.Command W m)
    (valid : JurisLean.Candidates.BusinessFeedbackLoop20261027.KnownBusinessInvariant initial)
    (bounded : roundSpent initial.learning ≤ initial.learning.limit) (h : List (Fin k)) :
    legalInvariant initial catalog (encode initial catalog h) := by
  have old := JurisLean.Candidates.BusinessFeedbackLoop20261027.arbitrary_finite_commands_consume_actual_posts
    (h.map catalog) initial valid bounded
  have same : (h.map catalog).foldl JurisLean.Candidates.BusinessFeedbackLoop20261027.step initial = replay initial catalog h := by
    simp [replay, List.foldl_map]
  rw [same] at old
  exact ⟨old.1, rfl, old.2.1, old.2.2⟩

theorem actual_law_preserves_invariant (initial : JurisLean.Candidates.BusinessFeedbackLoop20261027.State m)
    (catalog : Fin k → JurisLean.Candidates.BusinessFeedbackLoop20261027.Command W m) (pick : List (Fin k) → Fin k)
    (valid : JurisLean.Candidates.BusinessFeedbackLoop20261027.KnownBusinessInvariant initial)
    (bounded : roundSpent initial.learning ≤ initial.learning.limit) (h : List (Fin k)) :
    ∀ᵐ s ∂step (model initial catalog pick) (encode initial catalog h),
      legalInvariant initial catalog s := by
  rw [actual_step_law]
  simpa using (replay_invariant initial catalog valid bounded (h ++ [pick h]))

/-- Any finite original sequence is representable without changing its inputs. -/
theorem finite_sequence_catalog (commands : List (JurisLean.Candidates.BusinessFeedbackLoop20261027.Command W m)) (initial : JurisLean.Candidates.BusinessFeedbackLoop20261027.State m) :
    replay initial (fun i : Fin commands.length => commands.get i)
      (List.finRange commands.length) = commands.foldl JurisLean.Candidates.BusinessFeedbackLoop20261027.step initial := by
  simp [replay, ← List.foldl_map]

/-! Actual information use: exact factorization, followed by the original
accepted-source, time-cutoff, and permitted-policy theorems. -/

def measureView (current : Option Ledger.Handle) (input : JurisLean.Candidates.BusinessFeedbackLoop20261027.MeasurementInput m) :
    MeasurementResult :=
  match current with
  | none => .unknown .unknownCommit
  | some post => measureBusiness post input.dictionary input.now input.sources input.closures input.rows

theorem measurement_factors (state : JurisLean.Candidates.BusinessFeedbackLoop20261027.State m) (input : JurisLean.Candidates.BusinessFeedbackLoop20261027.MeasurementInput m) :
    JurisLean.Candidates.BusinessFeedbackLoop20261027.measureReported state.business input = measureView state.business.current input := rfl

theorem measurement_ignores_unseen_state (s t : JurisLean.Candidates.BusinessFeedbackLoop20261027.State m) (input : JurisLean.Candidates.BusinessFeedbackLoop20261027.MeasurementInput m)
    (view : s.business.current = t.business.current) :
    JurisLean.Candidates.BusinessFeedbackLoop20261027.measureReported s.business input = JurisLean.Candidates.BusinessFeedbackLoop20261027.measureReported t.business input := by
  rw [measurement_factors, measurement_factors, view]

theorem accepted_measurement_sources (state : JurisLean.Candidates.BusinessFeedbackLoop20261027.State m) (input : JurisLean.Candidates.BusinessFeedbackLoop20261027.MeasurementInput m)
    (out : BehaviorMeasurement) (accepted : JurisLean.Candidates.BusinessFeedbackLoop20261027.measureReported state.business input = .measured out) :
    ∃ post, state.business.current = some post ∧ out.actualPost = post ∧
      input.dictionary.context = post.gamma ∧
      ∀ row ∈ input.rows, row.dictionary = input.dictionary ∧
        row.occurredAt.ticks ≤ row.recordedAt.ticks ∧ row.recordedAt.ticks ≤ input.now.ticks ∧
        ∃ entry ∈ input.sources, entry.row = row := by
  cases hc : state.business.current with
  | none => simp [JurisLean.Candidates.BusinessFeedbackLoop20261027.measureReported, hc] at accepted
  | some post =>
      have hm : measureBusiness post input.dictionary input.now input.sources input.closures
          input.rows = .measured out := by simpa [JurisLean.Candidates.BusinessFeedbackLoop20261027.measureReported, hc] using accepted
      have bound := measurement_reads_actual_state_and_rows _ _ _ _ _ _ _ hm
      have sources := accepted_rows_are_external_and_current _ _ _ _ _ _ _ hm
      exact ⟨post, rfl, bound.1, sources.1, sources.2⟩

def adviceView (state : JurisLean.Candidates.BusinessFeedbackLoop20261027.State m) : Result (List (PolicyObservation m)) := state.policyRows

theorem advice_factors (context : Gamma) (input : JurisLean.Candidates.BusinessFeedbackLoop20261027.PolicyInput m) (state : JurisLean.Candidates.BusinessFeedbackLoop20261027.State m) :
    JurisLean.Candidates.BusinessFeedbackLoop20261027.adviseRecorded context input state.policyRows =
      JurisLean.Candidates.BusinessFeedbackLoop20261027.adviseRecorded context input (adviceView state) := rfl

theorem advice_ignores_unseen_state (context : Gamma) (input : JurisLean.Candidates.BusinessFeedbackLoop20261027.PolicyInput m)
    (s t : JurisLean.Candidates.BusinessFeedbackLoop20261027.State m) (view : adviceView s = adviceView t) :
    JurisLean.Candidates.BusinessFeedbackLoop20261027.adviseRecorded context input s.policyRows = JurisLean.Candidates.BusinessFeedbackLoop20261027.adviseRecorded context input t.policyRows := by
  exact congrArg (JurisLean.Candidates.BusinessFeedbackLoop20261027.adviseRecorded context input) view

theorem accepted_advice_is_visible_and_permitted (context : Gamma) (input : JurisLean.Candidates.BusinessFeedbackLoop20261027.PolicyInput m)
    (state : JurisLean.Candidates.BusinessFeedbackLoop20261027.State m) (out : PolicyAdvice m)
    (accepted : JurisLean.Candidates.BusinessFeedbackLoop20261027.adviseRecorded context input state.policyRows = .known out) :
    ∃ rows, adviceView state = .known rows ∧ out.observations = rows ∧
      input.design.acquiredAt.ticks ≤ context.knowledgeCutoff.ticks ∧
      input.design.acquiredAt.ticks ≤ context.recordCutoff.ticks ∧
      (∀ row ∈ rows, row.measured.observedAt.ticks ≤ context.knowledgeCutoff.ticks ∧
        row.measured.observedAt.ticks ≤ context.recordCutoff.ticks) ∧
      out.chosen ∈ input.permission.policies ∧ input.permission ∈ input.permissions ∧
      input.permission.context = context := by
  obtain ⟨rows, hr, ho, hd1, hd2, ht⟩ :=
    JurisLean.Candidates.BusinessFeedbackLoop20261027.known_advice_reads_recorded_data_within_cutoffs context input _ out accepted
  have measured : adviseMeasured context input.plan rows input.design input.designs
      input.permission input.permissions = .known out := by
    rw [hr] at accepted
    have timely : input.design.acquiredAt.ticks ≤ context.knowledgeCutoff.ticks ∧
        input.design.acquiredAt.ticks ≤ context.recordCutoff.ticks ∧
        (∀ row ∈ rows, row.measured.observedAt.ticks ≤ context.knowledgeCutoff.ticks ∧
          row.measured.observedAt.ticks ≤ context.recordCutoff.ticks) := ⟨hd1, hd2, ht⟩
    simpa only [JurisLean.Candidates.BusinessFeedbackLoop20261027.adviseRecorded, if_pos timely] using accepted
  have auth := advice_consumes_actual_measured_values_and_allowed_policy _ _ _ _ _ _ _ _ measured
  exact ⟨rows, hr, ho, hd1, hd2, ht, auth.2.2.1, auth.2.2.2.2.2.1, auth.2.2.2.2.2.2⟩

theorem learning_ignores_unseen_state (s t : JurisLean.Candidates.BusinessFeedbackLoop20261027.State m)
    (input : JurisLean.Candidates.BusinessFeedbackLoop20261027.FeedbackInput m)
    (observed : Result (PolicyObservation m)) (same : s.learning = t.learning) :
    JurisLean.Candidates.BusinessFeedbackLoop20261027.preparedState s.learning
      (JurisLean.Candidates.BusinessFeedbackLoop20261027.prepareObserved s.learning input observed) =
    JurisLean.Candidates.BusinessFeedbackLoop20261027.preparedState t.learning
      (JurisLean.Candidates.BusinessFeedbackLoop20261027.prepareObserved t.learning input observed) := by
  rw [same]

#print axioms actual_post_commutes
#print axioms actual_step_law
#print axioms replay_invariant
#print axioms actual_law_preserves_invariant
#print axioms finite_sequence_catalog
#print axioms accepted_measurement_sources
#print axioms accepted_advice_is_visible_and_permitted

end
end LegalMath20261109.BusinessProcess
