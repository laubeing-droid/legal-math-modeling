import JurisLean.Review20261110.DelayAugmentation
import JurisLean.BusinessProcessRealization
import JurisLean.Candidates.EventFeedbackConsumer20261027
import JurisLean.Candidates.BusinessFeedbackLoop20261027

/-!
Variable due times, pending outcomes and correction-aware feedback. Int time
uses the existing Instant.ticks domain. A missing completion is Option.none,
never a negative label. Source only; CI_NOT_RUN pending subject-bound evidence.
-/
set_option autoImplicit false

namespace LegalMath20261110.RemainingClosure.TemporalFeedback

open MeasureTheory ProbabilityTheory
open LegalMath20261108.ClosedLoop LegalMath20261108.SequentialFeedback
open LegalMath20261108.UnifiedFeedbackBridge
open LegalMath20261110.DelayAugmentation
open scoped ENNReal

noncomputable section

/-- The action records both the chosen action and its declared observation due time. -/
abbrev TimedAction := Bool × Option Int
/-- Occurrence index, optional due time, actual outcome. None permits noncompletion. -/
abbrev Job := Nat × (Option Int × Bool)
/-- Current time, pending jobs, complete ordered actual occurrences, last completed batch. -/
abbrev TimedHistory := Int × (List Job × (List (TimedAction × Bool) × List Job))

local instance : MeasurableSpace TimedHistory := ⊤
local instance : MeasurableSpace TimedAction := ⊤
local instance : MeasurableSpace (List Bool) := ⊤

def readyAt (now : Int) (job : Job) : Bool :=
  match job.2.1 with
  | none => false
  | some due => decide (due ≤ now)

def completedAt (now : Int) (jobs : List Job) : List Job := jobs.filter (readyAt now)
def waitingAt (now : Int) (jobs : List Job) : List Job :=
  jobs.filter (fun job => !(readyAt now job))

def submitted (h : TimedHistory) (a : TimedAction) (y : Bool) : List Job :=
  h.2.1 ++ [(h.2.2.1.length,(a.2,y))]

def appendTimed (h : TimedHistory) (a : TimedAction) (y : Bool) : TimedHistory :=
  (h.1+1, (waitingAt (h.1+1) (submitted h a y),
    (h.2.2.1 ++ [(a,y)], completedAt (h.1+1) (submitted h a y))))

def batchLabels (jobs : List Job) : List Bool := jobs.map (fun job => job.2.2)

def learnBatch (θ : ℝ) (labels : List Bool) : ℝ :=
  labels.foldl (fun parameter y => learnExample parameter (RepaymentExample.bit y)) θ

lemma measurable_learnBatch (labels : List Bool) : Measurable (fun θ => learnBatch θ labels) := by
  induction labels with
  | nil => exact measurable_id
  | cons y rest ih =>
      change Measurable (fun θ => learnBatch (learnExample θ (RepaymentExample.bit y)) rest)
      exact ih.comp (by unfold learnExample; fun_prop)

def numeric (x₀ : ℝ) (s : TimedHistory × ℝ) : State :=
  (currentX x₀ (s.1.2.2.1.map (fun e => (e.1.1,e.2))), s.2)

lemma measurable_numeric (x₀ : ℝ) : Measurable (numeric x₀) :=
  ((Measurable.of_discrete (f := fun h : TimedHistory =>
    currentX x₀ (h.2.2.1.map (fun e => (e.1.1,e.2))))).comp measurable_fst).prodMk measurable_snd

/-- The response law is the old actual feedback law, not an independent label generator. -/
def timedModel (x₀ : ℝ) (choose : TimedHistory → TimedAction) :
    Dynamics TimedHistory ℝ TimedAction Bool (List Bool) where
  policy := Kernel.deterministic (fun s => choose s.1)
    (Measurable.of_discrete.comp measurable_fst)
  outcome := model.outcome.comap (fun z => (numeric x₀ z.1,z.2.1))
    (((measurable_numeric x₀).comp measurable_fst).prodMk
      ((Measurable.of_discrete (f := fun a : TimedAction => a.1)).comp measurable_snd))
  append := appendTimed
  measure := fun h _ _ => batchLabels h.2.2.2
  learn := learnBatch
  measurable_append := Measurable.of_discrete
  measurable_measure := Measurable.of_discrete
  measurable_learn := measurable_from_prod_countable_left measurable_learnBatch

instance (x₀ : ℝ) (choose : TimedHistory → TimedAction) :
    IsMarkovKernel (timedModel x₀ choose).policy := by
  dsimp [timedModel]
  infer_instance

instance (x₀ : ℝ) (choose : TimedHistory → TimedAction) :
    IsMarkovKernel (timedModel x₀ choose).outcome := by
  dsimp [timedModel]
  infer_instance

theorem variable_delay_markov (x₀ : ℝ) (choose : TimedHistory → TimedAction) :
    IsMarkovKernel (step (timedModel x₀ choose)) := inferInstance

theorem ordered_occurrences_retained (h : TimedHistory) (a : TimedAction) (y : Bool) :
    h.2.2.1 <+: (appendTimed h a y).2.2.1 := List.prefix_append _ _

theorem completion_update_eq (x₀ θ : ℝ) (choose : TimedHistory → TimedAction)
    (h : TimedHistory) (a : TimedAction) (y : Bool) :
    (update (timedModel x₀ choose) ((h,θ),(a,y))).2 =
      learnBatch θ (batchLabels (completedAt (h.1+1) (submitted h a y))) := rfl

lemma completed_eq_nil (now : Int) (jobs : List Job)
    (pending : ∀ job ∈ jobs, readyAt now job = false) : completedAt now jobs = [] := by
  induction jobs with
  | nil => rfl
  | cons job rest ih =>
      have hj := pending job (by simp)
      have hr := ih (fun j h => pending j (by simp [h]))
      change (job :: rest).filter (readyAt now) = []
      rw [List.filter_cons,hj]
      exact hr

theorem uncompleted_events_do_not_update (x₀ θ : ℝ)
    (choose : TimedHistory → TimedAction) (h : TimedHistory) (a : TimedAction) (y : Bool)
    (pending : ∀ job ∈ submitted h a y, readyAt (h.1+1) job = false) :
    (update (timedModel x₀ choose) ((h,θ),(a,y))).2 = θ := by
  rw [completion_update_eq, completed_eq_nil _ _ pending]
  rfl

theorem no_fabricated_zero_label (now : Int) (jobs : List Job) (label : Bool)
    (member : label ∈ batchLabels (completedAt now jobs)) :
    ∃ job ∈ jobs, readyAt now job = true ∧ job.2.2 = label := by
  obtain ⟨job, hj, he⟩ := List.mem_map.mp member
  exact ⟨job, (List.mem_filter.mp hj).1, (List.mem_filter.mp hj).2, he⟩

theorem noncompletion_stays_pending (now : Int) (jobs : List Job) (job : Job)
    (member : job ∈ jobs) (never : job.2.1 = none) :
    job ∈ waitingAt now jobs ∧ job ∉ completedAt now jobs := by
  simp [waitingAt, completedAt, readyAt, never, member]

theorem due_time_exact (now due : Int) (event : Nat) (y : Bool) :
    readyAt now (event,(some due,y)) = true ↔ due ≤ now := by simp [readyAt]

/-- Equal current numeric coordinates lose the pending information needed for
next learning. The full history above retains it and is Markov. -/
theorem pending_is_needed (x₀ : ℝ) (choose : TimedHistory → TimedAction) :
    numeric x₀ (((0, ([(0,(some 0,false))],([],[]))),0)) =
      numeric x₀ (((0, ([(0,(none,false))],([],[]))),0)) ∧
    (update (timedModel x₀ choose)
      ((((0, ([(0,(some 0,false))],([],[]))),0)),((false,none),false))).2 ≠
    (update (timedModel x₀ choose)
      ((((0, ([(0,(none,false))],([],[]))),0)),((false,none),false))).2 := by
  constructor
  · rfl
  · norm_num [completion_update_eq, submitted, completedAt, readyAt, batchLabels,
      learnBatch, learnExample, RepaymentExample.bit]

section ActualBusiness
open JurisLean.Candidates.Final20261021
open JurisLean.Candidates.BusinessMeasurement20261027
open JurisLean.Candidates.EventFeedbackConsumer20261027

/-- An actual incomplete observation has no label, rather than the label false. -/
def businessCompletion : MeasurementResult → Option Bool
  | .unknown _ => none
  | .measured result => some result.label

theorem actual_unclosed_window_is_pending (post : Ledger.Handle) (d : MeasurementDictionary)
    (now : Instant) (sources : List ObservationAttestation) (closures : List WindowClosure)
    (rows : List MeasurementRow) (total : ℚ)
    (measured : measuredTotal post d rows = some total)
    (below : total < measurementThreshold d)
    (unclosed : windowComplete d now rows closures = false) :
    businessCompletion (measureBusiness post d now sources closures rows) = none := by
  unfold measureBusiness
  split
  · rfl
  · simp [measured, not_le.mpr below, unclosed, businessCompletion]

theorem actual_negative_requires_closed_window (post : Ledger.Handle) (d : MeasurementDictionary)
    (now : Instant) (sources : List ObservationAttestation) (closures : List WindowClosure)
    (rows : List MeasurementRow)
    (negative : businessCompletion (measureBusiness post d now sources closures rows) = some false) :
    windowComplete d now rows closures = true ∧ d.windowEnd.ticks ≤ now.ticks := by
  cases actual : measureBusiness post d now sources closures rows with
  | unknown reason => simp [actual, businessCompletion] at negative
  | measured receipt =>
      have label : receipt.label = false := by simpa [actual, businessCompletion] using negative
      have facts := negative_requires_complete_closed_window post d now sources closures rows
        receipt actual label
      exact ⟨facts.1,facts.2.1⟩

/-- Pending windows enter the original business continuation without creating
an observation or an additional training sample. Older valid queue entries
remain eligible; this theorem does not suppress unrelated completed feedback. -/
theorem pending_continuation_adds_no_observation {m : Nat}
    (state : JurisLean.Candidates.BusinessFeedbackLoop20261027.State m)
    (measurement : JurisLean.Candidates.BusinessFeedbackLoop20261027.MeasurementInput m)
    (policy : JurisLean.Candidates.BusinessFeedbackLoop20261027.PolicyInput m)
    (feedback : JurisLean.Candidates.BusinessFeedbackLoop20261027.FeedbackInput m)
    (reason : MeasurementFailure)
    (pending : JurisLean.Candidates.BusinessFeedbackLoop20261027.measureReported
      state.business measurement = .unknown reason) :
    (JurisLean.Candidates.BusinessFeedbackLoop20261027.continueBusiness
      state measurement policy feedback).post.observationHistory = state.observationHistory := by
  simp [JurisLean.Candidates.BusinessFeedbackLoop20261027.continueBusiness, pending,
    JurisLean.Candidates.MeasuredPolicy20261027.consumeMeasurement,
    JurisLean.Candidates.BusinessFeedbackLoop20261027.enqueueObserved]

theorem pending_episode_keeps_learner_when_queue_empty {W : Type} {m : Nat}
    (state : JurisLean.Candidates.BusinessFeedbackLoop20261027.State m)
    (action : JurisLean.Candidates.BusinessFeedbackLoop20261027.ActionInput W m)
    (measurement : JurisLean.Candidates.BusinessFeedbackLoop20261027.MeasurementInput m)
    (policy : JurisLean.Candidates.BusinessFeedbackLoop20261027.PolicyInput m)
    (feedback : JurisLean.Candidates.BusinessFeedbackLoop20261027.FeedbackInput m)
    (reason : MeasurementFailure)
    (pending : JurisLean.Candidates.BusinessFeedbackLoop20261027.measureReported
      (JurisLean.Candidates.BusinessFeedbackLoop20261027.act state action).post.business
      measurement = .unknown reason)
    (emptyQueue : state.feedbackQueue = []) :
    (JurisLean.Candidates.BusinessFeedbackLoop20261027.episode
      state action measurement policy feedback).continuation.post.learning = state.learning := by
  have frame : (JurisLean.Candidates.BusinessFeedbackLoop20261027.act state action).post.learning =
      state.learning := by
    cases hc : state.business.current <;>
      simp [JurisLean.Candidates.BusinessFeedbackLoop20261027.act,hc]
  have queue : (JurisLean.Candidates.BusinessFeedbackLoop20261027.act state action).post.feedbackQueue = [] := by
    cases hc : state.business.current <;>
      simp [JurisLean.Candidates.BusinessFeedbackLoop20261027.act,hc,emptyQueue]
  simpa [JurisLean.Candidates.BusinessFeedbackLoop20261027.episode,
    JurisLean.Candidates.BusinessFeedbackLoop20261027.continueBusiness,pending,
    JurisLean.Candidates.MeasuredPolicy20261027.consumeMeasurement,
    JurisLean.Candidates.BusinessFeedbackLoop20261027.enqueueObserved,queue,
    JurisLean.Candidates.BusinessFeedbackLoop20261027.prepareQueued,
    JurisLean.Candidates.BusinessFeedbackLoop20261027.preparedState] using frame

/-- The original correction implementation retains the earlier record, one
current cell per event, and supplies the actual poststore to the next fit. -/
theorem actual_revision_and_refit {m : Nat} (s : Store m) (now : Instant)
    (permits : List (CorrectionPermit m)) (edit : Correction m) (unique : Unique s)
    (fresh : s.history.contains (.corrected edit) = false)
    (found : lookup s edit.supersedes.event = some edit.supersedes)
    (valid : correctionValid s now edit = true)
    (allowed : correctionAuthorized s now permits edit = true)
    (protocol : JurisLean.Candidates.LearningConsumer20261027.LearningProtocol) (loss : ℚ → Bool → ℚ) (models : List (List ℚ))
    (out : TrainingCandidate m)
    (fitted : fitFromStore (correct s now permits edit).post protocol loss models = .known out) :
    (correct s now permits edit).post.history = s.history ++ [.corrected edit] ∧
    Unique (correct s now permits edit).post ∧
    lookup (correct s now permits edit).post edit.supersedes.event = some (correctedCell edit) ∧
    out.snapshot = (correct s now permits edit).post ∧
    out.fitted.sampleSize = (trainingRows (correct s now permits edit).post).length ∧
    (trainingRows (correct s now permits edit).post).Pairwise (fun a b => a.event ≠ b.event) := by
  have correction := approved_correction_replaces_exact_prior s now permits edit fresh found valid allowed
  have oneCell := correction_preserves_event_uniqueness s now permits edit unique
  have fit := successful_fit_reads_current_valid_sample (correct s now permits edit).post
    protocol loss models out fitted
  exact ⟨correction.2, oneCell, correction.1, fit.1, fit.2.2.1,
    training_contains_no_repeated_event _ oneCell⟩

section RealizedPending
open JurisLean.Candidates.AdaptiveRoundLedger20261027
open LegalMath20261109.BusinessProcess

variable {W : Type} {m k : Nat}
local instance : MeasurableSpace (JurisLean.Candidates.BusinessFeedbackLoop20261027.State m) := ⊤
local instance : MeasurableSpace (RoundState m) := ⊤
local instance : MeasurableSpace (Fin k) := ⊤
local instance : MeasurableSpace (List (Fin k)) := ⊤

/-- A delayed actual business episode is a step of the already proved common
chain. The unchanged learner is derived from its real pending measurement. -/
theorem pending_episode_on_original_chain
    (initial : JurisLean.Candidates.BusinessFeedbackLoop20261027.State m)
    (catalog : Fin k → JurisLean.Candidates.BusinessFeedbackLoop20261027.Command W m)
    (pick : List (Fin k) → Fin k) (h : List (Fin k)) (a : Fin k)
    (action : JurisLean.Candidates.BusinessFeedbackLoop20261027.ActionInput W m)
    (measurement : JurisLean.Candidates.BusinessFeedbackLoop20261027.MeasurementInput m)
    (policy : JurisLean.Candidates.BusinessFeedbackLoop20261027.PolicyInput m)
    (feedback : JurisLean.Candidates.BusinessFeedbackLoop20261027.FeedbackInput m)
    (command : catalog a = .episode action measurement policy feedback)
    (reason : MeasurementFailure)
    (pending : JurisLean.Candidates.BusinessFeedbackLoop20261027.measureReported
      (JurisLean.Candidates.BusinessFeedbackLoop20261027.act (replay initial catalog h) action).post.business
      measurement = .unknown reason)
    (emptyQueue : (replay initial catalog h).feedbackQueue = []) :
    update (model initial catalog pick)
      (encode initial catalog h,
        (a,JurisLean.Candidates.BusinessFeedbackLoop20261027.step (replay initial catalog h) (catalog a))) =
        encode initial catalog (h ++ [a]) ∧
      (replay initial catalog (h ++ [a])).learning = (replay initial catalog h).learning := by
  refine ⟨actual_post_commutes initial catalog pick h a, ?_⟩
  rw [replay_append,command]
  exact pending_episode_keeps_learner_when_queue_empty _ action measurement policy feedback reason pending emptyQueue

end RealizedPending

end ActualBusiness

#print axioms variable_delay_markov
#print axioms completion_update_eq
#print axioms uncompleted_events_do_not_update
#print axioms no_fabricated_zero_label
#print axioms noncompletion_stays_pending
#print axioms actual_negative_requires_closed_window
#print axioms actual_revision_and_refit

end
end LegalMath20261110.RemainingClosure.TemporalFeedback
