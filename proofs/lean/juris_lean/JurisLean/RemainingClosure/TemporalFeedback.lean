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

/-- The observable view hides the labels of all still-pending occurrences. -/
abbrev VisibleTimedHistory :=
  Int × (List (Nat × Option Int) × List (TimedAction × Option Bool))

local instance : MeasurableSpace VisibleTimedHistory := ⊤

def visibleTimedHistory (h : TimedHistory) : VisibleTimedHistory :=
  (h.1, (h.2.1.map (fun job => (job.1,job.2.1)),
    h.2.2.1.zipIdx.map (fun entry =>
      (entry.1.1, if h.2.1.any (fun job => job.1 == entry.2) then none else some entry.1.2))))

lemma measurable_visibleTimedHistory : Measurable visibleTimedHistory := Measurable.of_discrete

/-- Controlled policies read the visible record and the current private
parameter. The physical outcome kernel is unchanged. -/
def observedTimedModel (x₀ : ℝ) (choose : VisibleTimedHistory × ℝ → TimedAction)
    (hc : Measurable choose) : Dynamics TimedHistory ℝ TimedAction Bool (List Bool) :=
  { timedModel x₀ (fun _ => (false,none)) with policy :=
      (Kernel.deterministic (fun s => choose (visibleTimedHistory s.1,s.2))
        (hc.comp ((measurable_visibleTimedHistory.comp measurable_fst).prodMk measurable_snd))) }

instance (x₀ : ℝ) (choose : VisibleTimedHistory × ℝ → TimedAction)
    (hc : Measurable choose) : IsMarkovKernel (observedTimedModel x₀ choose hc).policy := by
  dsimp [observedTimedModel]
  infer_instance

instance (x₀ : ℝ) (choose : VisibleTimedHistory × ℝ → TimedAction)
    (hc : Measurable choose) : IsMarkovKernel (observedTimedModel x₀ choose hc).outcome := by
  change IsMarkovKernel (timedModel x₀ (fun _ => (false,none))).outcome
  infer_instance

theorem visible_policy_no_leak (x₀ : ℝ) (choose : VisibleTimedHistory × ℝ → TimedAction)
    (hc : Measurable choose) (h t : TimedHistory) (θ : ℝ)
    (same : visibleTimedHistory h = visibleTimedHistory t) :
    (observedTimedModel x₀ choose hc).policy (h,θ) =
      (observedTimedModel x₀ choose hc).policy (t,θ) := by
  simp [observedTimedModel,Kernel.deterministic_apply,same]

theorem controlled_next_choice_reads_completed_feedback (x₀ θ : ℝ)
    (choose : VisibleTimedHistory × ℝ → TimedAction) (hc : Measurable choose)
    (h : TimedHistory) (a : TimedAction) (y : Bool) :
    (observedTimedModel x₀ choose hc).policy
      (update (observedTimedModel x₀ choose hc) ((h,θ),(a,y))) =
      Measure.dirac (choose (visibleTimedHistory (appendTimed h a y),
        learnBatch θ (batchLabels (completedAt (h.1+1) (submitted h a y))))) := by
  simp [observedTimedModel,timedModel,Kernel.deterministic_apply,update,
    historyOut,parameterOut,feedback]

def thresholdChoice (due : Option Int) (s : VisibleTimedHistory × ℝ) : TimedAction :=
  (decide ((1/2:ℝ) < s.2),due)

lemma measurable_thresholdChoice (due : Option Int) : Measurable (thresholdChoice due) := by
  have hm : Measurable (fun s : VisibleTimedHistory × ℝ =>
      if (1/2:ℝ) < s.2 then ((true,due) : TimedAction) else (false,due)) :=
    Measurable.ite (measurableSet_lt measurable_const measurable_snd)
      measurable_const measurable_const
  convert hm using 1
  funext s
  by_cases h : (1/2:ℝ) < s.2 <;> simp [thresholdChoice,h]

/-- This controlled instance actually changes its next choice after a
completed actual outcome, while pending labels stay outside its observation. -/
theorem completed_feedback_changes_controlled_choice (x₀ : ℝ) :
    thresholdChoice (some 1) (visibleTimedHistory (0,([],([],[]))),0) = (false,some 1) ∧
    (observedTimedModel x₀ (thresholdChoice (some 1)) (measurable_thresholdChoice (some 1))).policy
      (update (observedTimedModel x₀ (thresholdChoice (some 1)) (measurable_thresholdChoice (some 1)))
        ((((0,([],([],[]))),0)),((false,some 1),true))) =
      Measure.dirac (true,some 1) := by
  constructor
  · norm_num [thresholdChoice]
  · rw [controlled_next_choice_reads_completed_feedback]
    norm_num [thresholdChoice,submitted,completedAt,readyAt,batchLabels,learnBatch,
      learnExample,RepaymentExample.bit]

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

namespace GeneralArrival

open JurisLean.Candidates.Final20261021
open JurisLean.Candidates.AdaptiveRoundLedger20261027
open JurisLean.Candidates.EventFeedbackConsumer20261027
open JurisLean.Candidates.ValidatedFeedbackLoad20261027
open JurisLean.Candidates.ProtectedFeedback20261027

abbrev BusinessState (m : Nat) := JurisLean.Candidates.BusinessFeedbackLoop20261027.State m
abbrev MeasurementRequest (m : Nat) := JurisLean.Candidates.BusinessFeedbackLoop20261027.MeasurementInput m
/-- Actual business and learner, with the unresolved measurement view. The
full immutable request/revision history remains in the common occurrence log. -/
abbrev Source (m : Nat) := BusinessState m × List (MeasurementRequest m)
abbrev ArrivalLog := List (Nat × Nat)

/-- Reports may arrive later, never arrive, or revise the same measurement.
No completion time is selected when the original physical event occurs. -/
inductive Arrival (m : Nat)
  | observe (measurement : MeasurementRequest m)
      (policy : JurisLean.Candidates.BusinessFeedbackLoop20261027.PolicyInput m)
      (feedback : JurisLean.Candidates.BusinessFeedbackLoop20261027.FeedbackInput m)
  | revise (now : Instant) (permits : List (CorrectionPermit m)) (change : Change m)
      (protocol : JurisLean.Candidates.LearningConsumer20261027.LearningProtocol)
      (validation : ValidationPlan)

def pendingView {m : Nat} (queue : List (MeasurementRequest m)) (state : BusinessState m)
    (request : MeasurementRequest m) : List (MeasurementRequest m) :=
  let others := queue.filter (fun old => decide (old.dictionary.unit ≠ request.dictionary.unit))
  match JurisLean.Candidates.BusinessFeedbackLoop20261027.measureReported state.business request with
  | .unknown _ => others ++ [request]
  | .measured _ => others

def dueQueue {m : Nat} (state : Source m) : List (MeasurementId × Instant) :=
  state.2.map (fun request => (request.dictionary.unit,request.dictionary.windowEnd))

def applyArrival {m : Nat} (state : Source m) : Arrival m → Source m
  | .observe measurement policy feedback =>
      ((JurisLean.Candidates.BusinessFeedbackLoop20261027.continueBusiness
        state.1 measurement policy feedback).post,
        pendingView state.2 state.1 measurement)
  | .revise now permits change protocol validation =>
      ({state.1 with learning := beginAdaptiveRound state.1.learning now permits change protocol validation},
        state.2)

/-- A physical business command is executed once. An episode's own pending
window is retained in the same queue as externally arriving later reports. -/
def applyCommand {W : Type} {m : Nat} (state : Source m) :
    Option (JurisLean.Candidates.BusinessFeedbackLoop20261027.Command W m) → Source m
  | none => state
  | some command =>
      (JurisLean.Candidates.BusinessFeedbackLoop20261027.step state.1 command,
        match command with
        | .episode action measurement _ _ =>
            pendingView state.2
              (JurisLean.Candidates.BusinessFeedbackLoop20261027.act state.1 action).post measurement
        | _ => state.2)

def sourceStep {W : Type} {m : Nat}
    (commands : Nat → Option (JurisLean.Candidates.BusinessFeedbackLoop20261027.Command W m))
    (reports : Nat → Arrival m) (state : Source m) (action report : Nat) : Source m :=
  applyArrival (applyCommand state (commands action)) (reports report)

def replay {W : Type} {m : Nat} (initial : Source m)
    (commands : Nat → Option (JurisLean.Candidates.BusinessFeedbackLoop20261027.Command W m))
    (reports : Nat → Arrival m) (history : ArrivalLog) : Source m :=
  history.foldl (fun state event => sourceStep commands reports state event.1 event.2) initial

lemma replay_append {W : Type} {m : Nat} (initial : Source m)
    (commands : Nat → Option (JurisLean.Candidates.BusinessFeedbackLoop20261027.Command W m))
    (reports : Nat → Arrival m) (history : ArrivalLog) (action report : Nat) :
    replay initial commands reports (history ++ [(action,report)]) =
      sourceStep commands reports (replay initial commands reports history) action report := by
  simp [replay,List.foldl_append]

variable {W : Type} {m : Nat}
local instance : MeasurableSpace ArrivalLog := ⊤
local instance : MeasurableSpace (RoundState m) := ⊤

def encode (initial : Source m)
    (commands : Nat → Option (JurisLean.Candidates.BusinessFeedbackLoop20261027.Command W m))
    (reports : Nat → Arrival m) (history : ArrivalLog) : ArrivalLog × RoundState m :=
  (history,(replay initial commands reports history).1.learning)

/-- The arrival kernel is arbitrary and may depend on the entire current
history and action. This includes outcome-dependent random delays, repeated
unknown reports, and later corrections of the original event. -/
def arrivalModel (initial : Source m)
    (commands : Nat → Option (JurisLean.Candidates.BusinessFeedbackLoop20261027.Command W m))
    (reports : Nat → Arrival m)
    (policy : Kernel (ArrivalLog × RoundState m) Nat)
    (arrival : Kernel ((ArrivalLog × RoundState m) × Nat) Nat) :
    Dynamics ArrivalLog (RoundState m) Nat Nat (RoundState m) where
  policy := policy
  outcome := arrival
  append := fun history action report => history ++ [(action,report)]
  measure := fun history _ _ => (replay initial commands reports history).1.learning
  learn := fun _ actual => actual
  measurable_append := Measurable.of_discrete
  measurable_measure := (Measurable.of_discrete (f := fun history : ArrivalLog =>
    (replay initial commands reports history).1.learning)).comp measurable_fst
  measurable_learn := measurable_snd

instance (initial : Source m)
    (commands : Nat → Option (JurisLean.Candidates.BusinessFeedbackLoop20261027.Command W m))
    (reports : Nat → Arrival m) (policy : Kernel (ArrivalLog × RoundState m) Nat)
    (arrival : Kernel ((ArrivalLog × RoundState m) × Nat) Nat) [IsMarkovKernel policy] :
    IsMarkovKernel (arrivalModel initial commands reports policy arrival).policy := by
  change IsMarkovKernel policy
  infer_instance

instance (initial : Source m)
    (commands : Nat → Option (JurisLean.Candidates.BusinessFeedbackLoop20261027.Command W m))
    (reports : Nat → Arrival m) (policy : Kernel (ArrivalLog × RoundState m) Nat)
    (arrival : Kernel ((ArrivalLog × RoundState m) × Nat) Nat) [IsMarkovKernel arrival] :
    IsMarkovKernel (arrivalModel initial commands reports policy arrival).outcome := by
  change IsMarkovKernel arrival
  infer_instance

theorem arbitrary_arrival_markov (initial : Source m)
    (commands : Nat → Option (JurisLean.Candidates.BusinessFeedbackLoop20261027.Command W m))
    (reports : Nat → Arrival m) (policy : Kernel (ArrivalLog × RoundState m) Nat)
    (arrival : Kernel ((ArrivalLog × RoundState m) × Nat) Nat)
    [IsMarkovKernel policy] [IsMarkovKernel arrival] :
    IsMarkovKernel (step (arrivalModel initial commands reports policy arrival)) := inferInstance

theorem actual_arrival_commutes (initial : Source m)
    (commands : Nat → Option (JurisLean.Candidates.BusinessFeedbackLoop20261027.Command W m))
    (reports : Nat → Arrival m) (policy : Kernel (ArrivalLog × RoundState m) Nat)
    (arrival : Kernel ((ArrivalLog × RoundState m) × Nat) Nat)
    (history : ArrivalLog) (action report : Nat) :
    update (arrivalModel initial commands reports policy arrival)
      (encode initial commands reports history,(action,report)) =
      encode initial commands reports (history ++ [(action,report)]) := rfl

theorem actual_private_post_is_original_source_step (initial : Source m)
    (commands : Nat → Option (JurisLean.Candidates.BusinessFeedbackLoop20261027.Command W m))
    (reports : Nat → Arrival m) (policy : Kernel (ArrivalLog × RoundState m) Nat)
    (arrival : Kernel ((ArrivalLog × RoundState m) × Nat) Nat)
    (history : ArrivalLog) (action report : Nat) :
    (update (arrivalModel initial commands reports policy arrival)
      (encode initial commands reports history,(action,report))).2 =
      (sourceStep commands reports (replay initial commands reports history) action report).1.learning := by
  change (replay initial commands reports (history ++ [(action,report)])).1.learning = _
  rw [replay_append]

/-- The same joint action/report draw drives the actual legacy poststate and
its actual current learner, for arbitrary (not prescheduled) arrival laws. -/
theorem actual_joint_arrival_law (initial : Source m)
    (commands : Nat → Option (JurisLean.Candidates.BusinessFeedbackLoop20261027.Command W m))
    (reports : Nat → Arrival m) (policy : Kernel (ArrivalLog × RoundState m) Nat)
    (arrival : Kernel ((ArrivalLog × RoundState m) × Nat) Nat)
    [IsMarkovKernel policy] [IsMarkovKernel arrival] (history : ArrivalLog) :
    step (arrivalModel initial commands reports policy arrival) (encode initial commands reports history) =
      (joint (arrivalModel initial commands reports policy arrival)
        (encode initial commands reports history)).map
          (fun event => encode initial commands reports (history ++ [event])) := by
  ext B hB
  rw [step_apply _ _ hB,Measure.map_apply Measurable.of_discrete hB]
  rfl

theorem actual_joint_arrival_readout_law {V : Type*} [MeasurableSpace V]
    (initial : Source m)
    (commands : Nat → Option (JurisLean.Candidates.BusinessFeedbackLoop20261027.Command W m))
    (reports : Nat → Arrival m) (policy : Kernel (ArrivalLog × RoundState m) Nat)
    (arrival : Kernel ((ArrivalLog × RoundState m) × Nat) Nat)
    [IsMarkovKernel policy] [IsMarkovKernel arrival] (history : ArrivalLog) (read : Source m → V) :
    (step (arrivalModel initial commands reports policy arrival) (encode initial commands reports history)).map
        (fun current => read (replay initial commands reports current.1)) =
      (joint (arrivalModel initial commands reports policy arrival)
        (encode initial commands reports history)).map (fun event =>
          read (sourceStep commands reports (replay initial commands reports history) event.1 event.2)) := by
  have hr : Measurable (fun current : ArrivalLog × RoundState m =>
      read (replay initial commands reports current.1)) :=
    (Measurable.of_discrete (f := fun log : ArrivalLog =>
      read (replay initial commands reports log))).comp measurable_fst
  rw [actual_joint_arrival_law,Measure.map_map hr Measurable.of_discrete]
  congr 1
  funext event
  dsimp [Function.comp_def,encode]
  rw [replay_append]

theorem next_policy_uses_actual_arrival_post (initial : Source m)
    (commands : Nat → Option (JurisLean.Candidates.BusinessFeedbackLoop20261027.Command W m))
    (reports : Nat → Arrival m) (policy : Kernel (ArrivalLog × RoundState m) Nat)
    (arrival : Kernel ((ArrivalLog × RoundState m) × Nat) Nat)
    [IsMarkovKernel policy] [IsMarkovKernel arrival] (history : ArrivalLog)
    (B : Set Nat) (hB : MeasurableSet B) :
    nextAction (arrivalModel initial commands reports policy arrival) (encode initial commands reports history) B =
      ∫⁻ action, ∫⁻ report, policy
        (encode initial commands reports (history ++ [(action,report)])) B
          ∂arrival (encode initial commands reports history,action)
          ∂policy (encode initial commands reports history) :=
  nextAction_apply (arrivalModel initial commands reports policy arrival)
    (encode initial commands reports history) hB

/-- An unclosed request remains in the due-time queue; its due time alone
never turns missing evidence into a false outcome. -/
theorem unknown_request_remains_pending (state : Source m) (request : MeasurementRequest m)
    (policy : JurisLean.Candidates.BusinessFeedbackLoop20261027.PolicyInput m)
    (feedback : JurisLean.Candidates.BusinessFeedbackLoop20261027.FeedbackInput m)
    (reason : JurisLean.Candidates.BusinessMeasurement20261027.MeasurementFailure)
    (pending : JurisLean.Candidates.BusinessFeedbackLoop20261027.measureReported
      state.1.business request = .unknown reason) :
    request ∈ (applyArrival state (.observe request policy feedback)).2 ∧
      (request.dictionary.unit,request.dictionary.windowEnd) ∈
        dueQueue (applyArrival state (.observe request policy feedback)) ∧
      (applyArrival state (.observe request policy feedback)).1.observationHistory =
        state.1.observationHistory := by
  have member : request ∈ (applyArrival state (.observe request policy feedback)).2 := by
    simp [applyArrival,pendingView,pending]
  exact ⟨member,List.mem_map.mpr ⟨request,member,rfl⟩,
    pending_continuation_adds_no_observation state.1 request policy feedback reason pending⟩

theorem completed_request_leaves_pending_queue (state : Source m) (request : MeasurementRequest m)
    (policy : JurisLean.Candidates.BusinessFeedbackLoop20261027.PolicyInput m)
    (feedback : JurisLean.Candidates.BusinessFeedbackLoop20261027.FeedbackInput m)
    (out : JurisLean.Candidates.BusinessMeasurement20261027.BehaviorMeasurement)
    (completed : JurisLean.Candidates.BusinessFeedbackLoop20261027.measureReported
      state.1.business request = .measured out) :
    ∀ old ∈ (applyArrival state (.observe request policy feedback)).2,
      old.dictionary.unit ≠ request.dictionary.unit := by
  intro old member
  have filtered : old ∈ state.2.filter
      (fun item => decide (item.dictionary.unit ≠ request.dictionary.unit)) := by
    simpa [applyArrival,pendingView,completed] using member
  exact of_decide_eq_true (List.mem_filter.mp filtered).2

/-- Later reports and corrections do not repeat a physical business action. -/
theorem arrival_preserves_actual_business (state : Source m) (report : Arrival m) :
    (applyArrival state report).1.business = state.1.business := by
  cases report with
  | observe measurement policy feedback => rfl
  | revise now permits change protocol validation => rfl

/-- The general arrival language uses the exact original correction/fit path.
It records the real postjournal before a later assessment can load a model. -/
theorem revision_consumes_actual_corrected_store (state : Source m)
    (now : Instant) (permits : List (CorrectionPermit m)) (change : Change m)
    (protocol : JurisLean.Candidates.LearningConsumer20261027.LearningProtocol)
    (validation : ValidationPlan)
    (idle : state.1.learning.pending.isSome = false)
    (within : state.1.learning.records.length < state.1.learning.horizon)
    (lossSame : protocol.lossVersion = state.1.learning.service.lossVersion) :
    (applyArrival state (.revise now permits change protocol validation)).1.learning.service.journal =
      (applyChange now permits state.1.learning.service.journal change).post ∧
    readLoaded (applyArrival state (.revise now permits change protocol validation)).1.learning.service =
      readLoaded state.1.learning.service := by
  have actual := next_candidate_consumes_current_loaded_and_actual_post state.1.learning.service
    now permits change protocol state.1.learning.learner.proposals lossSame
  simpa [applyArrival,beginAdaptiveRound,idle,not_le.mpr within] using actual.2.2.2

#print axioms arbitrary_arrival_markov
#print axioms actual_arrival_commutes
#print axioms actual_joint_arrival_law
#print axioms next_policy_uses_actual_arrival_post
#print axioms unknown_request_remains_pending
#print axioms completed_request_leaves_pending_queue
#print axioms arrival_preserves_actual_business
#print axioms revision_consumes_actual_corrected_store

end GeneralArrival

#print axioms variable_delay_markov
#print axioms completion_update_eq
#print axioms uncompleted_events_do_not_update
#print axioms no_fabricated_zero_label
#print axioms noncompletion_stays_pending
#print axioms actual_negative_requires_closed_window
#print axioms actual_revision_and_refit

end
end LegalMath20261110.RemainingClosure.TemporalFeedback
