import JurisLean.Candidates.ValidatedFeedbackLoad20261027

/-!
Original 14.5 / S14: old weights are reissued against the current journal,
protocol, protected-domain evaluation and independent current permission.
Neither the archived state nor its historical authorization is restored.
-/

namespace JurisLean.Candidates.CurrentContextRollback20261027

open JurisLean.Candidates.Final20261021
open JurisLean.Candidates.LearningERM20261027
open JurisLean.Candidates.LearningConsumer20261027
open JurisLean.Candidates.EventFeedbackConsumer20261027
open JurisLean.Candidates.ProtectedFeedback20261027
open JurisLean.Candidates.ValidatedFeedbackLoad20261027

structure RollbackRequest (m : Nat) where
  archived : TrainingCandidate m
  protocol : LearningProtocol
  plan : ValidationPlan
  blocks : List (DomainBlock m)
  sampling : SamplingReceipt m
  permit : LoadPermit m
  deriving DecidableEq, Repr

-- The singleton fit recomputes the archived weights' score on the actual
-- current training rows; it does not copy the archived score or snapshot.
def proposeRollback {m : Nat} (s : Service m) (request : RollbackRequest m) :
    Result (TrainingCandidate m) :=
  if request.protocol.lossVersion ≠ s.lossVersion then .unknown .targetMismatch
  else fitFromStore s.journal request.protocol binaryLoss [request.archived.fitted.table]

def evaluateRollback {m : Nat} (s : Service m) (request : RollbackRequest m) :
    Result (Evaluation m) :=
  match proposeRollback s request with
  | .known candidate => evaluate request.plan (readLoaded s) candidate binaryLoss request.blocks
  | .unknown why => .unknown why
  | .rejected why => .rejected why
  | .conflict a b => .conflict a b

def attemptRollback {m : Nat} (s : Service m) (request : RollbackRequest m)
    (samplingCatalog : List (SamplingReceipt m)) (authorityCatalog : List (LoadPermit m)) :
    Result (LoadOutcome m) :=
  match evaluateRollback s request with
  | .known evaluation =>
      .known (activate s evaluation samplingCatalog request.sampling authorityCatalog request.permit)
  | .unknown why => .unknown why
  | .rejected why => .rejected why
  | .conflict a b => .conflict a b

def rollbackPost {m : Nat} (s : Service m) (request : RollbackRequest m)
    (samplingCatalog : List (SamplingReceipt m)) (authorityCatalog : List (LoadPermit m)) : Service m :=
  match attemptRollback s request samplingCatalog authorityCatalog with
  | .known out => out.post
  | _ => s

theorem rollback_proposal_uses_current_sample {m : Nat} (s : Service m)
    (request : RollbackRequest m) (candidate : TrainingCandidate m)
    (produced : proposeRollback s request = .known candidate) :
    candidate.snapshot = s.journal ∧ candidate.fitted.protocol = request.protocol ∧
      candidate.fitted.table = request.archived.fitted.table ∧
      candidate.fitted.sampleSize = (trainingRows s.journal).length ∧
      candidate.fitted.empiricalRisk =
        empiricalScore (tableLoss binaryLoss) (trainingData s.journal) candidate.fitted.table := by
  unfold proposeRollback at produced
  split at produced
  · cases produced
  · have bound := successful_fit_reads_current_valid_sample s.journal request.protocol binaryLoss
      [request.archived.fitted.table] candidate produced
    exact ⟨bound.1, bound.2.1, by simpa using bound.2.2.2.2.1,
      bound.2.2.1, bound.2.2.2.2.2.1⟩

theorem wrong_current_loss_blocks_rollback {m : Nat} (s : Service m)
    (request : RollbackRequest m) (wrong : request.protocol.lossVersion ≠ s.lossVersion) :
    proposeRollback s request = .unknown .targetMismatch := by
  simp [proposeRollback, wrong]

theorem rollback_evaluation_consumes_reissued_candidate {m : Nat} (s : Service m)
    (request : RollbackRequest m) (evaluation : Evaluation m)
    (produced : evaluateRollback s request = .known evaluation) :
    ∃ candidate, proposeRollback s request = .known candidate ∧
      evaluate request.plan (readLoaded s) candidate binaryLoss request.blocks = .known evaluation := by
  cases hp : proposeRollback s request with
  | known candidate =>
      exact ⟨candidate, hp, by simpa [evaluateRollback, hp] using produced⟩
  | unknown why => simp [evaluateRollback, hp] at produced
  | rejected why => simp [evaluateRollback, hp] at produced
  | conflict a b => simp [evaluateRollback, hp] at produced

theorem rollback_attempt_is_actual_activation {m : Nat} (s : Service m)
    (request : RollbackRequest m) (samplingCatalog : List (SamplingReceipt m))
    (authorityCatalog : List (LoadPermit m)) (out : LoadOutcome m)
    (produced : attemptRollback s request samplingCatalog authorityCatalog = .known out) :
    ∃ evaluation, evaluateRollback s request = .known evaluation ∧
      out = activate s evaluation samplingCatalog request.sampling authorityCatalog request.permit := by
  cases he : evaluateRollback s request with
  | known evaluation =>
      exact ⟨evaluation, he, by simpa [attemptRollback, he] using produced.symm⟩
  | unknown why => simp [attemptRollback, he] at produced
  | rejected why => simp [attemptRollback, he] at produced
  | conflict a b => simp [attemptRollback, he] at produced

theorem rollback_loaded_weights_have_current_snapshot {m : Nat} (s : Service m)
    (request : RollbackRequest m) (samplingCatalog : List (SamplingReceipt m))
    (authorityCatalog : List (LoadPermit m)) (out : LoadOutcome m)
    (produced : attemptRollback s request samplingCatalog authorityCatalog = .known out)
    (loaded : out.status = .loaded) :
    (readLoaded out.post).fitted.table = request.archived.fitted.table ∧
      (readLoaded out.post).snapshot = s.journal ∧
      (readLoaded out.post).fitted.protocol = request.protocol ∧
      out.readback = some (readLoaded out.post) := by
  obtain ⟨evaluation, he, rfl⟩ :=
    rollback_attempt_is_actual_activation s request samplingCatalog authorityCatalog out produced
  obtain ⟨candidate, hp, computed⟩ :=
    rollback_evaluation_consumes_reissued_candidate s request evaluation he
  have input := (evaluation_is_actual_input_and_computation request.plan (readLoaded s)
    candidate binaryLoss request.blocks evaluation computed).2.2.2
  have exactLoaded := loaded_package_is_actual_written_readback s evaluation
    samplingCatalog request.sampling authorityCatalog request.permit loaded
  have bound := rollback_proposal_uses_current_sample s request candidate hp
  have model : readLoaded (activate s evaluation samplingCatalog request.sampling
      authorityCatalog request.permit).post = candidate := by
    rw [exactLoaded.2.2.2.2.2.2.1, input]
    rfl
  exact ⟨by rw [model]; exact bound.2.2.1,
    by rw [model]; exact bound.1, by rw [model]; exact bound.2.1,
    exactLoaded.2.2.2.2.2.2.2⟩

theorem rollback_keeps_current_rules_and_training {m : Nat} (s : Service m)
    (request : RollbackRequest m) (samplingCatalog : List (SamplingReceipt m))
    (authorityCatalog : List (LoadPermit m)) :
    (rollbackPost s request samplingCatalog authorityCatalog).gamma = s.gamma ∧
      (rollbackPost s request samplingCatalog authorityCatalog).journal = s.journal ∧
      (rollbackPost s request samplingCatalog authorityCatalog).principal = s.principal ∧
      (rollbackPost s request samplingCatalog authorityCatalog).lossVersion = s.lossVersion := by
  cases he : evaluateRollback s request with
  | known evaluation =>
      have frame := activation_keeps_rules_mechanism_and_training s evaluation samplingCatalog
        request.sampling authorityCatalog request.permit
      simpa [rollbackPost, attemptRollback, he] using
        And.intro frame.1 (And.intro frame.2.2.2 (And.intro frame.2.1 frame.2.2.1))
  | unknown why => simp [rollbackPost, attemptRollback, he]
  | rejected why => simp [rollbackPost, attemptRollback, he]
  | conflict a b => simp [rollbackPost, attemptRollback, he]

theorem rollback_preserves_current_history {m : Nat} (s : Service m)
    (request : RollbackRequest m) (samplingCatalog : List (SamplingReceipt m))
    (authorityCatalog : List (LoadPermit m)) :
    ∃ suffix, (rollbackPost s request samplingCatalog authorityCatalog).history = s.history ++ suffix := by
  cases he : evaluateRollback s request with
  | known evaluation =>
      obtain ⟨entry, appended⟩ := every_activation_attempt_retains_history s evaluation samplingCatalog
        request.sampling authorityCatalog request.permit
      exact ⟨[entry], by simpa [rollbackPost, attemptRollback, he] using appended⟩
  | unknown why => exact ⟨[], by simp [rollbackPost, attemptRollback, he]⟩
  | rejected why => exact ⟨[], by simp [rollbackPost, attemptRollback, he]⟩
  | conflict a b => exact ⟨[], by simp [rollbackPost, attemptRollback, he]⟩

theorem refused_rollback_keeps_actual_prediction {m : Nat} (s : Service m)
    (request : RollbackRequest m) (samplingCatalog : List (SamplingReceipt m))
    (authorityCatalog : List (LoadPermit m))
    (notLoaded : ¬ ∃ out, attemptRollback s request samplingCatalog authorityCatalog = .known out ∧
      out.status = .loaded) :
    readLoaded (rollbackPost s request samplingCatalog authorityCatalog) = readLoaded s ∧
      ∀ query, predictLoaded (rollbackPost s request samplingCatalog authorityCatalog) query =
        predictLoaded s query := by
  cases he : evaluateRollback s request with
  | known evaluation =>
      have refused : (activate s evaluation samplingCatalog request.sampling authorityCatalog request.permit).status ≠ .loaded := by
        intro loaded
        exact notLoaded ⟨_, by simp [attemptRollback, he], loaded⟩
      have kept := refusal_keeps_actual_prediction s evaluation samplingCatalog request.sampling
        authorityCatalog request.permit refused
      simpa [rollbackPost, attemptRollback, he] using And.intro kept.1 kept.2.2
  | unknown why => simp [rollbackPost, attemptRollback, he]
  | rejected why => simp [rollbackPost, attemptRollback, he]
  | conflict a b => simp [rollbackPost, attemptRollback, he]

theorem historical_permission_cannot_authorize_new_evaluation {m : Nat} (s : Service m)
    (request : RollbackRequest m) (samplingCatalog : List (SamplingReceipt m))
    (authorityCatalog : List (LoadPermit m)) (evaluation : Evaluation m)
    (computed : evaluateRollback s request = .known evaluation)
    (different : request.permit.evaluation ≠ evaluation) :
    ¬ ∃ out, attemptRollback s request samplingCatalog authorityCatalog = .known out ∧
      out.status = .loaded := by
  rintro ⟨out, produced, loaded⟩
  have actual : activate s evaluation samplingCatalog request.sampling authorityCatalog request.permit = out := by
    simpa [attemptRollback, computed] using produced
  have permitted := (loaded_package_is_actual_written_readback s evaluation samplingCatalog
    request.sampling authorityCatalog request.permit (by simpa [actual] using loaded)).2.2.2.2.2.1
  have denied := replaced_candidate_does_not_reuse_old_permit authorityCatalog s evaluation request.permit different
  rw [denied] at permitted
  contradiction

end JurisLean.Candidates.CurrentContextRollback20261027
