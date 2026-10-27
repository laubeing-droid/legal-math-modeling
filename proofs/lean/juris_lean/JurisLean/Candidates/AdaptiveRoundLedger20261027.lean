import JurisLean.Candidates.ValidatedFeedbackLoad20261027

/-!
Original E15: finite actual round accounting. Candidate generation happens in
beginAdaptiveRound before finishAdaptiveRound receives a validation block.
The append-only round prefix identifies visible feedback. External catalogues
and chronological declarations remain trusted inputs, not proofs of iid or law.
No function here changes the fixed checker, legal context or permission policy.
-/

namespace JurisLean.Candidates.AdaptiveRoundLedger20261027

open JurisLean.Candidates.Final20261021
open JurisLean.Candidates.LearningConsumer20261027
open JurisLean.Candidates.EventFeedbackConsumer20261027
open JurisLean.Candidates.ProtectedFeedback20261027
open JurisLean.Candidates.ValidatedFeedbackLoad20261027

structure RoundLearner where
  version : Nat
  proposals : List (List ℚ)
  deriving DecidableEq, Repr

inductive RoundClaim where
  | currentFiniteRound | unboundedImprovement
  deriving DecidableEq, Repr

structure RoundRequest (m : Nat) where
  round : Nat
  checker : Nat
  claim : RoundClaim
  blocks : List (DomainBlock m)
  sampling : SamplingReceipt m
  permit : LoadPermit m
  deriving DecidableEq, Repr

structure RoundDeclaration (m : Nat) where
  learner : RoundLearner
  generatedAt : Instant
  visiblePrefix : Nat
  prepared : Prepared m
  plan : ValidationPlan
  deriving DecidableEq, Repr

inductive RoundStatus where
  | evaluated | generationUnresolved | evaluationUnresolved
  | adaptiveCertificateInvalid | riskCertificateMissing | budgetExceeded
  | trustRootMismatch | claimScopeExceeded | generationMismatch | protectedScopeMismatch
  | replayed | keyConflict | roundMismatch | generationMissing
  deriving DecidableEq, Repr

structure RoundRecord (m : Nat) where
  declaration : RoundDeclaration m
  request : RoundRequest m
  status : RoundStatus
  evaluation : Option (Result (Evaluation m))
  load : Option (LoadOutcome m)
  charge : ℚ
  deriving DecidableEq, Repr

structure LearnerPermit where
  checker : Nat
  before : RoundLearner
  after : RoundLearner
  grant : Authorization.Grant
  deriving DecidableEq, Repr

structure RoundState (m : Nat) where
  service : Service m
  learner : RoundLearner
  checker : Nat
  horizon : Nat
  limit : ℚ
  protectedDomains : List Nat
  records : List (RoundRecord m)
  pending : Option (RoundDeclaration m)
  learnerChanges : List LearnerPermit
  deriving DecidableEq, Repr

def roundSpent {m : Nat} (s : RoundState m) : ℚ :=
  (s.records.map RoundRecord.charge).sum

def requestedEvents {m : Nat} (r : RoundRequest m) : List EventId :=
  r.blocks.flatMap (fun b => b.rows.map (fun row => row.event))

-- Includes blocks from declined/unknown evaluations, not just loaded models.
def exposedRoundEvents {m : Nat} (s : RoundState m) : List EventId :=
  s.records.flatMap (fun record => requestedEvents record.request)

def roundCost {m : Nat} (r : RoundRequest m) : ℚ :=
  (r.blocks.map DomainBlock.delta).sum

def beginAdaptiveRound {m : Nat} (s : RoundState m) (now : Instant)
    (correctionPermits : List (CorrectionPermit m)) (change : Change m)
    (protocol : LearningProtocol) (plan : ValidationPlan) : RoundState m :=
  if s.pending.isSome ∨ s.horizon ≤ s.records.length then s
  else
    let prepared := prepareNext s.service now correctionPermits change protocol s.learner.proposals
    let declared : RoundDeclaration m :=
      ⟨s.learner, now, s.records.length, prepared, { plan with models := prepared.models }⟩
    { s with service := prepared.post, pending := some declared }

def emptyRoundRecord {m : Nat} (d : RoundDeclaration m) (r : RoundRequest m)
    (status : RoundStatus) : RoundRecord m :=
  ⟨d, r, status, none, none, 0⟩

def assessAdaptiveRound {m : Nat} (s : RoundState m) (d : RoundDeclaration m)
    (r : RoundRequest m) (samplingCatalog : List (SamplingReceipt m))
    (authorityCatalog : List (LoadPermit m)) : RoundRecord m :=
  if r.checker ≠ s.checker then emptyRoundRecord d r .trustRootMismatch
  else if r.claim ≠ .currentFiniteRound then emptyRoundRecord d r .claimScopeExceeded
  else if d.plan.domains ≠ s.protectedDomains then emptyRoundRecord d r .protectedScopeMismatch
  else if d.visiblePrefix ≠ s.records.length ∨ d.learner ≠ s.learner ∨
      d.prepared.post ≠ s.service then emptyRoundRecord d r .generationMismatch
  else if ¬ (∀ event ∈ requestedEvents r, event ∉ exposedRoundEvents s) then
    emptyRoundRecord d r .adaptiveCertificateInvalid
  else if ¬ (r.sampling ∈ samplingCatalog ∧ r.sampling.plan = d.plan ∧
      r.sampling.parent = d.prepared.parent ∧ r.sampling.blocks = r.blocks ∧
      d.generatedAt.ticks ≤ r.sampling.declaredAt.ticks ∧
      r.sampling.declaredAt.ticks < r.sampling.acquiredAt.ticks) then
    emptyRoundRecord d r .riskCertificateMissing
  else if ¬ (0 ≤ roundCost r ∧ roundSpent s + roundCost r ≤ s.limit) then
    emptyRoundRecord d r .budgetExceeded
  else
    match d.prepared.candidate with
    | .known candidate =>
        let computed := evaluate d.plan d.prepared.parent candidate binaryLoss r.blocks
        match computed with
        | .known evaluation =>
            let loaded := activate s.service evaluation samplingCatalog r.sampling
              authorityCatalog r.permit
            ⟨d, r, .evaluated, some computed, some loaded, roundCost r⟩
        | _ => { emptyRoundRecord d r .evaluationUnresolved with evaluation := some computed }
    | _ => emptyRoundRecord d r .generationUnresolved

def appendRoundRecord {m : Nat} (s : RoundState m) (record : RoundRecord m) : RoundState m :=
  let actualPost := match record.load with
    | some outcome => outcome.post
    | none => s.service
  { s with service := actualPost, records := s.records ++ [record], pending := none }

structure RoundOutcome (m : Nat) where
  status : RoundStatus
  post : RoundState m
  receipt : Option (RoundRecord m)
  deriving DecidableEq, Repr

-- The existing business key is the monotone round number, not a digest.
-- A replay returns its original receipt without restoring an older state.
def finishAdaptiveRound {m : Nat} (s : RoundState m) (r : RoundRequest m)
    (samplingCatalog : List (SamplingReceipt m))
    (authorityCatalog : List (LoadPermit m)) : RoundOutcome m :=
  match s.records.find? (fun entry => entry.request.round == r.round) with
  | some old =>
      if old.request = r then ⟨.replayed, s, some old⟩
      else ⟨.keyConflict, s, none⟩
  | none =>
      if r.round ≠ s.records.length then ⟨.roundMismatch, s, none⟩
      else if s.horizon ≤ s.records.length then ⟨.claimScopeExceeded, s, none⟩
      else match s.pending with
      | none => ⟨.generationMissing, s, none⟩
      | some declared =>
          let record := assessAdaptiveRound s declared r samplingCatalog authorityCatalog
          ⟨record.status, appendRoundRecord s record, some record⟩

-- This fixed syntactic checker only certifies a finite table class. It does
-- not authorize deployment and cannot replace its own code or trusted root.
def learnerShapeValid (m : Nat) (learner : RoundLearner) : Bool :=
  decide (∀ table ∈ learner.proposals, table.length = m ∧
    ∀ q ∈ table, 0 ≤ q ∧ q ≤ 1)

def changeRoundLearner {m : Nat} (s : RoundState m) (next : RoundLearner)
    (catalog : List LearnerPermit) (permit : LearnerPermit) : RoundState m :=
  if s.pending = none ∧ learnerShapeValid m next = true ∧
      s.learner.version < next.version ∧ permit ∈ catalog ∧
      permit.checker = s.checker ∧ permit.before = s.learner ∧ permit.after = next ∧
      Authorization.checkGrant s.service.gamma s.service.principal 3 next.version
        (.party s.service.principal) none none permit.grant = true then
    { s with learner := next, learnerChanges := s.learnerChanges ++ [permit] }
  else s

theorem generation_uses_actual_loaded_and_learner {m : Nat}
    (s : RoundState m) (now : Instant) (permits : List (CorrectionPermit m))
    (change : Change m) (protocol : LearningProtocol) (plan : ValidationPlan)
    (free : s.pending = none) (room : s.records.length < s.horizon) :
    (beginAdaptiveRound s now permits change protocol plan).pending =
      some ⟨s.learner, now, s.records.length,
        prepareNext s.service now permits change protocol s.learner.proposals,
        { plan with models := (readLoaded s.service).fitted.table :: s.learner.proposals }⟩ ∧
    (beginAdaptiveRound s now permits change protocol plan).service.journal =
      (applyChange now permits s.service.journal change).post ∧
    (beginAdaptiveRound s now permits change protocol plan).records = s.records := by
  simp [beginAdaptiveRound, free, Nat.not_le_of_lt room, prepareNext, processAndFit]

theorem recorded_prefix_and_next_round {m : Nat} (s : RoundState m) (record : RoundRecord m) :
    (appendRoundRecord s record).records.take s.records.length = s.records ∧
    (appendRoundRecord s record).records.length = s.records.length + 1 ∧
    (appendRoundRecord s record).pending = none ∧
    roundSpent (appendRoundRecord s record) = roundSpent s + record.charge := by
  simp [appendRoundRecord, roundSpent]

theorem evaluated_round_spends_its_actual_block_budget {m : Nat}
    (s : RoundState m) (d : RoundDeclaration m) (r : RoundRequest m)
    (samples : List (SamplingReceipt m)) (permits : List (LoadPermit m))
    (computed : (assessAdaptiveRound s d r samples permits).status = .evaluated) :
    (assessAdaptiveRound s d r samples permits).charge =
      (r.blocks.map DomainBlock.delta).sum := by
  unfold assessAdaptiveRound at computed ⊢
  split_ifs at computed ⊢ <;> try simp_all [emptyRoundRecord, roundCost]
  all_goals split at computed <;> try simp_all [emptyRoundRecord, roundCost]
  all_goals split at computed <;> simp_all [emptyRoundRecord, roundCost]

theorem assessed_round_stays_within_budget {m : Nat}
    (s : RoundState m) (d : RoundDeclaration m) (r : RoundRequest m)
    (samples : List (SamplingReceipt m)) (permits : List (LoadPermit m))
    (bounded : roundSpent s ≤ s.limit) :
    0 ≤ (assessAdaptiveRound s d r samples permits).charge ∧
    roundSpent s + (assessAdaptiveRound s d r samples permits).charge ≤ s.limit := by
  cases candidateEq : d.prepared.candidate <;>
    simp only [assessAdaptiveRound, candidateEq]
  all_goals split_ifs <;> try simp_all [emptyRoundRecord]
  all_goals first | assumption | (split <;> simp_all [emptyRoundRecord])

theorem finish_round_preserves_budget {m : Nat} (s : RoundState m) (r : RoundRequest m)
    (samples : List (SamplingReceipt m)) (permits : List (LoadPermit m))
    (bounded : roundSpent s ≤ s.limit) :
    roundSpent (finishAdaptiveRound s r samples permits).post ≤ s.limit := by
  unfold finishAdaptiveRound
  split
  · split <;> exact bounded
  · split_ifs <;> try exact bounded
    split
    · exact bounded
    · simpa only [(recorded_prefix_and_next_round s _).2.2.2] using
        (assessed_round_stays_within_budget s _ r samples permits bounded).2

theorem exact_round_replay_retains_current_state {m : Nat}
    (s : RoundState m) (r : RoundRequest m) (old : RoundRecord m)
    (samples : List (SamplingReceipt m)) (permits : List (LoadPermit m))
    (found : s.records.find? (fun entry => entry.request.round == r.round) = some old)
    (same : old.request = r) :
    finishAdaptiveRound s r samples permits = ⟨.replayed, s, some old⟩ := by
  simp [finishAdaptiveRound, found, same]

theorem changed_round_key_does_not_spend_or_load {m : Nat}
    (s : RoundState m) (r : RoundRequest m) (old : RoundRecord m)
    (samples : List (SamplingReceipt m)) (permits : List (LoadPermit m))
    (found : s.records.find? (fun entry => entry.request.round == r.round) = some old)
    (changed : old.request ≠ r) :
    finishAdaptiveRound s r samples permits = ⟨.keyConflict, s, none⟩ := by
  simp [finishAdaptiveRound, found, changed]

theorem evaluated_round_has_fresh_events_and_current_checker {m : Nat}
    (s : RoundState m) (d : RoundDeclaration m) (r : RoundRequest m)
    (samples : List (SamplingReceipt m)) (permits : List (LoadPermit m))
    (computed : (assessAdaptiveRound s d r samples permits).status = .evaluated) :
    r.checker = s.checker ∧ r.claim = .currentFiniteRound ∧ d.plan.domains = s.protectedDomains ∧
    ∀ event ∈ requestedEvents r, event ∉ exposedRoundEvents s := by
  unfold assessAdaptiveRound at computed
  split_ifs at computed <;> simp_all [emptyRoundRecord]
  all_goals split at computed <;> simp_all [emptyRoundRecord]

theorem learner_change_keeps_service_budget_and_trusted_root {m : Nat}
    (s : RoundState m) (next : RoundLearner) (catalog : List LearnerPermit)
    (permit : LearnerPermit) :
    (changeRoundLearner s next catalog permit).service = s.service ∧
    (changeRoundLearner s next catalog permit).checker = s.checker ∧
    (changeRoundLearner s next catalog permit).records = s.records ∧
    (changeRoundLearner s next catalog permit).limit = s.limit ∧
    (changeRoundLearner s next catalog permit).horizon = s.horizon ∧
    (changeRoundLearner s next catalog permit).protectedDomains = s.protectedDomains := by
  unfold changeRoundLearner
  split <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem self_issued_or_new_checker_permission_cannot_change_learner {m : Nat}
    (s : RoundState m) (next : RoundLearner) (catalog : List LearnerPermit)
    (permit : LearnerPermit)
    (untrusted : permit ∉ catalog ∨ permit.checker ≠ s.checker) :
    changeRoundLearner s next catalog permit = s := by
  rcases untrusted with absent | changed
  · simp [changeRoundLearner, absent]
  · simp [changeRoundLearner, changed]

theorem changed_learner_is_actual_next_generator {m : Nat}
    (s : RoundState m) (next : RoundLearner) (catalog : List LearnerPermit)
    (permit : LearnerPermit) (changed : (changeRoundLearner s next catalog permit).learner = next)
    (now : Instant) (corrections : List (CorrectionPermit m)) (change : Change m)
    (protocol : LearningProtocol) (plan : ValidationPlan)
    (free : (changeRoundLearner s next catalog permit).pending = none)
    (room : (changeRoundLearner s next catalog permit).records.length <
      (changeRoundLearner s next catalog permit).horizon) :
    (beginAdaptiveRound (changeRoundLearner s next catalog permit)
      now corrections change protocol plan).pending =
      some ⟨next, now, (changeRoundLearner s next catalog permit).records.length,
        prepareNext s.service now corrections change protocol next.proposals,
        { plan with models := (readLoaded s.service).fitted.table :: next.proposals }⟩ := by
  have generated := (generation_uses_actual_loaded_and_learner
    (changeRoundLearner s next catalog permit) now corrections change protocol plan free room).1
  simpa only [changed, (learner_change_keeps_service_budget_and_trusted_root
    s next catalog permit).1] using generated


theorem assessed_load_comes_from_actual_activation {m : Nat}
    (s : RoundState m) (d : RoundDeclaration m) (r : RoundRequest m)
    (samples : List (SamplingReceipt m)) (permits : List (LoadPermit m))
    (evaluation : Evaluation m) (loaded : LoadOutcome m)
    (actualEvaluation : (assessAdaptiveRound s d r samples permits).evaluation = some (.known evaluation))
    (actualLoad : (assessAdaptiveRound s d r samples permits).load = some loaded) :
    loaded = activate s.service evaluation samples r.sampling permits r.permit := by
  unfold assessAdaptiveRound at actualEvaluation actualLoad
  split_ifs at actualEvaluation actualLoad <;> try simp_all [emptyRoundRecord]
  all_goals split at actualEvaluation <;> try simp_all [emptyRoundRecord]
  all_goals split at actualEvaluation <;> simp_all [emptyRoundRecord]

theorem recorded_load_is_actual_next_service {m : Nat}
    (s : RoundState m) (record : RoundRecord m) (loaded : LoadOutcome m)
    (actual : record.load = some loaded) :
    (appendRoundRecord s record).service = loaded.post := by
  simp [appendRoundRecord, actual]

inductive RoundAction (m : Nat) where
  | generate (now : Instant) (permits : List (CorrectionPermit m)) (change : Change m)
      (protocol : LearningProtocol) (plan : ValidationPlan)
  | assess (request : RoundRequest m) (samples : List (SamplingReceipt m))
      (permits : List (LoadPermit m))
  | learner (next : RoundLearner) (catalog : List LearnerPermit) (permit : LearnerPermit)

def applyRoundAction {m : Nat} (s : RoundState m) : RoundAction m → RoundState m
  | .generate now permits change protocol plan =>
      beginAdaptiveRound s now permits change protocol plan
  | .assess request samples permits => (finishAdaptiveRound s request samples permits).post
  | .learner next catalog permit => changeRoundLearner s next catalog permit

theorem every_round_action_keeps_budget_bound {m : Nat}
    (s : RoundState m) (action : RoundAction m) (bounded : roundSpent s ≤ s.limit) :
    (applyRoundAction s action).limit = s.limit ∧
    roundSpent (applyRoundAction s action) ≤ s.limit := by
  cases action with
  | generate now permits change protocol plan =>
      simp only [applyRoundAction]
      unfold beginAdaptiveRound
      split <;> exact ⟨rfl, bounded⟩
  | learner next catalog permit =>
      simp only [applyRoundAction]
      unfold changeRoundLearner
      split <;> exact ⟨rfl, bounded⟩
  | assess r samples permits =>
      simp only [applyRoundAction]
      refine ⟨?_, finish_round_preserves_budget s r samples permits bounded⟩
      unfold finishAdaptiveRound
      split
      · split <;> rfl
      · split_ifs <;> try rfl
        split <;> rfl

theorem arbitrary_finite_round_actions_keep_budget {m : Nat}
    (actions : List (RoundAction m)) (s : RoundState m) (bounded : roundSpent s ≤ s.limit) :
    (actions.foldl applyRoundAction s).limit = s.limit ∧
    roundSpent (actions.foldl applyRoundAction s) ≤ s.limit := by
  induction actions generalizing s with
  | nil => exact ⟨rfl, bounded⟩
  | cons action rest ih =>
      have one := every_round_action_keeps_budget_bound s action bounded
      have all := ih (applyRoundAction s action) (by simpa only [one.1] using one.2)
      simpa only [List.foldl_cons, one.1] using all


end JurisLean.Candidates.AdaptiveRoundLedger20261027

