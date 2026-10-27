import JurisLean.Candidates.AdaptiveRoundLedger20261027
import JurisLean.Candidates.ValidatedFeedbackLoadAudit20261027

#check JurisLean.Candidates.AdaptiveRoundLedger20261027.generation_uses_actual_loaded_and_learner
#print axioms JurisLean.Candidates.AdaptiveRoundLedger20261027.generation_uses_actual_loaded_and_learner
#check JurisLean.Candidates.AdaptiveRoundLedger20261027.recorded_prefix_and_next_round
#print axioms JurisLean.Candidates.AdaptiveRoundLedger20261027.recorded_prefix_and_next_round
#check JurisLean.Candidates.AdaptiveRoundLedger20261027.evaluated_round_spends_its_actual_block_budget
#print axioms JurisLean.Candidates.AdaptiveRoundLedger20261027.evaluated_round_spends_its_actual_block_budget
#check JurisLean.Candidates.AdaptiveRoundLedger20261027.assessed_round_stays_within_budget
#print axioms JurisLean.Candidates.AdaptiveRoundLedger20261027.assessed_round_stays_within_budget
#check JurisLean.Candidates.AdaptiveRoundLedger20261027.finish_round_preserves_budget
#print axioms JurisLean.Candidates.AdaptiveRoundLedger20261027.finish_round_preserves_budget
#check JurisLean.Candidates.AdaptiveRoundLedger20261027.exact_round_replay_retains_current_state
#print axioms JurisLean.Candidates.AdaptiveRoundLedger20261027.exact_round_replay_retains_current_state
#check JurisLean.Candidates.AdaptiveRoundLedger20261027.changed_round_key_does_not_spend_or_load
#print axioms JurisLean.Candidates.AdaptiveRoundLedger20261027.changed_round_key_does_not_spend_or_load
#check JurisLean.Candidates.AdaptiveRoundLedger20261027.evaluated_round_has_fresh_events_and_current_checker
#print axioms JurisLean.Candidates.AdaptiveRoundLedger20261027.evaluated_round_has_fresh_events_and_current_checker
#check JurisLean.Candidates.AdaptiveRoundLedger20261027.learner_change_keeps_service_budget_and_trusted_root
#print axioms JurisLean.Candidates.AdaptiveRoundLedger20261027.learner_change_keeps_service_budget_and_trusted_root
#check JurisLean.Candidates.AdaptiveRoundLedger20261027.self_issued_or_new_checker_permission_cannot_change_learner
#print axioms JurisLean.Candidates.AdaptiveRoundLedger20261027.self_issued_or_new_checker_permission_cannot_change_learner
#check JurisLean.Candidates.AdaptiveRoundLedger20261027.changed_learner_is_actual_next_generator
#print axioms JurisLean.Candidates.AdaptiveRoundLedger20261027.changed_learner_is_actual_next_generator
#check JurisLean.Candidates.AdaptiveRoundLedger20261027.assessed_load_comes_from_actual_activation
#print axioms JurisLean.Candidates.AdaptiveRoundLedger20261027.assessed_load_comes_from_actual_activation
#check JurisLean.Candidates.AdaptiveRoundLedger20261027.recorded_load_is_actual_next_service
#print axioms JurisLean.Candidates.AdaptiveRoundLedger20261027.recorded_load_is_actual_next_service
#check JurisLean.Candidates.AdaptiveRoundLedger20261027.every_round_action_keeps_budget_bound
#print axioms JurisLean.Candidates.AdaptiveRoundLedger20261027.every_round_action_keeps_budget_bound
#check JurisLean.Candidates.AdaptiveRoundLedger20261027.arbitrary_finite_round_actions_keep_budget
#print axioms JurisLean.Candidates.AdaptiveRoundLedger20261027.arbitrary_finite_round_actions_keep_budget

open JurisLean.Candidates.Final20261021
open JurisLean.Candidates.LearningConsumer20261027
open JurisLean.Candidates.SampleCalibrationConsumer20261027
open JurisLean.Candidates.EventFeedbackConsumer20261027
open JurisLean.Candidates.ProtectedFeedback20261027
open JurisLean.Candidates.ValidatedFeedbackLoad20261027
open JurisLean.Candidates.AdaptiveRoundLedger20261027
open ValidatedFeedbackLoadFixture

namespace AdaptiveRoundLedgerFixture

def base (s : Service 2) : RoundState 2 :=
  ⟨s, ⟨1, [[0, 1]]⟩, 55, 3, 1/5, [10, 20], [], none, []⟩

def generate (s : RoundState 2) (loss : Nat := 7) : RoundState 2 :=
  beginAdaptiveRound s ⟨10 + 20 * s.records.length⟩ [] (.observed second)
    { protocol with
      fit := { protocol.fit with modelVersion := 5 + s.records.length }
      lossVersion := loss } plan

def freshBlocks (e : Evaluation 2) : List (DomainBlock 2) :=
  e.blocks.map (fun b => { b with
    snapshot := b.snapshot + 1
    rows := b.rows.map (fun row => { row with event := ⟨row.event.value + 1000000⟩ }) })

def request (s : RoundState 2) (fallback : Evaluation 2) (blocks : List (DomainBlock 2)) :
    RoundRequest 2 :=
  match s.pending with
  | none => ⟨s.records.length, s.checker, .currentFiniteRound, blocks,
      sampling fallback, permit s.service fallback⟩
  | some d =>
      let evaluated := match d.prepared.candidate with
        | .known c => match evaluate d.plan d.prepared.parent c binaryLoss blocks with
          | .known e => e
          | _ => fallback
        | _ => fallback
      ⟨s.records.length, s.checker, .currentFiniteRound, blocks,
        ⟨d.plan, d.prepared.parent, blocks, ⟨d.generatedAt.ticks + 1⟩,
          ⟨d.generatedAt.ticks + 2⟩, ⟨40⟩⟩,
        permit s.service evaluated⟩

def complete (s : RoundState 2) (r : RoundRequest 2) : RoundOutcome 2 :=
  finishAdaptiveRound s r [r.sampling] [r.permit]

def firstRound (s : Service 2) (e : Evaluation 2) : RoundOutcome 2 :=
  let generated := generate (base s)
  complete generated (request generated e e.blocks)

def twoRounds (s : Service 2) (e : Evaluation 2) : RoundOutcome 2 :=
  let first := firstRound s e
  let next := generate first.post 700
  complete next (request next e (freshBlocks e))

def learnerPermit (s : RoundState 2) (next : RoundLearner) : LearnerPermit :=
  ⟨s.checker, s.learner, next,
    ⟨⟨60⟩, s.service.principal, s.service.gamma.caseId, s.service.gamma,
      .party s.service.principal, 3, next.version, none, none,
      s.service.gamma.normVersion, ⟨0⟩, ⟨20⟩⟩⟩

/-- info: true -/
#guard_msgs in
#eval check (fun s e =>
  let out := firstRound s e
  decide (out.status = .evaluated ∧ out.post.records.length = 1 ∧
    roundSpent out.post = 1/10 ∧ twoPointRisk s = 1/2 ∧ twoPointRisk out.post.service = 0 ∧
    out.post.service.gamma = s.gamma ∧ out.post.checker = 55 ∧
    (out.receipt.bind RoundRecord.load).map LoadOutcome.status = some .loaded))

/-- info: true -/
#guard_msgs in
#eval check (fun s e =>
  let out := twoRounds s e
  decide (out.status = .generationUnresolved ∧ roundSpent out.post = 1/10 ∧
    out.post.records.length = 2 ∧ twoPointRisk out.post.service = 0 ∧
    out.post.service.gamma = s.gamma ∧ out.post.checker = 55 ∧
    (out.post.records.map (fun r => r.declaration.visiblePrefix)) = [0, 1]))

/-- info: true -/
#guard_msgs in
#eval check (fun s e =>
  let start := generate (base s)
  let original := request start e e.blocks
  let later := twoRounds s e
  let replay := complete later.post original
  decide (replay.status = .replayed ∧ replay.post = later.post ∧
    replay.receipt = (firstRound s e).receipt ∧ roundSpent replay.post = 1/10))

/-- info: true -/
#guard_msgs in
#eval check (fun s e =>
  let generated := generate (base s)
  let r := request generated e e.blocks
  let first := complete generated r
  let conflict := complete first.post { r with checker := 999 }
  decide (conflict.status = .keyConflict ∧ conflict.post = first.post ∧ conflict.receipt = none))

-- Renaming a validation snapshot does not make its observed events fresh.
/-- info: true -/
#guard_msgs in
#eval check (fun s e =>
  let next := generate (firstRound s e).post
  let reused := e.blocks.map (fun b => { b with snapshot := b.snapshot + 999 })
  let out := complete next (request next e reused)
  decide (out.status = .adaptiveCertificateInvalid ∧ roundSpent out.post = 1/10 ∧
    twoPointRisk out.post.service = 0))

/-- info: true -/
#guard_msgs in
#eval check (fun s e =>
  let generated := generate (base s)
  let r := request generated e e.blocks
  let out := finishAdaptiveRound generated r [] [r.permit]
  decide (out.status = .riskCertificateMissing ∧ roundSpent out.post = 0 ∧
    out.post.records.length = 1 ∧ out.post.service = generated.service))

/-- info: true -/
#guard_msgs in
#eval check (fun s e =>
  let generated := generate (base s)
  let r := request generated e e.blocks
  let early := { r with sampling := { r.sampling with declaredAt := ⟨0⟩ } }
  let out := complete generated early
  decide (out.status = .riskCertificateMissing ∧ roundSpent out.post = 0))

/-- info: true -/
#guard_msgs in
#eval check (fun s e =>
  let generated := generate (base s)
  let r := { request generated e e.blocks with checker := 56 }
  let out := complete generated r
  decide (out.status = .trustRootMismatch ∧ out.post.checker = 55 ∧
    out.post.service = generated.service ∧ roundSpent out.post = 0))

/-- info: true -/
#guard_msgs in
#eval check (fun s e =>
  let generated := generate (base s)
  let r := { request generated e e.blocks with claim := .unboundedImprovement }
  let out := complete generated r
  decide (out.status = .claimScopeExceeded ∧ out.post.service = generated.service))

/-- info: true -/
#guard_msgs in
#eval check (fun s e =>
  let generated := generate { base s with limit := 1/10 }
  let first := complete generated (request generated e e.blocks)
  let next := generate first.post
  let out := complete next (request next e (freshBlocks e))
  decide (out.status = .budgetExceeded ∧ roundSpent out.post = 1/10 ∧
    out.post.records.length = 2 ∧ twoPointRisk out.post.service = 0))

-- Computed evidence has spent its budget even when authorization refuses load.
/-- info: true -/
#guard_msgs in
#eval check (fun s e =>
  let generated := generate (base s)
  let r := request generated e e.blocks
  let out := finishAdaptiveRound generated r [r.sampling] []
  decide (out.status = .evaluated ∧ roundSpent out.post = 1/10 ∧
    twoPointRisk out.post.service = 1/2 ∧
    (out.receipt.bind RoundRecord.load).map LoadOutcome.status = some .authorityUnresolved))

-- Even a previously unqualified block is retained in the visible exposure history.
/-- info: true -/
#guard_msgs in
#eval check (fun s e =>
  let generated := generate (base s)
  let r := request generated e e.blocks
  let failed := finishAdaptiveRound generated r [] [r.permit]
  let next := generate failed.post
  let out := complete next (request next e e.blocks)
  decide (out.status = .adaptiveCertificateInvalid ∧ roundSpent out.post = 0))

/-- info: true -/
#guard_msgs in
#eval check (fun s _ =>
  let initial := base s
  let next : RoundLearner := ⟨2, [[1, 1]]⟩
  let p := learnerPermit initial next
  let updated := changeRoundLearner initial next [p] p
  let generated := generate updated
  decide (updated.learner = next ∧ updated.service = s ∧ updated.checker = 55 ∧
    updated.learnerChanges = [p] ∧
    generated.pending.map (fun d => d.prepared.models) = some [[0, 0], [1, 1]]))

/-- info: true -/
#guard_msgs in
#eval check (fun s _ =>
  let initial := base s
  let next : RoundLearner := ⟨2, [[1, 1]]⟩
  let p := learnerPermit initial next
  decide (changeRoundLearner initial next [] p = initial))

/-- info: true -/
#guard_msgs in
#eval check (fun s _ =>
  let initial := base s
  let next : RoundLearner := ⟨2, [[1, 1]]⟩
  let p := { learnerPermit initial next with checker := 56 }
  decide (changeRoundLearner initial next [p] p = initial))

/-- info: true -/
#guard_msgs in
#eval check (fun s _ =>
  let initial := generate (base s)
  let next : RoundLearner := ⟨2, [[1, 1]]⟩
  let p := learnerPermit initial next
  decide (changeRoundLearner initial next [p] p = initial))

/-- info: true -/
#guard_msgs in
#eval check (fun s _ =>
  let initial := base s
  let malformed : RoundLearner := ⟨2, [[2, 1]]⟩
  let p := learnerPermit initial malformed
  decide (changeRoundLearner initial malformed [p] p = initial))

-- A failed protected comparison still used the sampled evidence.
/-- info: true -/
#guard_msgs in
#eval check (fun s e =>
  let generated := generate (base s)
  let r := request generated e [mixedBlock, block 20 false]
  let out := complete generated r
  decide (out.status = .evaluated ∧ roundSpent out.post = 1/10 ∧
    twoPointRisk out.post.service = 1/2 ∧
    (out.receipt.bind RoundRecord.load).map LoadOutcome.status = some .protectedScopeFailed))

/-- info: true -/
#guard_msgs in
#eval check (fun s e =>
  let generated := generate (base s)
  let original := request generated e e.blocks
  let forged := { original with blocks := e.blocks.map (fun b => { b with delta := 1/1000 }) }
  let out := finishAdaptiveRound generated forged [original.sampling] [original.permit]
  decide (out.status = .riskCertificateMissing ∧ roundSpent out.post = 0))

-- A subsequent caller cannot silently drop an originally protected domain.
/-- info: true -/
#guard_msgs in
#eval check (fun s e =>
  let generated := beginAdaptiveRound (base s) ⟨10⟩ [] (.observed second)
    { protocol with fit := { protocol.fit with modelVersion := 5 } } { plan with domains := [10] }
  let out := complete generated (request generated e [mixedBlock])
  decide (out.status = .protectedScopeMismatch ∧ out.post.protectedDomains = [10, 20] ∧
    roundSpent out.post = 0 ∧ twoPointRisk out.post.service = 1/2))

end AdaptiveRoundLedgerFixture

