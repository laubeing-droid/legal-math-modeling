import JurisLean.Candidates.CurrentContextRollback20261027
import JurisLean.Candidates.ValidatedFeedbackLoadAudit20261027

#check JurisLean.Candidates.CurrentContextRollback20261027.rollback_proposal_uses_current_sample
#print axioms JurisLean.Candidates.CurrentContextRollback20261027.rollback_proposal_uses_current_sample
#check JurisLean.Candidates.CurrentContextRollback20261027.wrong_current_loss_blocks_rollback
#print axioms JurisLean.Candidates.CurrentContextRollback20261027.wrong_current_loss_blocks_rollback
#check JurisLean.Candidates.CurrentContextRollback20261027.rollback_evaluation_consumes_reissued_candidate
#print axioms JurisLean.Candidates.CurrentContextRollback20261027.rollback_evaluation_consumes_reissued_candidate
#check JurisLean.Candidates.CurrentContextRollback20261027.rollback_attempt_is_actual_activation
#print axioms JurisLean.Candidates.CurrentContextRollback20261027.rollback_attempt_is_actual_activation
#check JurisLean.Candidates.CurrentContextRollback20261027.rollback_loaded_weights_have_current_snapshot
#print axioms JurisLean.Candidates.CurrentContextRollback20261027.rollback_loaded_weights_have_current_snapshot
#check JurisLean.Candidates.CurrentContextRollback20261027.rollback_keeps_current_rules_and_training
#print axioms JurisLean.Candidates.CurrentContextRollback20261027.rollback_keeps_current_rules_and_training
#check JurisLean.Candidates.CurrentContextRollback20261027.rollback_preserves_current_history
#print axioms JurisLean.Candidates.CurrentContextRollback20261027.rollback_preserves_current_history
#check JurisLean.Candidates.CurrentContextRollback20261027.refused_rollback_keeps_actual_prediction
#print axioms JurisLean.Candidates.CurrentContextRollback20261027.refused_rollback_keeps_actual_prediction
#check JurisLean.Candidates.CurrentContextRollback20261027.historical_permission_cannot_authorize_new_evaluation
#print axioms JurisLean.Candidates.CurrentContextRollback20261027.historical_permission_cannot_authorize_new_evaluation

namespace JurisLean.Candidates.CurrentContextRollbackAudit20261027

open JurisLean.Candidates.Final20261021
open JurisLean.Candidates.LearningConsumer20261027
open JurisLean.Candidates.EventFeedbackConsumer20261027
open JurisLean.Candidates.ProtectedFeedback20261027
open JurisLean.Candidates.ValidatedFeedbackLoad20261027
open JurisLean.Candidates.CurrentContextRollback20261027
open ValidatedFeedbackLoadFixture

def currentScope : DataScope := { scope with ruleVersion := 2 }

def currentFirst : Observation 2 := { row 0 false 11 with scope := currentScope }
def currentSecond : Observation 2 := { row 1 true 12 with scope := currentScope }

def currentStore : Store 2 :=
  let start := emptyStore 2 currentScope [⟨currentFirst, ⟨11⟩⟩, ⟨currentSecond, ⟨12⟩⟩]
  (observe (observe start ⟨10⟩ currentFirst).post ⟨10⟩ currentSecond).post

def currentPlan : ValidationPlan := { plan with scope := currentScope }

def currentBlocks (harm : Bool) : List (DomainBlock 2) :=
  [sampledBlock currentPlan 10 501 (1/20) (1/10) 8 0
    (fun i : Fin 400 => ⟨200000 + i.val⟩)
    (fun i : Fin 400 => if harm then ((1 : Fin 2), false)
      else if i.val % 2 = 0 then (0, false) else (1, true)),
   sampledBlock currentPlan 20 502 (1/20) (1/10) 8 0
    (fun i : Fin 400 => ⟨300000 + i.val⟩)
    (fun _ : Fin 400 => ((1 : Fin 2), !harm))]

def rollbackCheck (harm : Bool)
    (f : Service 2 → RollbackRequest 2 → Evaluation 2 → Bool) : Bool :=
  match built with
  | .known (prior, oldEvaluation) =>
      let oldSampling := sampling oldEvaluation
      let oldPermit := permit prior oldEvaluation
      let priorLoaded := activate prior oldEvaluation [oldSampling] oldSampling [oldPermit] oldPermit
      match fitFromStore currentStore protocol binaryLoss [[0, 0]] with
      | .known current =>
          let service : Service 2 :=
            ⟨{ gamma with normVersion := 2 }, prior.principal, 7, current, currentStore, priorLoaded.post.history⟩
          let request : RollbackRequest 2 :=
            ⟨readLoaded priorLoaded.post, { protocol with fit := { protocol.fit with modelVersion := 99 } },
              currentPlan, currentBlocks harm, oldSampling, oldPermit⟩
          match evaluateRollback service request with
          | .known evaluation =>
              let request := { request with sampling := sampling evaluation, permit := permit service evaluation }
              f service request evaluation
          | _ => false
      | _ => false
  | _ => false

/-- info: true -/
#guard_msgs in
#eval rollbackCheck false (fun s request evaluation =>
  match attemptRollback s request [request.sampling] [request.permit] with
  | .known out => decide (out.status = .loaded ∧
      (readLoaded out.post).fitted.table = request.archived.fitted.table ∧
      (readLoaded out.post).snapshot = currentStore ∧
      (readLoaded out.post).fitted.protocol.fit.modelVersion = 99 ∧
      (readLoaded out.post).fitted.sampleSize = 2 ∧
      (readLoaded out.post).fitted.empiricalRisk = 0 ∧
      request.archived.snapshot.scope.ruleVersion = 1 ∧ out.post.gamma.normVersion = 2 ∧
      out.post.history.length = 2 ∧ out.post.journal = s.journal ∧
      twoPointRisk s = 1/2 ∧ twoPointRisk out.post = 0 ∧ evaluation.passesBounds = true)
  | _ => false)

/-- info: true -/
#guard_msgs in
#eval rollbackCheck false (fun s request _ =>
  match attemptRollback s request [request.sampling] [] with
  | .known out => decide (out.status = .authorityUnresolved ∧
      readLoaded out.post = readLoaded s ∧ out.post.history.length = 2)
  | _ => false)

/-- info: true -/
#guard_msgs in
#eval rollbackCheck false (fun s request _ =>
  match attemptRollback s request [] [request.permit] with
  | .known out => decide (out.status = .samplingUnresolved ∧ readLoaded out.post = readLoaded s)
  | _ => false)

/-- info: true -/
#guard_msgs in
#eval rollbackCheck true (fun s request evaluation =>
  match attemptRollback s request [request.sampling] [request.permit] with
  | .known out => decide (evaluation.passesBounds = false ∧ out.status = .protectedScopeFailed ∧
      readLoaded out.post = readLoaded s ∧ out.post.gamma.normVersion = 2)
  | _ => false)

/-- info: true -/
#guard_msgs in
#eval rollbackCheck false (fun s request _ =>
  let changed := { request with protocol := { request.protocol with lossVersion := 700 } }
  decide (proposeRollback s changed = .unknown .targetMismatch ∧
    rollbackPost s changed [request.sampling] [request.permit] = s))

/-- info: true -/
#guard_msgs in
#eval rollbackCheck false (fun s request _ =>
  let historical := { request.permit with evaluation := { request.permit.evaluation with candidate := request.archived } }
  let changed := { request with permit := historical }
  match attemptRollback s changed [request.sampling] [historical] with
  | .known out => decide (out.status = .authorityUnresolved ∧ readLoaded out.post = readLoaded s)
  | _ => false)

/-- info: true -/
#guard_msgs in
#eval rollbackCheck false (fun s request _ =>
  let changed := { request with blocks := request.blocks.map (fun b => { b with snapshot := b.snapshot + 1 }) }
  match attemptRollback s changed [request.sampling] [request.permit] with
  | .known out => decide (out.status = .samplingUnresolved ∧ readLoaded out.post = readLoaded s)
  | _ => false)

/-- info: true -/
#guard_msgs in
#eval rollbackCheck false (fun s request _ =>
  let changed := { request with archived := { request.archived with fitted := { request.archived.fitted with table := [0] } } }
  decide (rollbackPost s changed [request.sampling] [request.permit] = s))

end JurisLean.Candidates.CurrentContextRollbackAudit20261027
