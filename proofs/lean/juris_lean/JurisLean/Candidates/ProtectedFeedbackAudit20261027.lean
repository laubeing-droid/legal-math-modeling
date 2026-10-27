import JurisLean.Candidates.ProtectedFeedback20261027

#check JurisLean.Candidates.ProtectedFeedback20261027.protected_iid_joint_event
#print axioms JurisLean.Candidates.ProtectedFeedback20261027.protected_iid_joint_event
#check JurisLean.Candidates.ProtectedFeedback20261027.finite_radius_mono_models
#print axioms JurisLean.Candidates.ProtectedFeedback20261027.finite_radius_mono_models
#check JurisLean.Candidates.ProtectedFeedback20261027.verified_radius_covers_fixed_class
#print axioms JurisLean.Candidates.ProtectedFeedback20261027.verified_radius_covers_fixed_class
#check JurisLean.Candidates.ProtectedFeedback20261027.evaluation_is_actual_input_and_computation
#print axioms JurisLean.Candidates.ProtectedFeedback20261027.evaluation_is_actual_input_and_computation
#check JurisLean.Candidates.ProtectedFeedback20261027.evaluated_models_are_in_predeclared_class
#print axioms JurisLean.Candidates.ProtectedFeedback20261027.evaluated_models_are_in_predeclared_class
#check JurisLean.Candidates.ProtectedFeedback20261027.accepted_checks_every_actual_domain
#print axioms JurisLean.Candidates.ProtectedFeedback20261027.accepted_checks_every_actual_domain
#check JurisLean.Candidates.ProtectedFeedback20261027.accepted_on_joint_event_preserves_each_risk
#print axioms JurisLean.Candidates.ProtectedFeedback20261027.accepted_on_joint_event_preserves_each_risk
#check JurisLean.Candidates.ProtectedFeedback20261027.sampled_block_uses_exact_losses
#print axioms JurisLean.Candidates.ProtectedFeedback20261027.sampled_block_uses_exact_losses
#check JurisLean.Candidates.ProtectedFeedback20261027.actual_protected_evaluation_confidence
#print axioms JurisLean.Candidates.ProtectedFeedback20261027.actual_protected_evaluation_confidence
#check JurisLean.Candidates.ProtectedFeedback20261027.average_improvement_can_harm_protected_point
#print axioms JurisLean.Candidates.ProtectedFeedback20261027.average_improvement_can_harm_protected_point

open JurisLean.Candidates.Final20261021
open JurisLean.Candidates.LearningConsumer20261027
open JurisLean.Candidates.SampleCalibrationConsumer20261027
open JurisLean.Candidates.EventFeedbackConsumer20261027
open JurisLean.Candidates.ProtectedFeedback20261027

namespace ProtectedFeedbackFixture

def protocol : LearningProtocol :=
  ⟨⟨1, 2, 3, 4, 5, ⟨10⟩, ⟨1⟩⟩, 6, 7, 8, 9, 10, 11, 12, 1/10⟩
def scope : DataScope := ⟨1, 2, 3, 6, 8, 9, 10, 12, 1, 1, 1, .behavior⟩
def models : List (List ℚ) := [[0, 0], [0, 1]]
def row (feature : Fin 2) (label : Bool) (id : Nat) : Observation 2 :=
  ⟨scope, ⟨id⟩, ⟨id⟩, ⟨id⟩, ⟨id⟩, feature, label, ⟨id⟩, .external, ⟨0⟩⟩
def first : Observation 2 := row 0 false 1
def second : Observation 2 := row 1 true 2
def initial : Store 2 := emptyStore 2 scope [⟨first, ⟨1⟩⟩, ⟨second, ⟨2⟩⟩]
def oldState : Store 2 := (observe initial ⟨10⟩ first).post
def newState : Store 2 := (observe oldState ⟨10⟩ second).post
def plan : ValidationPlan := ⟨scope, 31, [10, 20], models, 1/10⟩

def block (domain : Nat) (criticalLabel : Bool) : DomainBlock 2 :=
  sampledBlock plan domain (100 + domain) (1/20) (1/10) 8 0
    (fun i : Fin 400 => ⟨10000 * domain + i.val⟩)
    (fun _ : Fin 400 => ((1 : Fin 2), criticalLabel))

def mixedBlock : DomainBlock 2 :=
  sampledBlock plan 10 110 (1/20) (1/10) 8 0
    (fun i : Fin 400 => ⟨100000 + i.val⟩)
    (fun i : Fin 400 => (if i.val % 2 = 0 then (0, false) else (1, true)))

def withActualFits (f : TrainingCandidate 2 → TrainingCandidate 2 → Result (Evaluation 2)) :
    Result (Evaluation 2) :=
  match fitFromStore oldState protocol binaryLoss models with
  | .known parent =>
      match fitFromStore newState protocol binaryLoss models with
      | .known candidate => f parent candidate
      | .unknown e => .unknown e
      | .rejected e => .rejected e
      | .conflict a b => .conflict a b
  | .unknown e => .unknown e
  | .rejected e => .rejected e
  | .conflict a b => .conflict a b

def run (p : ValidationPlan) (blocks : List (DomainBlock 2)) : Result (Evaluation 2) :=
  withActualFits (fun parent candidate => evaluate p parent candidate binaryLoss blocks)

-- Actual old/new fits, losses 1/2 -> 0 and 1 -> 0, both domains accepted.
/-- info: true -/
#guard_msgs in
#eval
  match run plan [mixedBlock, block 20 true] with
  | .known out => decide (out.parent.fitted.table = [0, 0] ∧ out.candidate.fitted.table = [0, 1] ∧
      out.accepted = true ∧ out.statistics.map DomainStatistics.oldEmpirical = [1/2, 1] ∧
      out.statistics.map DomainStatistics.newEmpirical = [0, 0] ∧ out.blocks = [mixedBlock, block 20 true])
  | _ => false

-- Population weights 9/10,1/10 improve average 9/10 -> 1/10, but the
-- protected point worsens 0 -> 1. The actual per-domain gate refuses it.
/-- info: true -/
#guard_msgs in
#eval
  match run plan [block 10 true, block 20 false] with
  | .known out => decide (out.accepted = false ∧
      out.statistics.map DomainStatistics.oldEmpirical = [1, 0] ∧
      out.statistics.map DomainStatistics.newEmpirical = [0, 1])
  | _ => false

-- An omitted protected domain is not an empty, automatically passing check.
/-- info: true -/
#guard_msgs in
#eval decide (run plan [mixedBlock] = Result.unknown Error.scopeMismatch)

/-- info: true -/
#guard_msgs in
#eval decide (run { plan with domains := [10, 10] } [mixedBlock, block 10 true] =
  Result.unknown Error.scopeMismatch)

-- Both domains must pay their budgets; the overall budget is not reusable.
/-- info: true -/
#guard_msgs in
#eval decide (run plan [{ mixedBlock with delta := 1/10 }, { block 20 true with delta := 1/10 }] =
  Result.unknown Error.scopeMismatch)

-- A claimed small delta/radius is checked arithmetically, not accepted as evidence.
/-- info: true -/
#guard_msgs in
#eval decide (run plan [{ mixedBlock with delta := 1/1000 }, block 20 true] =
  Result.unknown Error.missingEvidence)

/-- info: true -/
#guard_msgs in
#eval decide (run plan [{ mixedBlock with radius := 1/100 }, block 20 true] =
  Result.unknown Error.missingEvidence)

/-- info: true -/
#guard_msgs in
#eval decide (run plan [{ mixedBlock with rows := [] }, block 20 true] =
  Result.unknown Error.missingEvidence)

-- Post-validation expansion cannot reuse the smaller class certificate.
/-- info: true -/
#guard_msgs in
#eval decide (run { plan with models := [[0, 0]] } [mixedBlock, block 20 true] =
  Result.unknown Error.scopeMismatch)

/-- info: true -/
#guard_msgs in
#eval decide (run { plan with scope := { scope with target := 99 } } [mixedBlock, block 20 true] =
  Result.unknown Error.targetMismatch)

/-- info: true -/
#guard_msgs in
#eval decide (withActualFits (fun parent candidate =>
    evaluate plan parent { candidate with fitted := { candidate.fitted with
      protocol := { candidate.fitted.protocol with lossVersion := 99 } } }
      binaryLoss [mixedBlock, block 20 true]) = Result.unknown Error.targetMismatch)

/-- info: true -/
#guard_msgs in
#eval decide (run plan [{ mixedBlock with rows :=
    mixedBlock.rows.map (fun row => if row.event = ⟨100000⟩ then { row with event := ⟨1⟩ } else row) },
    block 20 true] = Result.unknown Error.missingEvidence)

/-- info: true -/
#guard_msgs in
#eval decide (run plan [{ mixedBlock with rows :=
    mixedBlock.rows.map (fun row => { row with event := ⟨800000⟩ }) }, block 20 true] =
  Result.unknown Error.missingEvidence)

/-- info: true -/
#guard_msgs in
#eval decide (run plan [mixedBlock, { block 20 true with protocol := 32 }] =
  Result.unknown Error.missingEvidence)

-- A changed model version is allowed when the declared target/feature/loss and
-- whole actual table membership are still checked; full-protocol equality
-- would incorrectly forbid ordinary candidate replacement.
/-- info: true -/
#guard_msgs in
#eval
  match withActualFits (fun parent candidate =>
    evaluate plan parent { candidate with fitted := { candidate.fitted with
      protocol := { candidate.fitted.protocol with fit := { candidate.fitted.protocol.fit with modelVersion := 55 } } } }
      binaryLoss [mixedBlock, block 20 true]) with
  | .known out => out.accepted
  | _ => false

-- Original 14.2 literal contrast: 100 different CASES/events, each externally
-- catalogued, are consumed by the actual fitter as 100 rows. This is not an iid claim.
/-- info: true -/
#guard_msgs in
#eval
  let observations := (List.range 100).map (fun i => row 0 false (100 + i))
  let initial := emptyStore 2 scope (observations.map (fun r => ⟨r, ⟨r.record.value⟩⟩))
  let final := runChanges ⟨10⟩ [] initial (observations.map Change.observed)
  match fitFromStore final protocol binaryLoss models with
  | .known out => decide (out.fitted.sampleSize = 100 ∧ final.cells.length = 100 ∧
      (final.cells.map Cell.caseId).toFinset.card = 100)
  | _ => false

-- 100 measurements of one actual case/event still give exactly one training row.
/-- info: true -/
#guard_msgs in
#eval
  let observations := (List.range 100).map (fun i =>
    { first with measurement := ⟨100 + i⟩, record := ⟨100 + i⟩, source := ⟨100 + i⟩ })
  let initial := emptyStore 2 scope (observations.map (fun r => ⟨r, ⟨r.record.value⟩⟩))
  let final := runChanges ⟨10⟩ [] initial (observations.map Change.observed)
  match fitFromStore final protocol binaryLoss models with
  | .known out => decide (out.fitted.sampleSize = 1 ∧ final.cells.length = 1 ∧ final.history.length = 100)
  | _ => false

end ProtectedFeedbackFixture
