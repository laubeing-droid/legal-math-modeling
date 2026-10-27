import JurisLean.Candidates.ValidatedFeedbackLoad20261027

#check JurisLean.Candidates.ValidatedFeedbackLoad20261027.activation_keeps_rules_mechanism_and_training
#print axioms JurisLean.Candidates.ValidatedFeedbackLoad20261027.activation_keeps_rules_mechanism_and_training
#check JurisLean.Candidates.ValidatedFeedbackLoad20261027.every_activation_attempt_retains_history
#print axioms JurisLean.Candidates.ValidatedFeedbackLoad20261027.every_activation_attempt_retains_history
#check JurisLean.Candidates.ValidatedFeedbackLoad20261027.refusal_keeps_actual_prediction
#print axioms JurisLean.Candidates.ValidatedFeedbackLoad20261027.refusal_keeps_actual_prediction
#check JurisLean.Candidates.ValidatedFeedbackLoad20261027.loaded_package_is_actual_written_readback
#print axioms JurisLean.Candidates.ValidatedFeedbackLoad20261027.loaded_package_is_actual_written_readback
#check JurisLean.Candidates.ValidatedFeedbackLoad20261027.replaced_candidate_does_not_reuse_old_permit
#print axioms JurisLean.Candidates.ValidatedFeedbackLoad20261027.replaced_candidate_does_not_reuse_old_permit
#check JurisLean.Candidates.ValidatedFeedbackLoad20261027.actual_loaded_risk_follows_computed_domain_bounds
#print axioms JurisLean.Candidates.ValidatedFeedbackLoad20261027.actual_loaded_risk_follows_computed_domain_bounds
#check JurisLean.Candidates.ValidatedFeedbackLoad20261027.changed_validation_snapshot_does_not_reuse_sampling_receipt
#print axioms JurisLean.Candidates.ValidatedFeedbackLoad20261027.changed_validation_snapshot_does_not_reuse_sampling_receipt
#check JurisLean.Candidates.ValidatedFeedbackLoad20261027.next_candidate_consumes_current_loaded_and_actual_post
#print axioms JurisLean.Candidates.ValidatedFeedbackLoad20261027.next_candidate_consumes_current_loaded_and_actual_post
#check JurisLean.Candidates.ValidatedFeedbackLoad20261027.newly_loaded_model_is_next_actual_parent
#print axioms JurisLean.Candidates.ValidatedFeedbackLoad20261027.newly_loaded_model_is_next_actual_parent

open JurisLean.Candidates.Final20261021
open JurisLean.Candidates.LearningConsumer20261027
open JurisLean.Candidates.SampleCalibrationConsumer20261027
open JurisLean.Candidates.EventFeedbackConsumer20261027
open JurisLean.Candidates.ProtectedFeedback20261027
open JurisLean.Candidates.ValidatedFeedbackLoad20261027

namespace ValidatedFeedbackLoadFixture

def protocol : LearningProtocol :=
  ⟨⟨1, 2, 3, 4, 5, ⟨10⟩, ⟨1⟩⟩, 6, 7, 8, 9, 10, 11, 12, 1/10⟩
def scope : DataScope := ⟨1, 2, 3, 6, 8, 9, 10, 12, 1, 1, 1, .behavior⟩
def row (feature : Fin 2) (label : Bool) (id : Nat) : Observation 2 :=
  ⟨scope, ⟨id⟩, ⟨id⟩, ⟨id⟩, ⟨id⟩, feature, label, ⟨id⟩, .external, ⟨0⟩⟩
def first : Observation 2 := row 0 false 1
def second : Observation 2 := row 1 true 2
def third : Observation 2 := row 0 true 3
def initial : Store 2 := emptyStore 2 scope
  [⟨first, ⟨1⟩⟩, ⟨second, ⟨2⟩⟩, ⟨third, ⟨3⟩⟩]
def oldState : Store 2 := (observe initial ⟨10⟩ first).post
def gamma : Gamma :=
  ⟨⟨1⟩, 0, 1, "synthetic", 1, 1, 1, ⟨10⟩, ⟨100⟩, ⟨100⟩, 1, 1, 1⟩
def plan : ValidationPlan := ⟨scope, 31, [10, 20], [[0, 0], [0, 1]], 1/10⟩
def block (domain : Nat) (label : Bool) : DomainBlock 2 :=
  sampledBlock plan domain (100 + domain) (1/20) (1/10) 8 0
    (fun i : Fin 400 => ⟨10000 * domain + i.val⟩)
    (fun _ : Fin 400 => ((1 : Fin 2), label))

def mixedBlock : DomainBlock 2 :=
  sampledBlock plan 10 110 (1/20) (1/10) 8 0
    (fun i : Fin 400 => ⟨100000 + i.val⟩)
    (fun i : Fin 400 => (if i.val % 2 = 0 then (0, false) else (1, true)))

def twoPointRisk (s : Service 2) : ℚ :=
  (binaryLoss (predictLoaded s 0) false + binaryLoss (predictLoaded s 1) true) / 2

def built : Result (Service 2 × Evaluation 2) :=
  match fitFromStore oldState protocol binaryLoss [[0, 0], [0, 1]] with
  | .known parent =>
      let s : Service 2 := ⟨gamma, ⟨7⟩, 7, parent, oldState, []⟩
      let prepared := prepareNext s ⟨10⟩ [] (.observed second)
        { protocol with fit := { protocol.fit with modelVersion := 5 } } [[0, 1]]
      match prepared.candidate with
      | .known candidate =>
          match evaluate { plan with models := prepared.models } prepared.parent candidate binaryLoss
              [mixedBlock, block 20 true] with
          | .known evaluation => .known (prepared.post, evaluation)
          | .unknown e => .unknown e
          | .rejected e => .rejected e
          | .conflict a b => .conflict a b
      | .unknown e => .unknown e
      | .rejected e => .rejected e
      | .conflict a b => .conflict a b
  | .unknown e => .unknown e
  | .rejected e => .rejected e
  | .conflict a b => .conflict a b

def sampling (e : Evaluation 2) : SamplingReceipt 2 :=
  ⟨e.plan, e.parent, e.blocks, ⟨11⟩, ⟨20⟩, ⟨40⟩⟩
def permit (s : Service 2) (e : Evaluation 2) : LoadPermit 2 :=
  ⟨e, ⟨⟨50⟩, s.principal, s.gamma.caseId, s.gamma, .party s.principal, 2,
    e.candidate.fitted.protocol.fit.modelVersion, none, none, s.gamma.normVersion, ⟨0⟩, ⟨20⟩⟩⟩
def check (f : Service 2 → Evaluation 2 → Bool) : Bool :=
  match built with
  | .known (s, e) => f s e
  | _ => false

-- Full executable chain: external observation -> actual post -> fitted
-- candidate -> sampled domain losses -> permission -> write -> actual read.
/-- info: true -/
#guard_msgs in
#eval check (fun s e =>
  let r := sampling e
  let p := permit s e
  let out := activate s e [r] r [p] p
  decide (out.status = .loaded ∧ predictLoaded s 1 = 0 ∧ predictLoaded out.post 1 = 1 ∧
    out.readback = some (readLoaded out.post) ∧ readLoaded out.post = e.candidate ∧
    out.post.history.length = 1 ∧ out.post.gamma = s.gamma ∧
    e.statistics.map DomainStatistics.oldEmpirical = [1/2, 1] ∧
    e.statistics.map DomainStatistics.newEmpirical = [0, 0] ∧
    twoPointRisk s = 1/2 ∧ twoPointRisk out.post = 0))

/-- info: true -/
#guard_msgs in
#eval check (fun s e =>
  let r := sampling e
  let p := permit s e
  let out := activate s e [r] r [] p
  decide (out.status = .authorityUnresolved ∧ readLoaded out.post = readLoaded s ∧
    predictLoaded out.post 1 = 0 ∧ out.readback = none ∧ out.post.history.length = 1))

/-- info: true -/
#guard_msgs in
#eval check (fun s e =>
  let r := sampling e
  let p := permit s e
  decide ((activate s e [] r [p] p).status = .samplingUnresolved))

-- A self-named protocol or a plan declared after the data is not qualified.
/-- info: true -/
#guard_msgs in
#eval check (fun s e =>
  let r := { sampling e with declaredAt := ⟨21⟩ }
  let p := permit s e
  decide ((activate s e [r] r [p] p).status = .samplingUnresolved))

-- Replacing the model after evaluation cannot keep the original statistics.
/-- info: true -/
#guard_msgs in
#eval check (fun s e =>
  let swapped := { e with candidate := { e.candidate with fitted := { e.candidate.fitted with table := [1, 1] } } }
  let r := sampling e
  let p := permit s e
  let out := activate s swapped [r] r [p] p
  decide (out.status = .invalidEvaluation ∧ readLoaded out.post = readLoaded s))

-- Even a catalogued grant for another exact package does not authorize this one.
/-- info: true -/
#guard_msgs in
#eval check (fun s e =>
  let r := sampling e
  let p := { permit s e with evaluation := { e with candidate := e.parent } }
  decide ((activate s e [r] r [p] p).status = .authorityUnresolved))

/-- info: true -/
#guard_msgs in
#eval check (fun s e =>
  let r := sampling e
  let p := permit s e
  let changedBlocks := e.blocks.map (fun b => { b with snapshot := b.snapshot + 1 })
  match evaluate e.plan e.parent e.candidate binaryLoss changedBlocks with
  | .known changed => decide ((activate s changed [r] r [p] p).status = .samplingUnresolved)
  | _ => false)

/-- info: true -/
#guard_msgs in
#eval check (fun s e =>
  let changed := { e with plan := { e.plan with scope := { e.plan.scope with target := 99 } } }
  let r := sampling e
  let p := permit s e
  decide ((activate s changed [r] r [p] p).status = .invalidEvaluation))

/-- info: true -/
#guard_msgs in
#eval check (fun s e =>
  let r := sampling e
  let p := permit s e
  let changed := { s with gamma := { s.gamma with normVersion := 2 } }
  let out := activate changed e [r] r [p] p
  decide (out.status = .contextMismatch ∧ out.post.gamma.normVersion = 2 ∧
    readLoaded out.post = readLoaded s))

/-- info: true -/
#guard_msgs in
#eval check (fun s e =>
  let r := sampling e
  let p := { permit s e with grant := { (permit s e).grant with untilDate := ⟨10⟩ } }
  decide ((activate s e [r] r [p] p).status = .authorityUnresolved))

-- Later observations can preserve the same active training values yet change
-- the full actual snapshot. An old evaluation cannot silently consume that state.
/-- info: true -/
#guard_msgs in
#eval check (fun s e =>
  let changed := { s with journal := (observe s.journal ⟨10⟩ first).post }
  let r := sampling e
  let p := permit s e
  let out := activate changed e [r] r [p] p
  decide (out.status = .snapshotMismatch ∧ readLoaded out.post = readLoaded s))

/-- info: true -/
#guard_msgs in
#eval check (fun s e =>
  match evaluate e.plan e.parent e.candidate binaryLoss [block 10 true, block 20 false] with
  | .known failing =>
      let r := sampling failing
      let p := permit s failing
      let out := activate s failing [r] r [p] p
      decide (out.status = .protectedScopeFailed ∧ readLoaded out.post = readLoaded s)
  | _ => false)

/-- info: true -/
#guard_msgs in
#eval check (fun s e =>
  let r := sampling e
  let p := permit s e
  let out := activate s e [r] r [p] p
  let replay := activate out.post e [r] r [p] p
  decide (replay.status = .parentMismatch ∧ readLoaded replay.post = e.candidate ∧
    replay.post.history.length = 2))

-- The following fit actually searches the newly loaded weights. No candidate
-- or model checkpoint is supplied through a parallel input.
/-- info: true -/
#guard_msgs in
#eval check (fun s e =>
  let r := sampling e
  let p := permit s e
  let out := activate s e [r] r [p] p
  let next := prepareNext out.post ⟨30⟩ [] (.observed third)
    { protocol with fit := { protocol.fit with modelVersion := 6 } } []
  match next.candidate with
  | .known candidate => decide (next.parent = e.candidate ∧ next.models = [[0, 1]] ∧
      candidate.fitted.table = [0, 1] ∧ candidate.fitted.sampleSize = 3 ∧
      candidate.snapshot = next.post.journal ∧ readLoaded next.post = e.candidate)
  | _ => false)

/-- info: true -/
#guard_msgs in
#eval check (fun s e =>
  let r := sampling e
  let p := permit s e
  let out := activate s e [r] r [p] p
  let next := prepareNext out.post ⟨30⟩ [] (.observed third)
    { protocol with fit := { protocol.fit with target := 999 } } []
  decide (next.candidate = Result.unknown Error.targetMismatch ∧
    readLoaded next.post = e.candidate ∧ predictLoaded next.post 1 = 1))

end ValidatedFeedbackLoadFixture
