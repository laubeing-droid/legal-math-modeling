import JurisLean.Candidates.Final20261021.Policy

namespace JurisLean.Candidates.Final20261021.RSI

structure Checkpoint where
  principal : PartyId
  task : Nat
  target : Nat
  feature : Nat
  ruleVersion : Nat
  mechanism : Nat
  scope : Nat
  version : Nat
  bytes : List UInt8
  prediction : ℚ
  evidence : SourceRef
  deriving DecidableEq, Repr

structure State where
  mechanism : Nat
  rules : Nat
  personal : PartyId → Option Checkpoint
  data : List Behavior.MeasurementLog
  logs : List Nat

def updatePersonal (s : State) (who : PartyId) (value : Checkpoint) : State :=
  { s with personal := fun j => if j = who then some value else s.personal j }

def appendData (s : State) (row : Behavior.MeasurementLog) : State :=
  { s with data := s.data ++ [row] }

def conditionalEstimate (weights outcomes : List ℚ) : Result ℚ :=
  if 0 < weights.sum then
    .known ((List.zipWith (· * ·) weights outcomes).sum / weights.sum)
  else .unknown .missingEvidence

def proposed_rule_service {X Y : Type} (eval : Nat → Nat → X → Y) (s : State) (x : X) :=
  eval s.mechanism s.rules x

theorem u13_1_noninterference {X Y : Type} (eval : Nat → Nat → X → Y)
    (s : State) (x : X) (who : PartyId) (value : Checkpoint) :
    proposed_rule_service eval (updatePersonal s who value) x = proposed_rule_service eval s x := rfl

theorem u13_2_personal_frame (s : State) (who : PartyId) (value : Checkpoint) :
    (updatePersonal s who value).rules = s.rules ∧
    (updatePersonal s who value).mechanism = s.mechanism ∧
    (updatePersonal s who value).data = s.data ∧
    ∀ j, j ≠ who → (updatePersonal s who value).personal j = s.personal j := by
  refine ⟨rfl, rfl, rfl, ?_⟩
  intro j hj
  simp [updatePersonal, hj]

-- Five write domains. Rule/mechanism changes require separate authorization
-- at the caller; these pure preparations do not authorize themselves.
inductive Update where
  | data (row : Behavior.MeasurementLog)
  | condition
  | personal (who : PartyId) (candidate : Checkpoint)
  | rule (version : Nat) (externalAuthority : SourceRef)
  | mechanism (version : Nat) (externalValidation externalAuthority : SourceRef)

def prepareUpdate (s : State) : Update → State
  | .data row => appendData s row
  | .condition => s
  | .personal who candidate => updatePersonal s who candidate
  | .rule v _ => { s with rules := v }
  | .mechanism v _ _ => { s with mechanism := v }

theorem u13_2_condition_does_not_train (s : State) : prepareUpdate s .condition = s := rfl
theorem u13_2_data_frame (s : State) (row : Behavior.MeasurementLog) :
    (prepareUpdate s (.data row)).rules = s.rules ∧
    (prepareUpdate s (.data row)).mechanism = s.mechanism ∧
    (prepareUpdate s (.data row)).personal = s.personal := ⟨rfl, rfl, rfl⟩

theorem u13_3_representation_transfer {X Z Z' Y : Type} (phi : X → Z)
    (b : Z ≃ Z') (g : Z → Y) (x : X) :
    (fun z' => g (b.symm z')) (b (phi x)) = g (phi x) := by simp

structure PredictionRequest where
  principal : PartyId
  task : Nat
  target : Nat
  feature : Nat
  ruleVersion : Nat
  mechanism : Nat
  scope : Nat
  deriving DecidableEq, Repr

def matches (r : PredictionRequest) (c : Checkpoint) : Bool :=
  decide (c.principal = r.principal ∧ c.task = r.task ∧ c.target = r.target ∧
    c.feature = r.feature ∧ c.ruleVersion = r.ruleVersion ∧ c.mechanism = r.mechanism ∧
    c.scope = r.scope ∧ 0 ≤ c.prediction ∧ c.prediction ≤ 1)

def proposed_checkpoint_service (request : PredictionRequest)
    (personal population prior retrieved : Option Checkpoint) : Result Checkpoint :=
  match [personal, population, prior, retrieved].filterMap id |>.find? (matches request) with
  | some checkpoint => .known checkpoint
  | none => .unknown .missingEvidence

theorem u13_4_missing_checkpoint_no_default (r : PredictionRequest) :
    proposed_checkpoint_service r none none none none = .unknown .missingEvidence := rfl

end JurisLean.Candidates.Final20261021.RSI
