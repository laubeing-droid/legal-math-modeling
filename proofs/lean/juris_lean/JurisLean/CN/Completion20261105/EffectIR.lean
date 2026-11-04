import JurisLean.CN.Completion20261105.State

/-!
V4 3.3: finite effect expressions for the adjust family. The public command
interpreters supply operands only after their actual source/permission checks.
There is no Situation constant or Situation -> Situation callback constructor.
Queries and native engines supply typed values; this evaluator writes only the
listed field. This is an internal interpretation, not a second public bypass.
-/
namespace JurisLean.CN.Completion20261105
open JurisLean.CN.Revision20261101

namespace EffectIR
inductive Write
  | cell (id : Ref .material) (value : EvidenceCell id)
  | model (theta : List Rat)
  | nextVersion
  | candidate (value : Candidate)
  | binding (value : Binding)
  | fact (value : Occurrence)
  | performance (value : Performance)
  | account (id : Ref .relation) (value : Native.Cash.State)

def write (s : Situation) : Write → Situation
  | .cell id value => s.withCore (s.core.setCell id value)
  | .model theta =>
    s.withCore (s.core.putState {s.core.state with A := {s.core.state.A with theta := theta}} rfl)
  | .nextVersion =>
    {s with core := {s.core with state := {s.core.state with
      A := {s.core.state.A with version := s.core.state.A.version + 1}}}}
  | .candidate value =>
    {s with core := {s.core with state := {s.core.state with
      candidates := value :: s.core.state.candidates}}}
  | .binding value =>
    s.withCore (s.core.putState {s.core.state with bindings := value :: s.core.state.bindings} rfl)
  | .fact value =>
    {s with core := {s.core with state := {s.core.state with F := s.core.state.F ++ [value]}}}
  | .performance value =>
    s.withCore (s.core.putState {s.core.state with ledger := s.core.state.ledger ++ [value]} rfl)
  | .account id value =>
    {s with accounts := fun key => if key = id then some value else s.accounts key}

def adjust : List Write → Situation → Situation
  | [],s => s
  | first :: rest,s => adjust rest (write s first)

def proposal (c : Candidate) : List Write := [.candidate c,.nextVersion]
def learning (theta : List Rat) (i : Ref .material) (raw : Raw i) : List Write :=
  [.cell i (.pending raw),.model theta]
def admission (i : Ref .material) (raw : Raw i) (r : Receipt raw) : List Write :=
  [.cell i (.accepted raw r)]
def payment (entry : Performance) (id : Ref .relation) (post : Native.Cash.State) : List Write :=
  [.performance entry,.account id post]

theorem adjust_append (a b : List Write) (s : Situation) :
    adjust (a ++ b) s = adjust b (adjust a s) := by
  induction a generalizing s with
  | nil => rfl
  | cons first rest ih => exact ih (write s first)

theorem proposal_lowering (s : Situation) (c : Candidate) :
    adjust (proposal c) s = {s with core := {s.core with state := propose s.core.state c}} := rfl

theorem learning_lowering (s : Situation) (theta : List Rat) (i : Ref .material) (raw : Raw i) :
    (adjust (learning theta i raw) s).core.state.A.theta = theta ∧
    (adjust (learning theta i raw) s).core.state.E i = .pending raw := by
  constructor
  · rfl
  · simp [adjust,learning,write,CaseState.setCell,setEvidence,Situation.withCore,CaseState.putState]

theorem admission_lowering (s : Situation) (i : Ref .material) (raw : Raw i) (r : Receipt raw) :
    (adjust (admission i raw r) s).core.state.E i = .accepted raw r := by
  simp [adjust,admission,write,CaseState.setCell,setEvidence,Situation.withCore]

theorem proposal_frame (s : Situation) (c : Candidate) :
    (adjust (proposal c) s).core.state.F = s.core.state.F ∧
    (adjust (proposal c) s).core.state.N = s.core.state.N ∧
    (adjust (proposal c) s).core.state.L = s.core.state.L ∧
    (adjust (proposal c) s).core.state.bindings = s.core.state.bindings := ⟨rfl,rfl,rfl,rfl⟩

theorem learning_frame (s : Situation) (theta : List Rat) (i : Ref .material) (raw : Raw i) :
    (adjust (learning theta i raw) s).core.state.F = s.core.state.F ∧
    (adjust (learning theta i raw) s).core.state.N = s.core.state.N ∧
    (adjust (learning theta i raw) s).core.state.L = s.core.state.L ∧
    (adjust (learning theta i raw) s).core.state.bindings = s.core.state.bindings := ⟨rfl,rfl,rfl,rfl⟩

#print axioms adjust_append
#print axioms proposal_lowering
#print axioms learning_lowering
#print axioms admission_lowering
#print axioms proposal_frame
#print axioms learning_frame
end EffectIR
end JurisLean.CN.Completion20261105
