import JurisLean.CN.Completion20261105.Program

/-!
V4 P4 / CNRun finite five-event obligation, now over the actual common graph.
This is a syntactic subgraph embedding, not a second transition semantics.
It excludes Decide/Bind/Occur/constitutive effects; no claim is made that all
mixed legal histories lack judgments or bindings.
-/
namespace JurisLean.CN.Completion20261105
open JurisLean.CN.Revision20261101

def Frame5 (a b : Situation) : Prop :=
  b.core.state.F = a.core.state.F ∧ b.core.state.N = a.core.state.N ∧
  b.core.state.L = a.core.state.L ∧ b.core.state.bindings = a.core.state.bindings ∧
  b.core.state.decisions = a.core.state.decisions

theorem Frame5.trans {a b c : Situation} (h : Frame5 a b) (k : Frame5 b c) : Frame5 a c :=
  ⟨k.1.trans h.1,k.2.1.trans h.2.1,k.2.2.1.trans h.2.2.1,
    k.2.2.2.1.trans h.2.2.2.1,k.2.2.2.2.trans h.2.2.2.2⟩

inductive FiveCommand
  | record (id : Ref .material) (raw : Raw id)
  | learn (r : Request) (theta : List Rat) (id : Ref .material) (raw : Raw id)
  | admitEvidence (r : Request) (m : Mode) (id : Ref .material) (raw : Raw id) (rc : Receipt raw)
  | withdraw (r : Request) (id : Ref .material) (why : Ref .document)
  | propose (out : EngineOutput)

def FiveCommand.Output : FiveCommand → Type
  | .record _ _ | .admitEvidence _ _ _ _ _ | .withdraw _ _ _ => Ref .material
  | .learn _ _ _ _ => Unit
  | .propose _ => Candidate
def FiveCommand.toCommand : (c : FiveCommand) → Command c.Output
  | .record i raw => .record i raw
  | .learn r theta i raw => .learn r theta i raw
  | .admitEvidence r m i raw rc => .admitEvidence r m i raw rc
  | .withdraw r i why => .withdraw r i why
  | .propose out => .institution (.propose out)

theorem five_actual_frame (s : Situation) (c : FiveCommand) :
    Frame5 s (executeCommand s c.toCommand).after := by
  cases c with
  | record i raw =>
    change Frame5 s (recordMaterial s i raw).after
    unfold recordMaterial
    split
    · exact ⟨rfl,rfl,rfl,rfl,rfl⟩
    · split <;> exact ⟨rfl,rfl,rfl,rfl,rfl⟩
  | learn r theta i raw =>
    change Frame5 s (learnMaterial s r theta i raw).after
    unfold learnMaterial
    split
    · exact ⟨rfl,rfl,rfl,rfl,rfl⟩
    · split <;> exact ⟨rfl,rfl,rfl,rfl,rfl⟩
  | admitEvidence r m i raw rc =>
    change Frame5 s (admission s r m i raw rc).after
    unfold admission
    split
    · exact ⟨rfl,rfl,rfl,rfl,rfl⟩
    · split
      · exact ⟨rfl,rfl,rfl,rfl,rfl⟩
      · split
        · split <;> exact ⟨rfl,rfl,rfl,rfl,rfl⟩
        · exact ⟨rfl,rfl,rfl,rfl,rfl⟩
  | withdraw r i why =>
    change Frame5 s (withdrawal s r i why).after
    unfold withdrawal
    split
    · exact ⟨rfl,rfl,rfl,rfl,rfl⟩
    · split
      · exact ⟨rfl,rfl,rfl,rfl,rfl⟩
      · split <;> exact ⟨rfl,rfl,rfl,rfl,rfl⟩
  | propose out => exact ⟨rfl,rfl,rfl,rfl,rfl⟩

inductive FiveHistory : Situation → Situation → Type 1
  | nil (s : Situation) : FiveHistory s s
  | snoc {a b : Situation} (h : FiveHistory a b) (c : FiveCommand) :
      FiveHistory a (executeCommand b c.toCommand).after

def FiveHistory.toHistory {a b : Situation} (h : FiveHistory a b) : History a b := by
  induction h with
  | nil => exact History.nil _
  | snoc h c ih => exact History.snoc ih c.toCommand

theorem FiveHistory.frame {a b : Situation} (h : FiveHistory a b) : Frame5 a b := by
  induction h with
  | nil => exact ⟨rfl,rfl,rfl,rfl,rfl⟩
  | snoc h c ih => exact ih.trans (five_actual_frame _ c)

theorem FiveHistory.no_new_decision_binding {a b : Situation} (h : FiveHistory a b)
    (none : ∀ d : DecideBinding, Binding.decide d ∉ a.core.state.bindings) :
    ∀ d : DecideBinding, Binding.decide d ∉ b.core.state.bindings := by
  intro d
  rw [h.frame.2.2.2.1]
  exact none d

#print axioms five_actual_frame
#print axioms FiveHistory.frame
#print axioms FiveHistory.no_new_decision_binding
end JurisLean.CN.Completion20261105
