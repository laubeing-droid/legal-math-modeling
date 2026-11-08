import Mathlib
import JurisLean.External.GameTheory.Theorems.Kuhn.KuhnModel

/-!
Finite personal records for a fixed-horizon perfect-recall episode.

This file proves only the finite/nonempty carrier, its horizon bound, the
global current/start/push equations of the existing identity core, and the
terminal action type. It does not instantiate the stochastic machine,
LocalSupportSignatureFull, or either complete Kuhn theorem.

Static source review only. Lean/Lake/Elan and CI have not been run.
-/

namespace LegalMath20261108.BoundedRecall

/-- At stage t, retain t+1 observations and the player's t past actions.
The whole record, not merely the last raw observation, is the core observation. -/
abbrev PersonalRecord (T : Nat) (Obs Action : Type) :=
  Σ t : Fin (T + 1), (Fin (t.val + 1) → Obs) × (Fin t.val → Action)

variable {T : Nat} {Obs Action : Type}

def stage (v : PersonalRecord T Obs Action) : Nat := v.1.val

theorem stage_le (v : PersonalRecord T Obs Action) : stage v ≤ T :=
  Nat.le_of_lt_succ v.1.isLt

def initialRecord (T : Nat) (o : Obs) : PersonalRecord T Obs Action :=
  ⟨⟨0, Nat.zero_lt_succ T⟩, (fun _ => o), (fun j => Fin.elim0 j)⟩

@[simp] theorem initial_stage (o : Obs) :
    stage (initialRecord (Action := Action) T o) = 0 := rfl

noncomputable instance [Fintype Obs] [Fintype Action] :
    Fintype (PersonalRecord T Obs Action) := by
  classical
  unfold PersonalRecord
  infer_instance

instance [Nonempty Obs] : Nonempty (PersonalRecord T Obs Action) := by
  obtain ⟨o⟩ := (inferInstance : Nonempty Obs)
  exact ⟨initialRecord T o⟩

/-- Use the existing semantic core, without any unbounded snapshot field. -/
def recordCore (T : Nat) (Obs Action : Type) :
    InfoStateCore (PersonalRecord T Obs Action) :=
  InfoStateCore.identity _

theorem core_carrier_finite [Fintype Obs] [Fintype Action] :
    Finite (recordCore T Obs Action).Carrier := by
  change Finite (PersonalRecord T Obs Action)
  infer_instance

theorem core_carrier_nonempty [Nonempty Obs] :
    Nonempty (recordCore T Obs Action).Carrier := by
  change Nonempty (PersonalRecord T Obs Action)
  infer_instance

/-- Both equations hold for all records, including unreachable combinations. -/
@[simp] theorem current_start (v : PersonalRecord T Obs Action) :
    (recordCore T Obs Action).current
      ((recordCore T Obs Action).start v) = v := rfl

@[simp] theorem current_push (h v : PersonalRecord T Obs Action) :
    (recordCore T Obs Action).current
      ((recordCore T Obs Action).push h v) = v := rfl

/-- Only the action becomes trivial at the horizon; the record is retained. -/
def ActionAt (v : PersonalRecord T Obs Action) : Type :=
  if stage v = T then Unit else Action

noncomputable instance [Fintype Action] (v : PersonalRecord T Obs Action) :
    Fintype (ActionAt v) := by
  unfold ActionAt
  split_ifs <;> infer_instance

instance [Nonempty Action] (v : PersonalRecord T Obs Action) :
    Nonempty (ActionAt v) := by
  unfold ActionAt
  split_ifs <;> infer_instance

theorem terminal_action_subsingleton (v : PersonalRecord T Obs Action)
    (ht : stage v = T) : Subsingleton (ActionAt v) := by
  simpa [ActionAt, ht] using (inferInstance : Subsingleton Unit)

end LegalMath20261108.BoundedRecall
