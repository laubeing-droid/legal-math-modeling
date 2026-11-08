import Mathlib
import JurisLean.FiniteHorizonRecords
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


/-- Convert the original vector record to the full list record used by the
finite-horizon game. Every action and its following observation is retained. -/
def toFiniteRecord (v : PersonalRecord T Obs Action) :
    LegalMath.FiniteHorizon.PersonalRecord T Obs Action :=
  (v.2.1 0, ⟨List.ofFn (fun i : Fin v.1.val => (v.2.2 i, v.2.1 i.succ)), by
    simpa using stage_le v⟩)

@[simp] theorem toFiniteRecord_stage (v : PersonalRecord T Obs Action) :
    LegalMath.FiniteHorizon.stage (toFiniteRecord v) = stage v := by
  simp [LegalMath.FiniteHorizon.stage, toFiniteRecord, stage]

@[simp] theorem toFiniteRecord_initial (o : Obs) :
    toFiniteRecord (initialRecord (Action := Action) T o) =
      LegalMath.FiniteHorizon.initialRecord T o := by
  simp [toFiniteRecord, initialRecord, LegalMath.FiniteHorizon.initialRecord]

theorem toFiniteRecord_event (v : PersonalRecord T Obs Action) (i : Fin (stage v)) :
    (toFiniteRecord v).2.val[i.val]'(by
      simpa [toFiniteRecord, stage] using i.isLt) = (v.2.2 i, v.2.1 i.succ) := by
  simp [toFiniteRecord, stage]

/-- No original observation, action, or stage is lost in the conversion. -/
theorem toFiniteRecord_injective : Function.Injective
    (toFiniteRecord : PersonalRecord T Obs Action → _) := by
  intro v w h
  rcases v with ⟨t, os, actions⟩
  rcases w with ⟨u, ps, other⟩
  have htu : t = u := Fin.ext (by
    simpa [toFiniteRecord, LegalMath.FiniteHorizon.stage, stage] using
      congrArg LegalMath.FiniteHorizon.stage h)
  cases htu
  have hzero : os 0 = ps 0 := congrArg Prod.fst h
  have hpairs : (fun i : Fin t.val => (actions i, os i.succ)) =
      (fun i : Fin t.val => (other i, ps i.succ)) :=
    List.ofFn_injective (congrArg (fun r => r.2.val) h)
  have ha : actions = other := funext (fun i => congrArg Prod.fst (congrFun hpairs i))
  have ho : os = ps := funext (fun i =>
    Fin.cases hzero (fun j => congrArg Prod.snd (congrFun hpairs j)) i)
  cases ha
  cases ho
  rfl

/-- Recover the vector representation from the actual complete list record. -/
def fromFiniteRecord (r : LegalMath.FiniteHorizon.PersonalRecord T Obs Action) :
    PersonalRecord T Obs Action :=
  ⟨⟨r.2.val.length, Nat.lt_succ_of_le r.2.property⟩,
    (Fin.cases r.1 (fun i => (r.2.val.get i).2), fun i => (r.2.val.get i).1)⟩

@[simp] theorem to_fromFiniteRecord
    (r : LegalMath.FiniteHorizon.PersonalRecord T Obs Action) :
    toFiniteRecord (fromFiniteRecord r) = r := by
  apply Prod.ext
  · rfl
  · apply Subtype.ext
    change List.ofFn (fun i : Fin r.2.val.length =>
      ((r.2.val.get i).1, (r.2.val.get i).2)) = r.2.val
    exact List.ofFn_get r.2.val

@[simp] theorem from_toFiniteRecord (v : PersonalRecord T Obs Action) :
    fromFiniteRecord (toFiniteRecord v) = v :=
  toFiniteRecord_injective (to_fromFiniteRecord (toFiniteRecord v))

/-- The two records are equivalent with all stage and event coordinates preserved. -/
def recordEquiv : PersonalRecord T Obs Action ≃
    LegalMath.FiniteHorizon.PersonalRecord T Obs Action where
  toFun := toFiniteRecord
  invFun := fromFiniteRecord
  left_inv := from_toFiniteRecord
  right_inv := to_fromFiniteRecord

/-- At the horizon both representations offer Unit; before it both offer Action. -/
theorem action_type_preserved (v : PersonalRecord T Obs Action) :
    ActionAt v = LegalMath.FiniteHorizon.ActionAt (toFiniteRecord v) := by
  unfold ActionAt LegalMath.FiniteHorizon.ActionAt
  rw [toFiniteRecord_stage]
  have hv := stage_le v
  split_ifs <;> first | rfl | omega

end LegalMath20261108.BoundedRecall
