import Mathlib

/-!
Bounded personal histories for finite-horizon perfect-recall games.
The terminal action is trivial; the complete personal record is retained.
-/

namespace LegalMath.FiniteHorizon

abbrev BoundedHistory (T : Nat) (α : Type) :=
  {xs : List α // xs.length ≤ T}

abbrev PersonalRecord (T : Nat) (Obs Action : Type) :=
  Obs × BoundedHistory T (Action × Obs)

variable {T : Nat} {α Obs Action : Type}

noncomputable instance boundedHistoryFintype [Finite α] :
    Fintype (BoundedHistory T α) :=
  (List.finite_length_le α T).fintype

instance boundedHistoryNonempty : Nonempty (BoundedHistory T α) :=
  ⟨⟨[], by simp⟩⟩

def stage (r : PersonalRecord T Obs Action) : Nat := r.2.val.length

theorem stage_le (r : PersonalRecord T Obs Action) : stage r ≤ T :=
  r.2.property

def initialRecord (T : Nat) (o : Obs) : PersonalRecord T Obs Action :=
  (o, ⟨[], by simp⟩)

@[simp] theorem initial_stage (o : Obs) :
    stage (initialRecord (Action := Action) T o) = 0 := rfl

def takeRecord (r : PersonalRecord T Obs Action) (n : Nat) :
    PersonalRecord T Obs Action :=
  (r.1, ⟨r.2.val.take n, by
    have hr := r.2.property
    simp only [List.length_take]
    omega⟩)

@[simp] theorem prefix_stage (r : PersonalRecord T Obs Action) (n : Nat) :
    stage (takeRecord r n) = min n (stage r) := by
  simp [takeRecord, stage]

@[simp] theorem prefix_self (r : PersonalRecord T Obs Action) :
    takeRecord r (stage r) = r := by
  apply Prod.ext
  · rfl
  · apply Subtype.ext
    simp [takeRecord, stage]

def append (r : PersonalRecord T Obs Action) (h : stage r < T)
    (a : Action) (o : Obs) : PersonalRecord T Obs Action :=
  (r.1, ⟨r.2.val ++ [(a, o)], by
    have hh : r.2.val.length < T := h
    simp only [List.length_append, List.length_singleton]
    omega⟩)

@[simp] theorem append_stage (r : PersonalRecord T Obs Action) (h : stage r < T)
    (a : Action) (o : Obs) :
    stage (append r h a o) = stage r + 1 := by
  simp [append, stage]

theorem prefix_append (r : PersonalRecord T Obs Action) (h : stage r < T)
    (a : Action) (o : Obs) (n : Nat) (hn : n ≤ stage r) :
    takeRecord (append r h a o) n = takeRecord r n := by
  apply Prod.ext
  · rfl
  · apply Subtype.ext
    exact List.take_append_of_le_length hn

@[simp] theorem prefix_append_self (r : PersonalRecord T Obs Action)
    (h : stage r < T) (a : Action) (o : Obs) :
    takeRecord (append r h a o) (stage r) = r := by
  rw [prefix_append r h a o _ (Nat.le_refl _), prefix_self]

theorem append_get_old (r : PersonalRecord T Obs Action) (h : stage r < T)
    (a : Action) (o : Obs) (n : Nat) (hn : n < stage r) :
    (append r h a o).2.val[n]'(by simpa [stage] using
      (show n < stage (append r h a o) by rw [append_stage]; omega)) =
      r.2.val[n]'hn := by
  exact List.getElem_append_left hn

@[simp] theorem append_get_last (r : PersonalRecord T Obs Action)
    (h : stage r < T) (a : Action) (o : Obs) :
    (append r h a o).2.val[stage r]'(by
      simpa [stage] using
        (show stage r < stage (append r h a o) by rw [append_stage]; omega)) =
      (a, o) := by
  simp [append, stage, List.getElem_append]

def ActionAt (r : PersonalRecord T Obs Action) : Type :=
  if stage r < T then Action else Unit

noncomputable instance actionAtFintype [Fintype Action]
    (r : PersonalRecord T Obs Action) : Fintype (ActionAt r) := by
  unfold ActionAt
  split_ifs <;> infer_instance

instance actionAtNonempty [Nonempty Action]
    (r : PersonalRecord T Obs Action) : Nonempty (ActionAt r) := by
  unfold ActionAt
  split_ifs <;> infer_instance

theorem terminal_action_subsingleton (r : PersonalRecord T Obs Action)
    (h : ¬ stage r < T) : Subsingleton (ActionAt r) := by
  simpa [ActionAt, h] using (inferInstance : Subsingleton Unit)

def ofAction (r : PersonalRecord T Obs Action) (h : stage r < T)
    (a : Action) : ActionAt r := by
  simpa only [ActionAt, if_pos h] using a

def toAction (r : PersonalRecord T Obs Action) (h : stage r < T)
    (a : ActionAt r) : Action := by
  simpa only [ActionAt, if_pos h] using a

@[simp] theorem toAction_ofAction (r : PersonalRecord T Obs Action)
    (h : stage r < T) (a : Action) :
    toAction r h (ofAction r h a) = a := by
  simp [toAction, ofAction]

@[simp] theorem ofAction_toAction (r : PersonalRecord T Obs Action)
    (h : stage r < T) (a : ActionAt r) :
    ofAction r h (toAction r h a) = a := by
  simp [toAction, ofAction]

theorem toAction_injective (r : PersonalRecord T Obs Action) (h : stage r < T) :
    Function.Injective (toAction r h) := by
  intro a b hab
  have := congrArg (ofAction r h) hab
  simpa using this

abbrev LocalPlan (T : Nat) (Obs Action : Type) :=
  (r : PersonalRecord T Obs Action) → ActionAt r

theorem toAction_plan_congr (π : LocalPlan T Obs Action)
    {r s : PersonalRecord T Obs Action} (hrs : r = s)
    (hr : stage r < T) (hs : stage s < T) :
    toAction r hr (π r) = toAction s hs (π s) := by
  subst s
  rfl

theorem toAction_eq_iff (r : PersonalRecord T Obs Action) (h : stage r < T)
    (x : ActionAt r) (a : Action) :
    toAction r h x = a ↔ x = ofAction r h a := by
  constructor
  · intro heq
    apply toAction_injective r h
    simpa using heq
  · intro heq
    rw [heq, toAction_ofAction]

def Req (r : PersonalRecord T Obs Action) (π : LocalPlan T Obs Action) : Prop :=
  ∀ (n : Nat) (hn : n < stage r),
    toAction (takeRecord r n)
      (by rw [prefix_stage]; have := stage_le r; omega)
      (π (takeRecord r n)) = (r.2.val[n]'hn).1

@[simp] theorem Req_initial (o : Obs) (π : LocalPlan T Obs Action) :
    Req (initialRecord T o) π := by
  intro n hn
  simp at hn

theorem Req_append (r : PersonalRecord T Obs Action) (h : stage r < T)
    (a : Action) (o : Obs) (π : LocalPlan T Obs Action) :
    Req (append r h a o) π ↔ Req r π ∧ π r = ofAction r h a := by
  have hr (n : Nat) : stage (takeRecord r n) < T := by
    rw [prefix_stage]
    omega
  have ha (n : Nat) (hn : n ≤ stage r) :
      stage (takeRecord (append r h a o) n) < T := by
    rw [prefix_stage, append_stage]
    omega
  constructor
  · intro hreq
    constructor
    · intro n hn
      have hh := hreq n (by rw [append_stage]; omega)
      calc
        _ = toAction (takeRecord (append r h a o) n) (ha n (Nat.le_of_lt hn))
            (π (takeRecord (append r h a o) n)) :=
          toAction_plan_congr π
            (prefix_append r h a o n (Nat.le_of_lt hn)).symm
            (hr n) (ha n (Nat.le_of_lt hn))
        _ = _ := hh
        _ = _ := congrArg Prod.fst (append_get_old r h a o n hn)
    · have hh := hreq (stage r) (by rw [append_stage]; omega)
      apply (toAction_eq_iff r h (π r) a).mp
      calc
        _ = toAction (takeRecord (append r h a o) (stage r)) (ha _ (Nat.le_refl _))
            (π (takeRecord (append r h a o) (stage r))) :=
          toAction_plan_congr π (prefix_append_self r h a o).symm h (ha _ (Nat.le_refl _))
        _ = _ := hh
        _ = a := congrArg Prod.fst (append_get_last r h a o)
  · rintro ⟨hreq, hlast⟩ n hn
    have hn' : n < stage r + 1 := by simpa using hn
    by_cases hlt : n < stage r
    · calc
        _ = toAction (takeRecord r n) (hr n) (π (takeRecord r n)) :=
          toAction_plan_congr π (prefix_append r h a o n (Nat.le_of_lt hlt))
            (ha n (Nat.le_of_lt hlt)) (hr n)
        _ = _ := hreq n hlt
        _ = _ := congrArg Prod.fst (append_get_old r h a o n hlt).symm
    · have heq : n = stage r := by omega
      subst n
      calc
        _ = toAction r h (π r) :=
          toAction_plan_congr π (prefix_append_self r h a o) (ha _ (Nat.le_refl _)) h
        _ = a := (toAction_eq_iff r h (π r) a).mpr hlast
        _ = _ := congrArg Prod.fst (append_get_last r h a o).symm

end LegalMath.FiniteHorizon
