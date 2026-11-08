import JurisLean.UnifiedFeedbackBridge

namespace LegalMath20261110.DelayAugmentation

open MeasureTheory ProbabilityTheory
open LegalMath20261108.ClosedLoop LegalMath20261108.SequentialFeedback
open LegalMath20261108.UnifiedFeedbackBridge

noncomputable section

/-- d+1 slots, oldest first; the head completes in the next transition. -/
abbrev Queue (d : Nat) := Fin (d+1) → Option Bool
abbrev DelayedHistory (d : Nat) := (List (Bool × Bool) × Queue d) × Option Bool

local instance : MeasurableSpace (Option Bool) := ⊤
local instance : MeasurableSpace (List (Bool × Bool)) := ⊤
local instance (d : Nat) : MeasurableSpace (Queue d) := ⊤

def shift (d : Nat) (q : Queue d) (incoming : Option Bool) : Queue d :=
  fun i => if hi : i.val < d then q ⟨i.val+1, by omega⟩ else incoming

def queueAt (d : Nat) (incoming : Nat → Option Bool) : Nat → Queue d
  | 0 => fun _ => none
  | t+1 => shift d (queueAt d incoming t) (incoming t)

theorem queueAt_entry (d : Nat) (incoming : Nat → Option Bool) (t : Nat) (i : Fin (d+1)) :
    queueAt d incoming t i =
      if d+1 ≤ t+i.val then incoming (t+i.val-(d+1)) else none := by
  induction t generalizing i with
  | zero =>
      have hi : ¬ d+1 ≤ 0+i.val := by omega
      rw [if_neg hi]
      rfl
  | succ t ih =>
      simp only [queueAt, shift]
      split
      · rename_i hi
        rw [ih]
        have eq : t+(i.val+1) = t+1+i.val := by omega
        simpa only [eq]
      · rename_i hi
        have eq : i.val = d := by omega
        have eligible : d+1 ≤ t+1+i.val := by omega
        rw [if_pos eligible]
        congr 1
        omega

theorem completes_after_delay (d : Nat) (incoming : Nat → Option Bool) (t : Nat) :
    queueAt d incoming (t+(d+1)) 0 = incoming t := by
  rw [queueAt_entry]
  have eligible : d+1 ≤ t+(d+1)+(0 : Fin (d+1)).val := by omega
  rw [if_pos eligible]
  congr 1
  simp

def learnDelayed (θ : ℝ) : Option Bool → ℝ
  | none => θ
  | some y => learnExample θ (RepaymentExample.bit y)

def delayedAppend (d : Nat) (h : DelayedHistory d) (a y : Bool) : DelayedHistory d :=
  ((h.1.1 ++ [(a,y)], shift d h.1.2 (some y)), h.1.2 0)

def currentX (x₀ : ℝ) (events : List (Bool × Bool)) : ℝ :=
  match events.getLast? with
  | none => x₀
  | some event => RepaymentExample.bit event.2

def numeric (d : Nat) (x₀ : ℝ) (s : DelayedHistory d × ℝ) : State :=
  (currentX x₀ s.1.1.1, s.2)

lemma measurable_numeric (d : Nat) (x₀ : ℝ) : Measurable (numeric d x₀) :=
  ((Measurable.of_discrete (f := fun h : DelayedHistory d => currentX x₀ h.1.1)).comp
    measurable_fst).prodMk measurable_snd

def delayedModel (d : Nat) (x₀ : ℝ) : Dynamics (DelayedHistory d) ℝ Bool Bool (Option Bool) where
  policy := Kernel.const (DelayedHistory d × ℝ) RepaymentExample.fair
  outcome := model.outcome.comap (fun z => (numeric d x₀ z.1, z.2))
    (((measurable_numeric d x₀).comp measurable_fst).prodMk measurable_snd)
  append := delayedAppend d
  measure := fun h _ _ => h.2
  learn := learnDelayed
  measurable_append := Measurable.of_discrete
  measurable_measure := Measurable.of_discrete
  measurable_learn := by
    apply measurable_from_prod_countable_left
    intro y
    cases y with
    | none => exact measurable_id
    | some y => dsimp [learnDelayed, learnExample]; fun_prop

instance (d : Nat) (x₀ : ℝ) : IsMarkovKernel (delayedModel d x₀).policy := by
  change IsMarkovKernel (Kernel.const (DelayedHistory d × ℝ) RepaymentExample.fair)
  infer_instance

instance (d : Nat) (x₀ : ℝ) : IsMarkovKernel (delayedModel d x₀).outcome := by
  dsimp [delayedModel]
  infer_instance

theorem delayed_markov (d : Nat) (x₀ : ℝ) : IsMarkovKernel (step (delayedModel d x₀)) :=
  inferInstance

theorem completion_update_eq (d : Nat) (x₀ θ : ℝ) (h : DelayedHistory d) (a y : Bool) :
    (update (delayedModel d x₀) ((h,θ),(a,y))).2 = learnDelayed θ (h.1.2 0) := rfl

theorem completion_at_time (d : Nat) (x₀ θ : ℝ) (events : List (Bool × Bool))
    (incoming : Nat → Option Bool) (t : Nat) (a y : Bool) :
    (update (delayedModel d x₀)
      ((((events, queueAt d incoming (t+(d+1))), none), θ), (a,y))).2 =
        learnDelayed θ (incoming t) := by
  rw [completion_update_eq, completes_after_delay]

/-- Dropping pending information loses the Markov update; this does not deny
that the original general Dynamics can already retain it in a full history. -/
theorem pending_is_needed_for_reduced_state (x₀ : ℝ) :
    (update (delayedModel 0 x₀)
      (((([], fun _ => some false), none), 0), (false,false))).2 ≠
    (update (delayedModel 0 x₀)
      (((([], fun _ => some true), none), 0), (false,false))).2 := by
  norm_num [completion_update_eq, learnDelayed, learnExample, RepaymentExample.bit]

#print axioms queueAt_entry
#print axioms completes_after_delay
#print axioms delayed_markov
#print axioms completion_update_eq
#print axioms completion_at_time
#print axioms pending_is_needed_for_reduced_state

end
end LegalMath20261110.DelayAugmentation
