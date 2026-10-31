import Mathlib
import JurisLean.External.GameTheory.Math.Probability

noncomputable section

open scoped BigOperators

namespace JurisLean.Candidates.U06_4ConditionalInformation20261031

open Math.Probability

variable {Ω A Y : Type} [Fintype Ω] [Fintype Y] [DecidableEq Y]

def fiberWeight (P : PMF Ω) (obs : Ω → Y) (y : Y) (w : Ω) : ℝ :=
  if obs w = y then (P w).toReal else 0

def signalMass (P : PMF Ω) (obs : Ω → Y) (y : Y) : ℝ :=
  ∑ w, fiberWeight P obs y w

private theorem fiberWeight_nonneg (P : PMF Ω) (obs : Ω → Y) (y : Y) (w : Ω) :
    0 ≤ fiberWeight P obs y w := by
  unfold fiberWeight
  split_ifs
  · exact ENNReal.toReal_nonneg
  · exact le_rfl

private theorem signalMass_nonneg (P : PMF Ω) (obs : Ω → Y) (y : Y) :
    0 ≤ signalMass P obs y :=
  Finset.sum_nonneg (fun w _ => fiberWeight_nonneg P obs y w)

def signalLaw (P : PMF Ω) (obs : Ω → Y) : PMF Y := PMF.map obs P

private theorem signal_law_mass (P : PMF Ω) (obs : Ω → Y) (y : Y) :
    (signalLaw P obs y).toReal = signalMass P obs y := by
  rw [signalLaw, PMF.map_apply, tsum_fintype]
  rw [ENNReal.toReal_sum (s := Finset.univ)
    (f := fun w => if y = obs w then P w else 0) (by
      intro w _
      by_cases same : y = obs w <;> simp [same, PMF.apply_ne_top])]
  unfold signalMass
  apply Finset.sum_congr rfl
  intro w _
  by_cases same : obs w = y <;> simp [fiberWeight, same, eq_comm]

private theorem signal_expect_eq_sum (P : PMF Ω) (obs : Ω → Y) (f : Y → ℝ) :
    expect (signalLaw P obs) f = ∑ y, signalMass P obs y * f y := by
  rw [expect_eq_sum]
  apply Finset.sum_congr rfl
  intro y _
  rw [signal_law_mass]

def conditionalLaw (P : PMF Ω) (obs : Ω → Y) (y : Y) : Option (PMF Ω) := by
  classical
  exact if h : ∃ w, obs w = y ∧ w ∈ P.support then
    some (P.filter {w | obs w = y} h)
  else none

/-- This totalization concerns only zero-mass signal fibers, never unknown data
or unresolved labels. Positive fibers use the actual normalized PMF.filter. -/
def conditionalScore (P : PMF Ω) (obs : Ω → Y)
    (utility : A → Ω → ℝ) (a : A) (y : Y) : ℝ :=
  match conditionalLaw P obs y with
  | some Q => expect Q (utility a)
  | none => 0

private theorem positive_signal_reachable (P : PMF Ω) (obs : Ω → Y) (y : Y)
    (positive : 0 < signalMass P obs y) :
    ∃ w, obs w = y ∧ w ∈ P.support := by
  classical
  by_contra absent
  have allZero : ∀ w, fiberWeight P obs y w = 0 := by
    intro w
    by_cases same : obs w = y
    · have zero : P w = 0 := by
        by_contra nonzero
        exact absent ⟨w, same, (PMF.mem_support_iff P w).mpr nonzero⟩
      simp [fiberWeight, same, zero]
    · simp [fiberWeight, same]
  have zero : signalMass P obs y = 0 := by
    simp [signalMass, allZero]
  linarith

private theorem fiber_sum_toReal (P : PMF Ω) (obs : Ω → Y) (y : Y) :
    (∑ w, ({z | obs z = y}.indicator (fun z => P z)) w).toReal =
      signalMass P obs y := by
  classical
  rw [ENNReal.toReal_sum (s := Finset.univ)
    (f := fun w => ({z | obs z = y}.indicator (fun z => P z)) w) (by
      intro w _
      by_cases same : obs w = y <;>
        simp [Set.indicator, same, PMF.apply_ne_top])]
  unfold signalMass
  apply Finset.sum_congr rfl
  intro w _
  by_cases same : obs w = y <;> simp [Set.indicator, fiberWeight, same]

private theorem conditional_score_fraction (P : PMF Ω) (obs : Ω → Y)
    (utility : A → Ω → ℝ) (a : A) (y : Y)
    (positive : 0 < signalMass P obs y) :
    conditionalScore P obs utility a y =
      (∑ w, fiberWeight P obs y w * utility a w) / signalMass P obs y := by
  classical
  have reachable := positive_signal_reachable P obs y positive
  have point : ∀ w,
      ((P.filter {z | obs z = y} reachable) w).toReal =
        fiberWeight P obs y w / signalMass P obs y := by
    intro w
    rw [PMF.filter_apply reachable w, ENNReal.toReal_mul,
      ENNReal.toReal_inv, tsum_fintype, fiber_sum_toReal]
    by_cases same : obs w = y <;>
      simp [Set.indicator, fiberWeight, same, div_eq_mul_inv]
  calc
    conditionalScore P obs utility a y =
        expect (P.filter {w | obs w = y} reachable) (utility a) := by
      simp [conditionalScore, conditionalLaw, reachable]
    _ = ∑ w, (fiberWeight P obs y w * utility a w) / signalMass P obs y := by
      rw [expect_eq_sum]
      apply Finset.sum_congr rfl
      intro w _
      rw [point]
      ring
    _ = (∑ w, fiberWeight P obs y w * utility a w) / signalMass P obs y := by
      simp only [Finset.sum_div]

private theorem weighted_conditional_score (P : PMF Ω) (obs : Ω → Y)
    (utility : A → Ω → ℝ) (a : A) (y : Y) :
    signalMass P obs y * conditionalScore P obs utility a y =
      ∑ w, fiberWeight P obs y w * utility a w := by
  by_cases zero : signalMass P obs y = 0
  · have weightsZero : ∀ w, fiberWeight P obs y w = 0 := by
      have allZero := (Finset.sum_eq_zero_iff_of_nonneg
        (fun w (_ : w ∈ (Finset.univ : Finset Ω)) => fiberWeight_nonneg P obs y w)).mp zero
      intro w
      exact allZero w (Finset.mem_univ w)
    simp [zero, weightsZero]
  · have positive : 0 < signalMass P obs y := by
      rcases lt_or_eq_of_le (signalMass_nonneg P obs y) with h | h
      · exact h
      · exact False.elim (zero h.symm)
    rw [conditional_score_fraction P obs utility a y positive]
    field_simp [zero] <;> ring

def policyScore (P : PMF Ω) (obs : Ω → Y) (utility : A → Ω → ℝ)
    (policy : Y → A) : ℝ :=
  expect P (fun w => utility (policy (obs w)) w)

private theorem policy_score_tower (P : PMF Ω) (obs : Ω → Y)
    (utility : A → Ω → ℝ) (policy : Y → A) :
    policyScore P obs utility policy =
      ∑ y, signalMass P obs y * conditionalScore P obs utility (policy y) y := by
  calc
    policyScore P obs utility policy =
        ∑ w, ∑ y, if obs w = y then (P w).toReal * utility (policy y) w else 0 := by
      rw [policyScore, expect_eq_sum]
      apply Finset.sum_congr rfl
      intro w _
      simp
    _ = ∑ y, ∑ w, if obs w = y then (P w).toReal * utility (policy y) w else 0 :=
      Finset.sum_comm
    _ = ∑ y, ∑ w, fiberWeight P obs y w * utility (policy y) w := by
      simp [fiberWeight, ite_mul]
    _ = ∑ y, signalMass P obs y * conditionalScore P obs utility (policy y) y := by
      apply Finset.sum_congr rfl
      intro y _
      exact (weighted_conditional_score P obs utility (policy y) y).symm

private theorem finite_expect_mono (P : PMF Ω) (f g : Ω → ℝ)
    (bound : ∀ w, f w ≤ g w) : expect P f ≤ expect P g := by
  rw [expect_eq_sum, expect_eq_sum]
  exact Finset.sum_le_sum (fun w _ =>
    mul_le_mul_of_nonneg_left (bound w) ENNReal.toReal_nonneg)

private def greedyAction (C : Finset A) (hC : C.Nonempty) (score : A → ℝ) : A := by
  classical
  exact Classical.choose (Finset.exists_mem_eq_sup' hC score)

private theorem greedyAction_spec (C : Finset A) (hC : C.Nonempty) (score : A → ℝ) :
    greedyAction C hC score ∈ C ∧ C.sup' hC score = score (greedyAction C hC score) := by
  classical
  exact Classical.choose_spec (Finset.exists_mem_eq_sup' hC score)

private theorem score_le_conditional_max (P : PMF Ω) (obs : Ω → Y)
    (utility : A → Ω → ℝ) (C : Finset A) (hC : C.Nonempty)
    (policy : Y → A) (feasible : ∀ y, policy y ∈ C) :
    policyScore P obs utility policy ≤
      expect (signalLaw P obs)
        (fun y => C.sup' hC (fun a => conditionalScore P obs utility a y)) := by
  rw [policy_score_tower, signal_expect_eq_sum]
  apply Finset.sum_le_sum
  intro y _
  exact mul_le_mul_of_nonneg_left
    (Finset.le_sup' (fun a => conditionalScore P obs utility a y) (feasible y))
    (signalMass_nonneg P obs y)

/-- Original 06.4 over arbitrary finite real probabilities and real utilities.
The same nonempty finite legal action set is available after every signal;
all C-valued signal strategies are feasible in this one-decision model. -/
theorem finite_conditional_value_of_information
    (P : PMF Ω) (obs : Ω → Y) (utility : A → Ω → ℝ)
    (C : Finset A) (hC : C.Nonempty) :
    C.sup' hC (fun a => expect P (utility a)) ≤
        expect (signalLaw P obs)
          (fun y => C.sup' hC (fun a => conditionalScore P obs utility a y)) ∧
      expect (signalLaw P obs)
          (fun y => C.sup' hC (fun a => conditionalScore P obs utility a y)) ≤
        expect P (fun w => C.sup' hC (fun a => utility a w)) := by
  classical
  constructor
  · apply Finset.sup'_le hC (fun a => expect P (utility a))
    intro a member
    exact score_le_conditional_max P obs utility C hC (fun _ => a) (fun _ => member)
  · let greedy : Y → A := fun y =>
      greedyAction C hC (fun a => conditionalScore P obs utility a y)
    have greedyValue :
        policyScore P obs utility greedy =
          expect (signalLaw P obs)
            (fun y => C.sup' hC (fun a => conditionalScore P obs utility a y)) := by
      rw [policy_score_tower, signal_expect_eq_sum]
      apply Finset.sum_congr rfl
      intro y _
      exact congrArg (fun value => signalMass P obs y * value)
        (greedyAction_spec C hC (fun a => conditionalScore P obs utility a y)).2.symm
    rw [← greedyValue]
    apply finite_expect_mono
    intro w
    exact Finset.le_sup' (fun a => utility a w)
      (greedyAction_spec C hC
        (fun a => conditionalScore P obs utility a (obs w))).1

/-- Original 06.4 robust clause: the same finite legal branches are retained,
and every old action embeds as a feasible policy ignoring the signal.
Only each branch's actual PMF is used; legal branches receive no prior. -/
theorem finite_robust_information_monotone
    {J : Type} (branches : Finset J) (hJ : branches.Nonempty)
    (P : J → PMF Ω) (obs : J → Ω → Y)
    (utility : J → A → Ω → ℝ)
    (C : Finset A) (hC : C.Nonempty) (policies : Finset (Y → A))
    (ignore : ∀ a ∈ C, (fun _ : Y => a) ∈ policies) :
    C.sup' hC (fun a => branches.inf' hJ
        (fun j => expect (P j) (utility j a))) ≤
      policies.sup' (by
        obtain ⟨a, ha⟩ := hC
        exact ⟨(fun _ => a), ignore a ha⟩)
        (fun policy => branches.inf' hJ
          (fun j => policyScore (P j) (obs j) (utility j) policy)) := by
  classical
  apply Finset.sup'_le hC
    (fun a => branches.inf' hJ (fun j => expect (P j) (utility j a)))
  intro a member
  simpa only [policyScore] using
    (Finset.le_sup'
      (fun policy => branches.inf' hJ
        (fun j => policyScore (P j) (obs j) (utility j) policy))
      (ignore a member))

end JurisLean.Candidates.U06_4ConditionalInformation20261031
