import Mathlib
import JurisLean.Candidates.Final20261021.Decision

/-!
U06.1, frozen master section 6: the remaining finite-horizon Bellman optimum,
empty-action terminal convention, and nonrectangular counterexample.
The existing free-information theorem is retained in Final20261021.Decision.

Time is the number of decisions remaining.  A policy sees this time, the past
state/action history and the present fully observed state.  It receives no
future states.  Its legality proof concerns only membership in the given legal
action set, never optimality.  An empty action set terminates with g(s), as
explicitly permitted by the frozen master; no maximum of an empty set occurs.
Rewards and kernels may vary with time.  No discounting or zero terminal reward
is imposed.  The trajectory definitions below use the given kernel itself.
-/

namespace JurisLean.Candidates.U06_1FiniteBellman20261030

open scoped BigOperators

universe u v

variable {S : Type u} {A : Type v} [Fintype S] [DecidableEq A]

structure Control (S : Type u) (A : Type v) [Fintype S] [DecidableEq A] where
  legal : ℕ → S → Finset A
  kernel : ℕ → S → A → S → ℝ
  kernel_nonneg : ∀ n s a, a ∈ legal (n + 1) s → ∀ s', 0 ≤ kernel (n + 1) s a s'
  kernel_one : ∀ n s a, a ∈ legal (n + 1) s → ∑ s', kernel (n + 1) s a s' = 1

abbrev History (S : Type u) (A : Type v) := List (S × A)

abbrev Policy (m : Control S A) :=
  ∀ n, History S A → ∀ s, (m.legal (n + 1) s).Nonempty →
    {a // a ∈ m.legal (n + 1) s}

noncomputable def policyValue (m : Control S A) (r : ℕ → S → A → ℝ)
    (g : S → ℝ) (π : Policy m) : ℕ → History S A → S → ℝ
  | 0, _, s => g s
  | n + 1, h, s =>
      if hn : (m.legal (n + 1) s).Nonempty then
        let a := (π n h s hn).val
        r (n + 1) s a + ∑ s', m.kernel (n + 1) s a s' *
          policyValue m r g π n ((s, a) :: h) s'
      else g s

noncomputable def bellman (m : Control S A) (r : ℕ → S → A → ℝ)
    (g : S → ℝ) : ℕ → S → ℝ
  | 0, s => g s
  | n + 1, s =>
      if hn : (m.legal (n + 1) s).Nonempty then
        (m.legal (n + 1) s).sup' hn (fun a =>
          r (n + 1) s a + ∑ s', m.kernel (n + 1) s a s' * bellman m r g n s')
      else g s

theorem terminal_and_empty_action (m : Control S A) (r : ℕ → S → A → ℝ)
    (g : S → ℝ) (π : Policy m) (n : ℕ) (h : History S A) (s : S)
    (hempty : ¬ (m.legal (n + 1) s).Nonempty) :
    bellman m r g 0 s = g s ∧ policyValue m r g π 0 h s = g s ∧
      bellman m r g (n + 1) s = g s ∧ policyValue m r g π (n + 1) h s = g s := by
  simp [bellman, policyValue, hempty]

theorem policy_value_le_bellman (m : Control S A) (r : ℕ → S → A → ℝ)
    (g : S → ℝ) (π : Policy m) (n : ℕ) (h : History S A) (s : S) :
    policyValue m r g π n h s ≤ bellman m r g n s := by
  classical
  induction n generalizing h s with
  | zero => exact le_rfl
  | succ n ih =>
      by_cases hn : (m.legal (n + 1) s).Nonempty
      · let a := (π n h s hn).val
        have ha : a ∈ m.legal (n + 1) s := (π n h s hn).property
        have hs : (∑ s', m.kernel (n + 1) s a s' *
            policyValue m r g π n ((s, a) :: h) s') ≤
            ∑ s', m.kernel (n + 1) s a s' * bellman m r g n s' := by
          apply Finset.sum_le_sum
          intro s' _
          exact mul_le_mul_of_nonneg_left (ih _ _) (m.kernel_nonneg n s a ha s')
        simp only [policyValue, bellman, dif_pos hn]
        calc
          r (n + 1) s a + (∑ s', m.kernel (n + 1) s a s' *
              policyValue m r g π n ((s, a) :: h) s') ≤
            r (n + 1) s a + ∑ s', m.kernel (n + 1) s a s' * bellman m r g n s' :=
              add_le_add (le_refl _) hs
          _ ≤ _ := Finset.le_sup' (fun b => r (n + 1) s b +
            ∑ s', m.kernel (n + 1) s b s' * bellman m r g n s') ha
      · simp [policyValue, bellman, hn]

noncomputable def greedy (m : Control S A) (r : ℕ → S → A → ℝ)
    (g : S → ℝ) : Policy m := by
  classical
  intro n _ s hn
  let hex := Finset.exists_mem_eq_sup' hn (fun a =>
    r (n + 1) s a + ∑ s', m.kernel (n + 1) s a s' * bellman m r g n s')
  exact ⟨Classical.choose hex, (Classical.choose_spec hex).1⟩

theorem greedy_step (m : Control S A) (r : ℕ → S → A → ℝ)
    (g : S → ℝ) (n : ℕ) (h : History S A) (s : S)
    (hn : (m.legal (n + 1) s).Nonempty) :
    bellman m r g (n + 1) s =
      r (n + 1) s (greedy m r g n h s hn).val +
        ∑ s', m.kernel (n + 1) s (greedy m r g n h s hn).val s' *
          bellman m r g n s' := by
  classical
  simpa only [bellman, dif_pos hn, greedy] using
    (Classical.choose_spec (Finset.exists_mem_eq_sup' hn (fun a =>
      r (n + 1) s a + ∑ s', m.kernel (n + 1) s a s' * bellman m r g n s'))).2

theorem greedy_value_eq_bellman (m : Control S A) (r : ℕ → S → A → ℝ)
    (g : S → ℝ) (n : ℕ) (h : History S A) (s : S) :
    policyValue m r g (greedy m r g) n h s = bellman m r g n s := by
  classical
  induction n generalizing h s with
  | zero => rfl
  | succ n ih =>
      by_cases hn : (m.legal (n + 1) s).Nonempty
      · simp only [policyValue, dif_pos hn]
        simp_rw [ih]
        exact (greedy_step m r g n h s hn).symm
      · simp [policyValue, bellman, hn]

theorem bellman_full_policy_optimum (m : Control S A) (r : ℕ → S → A → ℝ)
    (g : S → ℝ) :
    ∃ πstar : Policy m, ∀ n h s,
      policyValue m r g πstar n h s = bellman m r g n s ∧
      ∀ π : Policy m, policyValue m r g π n h s ≤ policyValue m r g πstar n h s := by
  refine ⟨greedy m r g, ?_⟩
  intro n h s
  refine ⟨greedy_value_eq_bellman m r g n h s, ?_⟩
  intro π
  rw [greedy_value_eq_bellman]
  exact policy_value_le_bellman m r g π n h s

/- A trace enumerates actual successor states.  On early termination it is
   padded by the constant state; the padding has unit mass at one trace and
   contributes neither further reward nor transitions. -/
def Trace (S : Type u) : ℕ → Type u
  | 0 => PUnit
  | n + 1 => S × Trace S n

instance traceFintype : (n : ℕ) → Fintype (Trace S n)
  | 0 => inferInstanceAs (Fintype PUnit)
  | n + 1 => by
      letI : Fintype (Trace S n) := traceFintype n
      exact inferInstanceAs (Fintype (S × Trace S n))

def terminalTrace (s : S) : (n : ℕ) → Trace S n
  | 0 => PUnit.unit
  | n + 1 => (s, terminalTrace s n)

noncomputable def trajectoryWeight (m : Control S A) (π : Policy m) :
    (n : ℕ) → History S A → S → Trace S n → ℝ
  | 0, _, _, _ => 1
  | n + 1, h, s, x => by
      classical
      exact if hn : (m.legal (n + 1) s).Nonempty then
        let a := (π n h s hn).val
        m.kernel (n + 1) s a x.1 * trajectoryWeight m π n ((s, a) :: h) x.1 x.2
      else if x = terminalTrace s (n + 1) then 1 else 0

noncomputable def realizedReturn (m : Control S A) (r : ℕ → S → A → ℝ)
    (g : S → ℝ) (π : Policy m) : (n : ℕ) → History S A → S → Trace S n → ℝ
  | 0, _, s, _ => g s
  | n + 1, h, s, x =>
      if hn : (m.legal (n + 1) s).Nonempty then
        let a := (π n h s hn).val
        r (n + 1) s a + realizedReturn m r g π n ((s, a) :: h) x.1 x.2
      else g s

theorem trajectory_weight_nonneg (m : Control S A) (π : Policy m)
    (n : ℕ) (h : History S A) (s : S) (x : Trace S n) :
    0 ≤ trajectoryWeight m π n h s x := by
  classical
  induction n generalizing h s with
  | zero => norm_num [trajectoryWeight]
  | succ n ih =>
      by_cases hn : (m.legal (n + 1) s).Nonempty
      · simp only [trajectoryWeight, dif_pos hn]
        exact mul_nonneg (m.kernel_nonneg n s _ (π n h s hn).property x.1) (ih _ _ _)
      · simp only [trajectoryWeight, dif_neg hn]
        split_ifs <;> norm_num

theorem trajectory_weight_one (m : Control S A) (π : Policy m)
    (n : ℕ) (h : History S A) (s : S) :
    ∑ x : Trace S n, trajectoryWeight m π n h s x = 1 := by
  classical
  induction n generalizing h s with
  | zero => simp [trajectoryWeight, Trace]
  | succ n ih =>
      by_cases hn : (m.legal (n + 1) s).Nonempty
      · change (∑ x : S × Trace S n, trajectoryWeight m π (n + 1) h s x) = 1
        simp only [trajectoryWeight, dif_pos hn, Fintype.sum_prod_type]
        simp_rw [← Finset.mul_sum, ih, mul_one]
        exact m.kernel_one n s _ (π n h s hn).property
      · simp [trajectoryWeight, hn]

noncomputable def trajectoryLaw (m : Control S A) (π : Policy m)
    (n : ℕ) (h : History S A) (s : S) : PMF (Trace S n) :=
  PMF.ofFintype (fun x => ENNReal.ofReal (trajectoryWeight m π n h s x)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun x _ => trajectory_weight_nonneg m π n h s x),
      trajectory_weight_one]
    exact ENNReal.ofReal_one)

theorem trajectory_law_mass (m : Control S A) (π : Policy m)
    (n : ℕ) (h : History S A) (s : S) (x : Trace S n) :
    (trajectoryLaw m π n h s x).toReal = trajectoryWeight m π n h s x := by
  rw [trajectoryLaw, PMF.ofFintype_apply, ENNReal.toReal_ofReal
    (trajectory_weight_nonneg m π n h s x)]

/- The finite expectation is taken over the normalized, nonnegative weights
   constructed from the actual kernels, rather than stipulated to equal V. -/
noncomputable def trajectoryExpectation (m : Control S A) (r : ℕ → S → A → ℝ)
    (g : S → ℝ) (π : Policy m) (n : ℕ) (h : History S A) (s : S) : ℝ :=
  ∑ x : Trace S n, trajectoryWeight m π n h s x * realizedReturn m r g π n h s x

theorem trajectory_expectation_eq_policy_value (m : Control S A)
    (r : ℕ → S → A → ℝ) (g : S → ℝ) (π : Policy m)
    (n : ℕ) (h : History S A) (s : S) :
    trajectoryExpectation m r g π n h s = policyValue m r g π n h s := by
  classical
  induction n generalizing h s with
  | zero => simp [trajectoryExpectation, trajectoryWeight, realizedReturn, policyValue, Trace]
  | succ n ih =>
      by_cases hn : (m.legal (n + 1) s).Nonempty
      · let a := (π n h s hn).val
        have hinner (s' : S) :
            (∑ x : Trace S n,
              (m.kernel (n + 1) s a s' * trajectoryWeight m π n ((s, a) :: h) s' x) *
                (r (n + 1) s a + realizedReturn m r g π n ((s, a) :: h) s' x)) =
              m.kernel (n + 1) s a s' * r (n + 1) s a +
                m.kernel (n + 1) s a s' * policyValue m r g π n ((s, a) :: h) s' := by
          calc
            _ = ∑ x : Trace S n,
                ((m.kernel (n + 1) s a s' * r (n + 1) s a) *
                  trajectoryWeight m π n ((s, a) :: h) s' x +
                m.kernel (n + 1) s a s' * (trajectoryWeight m π n ((s, a) :: h) s' x *
                  realizedReturn m r g π n ((s, a) :: h) s' x)) := by
                    apply Finset.sum_congr rfl
                    intro x _
                    ring
            _ = (m.kernel (n + 1) s a s' * r (n + 1) s a) *
                  (∑ x : Trace S n, trajectoryWeight m π n ((s, a) :: h) s' x) +
                m.kernel (n + 1) s a s' * trajectoryExpectation m r g π n ((s, a) :: h) s' := by
                  simp only [trajectoryExpectation, Finset.sum_add_distrib, Finset.mul_sum]
            _ = _ := by rw [trajectory_weight_one, ih, mul_one]
        change (∑ x : S × Trace S n,
          trajectoryWeight m π (n + 1) h s x * realizedReturn m r g π (n + 1) h s x) = _
        simp only [trajectoryWeight, realizedReturn, policyValue, dif_pos hn, Fintype.sum_prod_type]
        change (∑ s', ∑ x : Trace S n,
          (m.kernel (n + 1) s a s' * trajectoryWeight m π n ((s, a) :: h) s' x) *
            (r (n + 1) s a + realizedReturn m r g π n ((s, a) :: h) s' x)) = _
        simp_rw [hinner]
        rw [Finset.sum_add_distrib, ← Finset.sum_mul,
          m.kernel_one n s a (π n h s hn).property, one_mul]
      · simp [trajectoryExpectation, trajectoryWeight, realizedReturn, policyValue, hn, ite_mul]

theorem bellman_optimum_of_actual_trajectory_expectation (m : Control S A)
    (r : ℕ → S → A → ℝ) (g : S → ℝ) :
    ∃ πstar : Policy m, ∀ n h s,
      (∀ x : Trace S n, 0 ≤ trajectoryWeight m πstar n h s x) ∧
      (∑ x : Trace S n, trajectoryWeight m πstar n h s x = 1) ∧
      (∑ x : Trace S n, (trajectoryLaw m πstar n h s x).toReal *
        realizedReturn m r g πstar n h s x) = bellman m r g n s ∧
      ∀ π : Policy m,
        (∑ x : Trace S n, (trajectoryLaw m π n h s x).toReal * realizedReturn m r g π n h s x) ≤
        ∑ x : Trace S n, (trajectoryLaw m πstar n h s x).toReal *
          realizedReturn m r g πstar n h s x := by
  refine ⟨greedy m r g, ?_⟩
  intro n h s
  refine ⟨trajectory_weight_nonneg m _ n h s, trajectory_weight_one m _ n h s, ?_, ?_⟩
  · simp only [trajectory_law_mass]
    change trajectoryExpectation m r g _ n h s = _
    rw [trajectory_expectation_eq_policy_value, greedy_value_eq_bellman]
  · intro π
    simp only [trajectory_law_mass]
    change trajectoryExpectation m r g π n h s ≤ trajectoryExpectation m r g _ n h s
    rw [trajectory_expectation_eq_policy_value, trajectory_expectation_eq_policy_value,
      greedy_value_eq_bellman]
    exact policy_value_le_bellman m r g π n h s

theorem policy_value_sub (m : Control S A) (r₁ r₂ : ℕ → S → A → ℝ)
    (g₁ g₂ : S → ℝ) (π : Policy m) (n : ℕ) (h : History S A) (s : S) :
    policyValue m (fun t s a => r₁ t s a - r₂ t s a) (fun s => g₁ s - g₂ s) π n h s =
      policyValue m r₁ g₁ π n h s - policyValue m r₂ g₂ π n h s := by
  classical
  induction n generalizing h s with
  | zero => rfl
  | succ n ih =>
      by_cases hn : (m.legal (n + 1) s).Nonempty
      · simp only [policyValue, dif_pos hn]
        simp_rw [ih, mul_sub]
        rw [Finset.sum_sub_distrib]
        ring
      · simp [policyValue, hn]

theorem cost_counted_once (m : Control S A) (reward cost : ℕ → S → A → ℝ)
    (g : S → ℝ) (π : Policy m) (n : ℕ) (h : History S A) (s : S) :
    trajectoryExpectation m (fun t s a => reward t s a - cost t s a) g π n h s =
      trajectoryExpectation m reward g π n h s -
        trajectoryExpectation m cost (fun _ => 0) π n h s := by
  simp only [trajectory_expectation_eq_policy_value]
  simpa only [sub_zero] using policy_value_sub m reward cost g (fun _ => 0) π n h s

/- Two equiprobable states and a single model chosen before the state is seen.
   Each allowed model has mean 1/2.  Selecting a different adverse model after
   observing the state gives zero, but that payoff vector is no allowed model. -/
def coupledPayoff (model state : Bool) : ℝ := if model = state then 1 else 0

theorem nonrectangular_bellman_counterexample :
    (∀ model : Bool, (coupledPayoff model false + coupledPayoff model true) / 2 = (1 : ℝ) / 2) ∧
    (min (coupledPayoff false false) (coupledPayoff true false) +
      min (coupledPayoff false true) (coupledPayoff true true)) / 2 = 0 ∧
    (0 : ℝ) < 1 / 2 ∧
    ¬ ∃ model : Bool, ∀ state : Bool, coupledPayoff model state = 0 := by
  refine ⟨?_, ?_, by norm_num, ?_⟩
  · intro model
    cases model <;> norm_num [coupledPayoff]
  · norm_num [coupledPayoff]
  · rintro ⟨model, hmodel⟩
    have := hmodel model
    norm_num [coupledPayoff] at this

end JurisLean.Candidates.U06_1FiniteBellman20261030

-- Independent changed-module audit; retained until the closure evidence is bound.
#check JurisLean.Candidates.U06_1FiniteBellman20261030.terminal_and_empty_action
#print axioms JurisLean.Candidates.U06_1FiniteBellman20261030.terminal_and_empty_action
#check JurisLean.Candidates.U06_1FiniteBellman20261030.policy_value_le_bellman
#print axioms JurisLean.Candidates.U06_1FiniteBellman20261030.policy_value_le_bellman
#check JurisLean.Candidates.U06_1FiniteBellman20261030.greedy_step
#print axioms JurisLean.Candidates.U06_1FiniteBellman20261030.greedy_step
#check JurisLean.Candidates.U06_1FiniteBellman20261030.greedy_value_eq_bellman
#print axioms JurisLean.Candidates.U06_1FiniteBellman20261030.greedy_value_eq_bellman
#check JurisLean.Candidates.U06_1FiniteBellman20261030.bellman_full_policy_optimum
#print axioms JurisLean.Candidates.U06_1FiniteBellman20261030.bellman_full_policy_optimum
#check JurisLean.Candidates.U06_1FiniteBellman20261030.trajectory_weight_nonneg
#print axioms JurisLean.Candidates.U06_1FiniteBellman20261030.trajectory_weight_nonneg
#check JurisLean.Candidates.U06_1FiniteBellman20261030.trajectory_weight_one
#print axioms JurisLean.Candidates.U06_1FiniteBellman20261030.trajectory_weight_one
#check JurisLean.Candidates.U06_1FiniteBellman20261030.trajectory_law_mass
#print axioms JurisLean.Candidates.U06_1FiniteBellman20261030.trajectory_law_mass
#check JurisLean.Candidates.U06_1FiniteBellman20261030.trajectory_expectation_eq_policy_value
#print axioms JurisLean.Candidates.U06_1FiniteBellman20261030.trajectory_expectation_eq_policy_value
#check JurisLean.Candidates.U06_1FiniteBellman20261030.bellman_optimum_of_actual_trajectory_expectation
#print axioms JurisLean.Candidates.U06_1FiniteBellman20261030.bellman_optimum_of_actual_trajectory_expectation
#check JurisLean.Candidates.U06_1FiniteBellman20261030.policy_value_sub
#print axioms JurisLean.Candidates.U06_1FiniteBellman20261030.policy_value_sub
#check JurisLean.Candidates.U06_1FiniteBellman20261030.cost_counted_once
#print axioms JurisLean.Candidates.U06_1FiniteBellman20261030.cost_counted_once
#check JurisLean.Candidates.U06_1FiniteBellman20261030.nonrectangular_bellman_counterexample
#print axioms JurisLean.Candidates.U06_1FiniteBellman20261030.nonrectangular_bellman_counterexample
#check JurisLean.Candidates.Final20261021.Decision.u06_1_value_of_free_information
#print axioms JurisLean.Candidates.Final20261021.Decision.u06_1_value_of_free_information
