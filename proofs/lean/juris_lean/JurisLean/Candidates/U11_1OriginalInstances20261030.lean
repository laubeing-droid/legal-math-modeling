import JurisLean.Candidates.Final20261021.Behavior
import JurisLean.Candidates.Final20261021.Probability
import JurisLean.Seams.UnifiedNeedlesXU
import Mathlib.Data.Fintype.BigOperators

open scoped BigOperators

namespace JurisLean.Candidates.U11_1OriginalInstances20261030

open JurisLean.Candidates.Final20261021

/-!
CI_NOT_RUN. Original 11.2, 11.6 L162 and shared original 04.4 only.
These finite instances reuse the existing countermodel and observational-ambiguity
proofs. They neither establish real-world causal premises nor close all U11.1.
-/

/-- Original 11.2: connect the existing models to the common Bernoulli law
and zero observation-prediction error, without rebuilding the countermodels. -/
theorem original11_2_bernoulli_prediction_checks :
    (∑ _u : Bool, (1 / 2 : ℚ)) = 1 ∧
    (∀ z : Bool × Bool,
      (∑ u : Bool, (1 / 2 : ℚ) *
        (if (Behavior.m1.observedAction u, Behavior.m1.observedOutcome u) = z
          then 1 else 0)) =
      (∑ u : Bool, (1 / 2 : ℚ) *
        (if (Behavior.m2.observedAction u, Behavior.m2.observedOutcome u) = z
          then 1 else 0))) ∧
    ((∑ u : Bool, (1 / 2 : ℚ) *
        (if Behavior.m1.observedAction u = Behavior.m1.observedOutcome u
          then 0 else 1)) = 0 ∧
     (∑ u : Bool, (1 / 2 : ℚ) *
        (if Behavior.m2.observedAction u = Behavior.m2.observedOutcome u
          then 0 else 1)) = 0) ∧
    (Behavior.ate Behavior.m1 = 1 ∧ Behavior.ate Behavior.m2 = 0) := by
  have old := Behavior.u11_1_obs_equiv_models_distinct_ATE
  refine ⟨by norm_num [Fintype.sum_bool], ?_, ?_, old.2⟩
  · intro z
    apply Finset.sum_congr rfl
    intro u _
    rw [old.1 u]
  · constructor <;> simp [Behavior.m1, Behavior.m2]

/-- Original 11.6 L162: the same complete behavior model has a genuine positive
effect, while two external legal constraints disagree on the improved action. -/
theorem original11_6_same_behavior_different_constraints :
    let model : Bool → Behavior.CausalModel := fun _ => Behavior.m1
    let admissible : Bool → Bool → Prop :=
      fun law action => law = true ∨ action = false
    model false = model true ∧
      Behavior.ate (model false) = 1 ∧
      admissible true true ∧
      ¬ admissible false true := by
  dsimp
  exact ⟨rfl,
    Behavior.u11_1_obs_equiv_models_distinct_ATE.2.1,
    by simp, by simp⟩

/-- Original 04.4 L113: two actual finite probability tables have visible cells
of mass 1/4 each and an entirely failed/successful missing half. Here S=T=1;
M alone controls outcome visibility, so selection and missingness are distinct. -/
def originalMissingWorld (hidden : Bool) :
    Probability.FiniteLaw (Bool × Bool) where
  mass := fun z =>
    if z.1 then 1 / 4 else if z.2 = hidden then 1 / 2 else 0
  nonneg := by
    rintro ⟨m, y⟩
    fin_cases m <;> fin_cases y <;> fin_cases hidden <;> norm_num
  total := by
    fin_cases hidden <;>
      norm_num [Fintype.sum_prod_type, Fintype.sum_bool]

/-- Original 04.4 L113: the actual report retains M and replaces hidden Y by
None; the visible law is computed from the full finite probability table. -/
def originalMissingReport (hidden m : Bool) (report : Option Bool) : ℚ :=
  ∑ y : Bool,
    if (if m then some y else none) = report
    then (originalMissingWorld hidden).mass (m, y) else 0

/-- Original 04.4 L113/L117: the target mean is computed under the full actual
finite law, including the missing half, rather than chosen from visible data. -/
def originalMissingMean (hidden : Bool) : ℚ :=
  ∑ z : Bool × Bool,
    (originalMissingWorld hidden).mass z * Behavior.indicator z.2

/-- Original 04.4 L113/L117: exhibit the required two feasible endpoints with
identical complete reports, recording rate 1/2 and visible success rate 1/2. -/
theorem original04_4_two_feasible_endpoints :
    (∀ m report,
      originalMissingReport false m report =
        originalMissingReport true m report) ∧
    originalMissingMean false = 1 / 4 ∧
    originalMissingMean true = 3 / 4 ∧
    (∀ hidden,
      (∑ y : Bool, (originalMissingWorld hidden).mass (true, y)) = 1 / 2 ∧
      (originalMissingWorld hidden).mass (true, true) /
        (∑ y : Bool, (originalMissingWorld hidden).mass (true, y)) = 1 / 2) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro m report
    fin_cases m <;> fin_cases report <;>
      norm_num [originalMissingReport, originalMissingWorld, Fintype.sum_bool]
  · norm_num [originalMissingMean, originalMissingWorld, Behavior.indicator,
      Fintype.sum_prod_type, Fintype.sum_bool]
  · norm_num [originalMissingMean, originalMissingWorld, Behavior.indicator,
      Fintype.sum_prod_type, Fintype.sum_bool]
  · intro hidden
    norm_num [originalMissingWorld, Fintype.sum_bool]

/-- Original 04.4 L115: under externally supplied M-Y independence, recover
the target rate from actual recording and visible-outcome probabilities.
Independence is a joint-law factorization, not the desired mean identity. -/
theorem original04_4_mcar_recovers
    (P : Probability.FiniteLaw (Bool × Bool))
    (independent : ∀ m y, P.mass (m, y) =
      (∑ y' : Bool, P.mass (m, y')) *
        (∑ m' : Bool, P.mass (m', y)))
    (recording : (∑ y : Bool, P.mass (true, y)) = 1 / 2)
    (observed : P.mass (true, true) /
      (∑ y : Bool, P.mass (true, y)) = 1 / 2) :
    (∑ m : Bool, P.mass (m, true)) = 1 / 2 := by
  have factor := independent true true
  rw [recording] at factor observed
  have cell := (div_eq_iff (by norm_num : (1 / 2 : ℚ) ≠ 0)).mp observed
  linarith

/-- Original 04.4 L113/L117: instantiate the existing ambiguity theorem once.
Reliability requires covering both feasible models; it cannot justify a singleton. -/
theorem original04_4_compatible_endpoints_not_singleton
    (I : (Bool → Option Bool → ℚ) → ℚ × ℚ)
    (reliable : ∀ hidden : Bool,
      (I (originalMissingReport hidden)).1 ≤ originalMissingMean hidden ∧
        originalMissingMean hidden ≤ (I (originalMissingReport hidden)).2) :
    (I (originalMissingReport false)).1 <
      (I (originalMissingReport false)).2 := by
  have endpoints := original04_4_two_feasible_endpoints
  have visible : originalMissingReport false = originalMissingReport true := by
    funext m report
    exact endpoints.1 m report
  have different : originalMissingMean false ≠ originalMissingMean true := by
    rw [endpoints.2.1, endpoints.2.2.1]
    norm_num
  exact JurisLean.Seams.UnifiedNeedlesXU.observational_ambiguity_preserved
    originalMissingReport originalMissingMean I reliable false true visible different

end JurisLean.Candidates.U11_1OriginalInstances20261030