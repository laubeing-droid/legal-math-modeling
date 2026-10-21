import JurisLean.Candidates.Final20261021.Feedback

namespace JurisLean.Candidates.Final20261021.Iteration

inductive RiskTrace : ℝ → List ℝ → ℝ → Prop where
  | nil (r : ℝ) : RiskTrace r [] r
  | cons {r next last eps : ℝ} {budgets : List ℝ} : next ≤ r + eps →
      RiskTrace next budgets last → RiskTrace r (eps :: budgets) last

theorem u15_1_finite_cumulative_improvement {first last : ℝ} {budgets : List ℝ}
    (h : RiskTrace first budgets last) : last ≤ first + budgets.sum := by
  induction h with
  | nil r => simp
  | cons h ht ih => simp only [List.sum_cons]; linarith

theorem u15_2_preserved_predictions_equal_risk {Ω Y : Type} [Fintype Ω]
    (law : Probability.FiniteLaw Ω) (old new : Ω → Y) (loss : Y → Ω → ℚ)
    (same : ∀ x, old x = new x) :
    Probability.expectation law (fun x => loss (old x) x) =
      Probability.expectation law (fun x => loss (new x) x) := by
  simp_rw [same]

def exactRisk (predictions : Bool × Bool) : ℚ :=
  (Learning.zeroOne predictions.1 false + Learning.zeroOne predictions.2 true) / 2

theorem two_round_exact_risks :
    exactRisk (false, false) = 1/2 ∧ exactRisk (false, true) = 0 ∧
      exactRisk (true, false) = 1 := by norm_num [exactRisk, Learning.zeroOne]

def twoRounds (old better wrongTarget : Feedback.Assessed) : Feedback.Assessed :=
  let after1 := (Feedback.consider old better 0).2
  (Feedback.consider after1 wrongTarget 0).2

theorem u15_3_two_round_actual_state (old better wrongTarget : Feedback.Assessed)
    (same : better.scope = old.scope) (improves : better.upper ≤ old.lower)
    (wrong : wrongTarget.scope ≠ better.scope) : twoRounds old better wrongTarget = better := by
  simp [twoRounds, Feedback.consider, same, improves, wrong]

end JurisLean.Candidates.Final20261021.Iteration
