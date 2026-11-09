import JurisLean.RemainingClosure.W1Atoms

set_option autoImplicit false

/-! The constant 3/4 is attained by the actual primal law distance, not only
by an upper bound on a chosen coupling. Source only; CI_NOT_RUN. -/
namespace LegalMath.RemainingClosure.W1Sharp

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open LegalMath20261108.ClosedLoop LegalMath20261108.SequentialFeedback
open LegalMath20261108.UnifiedFeedbackBridge
open LegalMath20261110.FeedbackW1
open LegalMath.RemainingClosure.W1Atoms

noncomputable section

def leftState : State := (0,1/2)
def rightState : State := (1,1/2)

lemma left_in_square : leftState ∈ square := by norm_num [leftState,square]
lemma right_in_square : rightState ∈ square := by norm_num [rightState,square]

lemma witness_distance : dstar leftState rightState = 1 := by
  norm_num [leftState,rightState,dstar]

theorem witness_matrix_cost : w1 leftState rightState = 3/4 := by
  have upper := w1_contraction leftState rightState left_in_square right_in_square
  rw [witness_distance,mul_one] at upper
  apply le_antisymm upper
  have ne : {v | ∃ r, admissible (probability leftState) (probability rightState) r ∧
      v=cost leftState rightState r}.Nonempty :=
    ⟨_, _, monotone_admissible leftState rightState,rfl⟩
  apply le_csInf ne
  rintro v ⟨r,hr,rfl⟩
  have h := hr.2.1
  norm_num [leftState,probability,responseExample] at h
  norm_num [cost,leftState,rightState,probability,responseExample,
    after_formula,learnExample,RepaymentExample.bit,dstar]
  linarith

theorem witness_primal_cost :
    distributionW1 (step model leftState) (step model rightState) = (3/4:ℝ≥0∞) := by
  rw [← twoAtomIdentification leftState rightState,witness_matrix_cost,
    ENNReal.ofReal_div_of_pos (by norm_num : (0:ℝ) < 4)]
  norm_num

/-- No smaller nonnegative uniform law-contraction constant can work. -/
theorem contraction_constant_sharp (c : ℝ) (hc : 0 ≤ c)
    (bound : ∀ s t : State, s ∈ square → t ∈ square →
      distributionW1 (step model s) (step model t) ≤ ENNReal.ofReal (c*dstar s t)) :
    (3/4:ℝ) ≤ c := by
  have h := bound leftState rightState left_in_square right_in_square
  rw [witness_primal_cost,witness_distance,mul_one] at h
  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top h
  simpa [ENNReal.toReal_ofReal hc, ENNReal.toReal_div] using hreal

#print axioms witness_matrix_cost
#print axioms witness_primal_cost
#print axioms contraction_constant_sharp

end
end LegalMath.RemainingClosure.W1Sharp
