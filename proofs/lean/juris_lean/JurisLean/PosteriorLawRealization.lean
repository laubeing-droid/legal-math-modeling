import JurisLean.UnifiedFeedbackBridge
import JurisLean.Seams.UnifiedNeedlesS3b
import JurisLean.Seams.UnifiedPayoffChain
import JurisLean.FullMath.Probability.Brier

/-! One conditional world, its actual outcome marginal, and its cash-flow
readout. Rational histories embed exactly into the existing real feedback
process; the original informative-evidence witness is also realized. -/

namespace LegalMath20261109.PosteriorLaw

open MeasureTheory ProbabilityTheory
open LegalMath20261108.ClosedLoop LegalMath20261108.SequentialFeedback
open LegalMath20261108.UnifiedFeedbackBridge
open JurisLean.Seams.UnifiedNeedlesS3b
open JurisLean.Seams.UnifiedPayoffChain JurisLean.Seams.PayoffEquilibrium
open JurisLean.FullMath.Probability

noncomputable section

def embed (s : ℚ × ℚ) : State := ((s.1 : ℝ), (s.2 : ℝ))

def responseQ (s : ℚ × ℚ) : ℚ := s.1 / 4 + s.2 / 2 + 1/8

def probabilityQ (s : ℚ × ℚ) : ℚ := max 0 (min 1 (responseQ s))

theorem probabilityQ_bounds (s : ℚ × ℚ) : 0 ≤ probabilityQ s ∧ probabilityQ s ≤ 1 :=
  ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩

theorem probabilityQ_embed (s : ℚ × ℚ) : (probabilityQ s : ℝ) = probability (embed s) := by
  norm_num [probabilityQ, probability, responseQ, responseExample, embed,
    Rat.cast_max, Rat.cast_min]

def afterQ (s : ℚ × ℚ) (y : Bool) : ℚ × ℚ :=
  (if y then 1 else 0, s.2/4 + (if y then 1 else 0)/2 + 1/8)

theorem afterQ_embed (s : ℚ × ℚ) (y : Bool) : embed (afterQ s y) = after (embed s) y := by
  cases y <;> simp [embed, afterQ, after_formula, RepaymentExample.bit, learnExample]

/-- At a fixed observed history this is its conditional world distribution.
Unit means no additional pre-response evidence is being added at this step. -/
def historyModel (s : ℚ × ℚ) : PredictiveLegalModel Bool Unit Bool where
  prior := fun w => if w then probabilityQ s else 1 - probabilityQ s
  material := fun _ _ => 1
  obs := fun w y => if w = y then 1 else 0
  prior_nonneg := by
    intro w
    cases w
    · exact sub_nonneg.mpr (probabilityQ_bounds s).2
    · exact (probabilityQ_bounds s).1
  material_nonneg := by intros; norm_num
  obs_nonneg := by intros; split <;> norm_num
  prior_one := by simp [sum_bool_split] <;> ring
  material_one := by intros; simp
  obs_one := by intro w; cases w <;> simp [sum_bool_split]

theorem history_mass (s : ℚ × ℚ) : matMass (historyModel s) () = 1 := by
  simp [matMass, historyModel, sum_bool_split] <;> ring

def positiveHistory (s : ℚ × ℚ) : 0 < matMass (historyModel s) () := by
  rw [history_mass]; norm_num

theorem history_predictive (s : ℚ × ℚ) (y : Bool) :
    posteriorPredictive (historyModel s) () (positiveHistory s) y =
      if y then probabilityQ s else 1 - probabilityQ s := by
  simp only [posteriorPredictive, matPosterior, history_mass]
  cases y <;> simp [historyModel, sum_bool_split]

def xi (s : ℚ × ℚ) : Bool × Unit × Bool → ℚ :=
  posterior (legalJoint (historyModel s)) (materialEvent ())
    (by rw [legalJoint_material_mass, history_mass]; norm_num)

/-- This calls the original same-world posterior theorem, then identifies Q. -/
theorem xi_outcome_marginal (s : ℚ × ℚ) (y : Bool) :
    (∑ w, ∑ mt, xi s (w, mt, y)) =
      if y then probabilityQ s else 1 - probabilityQ s := by
  have old := (posterior_predictive_legal_target (historyModel s) () (positiveHistory s)
    (by rw [legalJoint_material_mass, history_mass]; norm_num)).1 y
  exact old.trans (history_predictive s y)

/-- The actual kernel uses precisely the marginal of Xi, including its weights. -/
theorem actual_Q_from_xi (s : ℚ × ℚ) (a : Bool) :
    model.outcome (embed s, a) =
      ENNReal.ofReal ((∑ w, ∑ mt, xi s (w, mt, false) : ℚ) : ℝ) • Measure.dirac false +
      ENNReal.ofReal ((∑ w, ∑ mt, xi s (w, mt, true) : ℚ) : ℝ) • Measure.dirac true := by
  rw [xi_outcome_marginal, xi_outcome_marginal]
  simp [model, outcomeKernel, coin, probabilityQ_embed]

theorem integral_coin (s : State) (f : Bool → ℝ) :
    ∫ y, f y ∂coin s = expBern (probability s) f := by
  rw [coin, integral_add_measure
    ((integrable_dirac (f := f) (a := false) (by simp)).smul_measure
      (c := ENNReal.ofReal (1-probability s)) (by simp))
    ((integrable_dirac (f := f) (a := true) (by simp)).smul_measure
      (c := ENNReal.ofReal (probability s)) (by simp))]
  simp [expBern, ENNReal.toReal_ofReal (probability_bounds s).1,
    ENNReal.toReal_ofReal (sub_nonneg.mpr (probability_bounds s).2), smul_eq_mul]

def reward (flows : Bool → Bool → PayFlow) (role : Role) (a y : Bool) : ℝ :=
  (legalReading role (flows a y) : ℝ)

def value (s : State) (flows : Bool → Bool → PayFlow) (role : Role) (a : Bool) : ℝ :=
  ∫ y, reward flows role a y ∂model.outcome (s, a)

/-- Utility and legal effects read exactly the Y used for the actual update. -/
theorem actual_payoff_from_same_xi (s : ℚ × ℚ) (flows : Bool → Bool → PayFlow)
    (role : Role) (a : Bool) :
    value (embed s) flows role a =
      ∑ y : Bool, reward flows role a y * ((∑ w, ∑ mt, xi s (w, mt, y) : ℚ) : ℝ) := by
  change (∫ y, reward flows role a y ∂coin (embed s)) = _
  rw [integral_coin]
  simp_rw [xi_outcome_marginal]
  simp [Fintype.univ_bool, probabilityQ_embed, expBern] <;> ring

theorem payoff_preserves_cash_encoding (role : Role) (fl : PayFlow) :
    (legalReading role { fl with entries := flipTags fl.entries } : ℝ) =
      (legalReading role fl : ℝ) := by
  exact_mod_cast cash_rewrite_propagates_to_reading role fl

/-- A pre-existing informative-evidence example, not only an empty-evidence law. -/
theorem informative_evidence_realizes_actual_Q :
    probability (embed ((1/2 : ℚ), (2/3 : ℚ))) =
      (posteriorPredictive witnessModel true witnessMatMass_pos true : ℝ) := by
  rw [posterior_predictive_bool_witness]
  norm_num [probability, embed, responseExample]

theorem informative_evidence_joint_readout (y : Bool) :
    (∑ w, ∑ mt, posterior (legalJoint witnessModel) (materialEvent true)
      (by rw [legalJoint_material_mass]; exact witnessMatMass_pos) (w, mt, y)) =
      posteriorPredictive witnessModel true witnessMatMass_pos y :=
  (posterior_predictive_legal_target witnessModel true witnessMatMass_pos
    (by rw [legalJoint_material_mass]; exact witnessMatMass_pos)).1 y

#print axioms probabilityQ_embed
#print axioms afterQ_embed
#print axioms xi_outcome_marginal
#print axioms actual_Q_from_xi
#print axioms actual_payoff_from_same_xi
#print axioms payoff_preserves_cash_encoding
#print axioms informative_evidence_realizes_actual_Q
#print axioms informative_evidence_joint_readout

end
end LegalMath20261109.PosteriorLaw
