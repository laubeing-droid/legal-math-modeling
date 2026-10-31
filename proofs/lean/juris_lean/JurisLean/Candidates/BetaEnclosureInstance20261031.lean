import JurisLean.Candidates.ExactProbability20261027
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace JurisLean.Candidates.BetaEnclosureInstance20261031

open MeasureTheory

noncomputable section

private def betaKernel (a b : ℚ) (t : ℝ) : ℝ :=
  t ^ ((a : ℝ) - 1) * (1 - t) ^ ((b : ℝ) - 1)

private theorem betaKernel_nonnegative (a b : ℚ) (t : ℝ)
    (ht : t ∈ Set.Icc (0 : ℝ) 1) : 0 ≤ betaKernel a b t := by
  exact mul_nonneg (Real.rpow_nonneg ht.1 _)
    (Real.rpow_nonneg (sub_nonneg.mpr ht.2) _)

/-- Supplied rational enclosures for the actual incomplete and complete Beta
integrals imply the clipped ratio enclosure and the existing explicit width
bound. No integral evaluation or approximation algorithm is assumed here. -/
theorem actual_beta_integrals_enclosure
    (a b : ℚ) (_ha : 0 < a) (_hb : 0 < b)
    (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1)
    (nL nU bL bU : ℚ)
    (numeratorLower : (nL : ℝ) ≤ ∫ t in 0..x, betaKernel a b t)
    (numeratorUpper : (∫ t in 0..x, betaKernel a b t) ≤ (nU : ℝ))
    (denominatorPositive : 0 < bL)
    (denominatorLower : (bL : ℝ) ≤ ∫ t in (0 : ℝ)..1, betaKernel a b t)
    (denominatorUpper : (∫ t in (0 : ℝ)..1, betaKernel a b t) ≤ (bU : ℝ)) :
    let N := ∫ t in 0..x, betaKernel a b t
    let B := ∫ t in (0 : ℝ)..1, betaKernel a b t
    (max 0 ((nL : ℝ) / (bU : ℝ)) ≤ N / B ∧
      N / B ≤ min 1 ((nU : ℝ) / (bL : ℝ))) ∧    (0 ≤ min 1 ((nU : ℝ) / (bL : ℝ)) - max 0 ((nL : ℝ) / (bU : ℝ)) ∧
      min 1 ((nU : ℝ) / (bL : ℝ)) - max 0 ((nL : ℝ) / (bU : ℝ)) ≤ 1 ∧
      min 1 ((nU : ℝ) / (bL : ℝ)) - max 0 ((nL : ℝ) / (bU : ℝ)) ≤
        ((nU : ℝ) - (nL : ℝ)) / (bU : ℝ) +
          (nU : ℝ) * ((bU : ℝ) - (bL : ℝ)) / ((bL : ℝ) * (bU : ℝ))) := by
  dsimp only
  have hbL : (0 : ℝ) < (bL : ℝ) := by
    exact_mod_cast denominatorPositive
  have hB : (0 : ℝ) < ∫ t in (0 : ℝ)..1, betaKernel a b t :=
    lt_of_lt_of_le hbL denominatorLower
  have integrable : IntervalIntegrable (betaKernel a b) volume (0 : ℝ) 1 :=
    intervalIntegral.intervalIntegrable_of_integral_ne_zero (ne_of_gt hB)
  have hN : (0 : ℝ) ≤ ∫ t in 0..x, betaKernel a b t := by
    apply intervalIntegral.integral_nonneg hx.1
    intro t ht
    exact betaKernel_nonnegative a b t ⟨ht.1, ht.2.trans hx.2⟩
  have nonnegative_ae :
      0 ≤ᵐ[volume.restrict (Set.Ioc (0 : ℝ) 1)] betaKernel a b := by
    apply (ae_restrict_iff' measurableSet_Ioc).mpr
    exact Filter.Eventually.of_forall fun t ht =>
      betaKernel_nonnegative a b t ⟨le_of_lt ht.1, ht.2⟩
  have hNB : (∫ t in 0..x, betaKernel a b t) ≤
      ∫ t in (0 : ℝ)..1, betaKernel a b t :=
    intervalIntegral.integral_mono_interval le_rfl hx.1 hx.2 nonnegative_ae integrable
  constructor
  · exact JurisLean.Candidates.Final20261021.Probability.u04_2_enclosed_propagation
      (∫ t in 0..x, betaKernel a b t) (∫ t in (0 : ℝ)..1, betaKernel a b t)
      (nL : ℝ) (nU : ℝ) (bL : ℝ) (bU : ℝ)
      hN hNB numeratorLower numeratorUpper hbL denominatorLower denominatorUpper
  · exact JurisLean.Candidates.ExactProbability20261027.supplied_enclosure_has_explicit_width_bound
      (∫ t in 0..x, betaKernel a b t) (∫ t in (0 : ℝ)..1, betaKernel a b t)
      (nL : ℝ) (nU : ℝ) (bL : ℝ) (bU : ℝ)
      hN hNB numeratorLower numeratorUpper hbL denominatorLower denominatorUpper

end
end JurisLean.Candidates.BetaEnclosureInstance20261031

#print axioms JurisLean.Candidates.BetaEnclosureInstance20261031.actual_beta_integrals_enclosure