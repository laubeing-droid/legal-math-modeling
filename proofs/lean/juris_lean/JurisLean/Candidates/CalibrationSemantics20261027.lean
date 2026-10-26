import JurisLean.Candidates.Final20261021.Probability
import Mathlib.Probability.CondVar

/-!
Original 05.1/05.2/05.3: conditional correctness, population calibration and
group calibration are different guarantees. The positive results below use
actual conditional expectations and conditional variance on a probability
space. Finite counterexamples retain normalized atom masses and actual bins.
-/

namespace JurisLean.Candidates.CalibrationSemantics20261027

open MeasureTheory ProbabilityTheory
open JurisLean.Candidates.Final20261021.Probability

theorem q05_1_conditional_correct_implies_calibration {Ω : Type*} [m₀ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (mX mScore : MeasurableSpace Ω)
    (scoreInformation : mScore ≤ mX) (observedInformation : mX ≤ m₀)
    (Y p : Ω → ℝ) (scoreMeasurable : AEStronglyMeasurable[mScore] p μ)
    (correct : μ[Y | mX] =ᵐ[μ] p) : μ[Y | mScore] =ᵐ[μ] p := by
  have scoreIntegrable : Integrable p μ := integrable_condExp.congr correct
  calc
    μ[Y | mScore] =ᵐ[μ] μ[μ[Y | mX] | mScore] :=
      (condExp_condExp_of_le scoreInformation observedInformation).symm
    _ =ᵐ[μ] μ[p | mScore] := condExp_congr_ae correct
    _ =ᵐ[μ] p := condExp_of_aestronglyMeasurable'
      (scoreInformation.trans observedInformation) scoreMeasurable scoreIntegrable

theorem q05_1_conditional_brier_decomposition {Ω : Type*} [m₀ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (m : MeasurableSpace Ω) (hm : m ≤ m₀)
    (Y p : Ω → ℝ) (hY : MemLp Y 2 μ) (hp : MemLp p 2 μ)
    (scoreMeasurable : StronglyMeasurable[m] p) :
    μ[(Y - p) ^ 2 | m] =ᵐ[μ] Var[Y; μ | m] + (μ[Y | m] - p) ^ 2 := by
  have expanded : μ[(Y - p) ^ 2 | m] =ᵐ[μ]
      μ[Y ^ 2 | m] - 2 * μ[Y | m] * p + p ^ 2 := by
    rw [sub_sq]
    have squareY : Integrable (Y ^ 2) μ := hY.integrable_sq
    have product : Integrable (2 * Y * p) μ := by
      rw [mul_assoc]
      exact (memLp_one_iff_integrable.1 <| hp.mul hY).const_mul _
    have squareP : Integrable (p ^ 2) μ := hp.integrable_sq
    filter_upwards [condExp_add (m := m) (squareY.sub product) squareP,
      condExp_sub (m := m) squareY product,
      condExp_mul_of_stronglyMeasurable_right scoreMeasurable product
        ((hY.integrable one_le_two).const_mul _), condExp_ofNat (m := m) 2 Y]
      with w h₀ h₁ h₂ h₃
    simp [h₀, h₁, h₂, h₃, condExp_of_stronglyMeasurable hm (scoreMeasurable.pow _) squareP]
  filter_upwards [expanded, condVar_ae_eq_condExp_sq_sub_sq_condExp hm hY] with w hRisk hVariance
  dsimp at hRisk hVariance ⊢
  rw [hRisk, hVariance]
  ring

theorem q05_1_conditional_brier_unique_optimum {Ω : Type*} [m₀ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (m : MeasurableSpace Ω) (hm : m ≤ m₀)
    (Y p : Ω → ℝ) (hY : MemLp Y 2 μ) (hp : MemLp p 2 μ)
    (scoreMeasurable : StronglyMeasurable[m] p) :
    ∀ᵐ w ∂μ, (Var[Y; μ | m]) w ≤ (μ[(Y - p) ^ 2 | m]) w ∧
      ((Var[Y; μ | m]) w = (μ[(Y - p) ^ 2 | m]) w ↔ p w = (μ[Y | m]) w) := by
  filter_upwards [q05_1_conditional_brier_decomposition μ m hm Y p hY hp scoreMeasurable]
    with w hRisk
  dsimp at hRisk
  constructor
  · nlinarith [sq_nonneg ((μ[Y | m]) w - p w)]
  · constructor
    · intro same
      nlinarith
    · intro same
      rw [same] at hRisk
      simpa using hRisk.symm

theorem q05_1_binary_conditional_variance {Ω : Type*} [m₀ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (m : MeasurableSpace Ω) (hm : m ≤ m₀)
    (Y : Ω → ℝ) (hY : MemLp Y 2 μ) (binary : ∀ᵐ w ∂μ, Y w = 0 ∨ Y w = 1) :
    Var[Y; μ | m] =ᵐ[μ] μ[Y | m] * (1 - μ[Y | m]) := by
  have square : Y ^ 2 =ᵐ[μ] Y := by
    filter_upwards [binary] with w hw
    rcases hw with hw | hw <;> simp [hw]
  filter_upwards [condVar_ae_eq_condExp_sq_sub_sq_condExp hm hY, condExp_congr_ae square]
    with w hVariance hSquare
  dsimp at hVariance hSquare ⊢
  rw [hVariance, hSquare]
  ring

theorem q05_1_binary_conditional_brier {Ω : Type*} [m₀ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (m : MeasurableSpace Ω) (hm : m ≤ m₀)
    (Y p : Ω → ℝ) (hY : MemLp Y 2 μ) (hp : MemLp p 2 μ)
    (scoreMeasurable : StronglyMeasurable[m] p) (binary : ∀ᵐ w ∂μ, Y w = 0 ∨ Y w = 1) :
    μ[(Y - p) ^ 2 | m] =ᵐ[μ]
      μ[Y | m] * (1 - μ[Y | m]) + (μ[Y | m] - p) ^ 2 := by
  filter_upwards [q05_1_conditional_brier_decomposition μ m hm Y p hY hp scoreMeasurable,
    q05_1_binary_conditional_variance μ m hm Y hY binary] with w hRisk hVariance
  dsimp at hRisk hVariance ⊢
  rw [hRisk, hVariance]

def bucketMass {Ω : Type} [Fintype Ω] (P : FiniteLaw Ω) (score : Ω → ℚ) (bin : ℚ) : ℚ :=
  expectation P (fun w => if score w = bin then 1 else 0)

def bucketSuccess {Ω : Type} [Fintype Ω] (P : FiniteLaw Ω)
    (score : Ω → ℚ) (label : Ω → Bool) (bin : ℚ) : ℚ :=
  expectation P (fun w => if score w = bin then (if label w then 1 else 0) else 0)

def calibrated {Ω : Type} [Fintype Ω] (P : FiniteLaw Ω)
    (score : Ω → ℚ) (label : Ω → Bool) : Prop :=
  ∀ bin, bucketSuccess P score label bin = bin * bucketMass P score bin

def groupRate {Ω : Type} [Fintype Ω] (P : FiniteLaw Ω)
    (group label : Ω → Bool) : Option ℚ :=
  let mass := expectation P (fun w => if group w then 1 else 0)
  if 0 < mass then
    some (expectation P (fun w => if group w then (if label w then 1 else 0) else 0) / mass)
  else none

def balancedAtoms : FiniteLaw Bool where
  mass := fun _ => 1/2
  nonneg := by intro w; norm_num
  total := by
    have univ : (Finset.univ : Finset Bool) = {false, true} := by decide
    norm_num [univ]

theorem q05_2_population_calibration_not_group_calibration :
    calibrated balancedAtoms (fun _ => 1/2) id ∧
      groupRate balancedAtoms id id = some 1 ∧
      groupRate balancedAtoms (fun w => !w) id = some 0 := by
  have univ : (Finset.univ : Finset Bool) = {false, true} := by decide
  refine ⟨?_, ?_, ?_⟩
  · intro bin
    by_cases same : (1/2 : ℚ) = bin
    · rw [← same]
      norm_num [bucketMass, bucketSuccess, expectation, balancedAtoms, univ]
    · simp [bucketMass, bucketSuccess, expectation, same]
  · norm_num [groupRate, expectation, balancedAtoms, univ]
  · norm_num [groupRate, expectation, balancedAtoms, univ]

theorem q05_1_normalized_score_not_calibrated :
    (∀ w : Bool, (0 : ℚ) ≤ (fun _ => 9/10) w ∧ (fun _ => (9/10 : ℚ)) w ≤ 1) ∧
      ¬ calibrated balancedAtoms (fun _ => 9/10) id := by
  have univ : (Finset.univ : Finset Bool) = {false, true} := by decide
  constructor
  · intro w
    norm_num
  · intro claim
    have impossible := claim (9/10)
    norm_num [bucketMass, bucketSuccess, expectation, balancedAtoms, univ] at impossible

def confidenceScore (w : Bool) : ℚ := if w then 1 else 1/2

theorem q05_3_higher_cutoff_can_raise_risk :
    groupRate balancedAtoms (fun w => decide ((1/2 : ℚ) ≤ confidenceScore w)) id = some (1/2) ∧
    groupRate balancedAtoms (fun w => decide ((1 : ℚ) ≤ confidenceScore w)) id = some 1 ∧
    expectation balancedAtoms (fun w => if (1/2 : ℚ) ≤ confidenceScore w then 1 else 0) = 1 ∧
    expectation balancedAtoms (fun w => if (1 : ℚ) ≤ confidenceScore w then 1 else 0) = 1/2 := by
  have univ : (Finset.univ : Finset Bool) = {false, true} := by decide
  norm_num [groupRate, expectation, balancedAtoms, confidenceScore, univ]

end JurisLean.Candidates.CalibrationSemantics20261027
