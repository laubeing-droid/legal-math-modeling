import JurisLean.Candidates.U05_1OriginalCalibrationInstances20261101
import JurisLean.Candidates.BernoulliMeanInstance20261031
import JurisLean.Candidates.LearningFiniteClass20261027

/-!
Frozen original05.2 L95/L97/L99 only. Reuse the admitted actual CE counterexample,
labelled atom law, and iid Bernoulli mean tail. Group sample sizes may differ;
no independence between groups is assumed. The confidence result estimates true
group success rates, not fitted-score calibration. The empirical-ECE counterexample
uses one observation and the same fairBoolLaw for sampling and population.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators
open JurisLean.Candidates.U04_1OriginalProbabilityInstances20261101
open JurisLean.Candidates.U05_1OriginalCalibrationInstances20261101
open JurisLean.Candidates.BernoulliMeanInstance20261031
open JurisLean.Candidates.LearningFiniteClass20261027

namespace JurisLean.Candidates.U05_2OriginalGroupCalibrationInstances20261101

private theorem fair_atom (b : Bool) : fairBoolLaw {b} = (1 / 2 : ENNReal) := by
  unfold fairBoolLaw
  rw [fixed_atom_measure_singleton]
  have hc : (((1 / 2 : ℚ) : ℝ)) = (1 / 2 : ℝ) := by norm_num
  rw [hc, ENNReal.ofReal_div_of_pos (by norm_num : 0 < (2 : ℝ))]
  norm_num

def scoreWithGroup (b : Bool) : ℝ × Bool := ((1 / 2 : ℝ), b)

private theorem score_group_information_full :
    MeasurableSpace.comap scoreWithGroup (inferInstance : MeasurableSpace (ℝ × Bool)) =
      (inferInstance : MeasurableSpace Bool) := by
  apply le_antisymm
  · have h : Measurable scoreWithGroup := measurable_const.prodMk measurable_id
    exact h.comap_le
  · have h : Measurable[MeasurableSpace.comap scoreWithGroup
        (inferInstance : MeasurableSpace (ℝ × Bool))] (id : Bool → Bool) :=
      (comap_measurable scoreWithGroup).snd
    exact fun s hs => h hs

/-- L95/L99 first level: actual score/group CE, both atoms and both group means. -/
theorem finite_population_calibration_not_group_calibration :
    (∀ b : Bool, fairBoolLaw {b} = (1 / 2 : ENNReal)) ∧
    (fairBoolLaw[fairLabel | MeasurableSpace.comap (fun _ : Bool => (1 / 2 : ℝ))
      (inferInstance : MeasurableSpace ℝ)] =ᵐ[fairBoolLaw] fun _ => (1 / 2 : ℝ)) ∧
    (fairBoolLaw[fairLabel | MeasurableSpace.comap scoreWithGroup
      (inferInstance : MeasurableSpace (ℝ × Bool))] = fairLabel) ∧
    ¬ (fairBoolLaw[fairLabel | MeasurableSpace.comap scoreWithGroup
      (inferInstance : MeasurableSpace (ℝ × Bool))]
        =ᵐ[fairBoolLaw] fun _ => (1 / 2 : ℝ)) := by
  have means : fairBoolLaw[fairLabel | MeasurableSpace.comap scoreWithGroup
      (inferInstance : MeasurableSpace (ℝ × Bool))] = fairLabel := by
    simpa only [score_group_information_full] using
      population_calibration_not_conditional_correctness.2.1
  have failure : ¬ (fairBoolLaw[fairLabel | MeasurableSpace.comap scoreWithGroup
      (inferInstance : MeasurableSpace (ℝ × Bool))]
        =ᵐ[fairBoolLaw] fun _ => (1 / 2 : ℝ)) := by
    simpa only [score_group_information_full] using
      population_calibration_not_conditional_correctness.2.2
  exact ⟨fair_atom, population_calibration_not_conditional_correctness.1, means, failure⟩

/-- L97: fixed groups and their own positive sample sizes. The admitted Bernoulli
mean theorem supplies each tail, including the actual observation-law/mean connection. -/
theorem fixed_groups_bernoulli_uniform_error
    {Ω : Type*} [MeasurableSpace Ω] {m : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (n : Fin m → ℕ) (hn : ∀ g, 0 < n g)
    (p : Fin m → ℝ) (hp0 : ∀ g, 0 ≤ p g) (hp1 : ∀ g, p g ≤ 1)
    (sample : (g : Fin m) → Fin (n g) → Ω → Bool)
    (sampleMeasurable : ∀ g i, Measurable (sample g i))
    (independent : ∀ g, iIndepFun (sample g) μ)
    (law : ∀ g i, IdentDistrib (sample g i) id μ
      (bernoulliMeasure (p g) (hp0 g) (hp1 g))
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    1 - δ ≤ μ.real {w | ∀ g : Fin m,
      |empiricalMean (fun i w => bitValue (sample g i w)) w - p g| ≤
        finiteRadius (n g) m δ} := by
  classical
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simpa using (show 1 - δ ≤ (1 : ℝ) by linarith)
  · have hmR : (1 : ℝ) ≤ m := by exact_mod_cast (Nat.succ_le_of_lt hm)
    have hmpos : (0 : ℝ) < m := by linarith
    have ratio : 1 < 2 * (m : ℝ) / δ := by
      apply (lt_div_iff₀ hδ).mpr
      nlinarith
    have logpos := Real.log_pos ratio
    have coefficient : (2 : ℝ) * (2 * (m : ℝ) / δ)⁻¹ = δ / (m : ℝ) := by
      field_simp [ne_of_gt hmpos, ne_of_gt hδ] <;> ring
    have rowBound (g : Fin m) :
        μ.real {w | finiteRadius (n g) m δ ≤
          |empiricalMean (fun i w => bitValue (sample g i w)) w - p g|} ≤
            δ / (m : ℝ) := by
      have hnR : (0 : ℝ) < n g := by exact_mod_cast (hn g)
      have radpos : 0 < finiteRadius (n g) m δ :=
        Real.sqrt_pos.mpr (div_pos logpos (by positivity))
      have radsq : (finiteRadius (n g) m δ) ^ 2 =
          Real.log (2 * (m : ℝ) / δ) / (2 * (n g : ℝ)) :=
        Real.sq_sqrt (le_of_lt (div_pos logpos (by positivity)))
      have exponent : -2 * (n g : ℝ) * (finiteRadius (n g) m δ) ^ 2 =
          -Real.log (2 * (m : ℝ) / δ) := by
        rw [radsq]
        field_simp [ne_of_gt hnR] <;> ring
      have bound := iid_bernoulli_mean_two_tail μ (hn g) (p g) (hp0 g) (hp1 g)
        (sample g) (independent g) (law g) (finiteRadius (n g) m δ) radpos
      rw [exponent, Real.exp_neg, Real.exp_log (lt_trans (by norm_num) ratio)] at bound
      rw [coefficient] at bound
      exact bound    have unionBound : μ.real (⋃ g : Fin m, {w | finiteRadius (n g) m δ ≤
        |empiricalMean (fun i w => bitValue (sample g i w)) w - p g|}) ≤ δ := by
      calc
        _ ≤ ∑ g : Fin m, μ.real {w | finiteRadius (n g) m δ ≤
            |empiricalMean (fun i w => bitValue (sample g i w)) w - p g|} := by
          simpa using measureReal_biUnion_finset_le (μ := μ) (Finset.univ : Finset (Fin m))
            (fun g => {w | finiteRadius (n g) m δ ≤
              |empiricalMean (fun i w => bitValue (sample g i w)) w - p g|})
        _ ≤ ∑ _g : Fin m, δ / (m : ℝ) :=
          Finset.sum_le_sum (fun g _ => rowBound g)
        _ = δ := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          field_simp [ne_of_gt hmpos] <;> ring
    have bitMeasurable : Measurable bitValue := by
      unfold bitValue
      fun_prop
    have deviation (g : Fin m) :
        Measurable (fun w => |empiricalMean (fun i w => bitValue (sample g i w)) w - p g|) := by
      have each : ∀ i, Measurable (fun w => bitValue (sample g i w)) :=
        fun i => bitMeasurable.comp (sampleMeasurable g i)
      unfold empiricalMean
      fun_prop
    have goodMeasurable : MeasurableSet {w | ∀ g : Fin m,
        |empiricalMean (fun i w => bitValue (sample g i w)) w - p g| ≤
          finiteRadius (n g) m δ} := by
      have h := (Finset.univ : Finset (Fin m)).measurableSet_biInter
        (f := fun g => {w | |empiricalMean (fun i w => bitValue (sample g i w)) w - p g| ≤
          finiteRadius (n g) m δ})
        (fun g _ => measurableSet_le (deviation g) measurable_const)
      convert h using 1 <;> ext w <;> simp
    have failure : {w | ∀ g : Fin m,
        |empiricalMean (fun i w => bitValue (sample g i w)) w - p g| ≤
          finiteRadius (n g) m δ}ᶜ ⊆
        ⋃ g : Fin m, {w | finiteRadius (n g) m δ ≤
          |empiricalMean (fun i w => bitValue (sample g i w)) w - p g|} := by
      intro w hw
      simp only [Set.mem_compl_iff, Set.mem_setOf_eq] at hw
      push_neg at hw
      obtain ⟨g, bad⟩ := hw
      simp only [Set.mem_iUnion, Set.mem_setOf_eq]
      exact ⟨g, le_of_lt bad⟩
    have failed := le_trans (measureReal_mono (μ := μ) failure (measure_ne_top μ _)) unionBound
    rw [measureReal_compl goodMeasurable] at failed
    have total : μ.real Set.univ = 1 := by simp
    rw [total] at failed
    linarith

/-- The standard empirical ECE for one fixed bin, one observation and forecast 1:
its bin weight is 1 and its empirical accuracy is the existing sample mean. -/
def oneSampleECE (b : Bool) : ℝ :=
  |empiricalMean (fun _ : Fin 1 => fairLabel) b - 1|

/-- L99 second level: zero empirical ECE has probability 1/2 under the same
population law, while the fixed forecast 1 is not population calibrated. -/
theorem zero_empirical_ece_not_population_calibration :
    (fairBoolLaw.real {b | oneSampleECE b = 0} = (1 / 2 : ℝ)) ∧
    ¬ (fairBoolLaw[fairLabel | MeasurableSpace.comap (fun _ : Bool => (1 : ℝ))
      (inferInstance : MeasurableSpace ℝ)] =ᵐ[fairBoolLaw] fun _ => (1 : ℝ)) := by
  have zeroEvent : {b : Bool | oneSampleECE b = 0} = {true} := by
    ext b
    cases b <;> norm_num [oneSampleECE, empiricalMean, fairLabel]
  have probability : fairBoolLaw.real {b | oneSampleECE b = 0} = (1 / 2 : ℝ) := by
    rw [zeroEvent]
    change (fairBoolLaw {true}).toReal = (1 / 2 : ℝ)
    rw [fair_atom true]
    norm_num
  have populationFailure : ¬ (fairBoolLaw[fairLabel |
      MeasurableSpace.comap (fun _ : Bool => (1 : ℝ))
        (inferInstance : MeasurableSpace ℝ)] =ᵐ[fairBoolLaw] fun _ => (1 : ℝ)) := by
    intro claimed
    have halfMean : fairBoolLaw[fairLabel |
        MeasurableSpace.comap (fun _ : Bool => (1 : ℝ))
          (inferInstance : MeasurableSpace ℝ)] =ᵐ[fairBoolLaw] fun _ => (1 / 2 : ℝ) := by
      simpa only [MeasurableSpace.comap_const] using
        population_calibration_not_conditional_correctness.1
    have mismatch := halfMean.symm.trans claimed
    obtain ⟨b, hb⟩ := mismatch.exists
    norm_num at hb
  exact ⟨probability, populationFailure⟩

end JurisLean.Candidates.U05_2OriginalGroupCalibrationInstances20261101