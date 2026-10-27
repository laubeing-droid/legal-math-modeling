import JurisLean.Candidates.ProtectedFeedback20261027
import Mathlib.Probability.ConditionalProbability
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
Original 15.2/15.3 and correction S15. A finite visible history fixes each
round's candidate class, budget, sample count and decision to continue.
The conditional laws below are actual restrictions of one common measure.
They are explicit sampling premises, not facts inferred from IDs or scores.
-/

namespace JurisLean.Candidates.AdaptiveValidation20261027

open MeasureTheory ProbabilityTheory
open JurisLean.Candidates.LearningFiniteClass20261027
open JurisLean.Candidates.ProtectedFeedback20261027
open JurisLean.Candidates.LearningERM20261027

noncomputable section

def historyCell {Ω H : Type*} (history : Ω → H) (h : H) : Set Ω :=
  {w | history w = h}

theorem conditional_event_mass {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (cell bad : Set Ω)
    (measurable : MeasurableSet cell) :
    μ.real (cell ∩ bad) = μ.real cell * (μ[|cell]).real bad := by
  have h := congrArg ENNReal.toReal (cond_mul_eq_inter measurable bad μ)
  simpa only [ENNReal.toReal_mul, Measure.real, mul_comm] using h.symm

-- A history-dependent continuation mask includes any predictable finite
-- stopping rule. No independence between rounds is assumed.
theorem predictable_failure_budget {Ω H T : Type*} [MeasurableSpace Ω]
    [Fintype H] [Fintype T] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (history : T → Ω → H)
    (cells : ∀ t h, MeasurableSet (historyCell (history t) h))
    (active : T → H → Bool) (bad : T → H → Set Ω) (delta : T → H → ℝ)
    (conditional : ∀ t h, μ (historyCell (history t) h) ≠ 0 →
      (μ[|historyCell (history t) h]).real (bad t h) ≤ delta t h) :
    μ.real {w | ∃ t, active t (history t w) = true ∧ w ∈ bad t (history t w)} ≤
      ∑ t, ∑ h, if active t h then μ.real (historyCell (history t) h) * delta t h else 0 := by
  classical
  let pieces (t : T) (h : H) : Set Ω :=
    if active t h then historyCell (history t) h ∩ bad t h else ∅
  have included :
      {w | ∃ t, active t (history t w) = true ∧ w ∈ bad t (history t w)} ⊆
        ⋃ t, ⋃ h, pieces t h := by
    rintro w ⟨t, enabled, failed⟩
    exact Set.mem_iUnion.mpr ⟨t, Set.mem_iUnion.mpr
      ⟨history t w, by simp [pieces, enabled, historyCell, failed]⟩⟩
  have pieceBound (t : T) (h : H) :
      μ.real (pieces t h) ≤
        if active t h then μ.real (historyCell (history t) h) * delta t h else 0 := by
    by_cases enabled : active t h = true
    · simp only [pieces, enabled, ↓reduceIte]
      by_cases zero : μ (historyCell (history t) h) = 0
      · have z : μ (historyCell (history t) h ∩ bad t h) = 0 :=
          measure_mono_null Set.inter_subset_left zero
        simp [Measure.real, z, zero]
      · rw [conditional_event_mass μ _ _ (cells t h)]
        exact mul_le_mul_of_nonneg_left (conditional t h zero) (by positivity)
    · simp [pieces, enabled]
  calc
    _ ≤ μ.real (⋃ t, ⋃ h, pieces t h) := measureReal_mono (μ := μ) included
    _ ≤ ∑ t, μ.real (⋃ h, pieces t h) := measureReal_iUnion_fintype_le _
    _ ≤ ∑ t, ∑ h, μ.real (pieces t h) :=
      Finset.sum_le_sum fun t _ => measureReal_iUnion_fintype_le _
    _ ≤ _ := Finset.sum_le_sum fun t _ => Finset.sum_le_sum fun h _ => pieceBound t h

theorem history_budget_is_expected_spend {Ω H T : Type*} [MeasurableSpace Ω]
    [Fintype H] [Fintype T] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (history : T → Ω → H)
    (cells : ∀ t h, MeasurableSet (historyCell (history t) h))
    (active : T → H → Bool) (delta : T → H → ℝ) :
    (∫ w, ∑ t, if active t (history t w) then delta t (history t w) else 0 ∂μ) =
      ∑ t, ∑ h, if active t h then μ.real (historyCell (history t) h) * delta t h else 0 := by
  classical
  let term (t : T) (h : H) : Ω → ℝ :=
    (historyCell (history t) h).indicator (fun _ => if active t h then delta t h else 0)
  have integrable (t : T) (h : H) : Integrable (term t h) μ :=
    (integrable_const _).indicator (cells t h)
  have expansion (w : Ω) :
      (∑ t, if active t (history t w) then delta t (history t w) else 0) =
        ∑ t, ∑ h, term t h w := by
    apply Finset.sum_congr rfl
    intro t _
    symm
    calc
      (∑ h, term t h w) = term t (history t w) w := by
        apply Finset.sum_eq_single (history t w)
        · intro h _ different
          have reversed : history t w ≠ h := Ne.symm different
          simp [term, historyCell, Set.indicator, reversed]
        · intro absent
          exact (absent (Finset.mem_univ _)).elim
      _ = _ := by simp [term, historyCell, Set.indicator]
  calc
    _ = ∫ w, ∑ t, ∑ h, term t h w ∂μ :=
      integral_congr_ae (Filter.Eventually.of_forall expansion)
    _ = ∑ t, ∫ w, ∑ h, term t h w ∂μ :=
      integral_finsetSum _ (fun t _ => integrable_finsetSum _ (fun h _ => integrable t h))
    _ = ∑ t, ∑ h, ∫ w, term t h w ∂μ := by
      apply Finset.sum_congr rfl
      intro t _
      exact integral_finsetSum _ (fun h _ => integrable t h)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro t _
      apply Finset.sum_congr rfl
      intro h _
      dsimp [term]
      rw [integral_indicator (cells t h)]
      by_cases enabled : active t h = true <;>
        simp [enabled, setIntegral_const, smul_eq_mul]

theorem predictable_failure_expected_budget {Ω H T : Type*} [MeasurableSpace Ω]
    [Fintype H] [Fintype T] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (history : T → Ω → H)
    (cells : ∀ t h, MeasurableSet (historyCell (history t) h))
    (active : T → H → Bool) (bad : T → H → Set Ω) (delta : T → H → ℝ)
    (conditional : ∀ t h, μ (historyCell (history t) h) ≠ 0 →
      (μ[|historyCell (history t) h]).real (bad t h) ≤ delta t h) :
    μ.real {w | ∃ t, active t (history t w) = true ∧ w ∈ bad t (history t w)} ≤
      ∫ w, ∑ t, if active t (history t w) then delta t (history t w) else 0 ∂μ := by
  rw [history_budget_is_expected_spend μ history cells active delta]
  exact predictable_failure_budget μ history cells active bad delta conditional

-- Candidates and sample counts may vary with the PRE-sample visible history.
-- Within each positive-mass history atom, iid laws derive the conditional
-- guarantee; a candidate's self-reported delta is not used as such a guarantee.
theorem fresh_iid_history_budget {Ω Z H K T : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Z] [Fintype H] [Fintype T]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (P : Measure Z) [IsProbabilityMeasure P]
    (history : T → Ω → H)
    (cells : ∀ t h, MeasurableSet (historyCell (history t) h))
    (active : T → H → Bool)
    (n : T → H → ℕ) (positive : ∀ t h, 0 < n t h)
    (models : T → H → Finset K) (nonempty : ∀ t h, (models t h).Nonempty)
    (sample : (t : T) → (h : H) → Fin (n t h) → Ω → Z)
    (measurable : ∀ t h i, Measurable (sample t h i))
    (independent : ∀ t h, μ (historyCell (history t) h) ≠ 0 →
      iIndepFun (sample t h) (μ[|historyCell (history t) h]))
    (law : ∀ t h, μ (historyCell (history t) h) ≠ 0 → ∀ i,
      IdentDistrib (sample t h i) id (μ[|historyCell (history t) h]) P)
    (loss : K → Z → ℚ)
    (lossMeasurable : ∀ t h k, k ∈ models t h → Measurable (fun z => (loss k z : ℝ)))
    (bounded : ∀ t h k, k ∈ models t h → ∀ z, (loss k z : ℝ) ∈ Set.Icc (0 : ℝ) 1)
    (delta : T → H → ℝ)
    (deltaPositive : ∀ t h, 0 < delta t h) (deltaBelowOne : ∀ t h, delta t h < 1) :
    μ.real {w | ∃ t, active t (history t w) = true ∧
      ¬ ∀ k ∈ models t (history t w),
        |(empiricalScore loss (fun i => sample t (history t w) i w) k : ℝ) -
          ∫ z, (loss k z : ℝ) ∂P| ≤
            finiteRadius (n t (history t w)) (models t (history t w)).card (delta t (history t w))} ≤
      ∫ w, ∑ t, if active t (history t w) then delta t (history t w) else 0 ∂μ := by
  classical
  let good (t : T) (h : H) : Set Ω := {w | ∀ k ∈ models t h,
    |(empiricalScore loss (fun i => sample t h i w) k : ℝ) - ∫ z, (loss k z : ℝ) ∂P| ≤
      finiteRadius (n t h) (models t h).card (delta t h)}
  apply predictable_failure_expected_budget μ history cells active
    (fun t h => (good t h)ᶜ) delta
  intro t h massPositive
  letI : IsProbabilityMeasure (μ[|historyCell (history t) h]) :=
    cond_isProbabilityMeasure massPositive
  have joint := protected_iid_joint_event (μ[|historyCell (history t) h])
    (fun _ : Unit => P) (fun _ => n t h) (fun _ => positive t h)
    (models t h) (nonempty t h) (fun _ => sample t h)
    (fun _ => measurable t h) (fun _ => independent t h massPositive)
    (fun _ => law t h massPositive) loss (lossMeasurable t h) (bounded t h)
    (fun _ => delta t h) (fun _ => deltaPositive t h) (fun _ => deltaBelowOne t h)
  have result : MeasurableSet (good t h) ∧
      1 - delta t h ≤ (μ[|historyCell (history t) h]).real (good t h) := by
    simpa [good] using joint
  rw [measureReal_compl result.1]
  have total : (μ[|historyCell (history t) h]).real Set.univ = 1 := by simp
  rw [total]
  linarith [result.2]

theorem sample_count_covers_radius (n M : ℕ) (positive : 0 < n)
    (delta epsilon : ℝ) (epsilonPositive : 0 < epsilon)
    (enough : Real.log (2 * (M : ℝ) / delta) / (2 * epsilon ^ 2) ≤ n) :
    finiteRadius n M delta ≤ epsilon := by
  have hn : (0 : ℝ) < n := by exact_mod_cast positive
  have cost : Real.log (2 * (M : ℝ) / delta) ≤ (n : ℝ) * (2 * epsilon ^ 2) :=
    (div_le_iff₀ (by positivity : 0 < 2 * epsilon ^ 2)).mp enough
  apply Real.sqrt_le_iff.mpr
  refine ⟨le_of_lt epsilonPositive, ?_⟩
  apply (div_le_iff₀ (by positivity : 0 < 2 * (n : ℝ))).mpr
  nlinarith

end

-- The learner only receives probe scores, not the validation-set membership.
def zeroLabelValidationScore {N : Nat} (points : Finset (Fin N))
    (prediction : Fin N → Bool) : ℚ :=
  (∑ x ∈ points, if prediction x then 1 else 0) / (points.card : ℚ)

def probeScores {N : Nat} (points : Finset (Fin N)) (x : Fin N) : ℚ :=
  zeroLabelValidationScore points (fun y => decide (y = x))

def fromProbeScores {N : Nat} (scores : Fin N → ℚ) (x : Fin N) : Bool :=
  decide (scores x = 0)

def uniformZeroRisk {N : Nat} (prediction : Fin N → Bool) : ℚ :=
  (∑ x, if prediction x then 1 else 0) / (N : ℚ)

theorem probe_score_reveals_membership {N : Nat} (points : Finset (Fin N)) (x : Fin N) :
    probeScores points x = if x ∈ points then (1 : ℚ) / points.card else 0 := by
  classical
  by_cases inside : x ∈ points <;> simp [probeScores, zeroLabelValidationScore, inside]

theorem feedback_model_eq_unseen {N : Nat} (points : Finset (Fin N))
    (nonempty : points.Nonempty) (x : Fin N) :
    fromProbeScores (probeScores points) x = decide (x ∉ points) := by
  have nonzero : (points.card : ℚ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Finset.card_pos.mpr nonempty))
  by_cases inside : x ∈ points <;>
    simp [fromProbeScores, probe_score_reveals_membership, inside, nonzero]

theorem feedback_model_zero_validation {N : Nat} (points : Finset (Fin N))
    (nonempty : points.Nonempty) :
    zeroLabelValidationScore points (fromProbeScores (probeScores points)) = 0 := by
  simp only [zeroLabelValidationScore]
  have total : (∑ x ∈ points, if fromProbeScores (probeScores points) x then (1 : ℚ) else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro x hx
    simp [feedback_model_eq_unseen points nonempty x, hx]
  rw [total]
  simp

theorem feedback_model_population_risk {N : Nat} (positive : 0 < N)
    (points : Finset (Fin N)) (nonempty : points.Nonempty) :
    uniformZeroRisk (fromProbeScores (probeScores points)) = 1 - (points.card : ℚ) / N := by
  classical
  have hn : (N : ℚ) ≠ 0 := by exact_mod_cast ne_of_gt positive
  have partition : (∑ x : Fin N, if x ∈ points then (1 : ℚ) else 0) +
      (∑ x : Fin N, if x ∉ points then (1 : ℚ) else 0) = N := by
    rw [← Finset.sum_add_distrib]
    calc
      _ = ∑ _x : Fin N, (1 : ℚ) := by
        apply Finset.sum_congr rfl
        intro x _
        by_cases inside : x ∈ points <;> simp [inside]
      _ = _ := by simp
  have seen : (∑ x : Fin N, if x ∈ points then (1 : ℚ) else 0) = points.card := by simp
  rw [seen] at partition
  have missing : (∑ x : Fin N, if x ∉ points then (1 : ℚ) else 0) =
      (N : ℚ) - points.card := by linarith
  simp only [uniformZeroRisk, feedback_model_eq_unseen points nonempty, decide_eq_true_eq]
  rw [missing]
  field_simp
  <;> ring

theorem feedback_model_large_population_risk {N n : Nat} (positive : 0 < N)
    (points : Finset (Fin N)) (nonempty : points.Nonempty) (atMost : points.card ≤ n) :
    1 - (n : ℚ) / N ≤ uniformZeroRisk (fromProbeScores (probeScores points)) := by
  rw [feedback_model_population_risk positive points nonempty]
  have counts : (points.card : ℚ) ≤ n := by exact_mod_cast atMost
  have fractions := div_le_div_of_nonneg_right counts (by positivity : (0 : ℚ) ≤ N)
  linarith

def fourPointFailureMass (bad : Fin 4 → Bool) : ℚ :=
  ∑ w, if bad w then 1 / 4 else 0

theorem three_failure_events_not_independent_formula :
    (∀ i : Fin 3, fourPointFailureMass (fun w => decide (w.val = i.val)) = 1 / 4) ∧
      fourPointFailureMass (fun w => decide (w.val < 3)) = 3 / 4 ∧
      (1 - (1 - (1 / 4 : ℚ)) ^ 3) = 37 / 64 ∧
      (37 / 64 : ℚ) < 3 / 4 := by
  constructor
  · intro i
    fin_cases i <;> norm_num [fourPointFailureMass, Fin.sum_univ_succ]
  · norm_num [fourPointFailureMass, Fin.sum_univ_succ]

end JurisLean.Candidates.AdaptiveValidation20261027
