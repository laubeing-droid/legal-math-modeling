import JurisLean.Candidates.LearningRisk20261027
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.Layercake

namespace JurisLean.Candidates.LearningBridge20261027

open MeasureTheory Set

noncomputable section

theorem integrable_unit_interval {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (f : Ω → ℝ)
    (measurable : Measurable f) (range : ∀ w, f w ∈ Icc (0 : ℝ) 1) :
    Integrable f μ := by
  apply (integrable_const (1 : ℝ)).mono' measurable.aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun w => by
    simpa [Real.norm_eq_abs, abs_of_nonneg (range w).1] using (range w).2)

-- No independence between predictions, recorded labels and target labels is used.
theorem u01_2_classification_label_bridge {Ω A : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (prediction label target : Ω → A) :
    μ.real {w | prediction w ≠ target w} ≤
      μ.real {w | prediction w ≠ label w} + μ.real {w | label w ≠ target w} := by
  have included : {w | prediction w ≠ target w} ⊆
      {w | prediction w ≠ label w} ∪ {w | label w ≠ target w} := by
    intro w hw
    by_cases hp : prediction w = label w
    · exact Or.inr (fun ht => hw (hp.trans ht))
    · exact Or.inl hp
  exact (measureReal_mono (μ := μ) included).trans (measureReal_union_le _ _)

theorem u01_2_same_bounded_loss_label_bridge {Ω A B : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (prediction : Ω → A) (label target : Ω → B) (loss : A → B → ℝ)
    (range : ∀ a b, loss a b ∈ Icc (0 : ℝ) 1)
    (labelMeasurable : Measurable (fun w => loss (prediction w) (label w)))
    (targetMeasurable : Measurable (fun w => loss (prediction w) (target w)))
    (disagreementMeasurable : MeasurableSet {w | label w ≠ target w}) :
    (∫ w, loss (prediction w) (target w) ∂μ) ≤
      (∫ w, loss (prediction w) (label w) ∂μ) + μ.real {w | label w ≠ target w} := by
  classical
  let mismatch : Ω → ℝ := {w | label w ≠ target w}.indicator (fun _ => 1)
  have mismatchInt : Integrable mismatch μ :=
    (integrable_const (1 : ℝ)).indicator disagreementMeasurable
  have labelInt := integrable_unit_interval μ _ labelMeasurable
    (fun w => range (prediction w) (label w))
  have targetInt := integrable_unit_interval μ _ targetMeasurable
    (fun w => range (prediction w) (target w))
  have pointwise (w : Ω) : loss (prediction w) (target w) ≤
      loss (prediction w) (label w) + mismatch w := by
    by_cases heq : label w = target w
    · simp [mismatch, heq]
    · have ht := (range (prediction w) (target w)).2
      have hl := (range (prediction w) (label w)).1
      have hm : mismatch w = 1 := by simp [mismatch, Set.indicator, heq]
      rw [hm]
      linarith
  have bound := integral_mono targetInt (labelInt.add mismatchInt) pointwise
  rw [integral_add' labelInt mismatchInt] at bound
  simpa [mismatch, integral_indicator_one disagreementMeasurable] using bound

-- A valid bridge upper bound has its own failure budget. These bounds may be
-- dependent; the union bound pays for both events without an independence claim.
theorem u01_2_joint_failure_budget {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (targetRisk labelRisk bridge labelUpper bridgeUpper : Ω → ℝ)
    (bridgeValid : ∀ w, targetRisk w ≤ labelRisk w + bridge w)
    (δlabel δbridge : ℝ)
    (labelFailure : μ.real {w | labelUpper w < labelRisk w} ≤ δlabel)
    (bridgeFailure : μ.real {w | bridgeUpper w < bridge w} ≤ δbridge) :
    μ.real {w | labelUpper w + bridgeUpper w < targetRisk w} ≤ δlabel + δbridge := by
  have included : {w | labelUpper w + bridgeUpper w < targetRisk w} ⊆
      {w | labelUpper w < labelRisk w} ∪ {w | bridgeUpper w < bridge w} := by
    intro w hw
    by_cases hl : labelUpper w < labelRisk w
    · exact Or.inl hl
    · right
      have valid := bridgeValid w
      dsimp at hw ⊢
      linarith
  exact (measureReal_mono (μ := μ) included).trans
    ((measureReal_union_le _ _).trans (add_le_add labelFailure bridgeFailure))

-- TV is the supremum of measurable EVENT differences on the complete joint
-- task space. It is not defined using the risk inequality that we must prove.
def jointTotalVariation {Ω : Type*} [MeasurableSpace Ω] (P Q : Measure Ω) : ℝ :=
  sSup {r | ∃ s : Set Ω, MeasurableSet s ∧ r = |P.real s - Q.real s|}

theorem event_distance_le_one {Ω : Type*} [MeasurableSpace Ω]
    (P Q : Measure Ω) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (s : Set Ω) :
    |P.real s - Q.real s| ≤ 1 := by
  have hp : P.real s ≤ 1 := by simpa using measureReal_mono (μ := P) (subset_univ s)
  have hq : Q.real s ≤ 1 := by simpa using measureReal_mono (μ := Q) (subset_univ s)
  have hp0 : 0 ≤ P.real s := by positivity
  have hq0 : 0 ≤ Q.real s := by positivity
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem event_distance_le_tv {Ω : Type*} [MeasurableSpace Ω]
    (P Q : Measure Ω) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (s : Set Ω) (hs : MeasurableSet s) :
    |P.real s - Q.real s| ≤ jointTotalVariation P Q := by
  apply le_csSup (s := {r | ∃ s : Set Ω, MeasurableSet s ∧ r = |P.real s - Q.real s|})
  · refine ⟨1, ?_⟩
    rintro _ ⟨s, _, rfl⟩
    exact event_distance_le_one P Q s
  · exact ⟨s, hs, rfl⟩

theorem u01_3_same_bounded_loss_tv {Ω : Type*} [MeasurableSpace Ω]
    (P Q : Measure Ω) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (f : Ω → ℝ) (measurable : Measurable f) (range : ∀ w, f w ∈ Icc (0 : ℝ) 1) :
    |(∫ w, f w ∂P) - ∫ w, f w ∂Q| ≤ jointTotalVariation P Q := by
  let p : ℝ → ℝ := fun t => P.real {w | t ≤ f w}
  let q : ℝ → ℝ := fun t => Q.real {w | t ≤ f w}
  have pMeasurable : Measurable p := by
    apply Antitone.measurable
    intro s t hst
    exact measureReal_mono (fun w hw => le_trans hst hw)
  have qMeasurable : Measurable q := by
    apply Antitone.measurable
    intro s t hst
    exact measureReal_mono (fun w hw => le_trans hst hw)
  have pRange (t : ℝ) : p t ∈ Icc (0 : ℝ) 1 := by
    refine ⟨by positivity, ?_⟩
    simpa [p] using measureReal_mono (μ := P) (subset_univ {w | t ≤ f w})
  have qRange (t : ℝ) : q t ∈ Icc (0 : ℝ) 1 := by
    refine ⟨by positivity, ?_⟩
    simpa [q] using measureReal_mono (μ := Q) (subset_univ {w | t ≤ f w})
  have pInt := integrable_unit_interval (volume.restrict (Ioc (0 : ℝ) 1)) p pMeasurable pRange
  have qInt := integrable_unit_interval (volume.restrict (Ioc (0 : ℝ) 1)) q qMeasurable qRange
  have pLayer := (integrable_unit_interval P f measurable range).integral_eq_integral_Ioc_meas_le
    (Filter.Eventually.of_forall (fun w => (range w).1))
    (Filter.Eventually.of_forall (fun w => (range w).2))
  have qLayer := (integrable_unit_interval Q f measurable range).integral_eq_integral_Ioc_meas_le
    (Filter.Eventually.of_forall (fun w => (range w).1))
    (Filter.Eventually.of_forall (fun w => (range w).2))
  have eventBound (t : ℝ) : |p t - q t| ≤ jointTotalVariation P Q :=
    event_distance_le_tv P Q _ (measurableSet_le measurable_const measurable)
  have upper := integral_mono pInt (qInt.add (integrable_const (jointTotalVariation P Q)))
    (fun t => by
      change p t ≤ q t + jointTotalVariation P Q
      have h := (abs_le.mp (eventBound t)).2
      linarith)
  have lower := integral_mono qInt (pInt.add (integrable_const (jointTotalVariation P Q)))
    (fun t => by
      change q t ≤ p t + jointTotalVariation P Q
      have h := (abs_le.mp (eventBound t)).1
      linarith)
  rw [integral_add' qInt (integrable_const _)] at upper
  rw [integral_add' pInt (integrable_const _)] at lower
  have constant : (∫ _t in Ioc (0 : ℝ) 1, jointTotalVariation P Q) = jointTotalVariation P Q := by
    simp
  rw [constant] at upper lower
  change (∫ t in Ioc (0 : ℝ) 1, P.real {w | t ≤ f w}) ≤
    (∫ t in Ioc (0 : ℝ) 1, Q.real {w | t ≤ f w}) + jointTotalVariation P Q at upper
  change (∫ t in Ioc (0 : ℝ) 1, Q.real {w | t ≤ f w}) ≤
    (∫ t in Ioc (0 : ℝ) 1, P.real {w | t ≤ f w}) + jointTotalVariation P Q at lower
  rw [← pLayer, ← qLayer] at upper lower
  exact abs_le.mpr ⟨by linarith, by linarith⟩

-- The same deterministic event supremum controls every member of any class;
-- selecting a member does not introduce a statistical union bound here.
theorem u01_3_all_models_tv {Ω H : Type*} [MeasurableSpace Ω]
    (P Q : Measure Ω) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (loss : H → Ω → ℝ) (measurable : ∀ h, Measurable (loss h))
    (range : ∀ h w, loss h w ∈ Icc (0 : ℝ) 1) :
    ∀ h, |(∫ w, loss h w ∂P) - ∫ w, loss h w ∂Q| ≤ jointTotalVariation P Q := by
  intro h
  exact u01_3_same_bounded_loss_tv P Q (loss h) (measurable h) (range h)

end
end JurisLean.Candidates.LearningBridge20261027

#print axioms JurisLean.Candidates.LearningBridge20261027.u01_2_classification_label_bridge
#print axioms JurisLean.Candidates.LearningBridge20261027.u01_2_same_bounded_loss_label_bridge
#print axioms JurisLean.Candidates.LearningBridge20261027.u01_2_joint_failure_budget
#print axioms JurisLean.Candidates.LearningBridge20261027.u01_3_same_bounded_loss_tv
#print axioms JurisLean.Candidates.LearningBridge20261027.u01_3_all_models_tv
