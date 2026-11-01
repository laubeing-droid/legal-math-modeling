import JurisLean.Candidates.SelectiveCalibration20261027
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic

/-!
Original 05.3 L103/L105/L107: retain real bounded losses, identify actual
acceptance mass, prove the true conditional-error ordering condition, and
connect the existing real IID uniform bound to the existing rational selector.
Rational empirical enclosures are explicit numerical certificates, not assumed
population-risk bounds. No exact comparison of arbitrary reals is claimed.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal

namespace JurisLean.Candidates.U05_3OriginalSelectiveRiskInstances20261101
open LearningFiniteClass20261027 SelectiveCalibration20261027

/-- `true` labels the loss numerator; `false` labels coverage. -/
def thresholdStatistic {Z H : Type*} (loss score : Z → ℝ)
    (cutoff : H → ℝ) (p : H × Bool) (z : Z) : ℝ :=
  if cutoff p.1 ≤ score z then (if p.2 then loss z else 1) else 0

private theorem unit_integrable {Z : Type*} [MeasurableSpace Z]
    (P : Measure Z) [IsProbabilityMeasure P] (f : Z → ℝ)
    (hf : Measurable f) (hr : ∀ z, f z ∈ Set.Icc (0 : ℝ) 1) : Integrable f P := by
  have hL2 : MemLp f 2 P := MemLp.of_bound hf.aestronglyMeasurable 1 <| by
    exact Filter.Eventually.of_forall (fun z => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hr z).1]
      exact (hr z).2)
  exact hL2.integrable one_le_two

/-- These are the original population numerator and probability of acceptance. -/
theorem threshold_population_quantities {Z : Type*} [MeasurableSpace Z]
    (P : Measure Z) (loss score : Z → ℝ) (hs : Measurable score) (t : ℝ) :
    (∫ z, thresholdStatistic loss score id (t, false) z ∂P) =
        P.real {z | t ≤ score z} ∧
    (∫ z, thresholdStatistic loss score id (t, true) z ∂P) =
        ∫ z in {z | t ≤ score z}, loss z ∂P := by
  have hA : MeasurableSet {z | t ≤ score z} := measurableSet_le measurable_const hs
  constructor
  · simpa [thresholdStatistic, Set.indicator, smul_eq_mul] using
      (integral_indicator_const (μ := P) (1 : ℝ) hA)
  · simpa [thresholdStatistic, Set.indicator] using
      (integral_indicator (μ := P) (f := loss) hA)

/-- The sufficient condition concerns the actual conditional error, not a name
attached to a model confidence score. It compares the two given thresholds. -/
theorem true_conditional_error_ordering {Z : Type*} [mZ : MeasurableSpace Z]
    (P : Measure Z) [IsProbabilityMeasure P] (loss score : Z → ℝ)
    (hl : Measurable loss) (hs : Measurable score)
    (lossRange : ∀ z, loss z ∈ Set.Icc (0 : ℝ) 1)
    (curve : ℝ → ℝ) (ordered : Antitone curve)
    (actual : P[loss | MeasurableSpace.comap score (inferInstance : MeasurableSpace ℝ)]
      =ᵐ[P] fun z => curve (score z))
    (low high : ℝ) (lh : low ≤ high)
    (positive : 0 < P.real {z | high ≤ score z}) :
    0 < P.real {z | low ≤ score z} ∧
      (∫ z in {z | high ≤ score z}, loss z ∂P) / P.real {z | high ≤ score z} ≤
      (∫ z in {z | low ≤ score z}, loss z ∂P) / P.real {z | low ≤ score z} := by
  let mS := MeasurableSpace.comap score (inferInstance : MeasurableSpace ℝ)
  have hm : mS ≤ mZ := hs.comap_le
  have hsS : Measurable[mS] score := comap_measurable score
  have hlInt : Integrable loss P := unit_integrable P loss hl lossRange
  have hEta : Integrable (fun z => curve (score z)) P :=
    (integrable_condExp (μ := P) (f := loss) (m := mS)).congr actual
  let A : Set Z := {z | low ≤ score z}
  let B : Set Z := {z | high ≤ score z}
  let D : Set Z := A \ B
  have hAm : MeasurableSet[mS] A := measurableSet_le measurable_const hsS
  have hBm : MeasurableSet[mS] B := measurableSet_le measurable_const hsS
  have hA : MeasurableSet A := hAm.mono hm
  have hB : MeasurableSet B := hBm.mono hm
  have hD : MeasurableSet D := hA.diff hB
  have hBA : B ⊆ A := fun z hz => le_trans lh hz
  have disj : Disjoint B D := Set.disjoint_left.2 (by
    intro z hzB hzD
    exact hzD.2 hzB)
  have union_eq : B ∪ D = A := by
    ext z
    constructor
    · intro hz
      rcases hz with hz | hz
      · exact hBA hz
      · exact hz.1
    · intro hz
      by_cases hzB : z ∈ B
      · exact Or.inl hzB
      · exact Or.inr ⟨hz, hzB⟩
  have integrals_eq (s : Set Z) (hsm : MeasurableSet[mS] s) :
      (∫ z in s, loss z ∂P) = ∫ z in s, curve (score z) ∂P := by
    calc
      (∫ z in s, loss z ∂P) = ∫ z in s, P[loss | mS] z ∂P :=
        (setIntegral_condExp hm hlInt hsm).symm
      _ = ∫ z in s, curve (score z) ∂P := by
        apply setIntegral_congr_ae (hsm.mono hm)
        filter_upwards [actual] with z hz
        exact fun _ => hz
  have split : (∫ z in A, curve (score z) ∂P) =
      (∫ z in B, curve (score z) ∂P) + ∫ z in D, curve (score z) ∂P := by
    rw [← union_eq]
    exact setIntegral_union disj hD hEta.integrableOn hEta.integrableOn
  have mass : P.real A = P.real B + P.real D := by
    calc
      P.real A = ∫ _ in A, (1 : ℝ) ∂P := by simp
      _ = (∫ _ in B, (1 : ℝ) ∂P) + ∫ _ in D, (1 : ℝ) ∂P := by
        rw [← union_eq]
        exact setIntegral_union disj hD (integrable_const 1).integrableOn
          (integrable_const 1).integrableOn
      _ = P.real B + P.real D := by simp
  have dnonneg : 0 ≤ P.real D := ENNReal.toReal_nonneg
  have lowPositive : 0 < P.real A := by linarith [positive, mass]
  have highBound : (∫ z in B, curve (score z) ∂P) ≤ curve high * P.real B := by
    calc
      _ ≤ ∫ _ in B, curve high ∂P :=
        setIntegral_mono_on hEta.integrableOn (integrable_const (curve high)).integrableOn
          hB (fun z hz => ordered hz)
      _ = curve high * P.real B := by simp [mul_comm]
  have removedBound : curve high * P.real D ≤ ∫ z in D, curve (score z) ∂P := by
    calc
      curve high * P.real D = ∫ _ in D, curve high ∂P := by simp [mul_comm]
      _ ≤ ∫ z in D, curve (score z) ∂P :=
        setIntegral_mono_on (integrable_const (curve high)).integrableOn hEta.integrableOn
          hD (fun z hz => ordered (le_of_lt (lt_of_not_ge hz.2)))
  have cross : (∫ z in B, curve (score z) ∂P) * P.real D ≤
      (∫ z in D, curve (score z) ∂P) * P.real B := by
    calc
      _ ≤ (curve high * P.real B) * P.real D :=
        mul_le_mul_of_nonneg_right highBound dnonneg
      _ = (curve high * P.real D) * P.real B := by ring
      _ ≤ (∫ z in D, curve (score z) ∂P) * P.real B :=
        mul_le_mul_of_nonneg_right removedBound (le_of_lt positive)
  refine ⟨lowPositive, ?_⟩
  rw [integrals_eq B hBm, integrals_eq A hAm]
  apply (div_le_div_iff₀ positive lowPositive).mpr
  rw [split, mass]
  nlinarith [cross]

/-- These are numerical interval operations over rational certificate data. -/
def clippedLower (q radius : ℚ) : ℚ := max 0 (q - radius)
def clippedUpper (q radius : ℚ) : ℚ := min 1 (q + radius)

/-- Reuse the existing selector; min(lower, numeratorUpper)/lower is exactly
min(1,numeratorUpper/lower) whenever the lower coverage is positive. -/
def certificateChoice {H : Type*} (candidates : List H) (lo hi : Bool → H → ℚ)
    (radius target : ℚ) : Option H :=
  selectPassing (fun h => clippedLower (lo false h) radius)
    (fun h => min (clippedLower (lo false h) radius) (clippedUpper (hi true h) radius))
    target candidates

private theorem capped_quotient (l u : ℚ) (hl : 0 < l) :
    min l u / l = min 1 (u / l) := by
  by_cases h : l ≤ u
  · rw [min_eq_left h, div_self (ne_of_gt hl)]
    rw [min_eq_left ((le_div_iff₀ hl).mpr (by simpa using h))]
  · have hu : u ≤ l := le_of_not_ge h
    rw [min_eq_right hu, min_eq_right ((div_le_iff₀ hl).mpr (by simpa using hu))]

private theorem capped_gate_iff (l u target : ℚ) :
    (0 < l ∧ min l u / l ≤ target) ↔ (0 < l ∧ min 1 (u / l) ≤ target) := by
  constructor <;> rintro ⟨hl, hg⟩ <;> refine ⟨hl, ?_⟩
  · simpa only [capped_quotient l u hl] using hg
  · simpa only [capped_quotient l u hl] using hg

/-- No passing certificate is an absence of recommendation, not a population
risk lower bound or proof that all true risks exceed target. -/
theorem certificateChoice_none_iff {H : Type*} (candidates : List H)
    (lo hi : Bool → H → ℚ) (radius target : ℚ) :
    certificateChoice candidates lo hi radius target = none ↔
      ∀ h ∈ candidates, ¬ (0 < clippedLower (lo false h) radius ∧
        min 1 (clippedUpper (hi true h) radius / clippedLower (lo false h) radius) ≤ target) := by
  simpa only [certificateChoice, capped_gate_iff] using
    q05_3_no_result_iff_no_threshold_passes
      (fun h => clippedLower (lo false h) radius)
      (fun h => min (clippedLower (lo false h) radius) (clippedUpper (hi true h) radius))
      target candidates

/-- Correct lower enclosures of zero empirical coverage cannot pass the gate. -/
theorem certificateChoice_no_valid_coverage {H : Type*} (candidates : List H)
    (lo hi : Bool → H → ℚ) (radius target : ℚ) (hr : 0 ≤ radius)
    (zero : ∀ h ∈ candidates, lo false h ≤ 0) :
    certificateChoice candidates lo hi radius target = none := by
  rw [certificateChoice_none_iff]
  intro h hh
  have hzero : clippedLower (lo false h) radius = 0 := by
    unfold clippedLower
    exact max_eq_left (sub_nonpos.mpr (le_trans (zero h hh) hr))
  simp [hzero]

private theorem clipped_interval_encloses (v : ℝ) (lo hi radius : ℚ)
    (hv : v ∈ Set.Icc (0 : ℝ) 1)
    (hl : (lo : ℝ) - (radius : ℝ) ≤ v) (hu : v ≤ (hi : ℝ) + (radius : ℝ)) :
    (clippedLower lo radius : ℝ) ≤ v ∧ v ≤ (clippedUpper hi radius : ℝ) := by
  constructor
  · unfold clippedLower
    by_cases h : 0 ≤ lo - radius
    · rw [max_eq_right h]
      simpa only [Rat.cast_sub] using hl
    · rw [max_eq_left (le_of_not_ge h)]
      simpa using hv.1
  · unfold clippedUpper
    by_cases h : hi + radius ≤ 1
    · rw [min_eq_right h]
      simpa only [Rat.cast_add] using hu
    · rw [min_eq_left (le_of_not_ge h)]
      simpa using hv.2

/-- Fixed finite thresholds, n positive IID validation observations, two bounded
statistics per threshold, and an explicit joint failure budget. Empirical
rational enclosures are checked against the actual sample means, not population
means. The selector performs rational comparisons; arbitrary real comparison
termination is neither assumed nor claimed. -/
theorem finite_threshold_interval_certificate {Ω X Y H : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X] [MeasurableSpace Y] [DecidableEq H] {n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (P : Measure (X × Y)) [IsProbabilityMeasure P]
    (hn : 0 < n) (first : H) (rest : List H) (cutoff : H → ℝ)
    (loss : X × Y → ℝ) (score : X → ℝ) (hl : Measurable loss) (hs : Measurable score)
    (lossRange : ∀ z, loss z ∈ Set.Icc (0 : ℝ) 1)
    (sample : Fin n → Ω → X × Y) (sampleMeasurable : ∀ i, Measurable (sample i))
    (independent : iIndepFun sample μ) (law : ∀ i, IdentDistrib (sample i) id μ P)
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) (radius target : ℚ) (requestedTarget : ℝ)
    (targetSafe : (target : ℝ) ≤ requestedTarget)
    (conservative : finiteRadius n (2 * (first :: rest).toFinset.card) δ ≤ (radius : ℝ))
    (lo hi : Ω → Bool → H → ℚ)
    (encloses : ∀ w h, h ∈ first :: rest → ∀ b : Bool,
      (lo w b h : ℝ) ≤ empiricalMean
        (fun i w => thresholdStatistic loss (fun z : X × Y => score z.1) cutoff (h, b) (sample i w)) w ∧
      empiricalMean (fun i w => thresholdStatistic loss (fun z : X × Y => score z.1) cutoff (h, b) (sample i w)) w ≤
        (hi w b h : ℝ)) :
    ∃ confidence : Set Ω, MeasurableSet confidence ∧ 1 - δ ≤ μ.real confidence ∧
      ∀ w ∈ confidence,
        (∀ h ∈ first :: rest, ∀ b : Bool,
          (clippedLower (lo w b h) radius : ℝ) ≤
              ∫ z, thresholdStatistic loss (fun z : X × Y => score z.1) cutoff (h, b) z ∂P ∧
          (∫ z, thresholdStatistic loss (fun z : X × Y => score z.1) cutoff (h, b) z ∂P) ≤
              (clippedUpper (hi w b h) radius : ℝ)) ∧
        ∀ h, certificateChoice (first :: rest) (lo w) (hi w) radius target = some h →
          0 < (∫ z, thresholdStatistic loss (fun z : X × Y => score z.1) cutoff (h, false) z ∂P) ∧
          (∫ z, thresholdStatistic loss (fun z : X × Y => score z.1) cutoff (h, true) z ∂P) /
              (∫ z, thresholdStatistic loss (fun z : X × Y => score z.1) cutoff (h, false) z ∂P) ≤
            min 1 ((clippedUpper (hi w true h) radius : ℝ) /
              (clippedLower (lo w false h) radius : ℝ)) ∧
          (∫ z, thresholdStatistic loss (fun z : X × Y => score z.1) cutoff (h, true) z ∂P) /
              (∫ z, thresholdStatistic loss (fun z : X × Y => score z.1) cutoff (h, false) z ∂P) ≤ (target : ℝ) ∧
          (∫ z, thresholdStatistic loss (fun z : X × Y => score z.1) cutoff (h, true) z ∂P) /
              (∫ z, thresholdStatistic loss (fun z : X × Y => score z.1) cutoff (h, false) z ∂P) ≤
            requestedTarget := by
  let T := (first :: rest).toFinset
  let family : Finset (H × Bool) := T.product Finset.univ
  let stat : H × Bool → X × Y → ℝ := thresholdStatistic loss (fun z : X × Y => score z.1) cutoff
  have statMeasurable (p : H × Bool) : Measurable (stat p) := by
    rcases p with ⟨t, b⟩
    cases b
    · change Measurable (fun z => if cutoff t ≤ score z.1 then (1 : ℝ) else 0)
      exact Measurable.ite (measurableSet_le measurable_const (hs.comp measurable_fst)) measurable_const measurable_const
    · change Measurable (fun z => if cutoff t ≤ score z.1 then loss z else 0)
      exact Measurable.ite (measurableSet_le measurable_const (hs.comp measurable_fst)) hl measurable_const
  have statRange (p : H × Bool) (z : X × Y) : stat p z ∈ Set.Icc (0 : ℝ) 1 := by
    rcases p with ⟨t, b⟩
    cases b
    · by_cases h : cutoff t ≤ score z.1 <;> simp [stat, thresholdStatistic, h]
    · by_cases h : cutoff t ≤ score z.1
      · simpa [stat, thresholdStatistic, h] using lossRange z
      · simp [stat, thresholdStatistic, h]
  have statIntegrable (p : H × Bool) : Integrable (stat p) P :=
    unit_integrable P (stat p) (statMeasurable p) (statRange p)
  have populationRange (p : H × Bool) : (∫ z, stat p z ∂P) ∈ Set.Icc (0 : ℝ) 1 := by
    refine ⟨integral_nonneg (fun z => (statRange p z).1), ?_⟩
    calc
      _ ≤ ∫ _ : X × Y, (1 : ℝ) ∂P :=
        integral_mono (statIntegrable p) (integrable_const 1) (fun z => (statRange p z).2)
      _ = 1 := by simp
  have familyNonempty : family.Nonempty := ⟨(first, false), by simp [family, T]⟩
  have familyCard : family.card = 2 * T.card := by simp [family, Nat.mul_comm]
  have radiusBound : finiteRadius n family.card δ ≤ (radius : ℝ) := by
    simpa only [familyCard] using conservative
  let confidence : Set Ω := {w | ∀ p ∈ family,
    |empiricalMean (fun i w => stat p (sample i w)) w - ∫ z, stat p z ∂P| ≤
      finiteRadius n family.card δ}
  have deviationMeasurable (p : H × Bool) : Measurable (fun w =>
      |empiricalMean (fun i w => stat p (sample i w)) w - ∫ z, stat p z ∂P|) := by
    have hm : ∀ i, Measurable (fun w => stat p (sample i w)) :=
      fun i => (statMeasurable p).comp (sampleMeasurable i)
    dsimp [empiricalMean]
    fun_prop
  have confidenceMeasurable : MeasurableSet confidence := by
    convert family.measurableSet_biInter
      (f := fun p => {w |
        |empiricalMean (fun i w => stat p (sample i w)) w - ∫ z, stat p z ∂P| ≤
          finiteRadius n family.card δ})
      (fun p _ => measurableSet_le (deviationMeasurable p) measurable_const) using 1 <;>
      ext w <;> simp [confidence]
  have probability : 1 - δ ≤ μ.real confidence :=
    u01_1_iid_empirical_risk_uniform μ P hn family familyNonempty sample sampleMeasurable
      independent law stat (fun p _ => statMeasurable p) (fun p _ z => statRange p z) δ hδ hδ1
  refine ⟨confidence, confidenceMeasurable, probability, ?_⟩
  intro w hw
  have bounds : ∀ h ∈ first :: rest, ∀ b : Bool,
      (clippedLower (lo w b h) radius : ℝ) ≤ (∫ z, stat (h, b) z ∂P) ∧
      (∫ z, stat (h, b) z ∂P) ≤ (clippedUpper (hi w b h) radius : ℝ) := by
    intro h hh b
    have member : (h, b) ∈ family := by
      exact Finset.mem_product.mpr ⟨by simpa [T] using hh, Finset.mem_univ b⟩
    have deviation : |empiricalMean (fun i w => stat (h, b) (sample i w)) w -
        ∫ z, stat (h, b) z ∂P| ≤ (radius : ℝ) := le_trans (hw (h, b) member) radiusBound
    have en := encloses w h hh b
    have lowerRaw : (lo w b h : ℝ) - (radius : ℝ) ≤ ∫ z, stat (h, b) z ∂P := by
      have hd := (abs_le.mp deviation).2
      linarith [en.1]
    have upperRaw : (∫ z, stat (h, b) z ∂P) ≤ (hi w b h : ℝ) + (radius : ℝ) := by
      have hd := (abs_le.mp deviation).1
      linarith [en.2]
    exact clipped_interval_encloses _ _ _ _ (populationRange (h, b)) lowerRaw upperRaw
  refine ⟨bounds, ?_⟩
  intro h selected
  have spec := q05_3_selectPassing_spec
    (fun h => clippedLower (lo w false h) radius)
    (fun h => min (clippedLower (lo w false h) radius) (clippedUpper (hi w true h) radius))
    target (first :: rest) h selected
  have positiveLower : 0 < (clippedLower (lo w false h) radius : ℝ) := by
    exact_mod_cast spec.2.1
  have positiveCoverage : 0 < ∫ z, stat (h, false) z ∂P :=
    lt_of_lt_of_le positiveLower (bounds h spec.1 false).1
  have numerator_le_coverage : (∫ z, stat (h, true) z ∂P) ≤ ∫ z, stat (h, false) z ∂P := by
    apply integral_mono (statIntegrable (h, true)) (statIntegrable (h, false))
    intro z
    by_cases ha : cutoff h ≤ score z.1
    · simpa [stat, thresholdStatistic, ha] using (lossRange z).2
    · simp [stat, thresholdStatistic, ha]
  have risk_le_one : (∫ z, stat (h, true) z ∂P) / (∫ z, stat (h, false) z ∂P) ≤ 1 := by
    apply (div_le_iff₀ positiveCoverage).mpr
    simpa using numerator_le_coverage
  have ratio : (∫ z, stat (h, true) z ∂P) / (∫ z, stat (h, false) z ∂P) ≤
      (clippedUpper (hi w true h) radius : ℝ) / (clippedLower (lo w false h) radius : ℝ) := by
    apply (div_le_div_iff₀ positiveCoverage positiveLower).mpr
    have nb := (bounds h spec.1 true).2
    have cb := (bounds h spec.1 false).1
    have nn := (populationRange (h, true)).1
    nlinarith
  have clippedRisk := le_min risk_le_one ratio
  have gate : min (1 : ℚ)
      (clippedUpper (hi w true h) radius / clippedLower (lo w false h) radius) ≤ target := by
    rw [← capped_quotient _ _ spec.2.1]
    exact spec.2.2
  have realGate : min (1 : ℝ)
      ((clippedUpper (hi w true h) radius : ℝ) / (clippedLower (lo w false h) radius : ℝ)) ≤
      (target : ℝ) := by exact_mod_cast gate
  exact ⟨positiveCoverage, clippedRisk, le_trans clippedRisk realGate,
    le_trans (le_trans clippedRisk realGate) targetSafe⟩

end JurisLean.Candidates.U05_3OriginalSelectiveRiskInstances20261101
