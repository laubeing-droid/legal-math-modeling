import JurisLean.Candidates.ExactProbability20261027
import JurisLean.Seams.UnifiedNeedlesS3a
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Probability.ConditionalProbability

/-!
U04.2, frozen manuscript §4: reuse the supplied enclosure and Beta integral;
realize the sharp three-event interval on one eight-atom probability space;
connect contamination to actual conditional measures, including the zero-Q(B)
branch. No assertion about probabilities of real legal interpretations is made.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators NNReal

namespace JurisLean.Candidates.U04_2SharpConditioning20261029

/-- The existing enclosure, with the frozen nonnegative numerator and width formula. -/
theorem frozen_enclosure_width (N B nL nU bL bU : ℝ)
    (hN : 0 ≤ N) (hNB : N ≤ B) (hnL : nL ≤ N) (hnU : N ≤ nU)
    (hbL : 0 < bL) (hLB : bL ≤ B) (hBU : B ≤ bU) :
    0 ≤ min 1 (nU / bL) - max 0 (nL / bU) ∧
      min 1 (nU / bL) - max 0 (nL / bU) ≤ 1 ∧
      min 1 (nU / bL) - max 0 (nL / bU) ≤
        (nU - max 0 nL) / bL + max 0 nL * (bU - bL) / (bL * bU) := by
  have hbU : 0 < bU := hbL.trans_le (hLB.trans hBU)
  have hplus : max 0 nL ≤ N := max_le hN hnL
  have hclip : max 0 (max 0 nL / bU) = max 0 (nL / bU) := by
    rcases le_total nL 0 with hn | hn
    · simp [max_eq_left hn,
        max_eq_left (div_nonpos_of_nonpos_of_nonneg hn hbU.le)]
    · simp [max_eq_right hn]
  have h := ExactProbability20261027.supplied_enclosure_has_explicit_width_bound
    N B (max 0 nL) nU bL bU hN hNB hplus hnU hbL hLB hBU
  rw [hclip] at h
  have hw : (nU - max 0 nL) / bU + nU * (bU - bL) / (bL * bU) =
      (nU - max 0 nL) / bL + max 0 nL * (bU - bL) / (bL * bU) := by
    field_simp [hbL.ne', hbU.ne'] <;> ring
  exact ⟨h.1, h.2.1, h.2.2.trans_eq hw⟩

/-- Only the frozen Beta(2,3) half-point is instantiated; the full integral is reused. -/
theorem beta_two_three_half :
    (∫ x in (0 : ℝ)..1, x * (1 - x) ^ 2) = 1 / 12 ∧
    (∫ x in (0 : ℝ)..(1 / 2), x * (1 - x) ^ 2) = 11 / 192 ∧
    (∫ x in (0 : ℝ)..(1 / 2), x * (1 - x) ^ 2) /
      (∫ x in (0 : ℝ)..1, x * (1 - x) ^ 2) = 11 / 16 := by
  have hb := JurisLean.Seams.UnifiedNeedlesS3a.betaInt_eq 1 2
  norm_num [JurisLean.Seams.UnifiedNeedlesS3a.betaInt,
    JurisLean.Seams.UnifiedNeedlesS3a.betaTwoConst, Nat.factorial] at hb
  have hd (x : ℝ) :
      HasDerivAt (fun y : ℝ => y ^ 2 / 2 - (2 / 3 : ℝ) * y ^ 3 + y ^ 4 / 4)
        (x * (1 - x) ^ 2) x := by
    convert (((hasDerivAt_pow 2 x).div_const 2).sub
      ((hasDerivAt_pow 3 x).const_mul (2 / 3 : ℝ))).add
      ((hasDerivAt_pow 4 x).div_const 4) using 1 <;> norm_num <;> ring
  have hc : Continuous (fun x : ℝ => x * (1 - x) ^ 2) := by fun_prop
  have hn := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := (0 : ℝ)) (b := (1 / 2 : ℝ)) (fun x _ => hd x)
    (hc.intervalIntegrable _ _)
  norm_num at hn
  refine ⟨hb, hn, ?_⟩
  rw [hn, hb]
  norm_num

/-- Bounds for three events on their actual common probability space. -/
theorem three_event_bounds {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (A B C : Set Ω)
    (hA : MeasurableSet A) (hB : MeasurableSet B) (hC : MeasurableSet C) :
    max 0 (μ.real A + μ.real B + μ.real C - 2) ≤ μ.real (A ∩ B ∩ C) ∧
      μ.real (A ∩ B ∩ C) ≤ min (min (μ.real A) (μ.real B)) (μ.real C) := by
  have hab := measureReal_union_add_inter (μ := μ) (s := A) hB
  have habc := measureReal_union_add_inter (μ := μ) (s := A ∩ B) hC
  have hu : μ.real (A ∪ B) ≤ 1 := measureReal_le_one
  have hv : μ.real ((A ∩ B) ∪ C) ≤ 1 := measureReal_le_one
  have ha : μ.real (A ∩ B ∩ C) ≤ μ.real A :=
    measureReal_mono (fun _ h => h.1.1)
  have hb : μ.real (A ∩ B ∩ C) ≤ μ.real B :=
    measureReal_mono (fun _ h => h.1.2)
  have hc : μ.real (A ∩ B ∩ C) ≤ μ.real C :=
    measureReal_mono (fun _ h => h.2)
  exact ⟨max_le measureReal_nonneg (by linarith), le_min (le_min ha hb) hc⟩

-- An explicit common space; its measurable structure is the discrete top space.
local instance : MeasurableSpace (Fin 8) := ⊤

def eventA : Finset (Fin 8) := {4, 5, 6, 7}
def eventB : Finset (Fin 8) := {2, 3, 6, 7}
def eventC : Finset (Fin 8) := {1, 3, 5, 7}
def eventABC : Finset (Fin 8) := {7}

private def sharpMass (p₁ p₂ p₃ t : ℝ) : Fin 8 → ℝ :=
  let r := max t (p₁ + p₂ - 1)
  let a := p₁ - r
  let b := p₂ - r
  let c := 1 - p₁ - p₂ + r
  let q := p₃ - t
  let u := min a q
  let v := min b (q - u)
  let z := q - u - v
  ![c - z, z, b - v, v, a - u, u, r - t, t]

private theorem sharpMass_properties (p₁ p₂ p₃ t : ℝ)
    (h₁ : 0 ≤ p₁ ∧ p₁ ≤ 1) (h₂ : 0 ≤ p₂ ∧ p₂ ≤ 1)
    (h₃ : 0 ≤ p₃ ∧ p₃ ≤ 1)
    (ht : max 0 (p₁ + p₂ + p₃ - 2) ≤ t ∧ t ≤ min (min p₁ p₂) p₃) :
    (∀ i, 0 ≤ sharpMass p₁ p₂ p₃ t i) ∧
      (∑ i, sharpMass p₁ p₂ p₃ t i) = 1 ∧
      (∑ i ∈ eventA, sharpMass p₁ p₂ p₃ t i) = p₁ ∧
      (∑ i ∈ eventB, sharpMass p₁ p₂ p₃ t i) = p₂ ∧
      (∑ i ∈ eventC, sharpMass p₁ p₂ p₃ t i) = p₃ ∧
      (∑ i ∈ eventABC, sharpMass p₁ p₂ p₃ t i) = t := by
  let r := max t (p₁ + p₂ - 1)
  let a := p₁ - r
  let b := p₂ - r
  let c := 1 - p₁ - p₂ + r
  let q := p₃ - t
  let u := min a q
  let v := min b (q - u)
  let z := q - u - v
  have ht0 : 0 ≤ t := (le_max_left _ _).trans ht.1
  have htl : p₁ + p₂ + p₃ - 2 ≤ t := (le_max_right _ _).trans ht.1
  have ht₁ : t ≤ p₁ := ht.2.trans ((min_le_left _ _).trans (min_le_left _ _))
  have ht₂ : t ≤ p₂ := ht.2.trans ((min_le_left _ _).trans (min_le_right _ _))
  have ht₃ : t ≤ p₃ := ht.2.trans (min_le_right _ _)
  have hr₁ : r ≤ p₁ := max_le ht₁ (by linarith [h₂.2])
  have hr₂ : r ≤ p₂ := max_le ht₂ (by linarith [h₁.2])
  have hrt : t ≤ r := le_max_left _ _
  have hrl : p₁ + p₂ - 1 ≤ r := le_max_right _ _
  have hru : r ≤ t + 1 - p₃ := max_le (by linarith [h₃.2]) (by linarith)
  have ha : 0 ≤ a := sub_nonneg.mpr hr₁
  have hb : 0 ≤ b := sub_nonneg.mpr hr₂
  have hc : 0 ≤ c := by dsimp [c]; linarith
  have hq : 0 ≤ q := sub_nonneg.mpr ht₃
  have hcap : q ≤ a + b + c := by dsimp [q, a, b, c]; linarith
  have hu0 : 0 ≤ u := le_min ha hq
  have hua : u ≤ a := min_le_left _ _
  have huq : u ≤ q := min_le_right _ _
  have hremain : q - u ≤ b + c := by
    rcases le_total a q with h | h
    · have he : u = a := min_eq_left h
      rw [he]; linarith
    · have he : u = q := min_eq_right h
      rw [he]; linarith
  have hv0 : 0 ≤ v := le_min hb (sub_nonneg.mpr huq)
  have hvb : v ≤ b := min_le_left _ _
  have hvq : v ≤ q - u := min_le_right _ _
  have hz0 : 0 ≤ z := by dsimp [z]; linarith
  have hzc : z ≤ c := by
    rcases le_total b (q - u) with h | h
    · have he : v = b := min_eq_left h
      dsimp [z]; rw [he]; linarith
    · have he : v = q - u := min_eq_right h
      dsimp [z]; rw [he]; linarith
  have hm : sharpMass p₁ p₂ p₃ t = ![c - z, z, b - v, v, a - u, u, r - t, t] := rfl
  rw [hm]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    fin_cases i <;> norm_num <;> linarith
  · simp [Fin.sum_univ_succ, z, v, u, q, c, b, a]
    <;> ring
  · unfold eventA
    rw [Finset.sum_insert (show (4 : Fin 8) ∉ ({5, 6, 7} : Finset (Fin 8)) by decide),
      Finset.sum_insert (show (5 : Fin 8) ∉ ({6, 7} : Finset (Fin 8)) by decide),
      Finset.sum_insert (show (6 : Fin 8) ∉ ({7} : Finset (Fin 8)) by decide),
      Finset.sum_singleton]
    change (a - u) + (u + ((r - t) + t)) = p₁
    dsimp [a]
    ring
  · unfold eventB
    rw [Finset.sum_insert (show (2 : Fin 8) ∉ ({3, 6, 7} : Finset (Fin 8)) by decide),
      Finset.sum_insert (show (3 : Fin 8) ∉ ({6, 7} : Finset (Fin 8)) by decide),
      Finset.sum_insert (show (6 : Fin 8) ∉ ({7} : Finset (Fin 8)) by decide),
      Finset.sum_singleton]
    change (b - v) + (v + ((r - t) + t)) = p₂
    dsimp [b]
    ring
  · unfold eventC
    rw [Finset.sum_insert (show (1 : Fin 8) ∉ ({3, 5, 7} : Finset (Fin 8)) by decide),
      Finset.sum_insert (show (3 : Fin 8) ∉ ({5, 7} : Finset (Fin 8)) by decide),
      Finset.sum_insert (show (5 : Fin 8) ∉ ({7} : Finset (Fin 8)) by decide),
      Finset.sum_singleton]
    change z + (v + (u + t)) = p₃
    dsimp [z, q]
    ring
  · unfold eventABC
    rw [Finset.sum_singleton]
    rfl

private def law (w : Fin 8 → ℝ) (h0 : ∀ i, 0 ≤ w i) (h1 : ∑ i, w i = 1) :
    Measure (Fin 8) :=
  (PMF.ofFintype (fun i => ENNReal.ofReal (w i)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => h0 i), h1]
    exact ENNReal.ofReal_one)).toMeasure

private instance law_probability (w : Fin 8 → ℝ) (h0 : ∀ i, 0 ≤ w i)
    (h1 : ∑ i, w i = 1) : IsProbabilityMeasure (law w h0 h1) := by
  unfold law
  infer_instance

private theorem law_real (w : Fin 8 → ℝ) (h0 : ∀ i, 0 ≤ w i)
    (h1 : ∑ i, w i = 1) (s : Finset (Fin 8)) :
    (law w h0 h1).real s = ∑ i ∈ s, w i := by
  unfold Measure.real law
  rw [PMF.toMeasure_apply_finset]
  simp only [PMF.ofFintype_apply]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => h0 i)]
  exact ENNReal.toReal_ofReal (Finset.sum_nonneg (fun i _ => h0 i))

/-- Every point in the sharp interval has a genuine common eight-atom law. -/
theorem three_event_sharp_realization (p₁ p₂ p₃ t : ℝ)
    (h₁ : 0 ≤ p₁ ∧ p₁ ≤ 1) (h₂ : 0 ≤ p₂ ∧ p₂ ≤ 1)
    (h₃ : 0 ≤ p₃ ∧ p₃ ≤ 1)
    (ht : max 0 (p₁ + p₂ + p₃ - 2) ≤ t ∧ t ≤ min (min p₁ p₂) p₃) :
    ∃ μ : Measure (Fin 8), IsProbabilityMeasure μ ∧
      μ.real eventA = p₁ ∧ μ.real eventB = p₂ ∧ μ.real eventC = p₃ ∧
      μ.real eventABC = t := by
  obtain ⟨h0, h1, ha, hb, hc, ht⟩ := sharpMass_properties p₁ p₂ p₃ t h₁ h₂ h₃ ht
  refine ⟨law (sharpMass p₁ p₂ p₃ t) h0 h1, inferInstance, ?_, ?_, ?_, ?_⟩
  all_goals rw [law_real]
  · exact ha
  · exact hb
  · exact hc
  · exact ht

/-- The attainable set is exactly the frozen interval, including both endpoints. -/
theorem three_event_identified_interval (p₁ p₂ p₃ t : ℝ)
    (h₁ : 0 ≤ p₁ ∧ p₁ ≤ 1) (h₂ : 0 ≤ p₂ ∧ p₂ ≤ 1)
    (h₃ : 0 ≤ p₃ ∧ p₃ ≤ 1) :
    (∃ μ : Measure (Fin 8), IsProbabilityMeasure μ ∧
      μ.real eventA = p₁ ∧ μ.real eventB = p₂ ∧ μ.real eventC = p₃ ∧
      μ.real eventABC = t) ↔
      max 0 (p₁ + p₂ + p₃ - 2) ≤ t ∧ t ≤ min (min p₁ p₂) p₃ := by
  constructor
  · rintro ⟨μ, hμ, ha, hb, hc, ht⟩
    letI := hμ
    have hi : (eventA : Set (Fin 8)) ∩ eventB ∩ eventC = eventABC := by
      ext i
      fin_cases i <;> decide
    have h := three_event_bounds μ eventA eventB eventC
      (by exact .of_discrete) (by exact .of_discrete) (by exact .of_discrete)
    simpa only [hi, ha, hb, hc, ht] using h
  · exact three_event_sharp_realization p₁ p₂ p₃ t h₁ h₂ h₃

/-- Both endpoints are attainable for every admissible triple of real marginals. -/
theorem three_event_endpoints (p₁ p₂ p₃ : ℝ)
    (h₁ : 0 ≤ p₁ ∧ p₁ ≤ 1) (h₂ : 0 ≤ p₂ ∧ p₂ ≤ 1)
    (h₃ : 0 ≤ p₃ ∧ p₃ ≤ 1) :
    ∀ t : ℝ, t = max 0 (p₁ + p₂ + p₃ - 2) ∨ t = min (min p₁ p₂) p₃ →
      ∃ μ : Measure (Fin 8), IsProbabilityMeasure μ ∧
        μ.real eventA = p₁ ∧ μ.real eventB = p₂ ∧ μ.real eventC = p₃ ∧
        μ.real eventABC = t := by
  have hLU : max 0 (p₁ + p₂ + p₃ - 2) ≤ min (min p₁ p₂) p₃ := by
    exact le_min (le_min (max_le h₁.1 (by linarith [h₂.2, h₃.2]))
      (max_le h₂.1 (by linarith [h₁.2, h₃.2])))
      (max_le h₃.1 (by linarith [h₁.2, h₂.2]))
  intro t ht
  apply three_event_sharp_realization p₁ p₂ p₃ t h₁ h₂ h₃
  rcases ht with rfl | rfl
  · exact ⟨le_rfl, hLU⟩
  · exact ⟨hLU, le_rfl⟩

/-- The actual mixture measure; coefficients are nonnegative and sum to one. -/
def contaminated {Ω : Type*} [MeasurableSpace Ω] (ε : ℝ)
    (h0 : 0 ≤ ε) (h1 : ε ≤ 1) (P Q : Measure Ω) : Measure Ω :=
  NNReal.mk (1 - ε) (sub_nonneg.mpr h1) • P + NNReal.mk ε h0 • Q

theorem contaminated_real {Ω : Type*} [MeasurableSpace Ω] (ε : ℝ)
    (h0 : 0 ≤ ε) (h1 : ε ≤ 1) (P Q : Measure Ω)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (S : Set Ω) :
    (contaminated ε h0 h1 P Q).real S = (1 - ε) * P.real S + ε * Q.real S := by
  unfold contaminated
  rw [measureReal_add_apply, measureReal_nnreal_smul_apply,
    measureReal_nnreal_smul_apply]
  rfl

theorem contaminated_probability {Ω : Type*} [MeasurableSpace Ω] (ε : ℝ)
    (h0 : 0 ≤ ε) (h1 : ε ≤ 1) (P Q : Measure Ω)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] :
    IsProbabilityMeasure (contaminated ε h0 h1 P Q) := by
  constructor
  have hf : IsFiniteMeasure (contaminated ε h0 h1 P Q) := by
    unfold contaminated
    infer_instance
  letI := hf
  rw [← ofReal_measureReal, contaminated_real]
  simp [Measure.real]

/-- Mixing compatible laws keeps the same marginals and interpolates the joint mass. -/
theorem compatible_law_mixture (P Q : Measure (Fin 8))
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (p₁ p₂ p₃ l u θ : ℝ) (hθ : 0 ≤ θ ∧ θ ≤ 1)
    (hP : P.real eventA = p₁ ∧ P.real eventB = p₂ ∧ P.real eventC = p₃ ∧
      P.real eventABC = l)
    (hQ : Q.real eventA = p₁ ∧ Q.real eventB = p₂ ∧ Q.real eventC = p₃ ∧
      Q.real eventABC = u) :
    IsProbabilityMeasure (contaminated θ hθ.1 hθ.2 P Q) ∧
      (contaminated θ hθ.1 hθ.2 P Q).real eventA = p₁ ∧
      (contaminated θ hθ.1 hθ.2 P Q).real eventB = p₂ ∧
      (contaminated θ hθ.1 hθ.2 P Q).real eventC = p₃ ∧
      (contaminated θ hθ.1 hθ.2 P Q).real eventABC = (1 - θ) * l + θ * u := by
  refine ⟨contaminated_probability θ hθ.1 hθ.2 P Q, ?_, ?_, ?_, ?_⟩
  · rw [contaminated_real, hP.1, hQ.1]; ring
  · rw [contaminated_real, hP.2.1, hQ.2.1]; ring
  · rw [contaminated_real, hP.2.2.1, hQ.2.2.1]; ring
  · rw [contaminated_real, hP.2.2.2, hQ.2.2.2]

private theorem conditional_real {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (A B : Set Ω) (hB : MeasurableSet B) :
    (cond μ B).real A = μ.real (B ∩ A) / μ.real B := by
  unfold Measure.real
  rw [cond_apply hB μ A, ENNReal.toReal_mul, ENNReal.toReal_inv]
  ring

/-- Algebra needed by the actual measure connector; no division by q is used. -/
private theorem conditional_contamination_algebra (ε ρ q x y : ℝ)
    (hε : 0 ≤ ε ∧ ε < 1) (hρ : 0 < ρ) (hq : 0 ≤ q ∧ q ≤ 1)
    (hx : 0 ≤ x ∧ x ≤ ρ) (hy : 0 ≤ y ∧ y ≤ q) :
    0 < (1 - ε) * ρ + ε * q ∧
      |((1 - ε) * x + ε * y) / ((1 - ε) * ρ + ε * q) - x / ρ| ≤
        ε * q / ((1 - ε) * ρ + ε * q) ∧
      ε * q / ((1 - ε) * ρ + ε * q) ≤ ε / ((1 - ε) * ρ + ε) := by
  let D := (1 - ε) * ρ + ε * q
  have hD : 0 < D := add_pos_of_pos_of_nonneg
    (mul_pos (sub_pos.mpr hε.2) hρ) (mul_nonneg hε.1 hq.1)
  have hE : 0 < (1 - ε) * ρ + ε := add_pos_of_pos_of_nonneg
    (mul_pos (sub_pos.mpr hε.2) hρ) hε.1
  have hlo : -(q * ρ) ≤ ρ * y - q * x := by
    nlinarith [mul_nonneg hρ.le hy.1, mul_le_mul_of_nonneg_left hx.2 hq.1]
  have hhi : ρ * y - q * x ≤ q * ρ := by
    nlinarith [mul_nonneg hq.1 hx.1, mul_le_mul_of_nonneg_left hy.2 hρ.le]
  have hid : ((1 - ε) * x + ε * y) / D - x / ρ =
      ε * (ρ * y - q * x) / (ρ * D) := by
    field_simp [hρ.ne', hD.ne'] <;> dsimp [D] <;> ring
  refine ⟨hD, ?_, ?_⟩
  · rw [hid, abs_le]
    constructor
    · apply (le_div_iff₀ (mul_pos hρ hD)).2
      have hscaled := mul_le_mul_of_nonneg_left hlo hε.1
      have hc : -(ε * q / D) * (ρ * D) = -(ε * (q * ρ)) := by
        field_simp [hD.ne'] <;> ring
      rw [hc]
      nlinarith
    · apply (div_le_iff₀ (mul_pos hρ hD)).2
      have hscaled := mul_le_mul_of_nonneg_left hhi hε.1
      have hc : (ε * q / D) * (ρ * D) = ε * (q * ρ) := by
        field_simp [hD.ne'] <;> ring
      rw [hc]
      exact hscaled
  · apply (div_le_div_iff₀ hD hE).2
    have hp : 0 ≤ ε * ((1 - ε) * ρ) :=
      mul_nonneg hε.1 (mul_nonneg (sub_pos.mpr hε.2).le hρ.le)
    have hs := mul_le_mul_of_nonneg_left hq.2 hp
    dsimp [D]
    nlinarith

/-- eta is the actual contaminating component's conditional mass, not a new axiom. -/
theorem conditional_contamination_bound {Ω : Type*} [MeasurableSpace Ω]
    (P Q : Measure Ω) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (ε : ℝ) (hε : 0 ≤ ε ∧ ε < 1) (A B : Set Ω)
    (hB : MeasurableSet B) (hρ : 0 < P.real B) :
    let M := contaminated ε hε.1 hε.2.le P Q
    let η := (NNReal.mk ε hε.1 • Q).real B / M.real B
    0 < M.real B ∧
      η = ε * Q.real B / ((1 - ε) * P.real B + ε * Q.real B) ∧
      |(cond M B).real A - (cond P B).real A| ≤ η ∧
      η ≤ ε / ((1 - ε) * P.real B + ε) := by
  have hx : 0 ≤ P.real (B ∩ A) ∧ P.real (B ∩ A) ≤ P.real B :=
    ⟨measureReal_nonneg, measureReal_mono inter_subset_left⟩
  have hy : 0 ≤ Q.real (B ∩ A) ∧ Q.real (B ∩ A) ≤ Q.real B :=
    ⟨measureReal_nonneg, measureReal_mono inter_subset_left⟩
  have h := conditional_contamination_algebra ε (P.real B) (Q.real B)
    (P.real (B ∩ A)) (Q.real (B ∩ A)) hε hρ
    ⟨measureReal_nonneg, measureReal_le_one⟩ hx hy
  dsimp only
  simp only [measureReal_nnreal_smul_apply, NNReal.coe_mk,
    conditional_real _ _ _ hB, contaminated_real]
  exact ⟨h.1, rfl, h.2.1, h.2.2⟩

/-- Zero Q(B) leaves P(.|B) unchanged, without interpreting Q(.|B). -/
theorem conditional_contamination_zero_component {Ω : Type*} [MeasurableSpace Ω]
    (P Q : Measure Ω) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (ε : ℝ) (hε : 0 ≤ ε ∧ ε < 1) (A B : Set Ω)
    (hB : MeasurableSet B) (hρ : 0 < P.real B) (hq : Q.real B = 0) :
    let M := contaminated ε hε.1 hε.2.le P Q
    (NNReal.mk ε hε.1 • Q).real B / M.real B = 0 ∧
      (cond M B).real A = (cond P B).real A := by
  have h := conditional_contamination_bound P Q ε hε A B hB hρ
  dsimp only at h ⊢
  have heta : (NNReal.mk ε hε.1 • Q).real B /
      (contaminated ε hε.1 hε.2.le P Q).real B = 0 := by
    rw [measureReal_nnreal_smul_apply, hq, mul_zero, zero_div]
  refine ⟨heta, sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm ?_ (abs_nonneg _)))⟩
  simpa only [heta] using h.2.2.1

private def smallP : Measure (Fin 8) :=
  law ![1 / 100, 0, 99 / 100, 0, 0, 0, 0, 0]
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])

private def smallQ : Measure (Fin 8) :=
  law ![0, 1, 0, 0, 0, 0, 0, 0]
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])

private instance : IsProbabilityMeasure smallP := by unfold smallP; infer_instance
private instance : IsProbabilityMeasure smallQ := by unfold smallQ; infer_instance

/-- A valid small-conditioning-event example: the change exceeds unconditional epsilon. -/
theorem conditioning_amplification_example :
    let A : Set (Fin 8) := ({1} : Finset (Fin 8))
    let B : Set (Fin 8) := ({0, 1} : Finset (Fin 8))
    let M := contaminated (1 / 10) (by norm_num) (by norm_num) smallP smallQ
    smallP.real B = 1 / 100 ∧ smallQ.real B = 1 ∧
      (cond smallP B).real A = 0 ∧ (cond M B).real A = 100 / 109 ∧
      |(cond M B).real A - (cond smallP B).real A| > (1 / 10 : ℝ) := by
  let A : Set (Fin 8) := ({1} : Finset (Fin 8))
  let B : Set (Fin 8) := ({0, 1} : Finset (Fin 8))
  have hPA : smallP.real A = 0 := by
    unfold smallP A
    rw [law_real]
    norm_num
  have hQA : smallQ.real A = 1 := by
    unfold smallQ A
    rw [law_real]
    norm_num
  have hPB : smallP.real B = 1 / 100 := by
    unfold smallP B
    rw [law_real]
    norm_num
  have hQB : smallQ.real B = 1 := by
    unfold smallQ B
    rw [law_real]
    norm_num
  have hBA : B ∩ A = A := by
    ext i
    fin_cases i <;> norm_num [A, B]
  have hcP : (cond smallP B).real A = 0 := by
    rw [conditional_real _ _ _ (by exact .of_discrete), hBA, hPA]
    norm_num
  have hcM :
      (cond (contaminated (1 / 10) (by norm_num) (by norm_num) smallP smallQ) B).real A =
        100 / 109 := by
    rw [conditional_real _ _ _ (by exact .of_discrete), hBA,
      contaminated_real, contaminated_real, hPA, hQA, hPB, hQB]
    norm_num
  change smallP.real B = _ ∧ smallQ.real B = _ ∧ _ ∧ _ ∧ _
  exact ⟨hPB, hQB, hcP, hcM, by rw [hcP, hcM]; norm_num⟩

/-- Invalid boundary inputs fail the frozen contracts; totalized division does not fix them. -/
theorem invalid_conditioning_and_enclosure_inputs :
    ¬ (0 < smallP.real ({1} : Finset (Fin 8))) ∧
      ¬ ((3 / 2 : ℝ) ≤ (11 / 16 : ℝ) ∧ (11 / 16 : ℝ) ≤ (8 / 5 : ℝ)) ∧
      ¬ (max 0 ((1 : ℝ) + 1 + 1 - 2) ≤ 0) := by
  have hP : smallP.real ({1} : Finset (Fin 8)) = 0 := by
    unfold smallP
    rw [law_real]
    norm_num
  rw [hP]
  norm_num

#check JurisLean.Candidates.ExactProbability20261027.supplied_enclosure_has_explicit_width_bound
#print axioms JurisLean.Candidates.ExactProbability20261027.supplied_enclosure_has_explicit_width_bound
#check JurisLean.Seams.UnifiedNeedlesS3a.betaInt_eq
#print axioms JurisLean.Seams.UnifiedNeedlesS3a.betaInt_eq
#check JurisLean.Candidates.U04_2SharpConditioning20261029.frozen_enclosure_width
#print axioms JurisLean.Candidates.U04_2SharpConditioning20261029.frozen_enclosure_width
#check JurisLean.Candidates.U04_2SharpConditioning20261029.beta_two_three_half
#print axioms JurisLean.Candidates.U04_2SharpConditioning20261029.beta_two_three_half
#check JurisLean.Candidates.U04_2SharpConditioning20261029.three_event_bounds
#print axioms JurisLean.Candidates.U04_2SharpConditioning20261029.three_event_bounds
#check JurisLean.Candidates.U04_2SharpConditioning20261029.three_event_sharp_realization
#print axioms JurisLean.Candidates.U04_2SharpConditioning20261029.three_event_sharp_realization
#check JurisLean.Candidates.U04_2SharpConditioning20261029.three_event_identified_interval
#print axioms JurisLean.Candidates.U04_2SharpConditioning20261029.three_event_identified_interval
#check JurisLean.Candidates.U04_2SharpConditioning20261029.three_event_endpoints
#print axioms JurisLean.Candidates.U04_2SharpConditioning20261029.three_event_endpoints
#check JurisLean.Candidates.U04_2SharpConditioning20261029.contaminated_real
#print axioms JurisLean.Candidates.U04_2SharpConditioning20261029.contaminated_real
#check JurisLean.Candidates.U04_2SharpConditioning20261029.contaminated_probability
#print axioms JurisLean.Candidates.U04_2SharpConditioning20261029.contaminated_probability
#check JurisLean.Candidates.U04_2SharpConditioning20261029.compatible_law_mixture
#print axioms JurisLean.Candidates.U04_2SharpConditioning20261029.compatible_law_mixture
#check JurisLean.Candidates.U04_2SharpConditioning20261029.conditional_contamination_bound
#print axioms JurisLean.Candidates.U04_2SharpConditioning20261029.conditional_contamination_bound
#check JurisLean.Candidates.U04_2SharpConditioning20261029.conditional_contamination_zero_component
#print axioms JurisLean.Candidates.U04_2SharpConditioning20261029.conditional_contamination_zero_component
#check JurisLean.Candidates.U04_2SharpConditioning20261029.conditioning_amplification_example
#print axioms JurisLean.Candidates.U04_2SharpConditioning20261029.conditioning_amplification_example
#check JurisLean.Candidates.U04_2SharpConditioning20261029.invalid_conditioning_and_enclosure_inputs
#print axioms JurisLean.Candidates.U04_2SharpConditioning20261029.invalid_conditioning_and_enclosure_inputs

end JurisLean.Candidates.U04_2SharpConditioning20261029
