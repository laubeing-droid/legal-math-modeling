import JurisLean.RemainingClosure.W1Transport

/-!
Both directions of the finite-matrix/measure-coupling identification. An
arbitrary coupling is forced onto the four actual atoms by its marginals;
finite support is derived, never assumed. Source only; CI_NOT_RUN.
-/
namespace LegalMath.RemainingClosure.W1Atoms

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open LegalMath20261108.ClosedLoop LegalMath20261108.SequentialFeedback
open LegalMath20261108.UnifiedFeedbackBridge
open LegalMath20261110.FeedbackW1
open LegalMath.RemainingClosure.W1Transport

noncomputable section

lemma after_distinct (s : State) : after s false ≠ after s true := by
  intro h
  have hf := congrArg Prod.fst h
  norm_num [after_formula, RepaymentExample.bit] at hf

def atomSet (s : State) : Finset State := by
  classical
  exact {after s false, after s true}

lemma step_supported_atoms (s : State) : ∀ᵐ u ∂step model s, u ∈ atomSet s := by
  classical
  rw [step_two_atoms, ae_add_measure_iff]
  exact ⟨ae_smul_measure (by simp [atomSet]) _, ae_smul_measure (by simp [atomSet]) _⟩

lemma coupling_probability (s t : State) (ρ : Measure (State × State))
    (hρ : ρ ∈ couplingMeasures (step model s) (step model t)) : IsProbabilityMeasure ρ :=
  ⟨by
    have hu := congrArg (fun μ : Measure State => μ Set.univ) hρ.1
    simpa only [Measure.map_apply measurable_fst MeasurableSet.univ,
      Set.preimage_univ, measure_univ] using hu⟩

lemma coupling_four_atoms (s t : State) (ρ : Measure (State × State))
    (hρ : ρ ∈ couplingMeasures (step model s) (step model t)) :
    ρ = ρ {(after s false, after t false)} • Measure.dirac (after s false, after t false) +
      ρ {(after s false, after t true)} • Measure.dirac (after s false, after t true) +
      ρ {(after s true, after t false)} • Measure.dirac (after s true, after t false) +
      ρ {(after s true, after t true)} • Measure.dirac (after s true, after t true) := by
  classical
  have hf : ∀ᵐ z ∂ρ, z.1 ∈ atomSet s := by
    apply (ae_map_iff measurable_fst.aemeasurable (by measurability)).mp
    simpa only [hρ.1] using step_supported_atoms s
  have hg : ∀ᵐ z ∂ρ, z.2 ∈ atomSet t := by
    apply (ae_map_iff measurable_snd.aemeasurable (by measurability)).mp
    simpa only [hρ.2] using step_supported_atoms t
  have both : ∀ᵐ z ∂ρ, z ∈ (atomSet s).product (atomSet t) := by
    filter_upwards [hf,hg] with z hz1 hz2
    exact Finset.mem_product.mpr ⟨hz1,hz2⟩
  have hd := Measure.ae_mem_finset_iff.mp both
  simpa [Finset.sum_product, atomSet, after_distinct, (after_distinct s).symm,
    (after_distinct t).symm, add_assoc] using hd

/-- The full measure coupling, including its cost, is determined by one cell. -/
theorem all_couplings_are_matrices (s t : State) (ρ : Measure (State × State))
    (hρ : ρ ∈ couplingMeasures (step model s) (step model t)) :
    ∃ r : ℝ, admissible (probability s) (probability t) r ∧ ρ = couplingAt s t r := by
  classical
  letI : IsProbabilityMeasure ρ := coupling_probability s t ρ hρ
  have hd := coupling_four_atoms s t ρ hρ
  have row0 : ρ {(after s false, after t false)} + ρ {(after s false, after t true)} =
      ENNReal.ofReal (1-probability s) := by
    have he := congrArg (fun μ : Measure State => μ {after s false}) hρ.1
    rw [hd, step_two_atoms] at he
    simpa [Measure.map_add _ _ measurable_fst, Measure.map_smul,
      Measure.map_dirac' measurable_fst, Measure.add_apply, Measure.smul_apply,
      smul_eq_mul, after_distinct, (after_distinct s).symm] using he
  have row1 : ρ {(after s true, after t false)} + ρ {(after s true, after t true)} =
      ENNReal.ofReal (probability s) := by
    have he := congrArg (fun μ : Measure State => μ {after s true}) hρ.1
    rw [hd, step_two_atoms] at he
    simpa [Measure.map_add _ _ measurable_fst, Measure.map_smul,
      Measure.map_dirac' measurable_fst, Measure.add_apply, Measure.smul_apply,
      smul_eq_mul, after_distinct, (after_distinct s).symm] using he
  have col1 : ρ {(after s false, after t true)} + ρ {(after s true, after t true)} =
      ENNReal.ofReal (probability t) := by
    have he := congrArg (fun μ : Measure State => μ {after t true}) hρ.2
    rw [hd, step_two_atoms] at he
    simpa [Measure.map_add _ _ measurable_snd, Measure.map_smul,
      Measure.map_dirac' measurable_snd, Measure.add_apply, Measure.smul_apply,
      smul_eq_mul, after_distinct, (after_distinct t).symm] using he
  have hr0 := congrArg ENNReal.toReal row0
  have hr1 := congrArg ENNReal.toReal row1
  have hc1 := congrArg ENNReal.toReal col1
  simp only [ENNReal.toReal_add (measure_ne_top ρ _) (measure_ne_top ρ _),
    ENNReal.toReal_ofReal (sub_nonneg.mpr (probability_bounds s).2)] at hr0
  simp only [ENNReal.toReal_add (measure_ne_top ρ _) (measure_ne_top ρ _),
    ENNReal.toReal_ofReal (probability_bounds s).1] at hr1
  simp only [ENNReal.toReal_add (measure_ne_top ρ _) (measure_ne_top ρ _),
    ENNReal.toReal_ofReal (probability_bounds t).1] at hc1
  let a : ℝ := (ρ {(after s false, after t false)}).toReal
  let b : ℝ := (ρ {(after s false, after t true)}).toReal
  let c : ℝ := (ρ {(after s true, after t false)}).toReal
  let r : ℝ := (ρ {(after s true, after t true)}).toReal
  have ha : 0 ≤ a := ENNReal.toReal_nonneg
  have hb : 0 ≤ b := ENNReal.toReal_nonneg
  have hc : 0 ≤ c := ENNReal.toReal_nonneg
  have hr : 0 ≤ r := ENNReal.toReal_nonneg
  change a+b=1-probability s at hr0
  change c+r=probability s at hr1
  change b+r=probability t at hc1
  have ea : a = 1-probability s-probability t+r := by linarith
  have eb : b = probability t-r := by linarith
  have ec : c = probability s-r := by linarith
  refine ⟨r, ⟨hr, by linarith, by linarith, by linarith⟩, ?_⟩
  have hma : ρ {(after s false, after t false)} =
      ENNReal.ofReal (1-probability s-probability t+r) := by
    rw [← ea]
    exact (ENNReal.ofReal_toReal (measure_ne_top ρ _)).symm
  have hmb : ρ {(after s false, after t true)} = ENNReal.ofReal (probability t-r) := by
    rw [← eb]
    exact (ENNReal.ofReal_toReal (measure_ne_top ρ _)).symm
  have hmc : ρ {(after s true, after t false)} = ENNReal.ofReal (probability s-r) := by
    rw [← ec]
    exact (ENNReal.ofReal_toReal (measure_ne_top ρ _)).symm
  have hmr : ENNReal.ofReal r = ρ {(after s true, after t true)} :=
    ENNReal.ofReal_toReal (measure_ne_top ρ _)
  simpa only [couplingAt, ← hma, ← hmb, ← hmc, hmr] using hd

lemma finite_cost_iInf (s t : State) :
    ENNReal.ofReal (w1 s t) =
      ⨅ r : {r : ℝ // admissible (probability s) (probability t) r},
        ENNReal.ofReal (cost s t r) := by
  letI : Nonempty {r : ℝ // admissible (probability s) (probability t) r} :=
    ⟨⟨_,monotone_admissible s t⟩⟩
  have eqset : {v | ∃ r, admissible (probability s) (probability t) r ∧ v = cost s t r} =
      Set.range (fun r : {r : ℝ // admissible (probability s) (probability t) r} => cost s t r) := by
    ext v
    constructor
    · rintro ⟨r,hr,hv⟩
      exact ⟨⟨r,hr⟩,hv.symm⟩
    · rintro ⟨r,rfl⟩
      exact ⟨r,r.property,rfl⟩
  rw [w1, eqset, sInf_range, ENNReal.ofReal_iInf]

/-- The exact original target, for every pair of real states. -/
theorem twoAtomIdentification : twoAtomIdentificationTarget := by
  intro s t
  rw [finite_cost_iInf]
  apply le_antisymm
  · apply le_sInf
    rintro v ⟨ρ,hρ,rfl⟩
    obtain ⟨r,hr,rfl⟩ := all_couplings_are_matrices s t ρ hρ
    rw [couplingAt_cost s t r hr]
    exact iInf_le _ ⟨r,hr⟩
  · refine le_iInf fun r => ?_
    exact (distributionW1_le_cost _ (couplingAt_mem s t r r.property)).trans_eq
      (couplingAt_cost s t r r.property)

#print axioms coupling_four_atoms
#print axioms all_couplings_are_matrices
#print axioms twoAtomIdentification

end
end LegalMath.RemainingClosure.W1Atoms
