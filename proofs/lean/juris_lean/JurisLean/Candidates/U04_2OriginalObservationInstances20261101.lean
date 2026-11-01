import JurisLean.Candidates.BernoulliMeanInstance20261031
import JurisLean.Candidates.LearningDependence20261027
import JurisLean.Candidates.ExactProbability20261027
import Mathlib.Probability.Independence.Basic

/-! Frozen04.2 L99 only: actual fixed-theta probability
laws, ten copies versus ten independent generated units. L101 uses the
existing generated-information and conditional-expectation declarations. -/

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators
open JurisLean.Candidates.BernoulliMeanInstance20261031

namespace JurisLean.Candidates.U04_2OriginalObservationInstances20261101

local instance : MeasurableSpace Bool := ⊤

theorem fixed_bernoulli_true_mass (theta : ℝ) (h0 : 0 ≤ theta) (h1 : theta ≤ 1) :
    bernoulliMeasure theta h0 h1 {true} = ENNReal.ofReal theta := by
  unfold bernoulliMeasure
  rw [PMF.toMeasure_apply_singleton _ true (by trivial), PMF.bernoulli_apply]
  rfl

private theorem fixed_bernoulli_probability (theta : ℝ)
    (h0 : 0 ≤ theta) (h1 : theta ≤ 1) :
    IsProbabilityMeasure (bernoulliMeasure theta h0 h1) := by
  unfold bernoulliMeasure
  infer_instance

/-- L99: the declared Bernoulli success marginal, on the given observation space. -/
theorem ten_copies_of_declared_marginal {Ω : Type*} [MeasurableSpace Ω]
    (theta : ℝ) (h0 : 0 ≤ theta) (_h1 : theta ≤ 1)
    (mu : Measure Ω) [IsProbabilityMeasure mu]
    (Z : Ω → Bool) (_hZ : Measurable Z)
    (hMass : mu (Z ⁻¹' ({true} : Set Bool)) = ENNReal.ofReal theta) :
    mu.real {w | ∀ _ : Fin 10, Z w = true} = theta := by
  have hs : {w | ∀ _ : Fin 10, Z w = true} = Z ⁻¹' ({true} : Set Bool) := by
    ext w
    constructor
    · intro h
      exact h 0
    · intro h i
      exact h
  change (mu {w | ∀ _ : Fin 10, Z w = true}).toReal = theta
  rw [hs, hMass, ENNReal.toReal_ofReal h0]

/-- L99: apply the existing finite independent-event product to the declared family,
rather than infer a likelihood from the number of files or assume a Pi law. -/
theorem ten_independent_of_declared_marginals {Ω : Type*} [MeasurableSpace Ω]
    (theta : ℝ) (h0 : 0 ≤ theta) (_h1 : theta ≤ 1)
    (mu : Measure Ω) [IsProbabilityMeasure mu]
    (X : Fin 10 → Ω → Bool) (_hX : ∀ i, Measurable (X i))
    (hInd : iIndepFun X mu)
    (hMass : ∀ i, mu ((X i) ⁻¹' ({true} : Set Bool)) = ENNReal.ofReal theta) :
    mu.real {w | ∀ i, X i w = true} = theta ^ 10 := by
  have hprod := hInd.measure_inter_preimage_eq_mul
    (Finset.univ : Finset (Fin 10)) (sets := fun _ => ({true} : Set Bool))
    (fun _ _ => measurableSet_singleton true)
  have hs :
      (⋂ i ∈ (Finset.univ : Finset (Fin 10)), (X i) ⁻¹' ({true} : Set Bool)) =
      {w | ∀ i, X i w = true} := by
    ext w
    simp
  have hp : mu {w | ∀ i, X i w = true} = (ENNReal.ofReal theta) ^ 10 := by
    simpa only [hs, hMass, Finset.prod_const, Finset.card_univ, Fintype.card_fin] using hprod
  change (mu {w | ∀ i, X i w = true}).toReal = theta ^ 10
  rw [hp, ENNReal.toReal_pow, ENNReal.toReal_ofReal h0]

def tenIndependentLaw (theta : ℝ) (h0 : 0 ≤ theta) (h1 : theta ≤ 1) :
    Measure (Fin 10 → Bool) :=
  Measure.pi (fun _ : Fin 10 => bernoulliMeasure theta h0 h1)

theorem ten_independent_law_probability (theta : ℝ)
    (h0 : 0 ≤ theta) (h1 : theta ≤ 1) :
    IsProbabilityMeasure (tenIndependentLaw theta h0 h1) := by
  letI := fixed_bernoulli_probability theta h0 h1
  unfold tenIndependentLaw
  infer_instance

theorem ten_copies_all_success_likelihood (theta : ℝ)
    (h0 : 0 ≤ theta) (h1 : theta ≤ 1) :
    (bernoulliMeasure theta h0 h1).real
      {w : Bool | ∀ _ : Fin 10, w = true} = theta := by
  letI := fixed_bernoulli_probability theta h0 h1
  exact ten_copies_of_declared_marginal theta h0 h1
    (bernoulliMeasure theta h0 h1) id measurable_id
    (by simpa using fixed_bernoulli_true_mass theta h0 h1)

theorem ten_independent_all_success_likelihood (theta : ℝ)
    (h0 : 0 ≤ theta) (h1 : theta ≤ 1) :
    (tenIndependentLaw theta h0 h1).real
      {w : Fin 10 → Bool | ∀ i, w i = true} = theta ^ 10 := by
  let nu := bernoulliMeasure theta h0 h1
  letI : IsProbabilityMeasure nu := fixed_bernoulli_probability theta h0 h1
  have hind : iIndepFun (fun i : Fin 10 => fun w : Fin 10 → Bool => w i)
      (Measure.pi (fun _ : Fin 10 => nu)) :=
    iIndepFun_pi (μ := fun _ : Fin 10 => nu)
      (X := fun _ : Fin 10 => (id : Bool → Bool))
      (fun _ => measurable_id.aemeasurable)
  have hmass (i : Fin 10) :
      (Measure.pi (fun _ : Fin 10 => nu))
        ((fun w : Fin 10 → Bool => w i) ⁻¹' ({true} : Set Bool)) =
      ENNReal.ofReal theta := by
    calc
      _ = (Measure.map (fun w : Fin 10 → Bool => w i)
          (Measure.pi (fun _ : Fin 10 => nu))) {true} :=
        (Measure.map_apply (measurable_pi_apply i) (measurableSet_singleton true)).symm
      _ = nu {true} := by
        rw [(measurePreserving_eval (fun _ : Fin 10 => nu) i).map_eq]
      _ = ENNReal.ofReal theta := fixed_bernoulli_true_mass theta h0 h1
  exact ten_independent_of_declared_marginals theta h0 h1
    (Measure.pi (fun _ : Fin 10 => nu))
    (fun i : Fin 10 => fun w : Fin 10 → Bool => w i)
    (fun i => measurable_pi_apply i) hind hmass

/-- L99/L131: the observation object is the same ten-coordinate tuple space. -/
def tenCopiedObservationLaw (theta : ℝ) (h0 : 0 ≤ theta) (h1 : theta ≤ 1) :
    Measure (Fin 10 → Bool) :=
  (bernoulliMeasure theta h0 h1).map (fun b : Bool => fun _ : Fin 10 => b)

/-- L131: wrong copied/IID mechanisms give different actual observation laws;
this is distinct from target ambiguity under one identical observation law. -/
theorem copied_and_independent_observation_laws_differ :
    tenCopiedObservationLaw (1 / 2) (by norm_num) (by norm_num) ≠
      tenIndependentLaw (1 / 2) (by norm_num) (by norm_num) := by
  let event : Set (Fin 10 → Bool) := {w | ∀ i, w i = true}
  have hrep : Measurable (fun b : Bool => fun _ : Fin 10 => b) :=
    measurable_pi_lambda _ (fun _ => measurable_id)
  have hEvent : MeasurableSet event := by
    have hs : event =
        ⋂ i : Fin 10, (fun w : Fin 10 → Bool => w i) ⁻¹' ({true} : Set Bool) := by
      ext w
      simp [event]
    rw [hs]
    exact MeasurableSet.iInter (fun i =>
      (measurableSet_singleton true).preimage (measurable_pi_apply i))
  have hcopy :
      (tenCopiedObservationLaw (1 / 2) (by norm_num) (by norm_num)).real event = 1 / 2 := by
    change (((bernoulliMeasure (1 / 2) (by norm_num) (by norm_num)).map
      (fun b : Bool => fun _ : Fin 10 => b)) event).toReal = 1 / 2
    rw [Measure.map_apply hrep hEvent]
    exact ten_copies_all_success_likelihood (1 / 2) (by norm_num) (by norm_num)
  have hind :
      (tenIndependentLaw (1 / 2) (by norm_num) (by norm_num)).real event =
        (1 / 2 : ℝ) ^ 10 :=
    ten_independent_all_success_likelihood (1 / 2) (by norm_num) (by norm_num)
  intro h
  have hh := congrArg (fun nu : Measure (Fin 10 → Bool) => nu.real event) h
  change (tenCopiedObservationLaw (1 / 2) (by norm_num) (by norm_num)).real event =
    (tenIndependentLaw (1 / 2) (by norm_num) (by norm_num)).real event at hh
  rw [hcopy, hind] at hh
  norm_num at hh

/-- L99: ten distinct model labels share one literal finite Bool cause.
No claim that model labels certify the identity of real-world observations. -/
theorem ten_distinct_labels_shared_cause :
    Function.Injective (fun i : Fin 10 => i) ∧
    ¬ iIndepFun (fun _ : Fin 10 => (id : Bool → Bool))
      (bernoulliMeasure (1 / 2) (by norm_num) (by norm_num)) := by
  refine ⟨fun _ _ h => h, ?_⟩
  have h0 : 0 ≤ (1 / 2 : ℝ) := by norm_num
  have h1 : (1 / 2 : ℝ) ≤ 1 := by norm_num
  letI := fixed_bernoulli_probability (1 / 2) h0 h1
  intro hi
  have hp := ten_independent_of_declared_marginals (1 / 2) h0 h1
    (bernoulliMeasure (1 / 2) h0 h1)
    (fun _ : Fin 10 => (id : Bool → Bool)) (fun _ => measurable_id) hi
    (fun _ => by simpa using fixed_bernoulli_true_mass (1 / 2) h0 h1)
  change (bernoulliMeasure (1 / 2) h0 h1).real
    {w : Bool | ∀ _ : Fin 10, w = true} = (1 / 2 : ℝ) ^ 10 at hp
  rw [ten_copies_all_success_likelihood] at hp
  norm_num at hp

end JurisLean.Candidates.U04_2OriginalObservationInstances20261101
