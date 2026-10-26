import JurisLean.Candidates.Final20261021.Learning
import Mathlib.Order.ConditionallyCompleteLattice.Basic

namespace JurisLean.Candidates.LearningRisk20261027

noncomputable section

-- Original U01.1 / correction S01: all three risks use one population and loss.
-- The csInf APIs below were checked in pinned Mathlib c5ea0035, not inferred
-- from a theorem name. These results do not certify a real measurement model.
def riskInf {H : Type*} (risk : H → ℝ) (models : Set H) : ℝ :=
  sInf (risk '' models)

theorem risk_image_bddBelow {H : Type*} (risk : H → ℝ) (models : Set H)
    (nonnegative : ∀ h ∈ models, 0 ≤ risk h) : BddBelow (risk '' models) := by
  refine ⟨0, ?_⟩
  rintro _ ⟨h, hh, rfl⟩
  exact nonnegative h hh

theorem riskInf_mono {H : Type*} (risk : H → ℝ) (small large : Set H)
    (nonempty : small.Nonempty) (included : small ⊆ large)
    (nonnegative : ∀ h ∈ large, 0 ≤ risk h) :
    riskInf risk large ≤ riskInf risk small := by
  apply csInf_le_csInf (risk_image_bddBelow risk large nonnegative)
  · obtain ⟨h, hh⟩ := nonempty
    exact ⟨risk h, ⟨h, hh, rfl⟩⟩
  · rintro _ ⟨h, hh, rfl⟩
    exact ⟨h, included hh, rfl⟩

theorem riskInf_eq_of_minimum {H : Type*} (risk : H → ℝ) (models : Set H)
    (chosen : H) (member : chosen ∈ models)
    (minimum : ∀ h ∈ models, risk chosen ≤ risk h) :
    riskInf risk models = risk chosen := by
  have lower : ∀ y ∈ risk '' models, risk chosen ≤ y := by
    rintro _ ⟨h, hh, rfl⟩
    exact minimum h hh
  apply le_antisymm
  · exact csInf_le ⟨risk chosen, lower⟩ ⟨chosen, member, rfl⟩
  · exact le_csInf ⟨risk chosen, ⟨chosen, member, rfl⟩⟩ lower

theorem u01_1_three_part_risk_decomposition {H : Type*} (risk : H → ℝ)
    (visible represented heads : Set H) (chosen : H) (member : chosen ∈ heads)
    (headIncluded : heads ⊆ represented) (representationIncluded : represented ⊆ visible)
    (nonnegative : ∀ h ∈ visible, 0 ≤ risk h) :
    risk chosen - riskInf risk visible =
      (riskInf risk represented - riskInf risk visible) +
      (riskInf risk heads - riskInf risk represented) +
      (risk chosen - riskInf risk heads) ∧
    0 ≤ riskInf risk represented - riskInf risk visible ∧
    0 ≤ riskInf risk heads - riskInf risk represented := by
  refine ⟨by ring, ?_, ?_⟩
  · exact sub_nonneg.mpr (riskInf_mono risk represented visible
      ⟨chosen, headIncluded member⟩ representationIncluded nonnegative)
  · exact sub_nonneg.mpr (riskInf_mono risk heads represented ⟨chosen, member⟩
      headIncluded (fun h hh => nonnegative h (representationIncluded hh)))

-- A uniform event controls an arbitrary data-selected member of this SAME class.
-- The optimization condition compares empirical risks, not the desired true risk.
theorem u01_1_uniform_event_erm_oracle {H : Type*} (risk empirical : H → ℝ)
    (models : Set H) (chosen : H) (member : chosen ∈ models) (ε opt : ℝ)
    (uniform : ∀ h ∈ models, |risk h - empirical h| ≤ ε)
    (optimization : ∀ h ∈ models, empirical chosen ≤ empirical h + opt) :
    risk chosen ≤ riskInf risk models + 2 * ε + opt := by
  have lower : risk chosen - 2 * ε - opt ≤ riskInf risk models := by
    change risk chosen - 2 * ε - opt ≤ sInf (risk '' models)
    have nonempty : (risk '' models).Nonempty := ⟨risk chosen, ⟨chosen, member, rfl⟩⟩
    apply le_csInf nonempty
    rintro _ ⟨h, hh, rfl⟩
    have hc := (abs_le.mp (uniform chosen member)).2
    have hh' := (abs_le.mp (uniform h hh)).1
    have ho := optimization h hh
    linarith
  linarith

theorem u01_1_total_excess_bound {H : Type*} (risk empirical : H → ℝ)
    (visible represented heads : Set H) (chosen : H) (member : chosen ∈ heads)
    (ε opt : ℝ) (uniform : ∀ h ∈ heads, |risk h - empirical h| ≤ ε)
    (optimization : ∀ h ∈ heads, empirical chosen ≤ empirical h + opt) :
    risk chosen - riskInf risk visible ≤
      (riskInf risk represented - riskInf risk visible) +
      (riskInf risk heads - riskInf risk represented) + 2 * ε + opt := by
  have bound := u01_1_uniform_event_erm_oracle risk empirical heads chosen member
    ε opt uniform optimization
  linarith

-- Finite visible input, binary 0-1 loss. Weights are population masses, and
-- eta(x) is the conditional positive-label probability, not a legal truth value.
def finiteBinaryRisk {X : Type*} [Fintype X] (weight eta : X → ℝ) (h : X → Bool) : ℝ :=
  ∑ x, weight x * (if h x then 1 - eta x else eta x)

def representedClass {X Z : Type*} (φ : X → Z) : Set (X → Bool) :=
  Set.range (fun g : Z → Bool => g ∘ φ)

def fiberBayes {Z : Type*} (q : Z → ℝ) : Z → Bool := by
  classical
  exact fun z => if (1 / 2 : ℝ) ≤ q z then true else false

theorem fiberBayes_minimizes {X Z : Type*} [Fintype X]
    (weight : X → ℝ) (nonnegative : ∀ x, 0 ≤ weight x) (φ : X → Z)
    (q : Z → ℝ) (h : X → Bool) :
    finiteBinaryRisk weight (q ∘ φ) (fiberBayes q ∘ φ) ≤
      finiteBinaryRisk weight (q ∘ φ) h := by
  apply Finset.sum_le_sum
  intro x _
  apply mul_le_mul_of_nonneg_left _ (nonnegative x)
  by_cases hq : (1 / 2 : ℝ) ≤ q (φ x)
  · have hq' : (2 : ℝ)⁻¹ ≤ q (φ x) := by simpa only [one_div] using hq
    cases hx : h x <;> simp [fiberBayes, Function.comp_def, hq', hx] <;> linarith
  · have hq' : ¬(2 : ℝ)⁻¹ ≤ q (φ x) := by simpa only [one_div] using hq
    cases hx : h x <;> simp [fiberBayes, Function.comp_def, hq', hx] <;> linarith

theorem u01_1_sufficient_representation_zero_gap {X Z : Type*} [Fintype X]
    (weight : X → ℝ) (nonnegative : ∀ x, 0 ≤ weight x) (φ : X → Z)
    (q : Z → ℝ) :
    riskInf (finiteBinaryRisk weight (q ∘ φ)) (representedClass φ) =
      riskInf (finiteBinaryRisk weight (q ∘ φ)) Set.univ := by
  have minimum := fun h => fiberBayes_minimizes weight nonnegative φ q h
  have represented := riskInf_eq_of_minimum (finiteBinaryRisk weight (q ∘ φ))
    (representedClass φ) (fiberBayes q ∘ φ) ⟨fiberBayes q, rfl⟩ (fun h _ => minimum h)
  have visible := riskInf_eq_of_minimum (finiteBinaryRisk weight (q ∘ φ))
    Set.univ (fiberBayes q ∘ φ) (Set.mem_univ _) (fun h _ => minimum h)
  exact represented.trans visible.symm

-- The lost-information example is the actual uniform two-point 0-1 risk.
def twoPointRisk (h : Bool → Bool) : ℝ :=
  (if h false = false then 0 else 1) / 2 + (if h true = true then 0 else 1) / 2

theorem twoPointRisk_is_uniform_binary_risk (h : Bool → Bool) :
    twoPointRisk h = finiteBinaryRisk (fun _ : Bool => (1 / 2 : ℝ))
      (fun x => if x then 1 else 0) h := by
  have univ : (Finset.univ : Finset Bool) = {false, true} := by decide
  cases hf : h false <;> cases ht : h true <;>
    norm_num [twoPointRisk, finiteBinaryRisk, univ, hf, ht]

theorem u01_1_collapsed_representation_half_gap :
    riskInf twoPointRisk Set.univ = 0 ∧
    riskInf twoPointRisk (representedClass (fun _ : Bool => ())) = (1 / 2 : ℝ) := by
  have nonnegative (h : Bool → Bool) : 0 ≤ twoPointRisk h := by
    cases hf : h false <;> cases ht : h true <;> norm_num [twoPointRisk, hf, ht]
  have exactZero : twoPointRisk id = 0 := by norm_num [twoPointRisk]
  have full := riskInf_eq_of_minimum twoPointRisk Set.univ id (Set.mem_univ _)
    (fun h _ => by rw [exactZero]; exact nonnegative h)
  have collapsed (h : Bool → Bool) (hh : h ∈ representedClass (fun _ : Bool => ())) :
      twoPointRisk h = (1 / 2 : ℝ) := by
    obtain ⟨g, rfl⟩ := hh
    cases hg : g () <;> norm_num [twoPointRisk, Function.comp_def, hg]
  have constant : (fun _ : Bool => false) ∈ representedClass (fun _ : Bool => ()) :=
    ⟨(fun _ : Unit => false), rfl⟩
  have repr := riskInf_eq_of_minimum twoPointRisk (representedClass (fun _ : Bool => ()))
    (fun _ => false) constant (fun h hh => by
      rw [collapsed _ constant, collapsed h hh])
  exact ⟨full.trans exactZero, repr.trans (collapsed _ constant)⟩

end
end JurisLean.Candidates.LearningRisk20261027

#print axioms JurisLean.Candidates.LearningRisk20261027.u01_1_three_part_risk_decomposition
#print axioms JurisLean.Candidates.LearningRisk20261027.u01_1_uniform_event_erm_oracle
#print axioms JurisLean.Candidates.LearningRisk20261027.u01_1_total_excess_bound
#print axioms JurisLean.Candidates.LearningRisk20261027.u01_1_sufficient_representation_zero_gap
#print axioms JurisLean.Candidates.LearningRisk20261027.u01_1_collapsed_representation_half_gap
