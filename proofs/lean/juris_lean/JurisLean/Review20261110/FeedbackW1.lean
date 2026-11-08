import JurisLean.UnifiedFeedbackBridge

/-!
Finite transport for the actual two-atom feedback kernel. This file proves the
one-step W1 estimate using all couplings of its two Bernoulli atoms. It does not
claim the measure-space completeness / invariant-measure theorem. The general
lifting and completeness obligations are explicitly recorded in the appendix.
Source only; CI_NOT_RUN until the subject-bound run is recorded.
-/
namespace LegalMath20261110.FeedbackW1

open MeasureTheory ProbabilityTheory
open LegalMath20261108.ClosedLoop LegalMath20261108.SequentialFeedback
open LegalMath20261108.UnifiedFeedbackBridge

noncomputable section

def dstar (s t : State) : ℝ := |s.1-t.1| + 4*|s.2-t.2|

lemma dstar_nonneg (s t : State) : 0 ≤ dstar s t := by
  unfold dstar
  positivity

lemma dstar_triangle (s t u : State) : dstar s u ≤ dstar s t + dstar t u := by
  have hx := abs_add_le (s.1-t.1) (t.1-u.1)
  have ht := abs_add_le (s.2-t.2) (t.2-u.2)
  rw [sub_add_sub_cancel] at hx ht
  dsimp [dstar]
  linarith

lemma same_outcome_distance (s t : State) (y : Bool) :
    dstar (after s y) (after t y) = |s.2-t.2| := by
  simp only [after_formula, dstar, sub_self, abs_zero, zero_add, learnExample]
  have e : s.2/4 + RepaymentExample.bit y/2 + 1/8 -
      (t.2/4 + RepaymentExample.bit y/2 + 1/8) = (s.2-t.2)/4 := by ring
  rw [e, abs_div]
  norm_num
  ring

lemma arbitrary_outcome_distance (s t : State) (y z : Bool) :
    dstar (after s y) (after t z) ≤ |s.2-t.2| + 3 := by
  calc
    dstar (after s y) (after t z) ≤
        dstar (after s y) (after t y) + dstar (after t y) (after t z) :=
      dstar_triangle _ _ _
    _ ≤ |s.2-t.2| + 3 := by
      rw [same_outcome_distance]
      cases y <;> cases z <;>
        norm_num [after_formula, dstar, learnExample, RepaymentExample.bit] <;>
        ring_nf <;> norm_num

/-- r is mass(1,1); the remaining three masses are fixed by the marginals. -/
def admissible (p q r : ℝ) : Prop :=
  0 ≤ r ∧ r ≤ p ∧ r ≤ q ∧ p+q-1 ≤ r

def cost (s t : State) (r : ℝ) : ℝ :=
  (1-probability s-probability t+r)*dstar (after s false) (after t false) +
  (probability t-r)*dstar (after s false) (after t true) +
  (probability s-r)*dstar (after s true) (after t false) +
  r*dstar (after s true) (after t true)

/-- Genuine primal W1 for the two transition measures: all 2x2 coupling
matrices are parameterized by r. It is not a marginal-only substitute. -/
def w1 (s t : State) : ℝ :=
  sInf {v | ∃ r, admissible (probability s) (probability t) r ∧ v = cost s t r}

lemma coupling_marginals (p q r : ℝ) :
    (1-p-q+r)+(q-r)=1-p ∧ (p-r)+r=p ∧
    (1-p-q+r)+(p-r)=1-q ∧ (q-r)+r=q := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> ring

lemma monotone_admissible (s t : State) :
    admissible (probability s) (probability t) (min (probability s) (probability t)) := by
  rcases probability_bounds s with ⟨hp0,hp1⟩
  rcases probability_bounds t with ⟨hq0,hq1⟩
  refine ⟨le_min hp0 hq0, min_le_left _ _, min_le_right _ _, ?_⟩
  exact le_min (by linarith) (by linarith)

lemma cost_nonneg (s t : State) (r : ℝ)
    (hr : admissible (probability s) (probability t) r) : 0 ≤ cost s t r := by
  rcases hr with ⟨hr0,hrp,hrq,hrlower⟩
  unfold cost
  have ha : 0 ≤ 1-probability s-probability t+r := by linarith
  have hb : 0 ≤ probability t-r := by linarith
  have hc : 0 ≤ probability s-r := by linarith
  exact add_nonneg (add_nonneg (add_nonneg (mul_nonneg ha (dstar_nonneg _ _))
    (mul_nonneg hb (dstar_nonneg _ _))) (mul_nonneg hc (dstar_nonneg _ _)))
    (mul_nonneg hr0 (dstar_nonneg _ _))

lemma monotone_cost_bound (s t : State) :
    cost s t (min (probability s) (probability t)) ≤
      |s.2-t.2| + 3*|probability s-probability t| := by
  have h01 := arbitrary_outcome_distance s t false true
  have h10 := arbitrary_outcome_distance s t true false
  rcases le_total (probability s) (probability t) with h | h
  · rw [min_eq_left h]
    have hpq : 0 ≤ probability t-probability s := by linarith
    have hm := mul_le_mul_of_nonneg_left h01 hpq
    simp only [cost, sub_self, zero_mul, add_zero, same_outcome_distance]
    rw [abs_of_nonpos (by linarith : probability s-probability t ≤ 0)]
    nlinarith
  · rw [min_eq_right h]
    have hpq : 0 ≤ probability s-probability t := by linarith
    have hm := mul_le_mul_of_nonneg_left h10 hpq
    simp only [cost, sub_self, zero_mul, zero_add, same_outcome_distance]
    rw [abs_of_nonneg (by linarith : 0 ≤ probability s-probability t)]
    nlinarith

lemma response_difference_bound (s t : State) (hs : s ∈ square) (ht : t ∈ square) :
    |probability s-probability t| ≤ |s.1-t.1|/4 + |s.2-t.2|/2 := by
  rw [probability_eq_response s hs, probability_eq_response t ht]
  have e : responseExample s.1 s.2-responseExample t.1 t.2 =
      (s.1-t.1)/4+(s.2-t.2)/2 := by unfold responseExample; ring
  rw [e]
  simpa [abs_div] using abs_add_le ((s.1-t.1)/4) ((s.2-t.2)/2)

/-- Expected cost of the common-uniform (monotone) coupling. -/
theorem one_step_contraction (s t : State) (hs : s ∈ square) (ht : t ∈ square) :
    cost s t (min (probability s) (probability t)) ≤ (3/4:ℝ)*dstar s t := by
  have hm := monotone_cost_bound s t
  have hp := response_difference_bound s t hs ht
  have hn := abs_nonneg (s.2-t.2)
  dsimp [dstar]
  linarith

/-- W1(K(s),K(t)) ≤ 3/4 d*(s,t), for the actual kernel's two-atom laws.
The arbitrary-input-law lifting is a separate, unproved Lean obligation. -/
theorem w1_contraction (s t : State) (hs : s ∈ square) (ht : t ∈ square) :
    w1 s t ≤ (3/4:ℝ)*dstar s t := by
  have lower : BddBelow {v | ∃ r, admissible (probability s) (probability t) r ∧ v = cost s t r} := by
    refine ⟨0, ?_⟩
    rintro v ⟨r,hr,rfl⟩
    exact cost_nonneg s t r hr
  exact (csInf_le lower ⟨_,monotone_admissible s t,rfl⟩).trans
    (one_step_contraction s t hs ht)

theorem actual_kernel_atoms (s : State) :
    step model s = ENNReal.ofReal (1-probability s) • Measure.dirac (after s false) +
      ENNReal.ofReal (probability s) • Measure.dirac (after s true) := step_two_atoms s

/-- Standard primal cost on arbitrary probability laws, distinct from the
finite matrix calculation above. These are explicit targets, not hypotheses
fed to the already proved finite estimate. Status: partial (Mathlib gap). -/
def couplingMeasures (μ ν : Measure State) : Set (Measure (State × State)) :=
  {ρ | ρ.map Prod.fst = μ ∧ ρ.map Prod.snd = ν}

def distributionW1 (μ ν : Measure State) : ℝ≥0∞ :=
  sInf ((fun ρ : Measure (State × State) =>
    ∫⁻ z, ENNReal.ofReal (dstar z.1 z.2) ∂ρ) '' couplingMeasures μ ν)

def twoAtomIdentificationTarget : Prop :=
  ∀ s t : State, ENNReal.ofReal (w1 s t) = distributionW1 (step model s) (step model t)

def generalW1LiftTarget : Prop :=
  ∀ μ ν : Measure State, IsProbabilityMeasure μ → IsProbabilityMeasure ν →
    μ square = 1 → ν square = 1 →
    distributionW1 (step model ∘ₘ μ) (step model ∘ₘ ν) ≤
      (3/4 : ℝ≥0∞) * distributionW1 μ ν

def uniqueInvariantLawTarget : Prop :=
  ∃! μ : Measure State,
    IsProbabilityMeasure μ ∧ μ square = 1 ∧ step model ∘ₘ μ = μ

#print axioms dstar_triangle
#print axioms coupling_marginals
#print axioms monotone_admissible
#print axioms cost_nonneg
#print axioms one_step_contraction
#print axioms w1_contraction
#print axioms actual_kernel_atoms

end
end LegalMath20261110.FeedbackW1
