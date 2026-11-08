import JurisLean.ClosedLoopKernel
import Mathlib.MeasureTheory.Function.FactorsThrough

namespace LegalMath20261110.ObservationBridge

open MeasureTheory ProbabilityTheory
open LegalMath20261108.ClosedLoop

variable {H Θ A O M V : Type*}
  [MeasurableSpace H] [MeasurableSpace Θ] [MeasurableSpace A]
  [MeasurableSpace O] [MeasurableSpace M] [MeasurableSpace V]

theorem doob_dynkin {X Y Z : Type*} [mY : MeasurableSpace Y]
    [MeasurableSpace Z] [StandardBorelSpace Z] [Nonempty Z] (obs : X → Y) (f : X → Z) :
    Measurable[mY.comap obs] f ↔ ∃ g : Y → Z, Measurable g ∧ f = g ∘ obs := by
  constructor
  · exact fun hf => hf.exists_eq_measurable_comp
  · rintro ⟨g, hg, rfl⟩
    have hm : Measurable[mY.comap obs] obs := fun s hs => ⟨s, hs, rfl⟩
    exact hg.comp hm

/-- Obs includes the entire usable input. Raw hidden outcomes have no extra
channel into the measurement. The physical outcome kernel is unrestricted. -/
structure ObsDynamics (H Θ A O M V : Type*)
    [MeasurableSpace H] [MeasurableSpace Θ] [MeasurableSpace A]
    [MeasurableSpace O] [MeasurableSpace M] [MeasurableSpace V] where
  dynamics : Dynamics H Θ A O M
  obs : H → V
  measurable_obs : Measurable obs
  policyView : Kernel (V × Θ) A
  measureView : V → M
  measurable_measureView : Measurable measureView
  policy_factors : ∀ h θ, dynamics.policy (h, θ) = policyView (obs h, θ)
  measure_factors : ∀ h a o, dynamics.measure h a o = measureView (obs h)

theorem no_leak (D : ObsDynamics H Θ A O M V) (h h' : H) (θ : Θ)
    (a a' : A) (o o' : O) (same : D.obs h = D.obs h') :
    D.dynamics.policy (h, θ) = D.dynamics.policy (h', θ) ∧
    D.dynamics.learn θ (D.dynamics.measure h a o) =
      D.dynamics.learn θ (D.dynamics.measure h' a' o') := by
  constructor
  · rw [D.policy_factors, D.policy_factors, same]
  · rw [D.measure_factors, D.measure_factors, same]

def usableView (_ : Bool) : Bool := false
def leakingMeasure (h : Bool) : Bool := h

theorem leak_counterexample : usableView false = usableView true ∧
    leakingMeasure false ≠ leakingMeasure true := by decide

theorem leak_has_no_factor : ¬ ∃ f : Bool → Bool, ∀ h, leakingMeasure h = f (usableView h) := by
  rintro ⟨f, hf⟩
  have h0 := hf false
  have h1 := hf true
  simp only [usableView, leakingMeasure] at h0 h1
  exact Bool.false_ne_true (h0.trans h1.symm)

#print axioms doob_dynkin
#print axioms no_leak
#print axioms leak_counterexample
#print axioms leak_has_no_factor

end LegalMath20261110.ObservationBridge
