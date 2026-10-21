import JurisLean.Candidates.Final20261021.Interfaces

namespace JurisLean.Candidates.Final20261021.Harness

def Safe {W S A : Type} (possible : W → Prop) (allowed : W → S → A → Prop)
    (successor : W → S → A → S → Prop) (invariant : W → S → Prop)
    (s : S) (a : A) : Prop :=
  ∀ w, possible w → allowed w s a ∧ ∀ t, successor w s a t → invariant w t

theorem u02_1_gate_sound_under_Ke {W S A : Type} (possible : W → Prop)
    (allowed : W → S → A → Prop) (successor : W → S → A → S → Prop)
    (invariant : W → S → Prop) (s t : S) (a : A) (w : W)
    (actualWorld : possible w) (safe : Safe possible allowed successor invariant s a)
    (actualStep : successor w s a t) : allowed w s a ∧ invariant w t :=
  ⟨(safe w actualWorld).1, (safe w actualWorld).2 t actualStep⟩

def tableSafe {W S A : Type} [Fintype W] [Fintype S]
    (possible : W → Bool) (allowed : W → S → A → Bool)
    (successor : W → S → A → S → Bool) (invariant : W → S → Bool)
    (s : S) (a : A) : Bool :=
  decide (∀ w, possible w = true → allowed w s a = true ∧
    ∀ t, successor w s a t = true → invariant w t = true)

def proposed_harness_gate {W S A : Type} [Fintype W] [Fintype S]
    (possible : W → Bool) (allowed : W → S → A → Bool)
    (successor : W → S → A → S → Bool) (invariant : W → S → Bool)
    (s : S) (candidates : List A) : List A :=
  candidates.filter (tableSafe possible allowed successor invariant s)

theorem u02_3_finite_gate_enumeration {W S A : Type} [Fintype W] [Fintype S]
    (possible : W → Bool) (allowed : W → S → A → Bool)
    (successor : W → S → A → S → Bool) (invariant : W → S → Bool)
    (s : S) (candidates : List A) (a : A) :
    a ∈ proposed_harness_gate possible allowed successor invariant s candidates ↔
      a ∈ candidates ∧ Safe (fun w => possible w = true)
        (fun w s a => allowed w s a = true) (fun w s a t => successor w s a t = true)
        (fun w t => invariant w t = true) s a := by
  simp [proposed_harness_gate, tableSafe, Safe]

-- Zero coverage is undefined, never reported as zero conditional risk.
def conditionalRisk (badAccepted accepted : ℚ) : Result ℚ :=
  if 0 < accepted then .known (badAccepted / accepted) else .unknown .notIdentified

theorem zero_coverage_not_zero_risk (b : ℚ) :
    conditionalRisk b 0 = .unknown .notIdentified := by simp [conditionalRisk]

open MeasureTheory

-- This measure may be P_H. The per-history-to-marginal tower step is
-- separately recorded in the clause ledger; it is not assumed proved here.
theorem risk_union_in_declared_measure {Ω I : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (s : Finset I)
    (bad : I → Set Ω) (δ : I → ℝ)
    (bound : ∀ i ∈ s, μ.real (bad i) ≤ δ i) :
    μ.real (⋃ i ∈ s, bad i) ≤ ∑ i ∈ s, δ i := by
  exact le_trans (measureReal_biUnion_finset_le s bad)
    (Finset.sum_le_sum fun i hi => bound i hi)

-- Validity must first hold in P_H; a bound in P need not survive conditioning.
theorem condition_to_global (globalBad insideBad outsideBad conditionMass α ε : ℝ)
    (positive : 0 < conditionMass) (massLeOne : conditionMass ≤ 1)
    (epsNonneg : 0 ≤ ε) (partition : globalBad = insideBad + outsideBad)
    (conditional : insideBad / conditionMass ≤ ε) (outside : outsideBad ≤ α) :
    globalBad ≤ α + ε := by
  have h := (div_le_iff₀ positive).mp conditional
  nlinarith

end JurisLean.Candidates.Final20261021.Harness
