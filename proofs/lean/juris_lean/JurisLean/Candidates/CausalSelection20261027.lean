import JurisLean.Candidates.Final20261021.Behavior
import JurisLean.Candidates.Final20261021.Policy
import Mathlib.Data.Fintype.BigOperators

/-!
Original 11.3--11.5 / correction S11: finite selection recovery and transport.
The generative kernel states the causal premises: treatment and recording
depend on X,A, not on the latent potential-outcome variable U. The response
under the observed action is the same potential-response function used under
intervention. These are modelling/identification premises, not results of fit.
-/

namespace JurisLean.Candidates.CausalSelection20261027

open JurisLean.Candidates.Final20261021

def retentionMass (rho : ℚ) (selected : Bool) : ℚ :=
  if selected then rho else 1 - rho

theorem retention_mass_sum (rho : ℚ) : (∑ s : Bool, retentionMass rho s) = 1 := by
  simp [Fintype.sum_bool, retentionMass]

def selectionJoint {X U A : Type*} (mass : X → ℚ) (latent : X → U → ℚ)
    (assignment recording : X → A → ℚ) (x : X) (u : U) (a : A) (s : Bool) : ℚ :=
  mass x * latent x u * assignment x a * retentionMass (recording x a) s

theorem full_selection_kernel_normalized {X U A : Type*}
    [Fintype X] [Fintype U] [Fintype A]
    (mass : X → ℚ) (latent : X → U → ℚ) (assignment recording : X → A → ℚ)
    (massTotal : ∑ x, mass x = 1) (latentTotal : ∀ x, ∑ u, latent x u = 1)
    (assignmentTotal : ∀ x, ∑ a, assignment x a = 1) :
    (∑ x, ∑ u, ∑ a, ∑ s : Bool, selectionJoint mass latent assignment recording x u a s) = 1 := by
  have selectedSum (x : X) (u : U) (a : A) :
      (∑ s : Bool, selectionJoint mass latent assignment recording x u a s) =
        mass x * latent x u * assignment x a := by
    simp only [selectionJoint, ← Finset.mul_sum, retention_mass_sum, mul_one]
  simp_rw [selectedSum, ← Finset.mul_sum, assignmentTotal, mul_one, latentTotal, massTotal]

theorem full_selection_kernel_nonnegative {X U A : Type*}
    (mass : X → ℚ) (latent : X → U → ℚ) (assignment recording : X → A → ℚ)
    (hm : ∀ x, 0 ≤ mass x) (hu : ∀ x u, 0 ≤ latent x u)
    (ha : ∀ x a, 0 ≤ assignment x a) (hr : ∀ x a, 0 ≤ recording x a ∧ recording x a ≤ 1)
    (x : X) (u : U) (a : A) (s : Bool) :
    0 ≤ selectionJoint mass latent assignment recording x u a s := by
  have positive : 0 ≤ retentionMass (recording x a) s := by
    cases s <;> simp only [retentionMass, Bool.false_eq_true, ↓reduceIte]
    · exact sub_nonneg.mpr (hr x a).2
    · exact (hr x a).1
  exact mul_nonneg (mul_nonneg (mul_nonneg (hm x) (hu x u)) (ha x a)) positive

def selectionRecoveryValue {X U A : Type*} [Fintype X] [Fintype U]
    (mass : X → ℚ) (latent : X → U → ℚ) (assignment recording : X → A → ℚ)
    (response : X → U → A → ℚ) (action : A) : ℚ :=
  ∑ x, ∑ u, selectionJoint mass latent assignment recording x u action true *
    (response x u action / (assignment x action * recording x action))

def interventionValue {X U A : Type*} [Fintype X] [Fintype U]
    (mass : X → ℚ) (latent : X → U → ℚ) (response : X → U → A → ℚ)
    (action : A) : ℚ :=
  ∑ x, mass x * ∑ u, latent x u * response x u action

-- Both treatment support and recording support are needed on populated X.
-- No denominator condition is imposed on genuinely zero-mass strata.
theorem selected_weight_recovery {X U A : Type*} [Fintype X] [Fintype U]
    (mass : X → ℚ) (latent : X → U → ℚ) (assignment recording : X → A → ℚ)
    (response : X → U → A → ℚ) (action : A)
    (support : ∀ x, mass x ≠ 0 → assignment x action ≠ 0 ∧ recording x action ≠ 0) :
    selectionRecoveryValue mass latent assignment recording response action =
      interventionValue mass latent response action := by
  unfold selectionRecoveryValue interventionValue
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u _
  by_cases zero : mass x = 0
  · simp [selectionJoint, zero]
  · obtain ⟨treatment, selected⟩ := support x zero
    simp only [selectionJoint, retentionMass, ↓reduceIte]
    field_simp [treatment, selected]
    <;> ring

def selectionPopulationMass {X U A : Type*} [Fintype X] [Fintype U] [Fintype A]
    (mass : X → ℚ) (latent : X → U → ℚ) (assignment recording : X → A → ℚ) : ℚ :=
  ∑ x, ∑ u, ∑ a, selectionJoint mass latent assignment recording x u a true

-- A database conditional on S=1 uses a different, normalized expectation.
-- Its normalization is computed from the full declared population kernel.
theorem selected_database_requires_population_normalization {X U A : Type*}
    [Fintype X] [Fintype U] [Fintype A]
    (mass : X → ℚ) (latent : X → U → ℚ) (assignment recording : X → A → ℚ)
    (response : X → U → A → ℚ) (action : A)
    (support : ∀ x, mass x ≠ 0 → assignment x action ≠ 0 ∧ recording x action ≠ 0)
    (nonzero : selectionPopulationMass mass latent assignment recording ≠ 0) :
    selectionPopulationMass mass latent assignment recording *
      (selectionRecoveryValue mass latent assignment recording response action /
        selectionPopulationMass mass latent assignment recording) =
      interventionValue mass latent response action := by
  rw [mul_div_cancel₀ _ nonzero]
  exact selected_weight_recovery mass latent assignment recording response action support

abbrev SelectionAtom := Bool × Bool
abbrev SelectionVisible := Bool × Bool × Option Bool

def colliderVisible (z : SelectionAtom) : SelectionVisible :=
  (z.1, z.1 == z.2, if z.1 == z.2 then some z.2 else none)

def directVisible (z : SelectionAtom) : SelectionVisible :=
  (z.1, z.2, if z.2 then some z.1 else none)

def visibleSelectionMass (view : SelectionAtom → SelectionVisible)
    (q : SelectionVisible) : ℚ :=
  ∑ z : SelectionAtom, if view z = q then 1/4 else 0

def selectedVisibleMean (view : SelectionAtom → SelectionVisible) (action : Bool) : ℚ :=
  visibleSelectionMass view (action, true, some true) /
    (visibleSelectionMass view (action, true, some true) +
      visibleSelectionMass view (action, true, some false))

def colliderPotential (_action : Bool) (z : SelectionAtom) : Bool := z.2
def directPotential (action : Bool) (_z : SelectionAtom) : Bool := action

def selectionInterventionMean (potential : Bool → SelectionAtom → Bool) (action : Bool) : ℚ :=
  ∑ z : SelectionAtom, (1/4) * Behavior.indicator (potential action z)

def selectionEffect (potential : Bool → SelectionAtom → Bool) : ℚ :=
  selectionInterventionMean potential true - selectionInterventionMean potential false

-- Complete visible law includes A,S and Y only when S=1, not just one score.
theorem selection_countermodels_have_identical_visible_law :
    ∀ a s : Bool, ∀ y : Option Bool,
      visibleSelectionMass colliderVisible (a, s, y) =
        visibleSelectionMass directVisible (a, s, y) := by decide

theorem selected_association_is_not_population_effect :
    selectedVisibleMean colliderVisible true - selectedVisibleMean colliderVisible false = 1 ∧
    selectedVisibleMean directVisible true - selectedVisibleMean directVisible false = 1 ∧
    selectionEffect colliderPotential = 0 ∧ selectionEffect directPotential = 1 := by decide

theorem no_visible_law_estimator_identifies_both
    (estimator : (SelectionVisible → ℚ) → ℚ) :
    ¬ (estimator (visibleSelectionMass colliderVisible) = selectionEffect colliderPotential ∧
       estimator (visibleSelectionMass directVisible) = selectionEffect directPotential) := by
  intro both
  have same : visibleSelectionMass colliderVisible = visibleSelectionMass directVisible := by
    funext q
    rcases q with ⟨a, s, y⟩
    exact selection_countermodels_have_identical_visible_law a s y
  have effects := selected_association_is_not_population_effect
  rw [same, effects.2.2.1, effects.2.2.2] at both
  linarith [both.1, both.2]

def transportedValue {X : Type*} [Fintype X]
    (source target sourceEffect : X → ℚ) : ℚ :=
  ∑ x, source x * (target x / source x) * sourceEffect x

def populationEffect {X : Type*} [Fintype X] (mass effect : X → ℚ) : ℚ :=
  ∑ x, mass x * effect x

theorem transport_requires_overlap_and_mean_stability {X : Type*} [Fintype X]
    (source target sourceEffect targetEffect : X → ℚ)
    (overlap : ∀ x, target x ≠ 0 → source x ≠ 0)
    (stable : ∀ x, target x ≠ 0 → sourceEffect x = targetEffect x) :
    transportedValue source target sourceEffect = populationEffect target targetEffect := by
  unfold transportedValue populationEffect
  apply Finset.sum_congr rfl
  intro x _
  by_cases zero : target x = 0
  · simp [zero]
  · have nonzero := overlap x zero
    rw [stable x zero]
    field_simp [nonzero]

def sourceMix (x : Bool) : ℚ := if x then 1/5 else 4/5
def targetMix (x : Bool) : ℚ := if x then 4/5 else 1/5
def stableGroupEffect (x : Bool) : ℚ := if x then -3/10 else 3/10

theorem actual_transport_reweights_the_target :
    populationEffect sourceMix stableGroupEffect = 9/50 ∧
    transportedValue sourceMix targetMix stableGroupEffect = -9/50 ∧
    targetMix false / sourceMix false = 1/4 ∧
    targetMix true / sourceMix true = 4 := by decide

-- Source observables and the target X law stay fixed. The target outcome
-- mechanism is unobserved; changing it can give effect 1 instead of -0.18.
structure TransportScenario where
  sourceDistribution : Bool → ℚ
  sourceEffects : Bool → ℚ
  targetDistribution : Bool → ℚ
  targetEffects : Bool → ℚ

def transportVisible (w : TransportScenario) :=
  (w.sourceDistribution, w.sourceEffects, w.targetDistribution)

def stableScenario : TransportScenario := ⟨sourceMix, stableGroupEffect, targetMix, stableGroupEffect⟩
def changedScenario : TransportScenario := ⟨sourceMix, stableGroupEffect, targetMix, fun _ => 1⟩

theorem source_and_target_mix_do_not_identify_new_effect :
    transportVisible stableScenario = transportVisible changedScenario ∧
    populationEffect stableScenario.targetDistribution stableScenario.targetEffects = -9/50 ∧
    populationEffect changedScenario.targetDistribution changedScenario.targetEffects = 1 := by
  refine ⟨rfl, ?_, ?_⟩ <;> decide

end JurisLean.Candidates.CausalSelection20261027

