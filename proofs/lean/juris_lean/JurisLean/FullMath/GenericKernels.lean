import Mathlib

/-!
Reusable PARAMETERIZED proof candidates for the whole-plan construction.
Status at package delivery: SOURCE_DRAFT_CI_NOT_RUN.
These lemmas are not the 57 targets or the 134 business instantiations.
Do not alias all targets to a generic interface lemma. Implement each required
contract and discharge its concrete interpretation/reflection obligations.
-/
namespace JurisLean.FullMath.Kernels

section Binding
variable {I : Type}
def checkInput [DecidableEq I] (expected submitted : I) : Bool :=
  decide (expected = submitted)

theorem input_exact [DecidableEq I] {expected submitted : I}
    (h : checkInput expected submitted = true) : expected = submitted := by
  exact of_decide_eq_true h

theorem input_observation [DecidableEq I] {expected submitted : I}
    (h : checkInput expected submitted = true) {O : Type} (view : I → O) :
    view expected = view submitted := by
  exact congrArg view (input_exact h)
end Binding

section Finite
variable {A : Type} [Fintype A] [DecidableEq A]
def solutionSet (pred : A → Bool) : Set A := {x | pred x = true}
def enumerateAll (pred : A → Bool) : Finset A := Finset.univ.filter (fun a => pred a = true)
def checkExact (pred : A → Bool) (out : Finset A) : Bool :=
  decide (∀ a : A, a ∈ out ↔ pred a = true)

theorem enumeration_member (pred : A → Bool) (a : A) :
    a ∈ enumerateAll pred ↔ pred a = true := by
  simp [enumerateAll]

theorem exact_check_reflects (pred : A → Bool) (out : Finset A)
    (h : checkExact pred out = true) : (↑out : Set A) = solutionSet pred := by
  have hp : ∀ a : A, a ∈ out ↔ pred a = true := of_decide_eq_true h
  ext a
  exact hp a

theorem enumeration_accepted (pred : A → Bool) :
    checkExact pred (enumerateAll pred) = true := by
  simp [checkExact, enumeration_member]

/-- Membership soundness and domain coverage are deliberately separate duties. -/
theorem partial_check_sound (pred : A → Bool) (out : Finset A)
    (h : ∀ a ∈ out, pred a = true) : (↑out : Set A) ⊆ solutionSet pred := by
  intro a ha
  exact h a ha
end Finite

section Relations
variable {X Y Z : Type}
def relComp (r : X → Y → Prop) (s : Y → Z → Prop) (x : X) (z : Z) : Prop :=
  ∃ y, r x y ∧ s y z

theorem composition_preserves_inclusion
    (r r' : X → Y → Prop) (s s' : Y → Z → Prop)
    (hr : ∀ x y, r x y → r' x y)
    (hs : ∀ y z, s y z → s' y z) :
    ∀ x z, relComp r s x z → relComp r' s' x z := by
  rintro x z ⟨y, hxy, hyz⟩
  exact ⟨y, hr x y hxy, hs y z hyz⟩
end Relations

section ReducedProduct
variable {J W : Type} {V : J → Type}
def joint (gamma : Set W) (project : (j : J) → W → V j)
    (components : (j : J) → Set (V j)) : Set W :=
  {w | w ∈ gamma ∧ ∀ j, project j w ∈ components j}

def reduced (gamma : Set W) (project : (j : J) → W → V j)
    (components : (j : J) → Set (V j)) (j : J) : Set (V j) :=
  {x | x ∈ components j ∧ ∃ w, w ∈ joint gamma project components ∧ project j w = x}

theorem reduced_preserves_joint (gamma : Set W) (project : (j : J) → W → V j)
    (components : (j : J) → Set (V j)) :
    joint gamma project (reduced gamma project components) = joint gamma project components := by
  ext w
  constructor
  · rintro ⟨hgamma, hr⟩
    exact ⟨hgamma, fun j => (hr j).1⟩
  · rintro ⟨hgamma, hc⟩
    refine ⟨hgamma, ?_⟩
    intro j
    exact ⟨hc j, w, ⟨hgamma, hc⟩, rfl⟩
end ReducedProduct

section Quantities

theorem clipped_conservation (r : ℚ) : max r 0 - max (-r) 0 = r := by
  by_cases h : 0 ≤ r
  · rw [max_eq_left h, max_eq_right (by linarith : -r ≤ 0)]
    ring
  · have hn : r ≤ 0 := le_of_not_ge h
    rw [max_eq_right hn, max_eq_left (by linarith : 0 ≤ -r)]
    ring

theorem complementary_unique (r c u : ℚ)
    (hc : 0 ≤ c) (hu : 0 ≤ u) (hcu : c*u=0) (hs : c-u=r) :
    c=max r 0 ∧ u=max (-r) 0 := by
  rcases mul_eq_zero.mp hcu with h | h
  · subst c
    have hr : r ≤ 0 := by linarith
    constructor
    · rw [max_eq_right hr]
    · rw [max_eq_left (by linarith : 0 ≤ -r)]
      linarith
  · subst u
    have hr : 0 ≤ r := by linarith
    constructor
    · rw [max_eq_left hr]
      linarith
    · rw [max_eq_right (by linarith : -r ≤ 0)]

variable {A : Type}
theorem finite_expected_conservation (s : Finset A) (p r c u : A → ℚ)
    (h : ∀ a ∈ s, c a-u a=r a) :
    (∑ a ∈ s, p a*c a) - (∑ a ∈ s, p a*u a) = ∑ a ∈ s, p a*r a := by
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro a ha
  rw [← mul_sub, h a ha]

/-- All inequality premises must be instantiated by actual module proofs. -/
theorem weighted_enclosure (s : Finset A) (p low value high : A → ℚ)
    (hp : ∀ a ∈ s, 0 ≤ p a)
    (hl : ∀ a ∈ s, low a ≤ value a)
    (hu : ∀ a ∈ s, value a ≤ high a) :
    (∑ a ∈ s, p a*low a) ≤ (∑ a ∈ s, p a*value a) ∧
    (∑ a ∈ s, p a*value a) ≤ (∑ a ∈ s, p a*high a) := by
  constructor
  · exact Finset.sum_le_sum (fun a ha => mul_le_mul_of_nonneg_left (hl a ha) (hp a ha))
  · exact Finset.sum_le_sum (fun a ha => mul_le_mul_of_nonneg_left (hu a ha) (hp a ha))

theorem contamination_bounds (eps p q l u : ℝ)
    (he0 : 0 ≤ eps) (he1 : eps ≤ 1)
    (hpl : l ≤ p) (hpu : p ≤ u) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    (1-eps)*l ≤ (1-eps)*p+eps*q ∧
    (1-eps)*p+eps*q ≤ (1-eps)*u+eps := by
  constructor <;> nlinarith

theorem brier_excess_identity (p q : ℝ) :
    (p*(q-1)^2+(1-p)*q^2) - (p*(p-1)^2+(1-p)*p^2) = (q-p)^2 := by
  ring

theorem settlement_in_legal_intersection (legal : Set ℚ) (lo hi s : ℚ)
    (h : s ∈ legal ∩ Set.Icc lo hi) : s ∈ legal ∧ lo ≤ s ∧ s ≤ hi := by
  exact ⟨h.1,h.2.1,h.2.2⟩
end Quantities

end JurisLean.FullMath.Kernels
