import JurisLean.FullMath.Core.Foundations

/-!
C01 — Relational composition: local inclusions transfer through the
composed relation via a shared witness; composition is associative, so
pipelines of any length compose without re-proving per length.
-/

namespace JurisLean.FullMath.Composition

variable {X Y Z W : Type}

/-- Composition via an explicit shared witness. -/
def relComp (r : X → Y → Prop) (s : Y → Z → Prop) (x : X) (z : Z) : Prop :=
  ∃ y, r x y ∧ s y z

/-- C01(a): local inclusions carry through the composition. -/
theorem comp_preserves_inclusion
    (r r' : X → Y → Prop) (s s' : Y → Z → Prop)
    (hr : ∀ x y, r x y → r' x y) (hs : ∀ y z, s y z → s' y z) :
    ∀ x z, relComp r s x z → relComp r' s' x z := by
  intro x z ⟨y, hxy, hyz⟩
  exact ⟨y, hr x y hxy, hs y z hyz⟩

/-- C01(b): composition is associative — pipelines of any length compose. -/
theorem relComp_assoc (r : X → Y → Prop) (s : Y → Z → Prop) (t : Z → W → Prop)
    (x : X) (w : W) :
    relComp (relComp r s) t x w ↔ relComp r (relComp s t) x w := by
  constructor
  · intro ⟨z, ⟨y, hxy, hyz⟩, hzw⟩
    exact ⟨y, hxy, z, hyz, hzw⟩
  · intro ⟨y, hxy, z, hyz, hzw⟩
    exact ⟨z, ⟨y, hxy, hyz⟩, hzw⟩

end JurisLean.FullMath.Composition
