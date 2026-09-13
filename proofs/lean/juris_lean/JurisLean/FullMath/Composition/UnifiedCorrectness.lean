import JurisLean.FullMath.Core.Foundations

/-!
C07 — Unified total correctness with claim downgrade: a Complete outcome
must exhibit equality; a Partial outcome only a subset; an Envelope
outcome only outer coverage — a partial result is never displayed as
complete — and empirical labels require a verification certificate.
-/

namespace JurisLean.FullMath.Composition

/-- Outcome modes of a run. -/
inductive ClaimMode where
  | completeMode
  | partialMode
  | envelopeMode

/-- The claim each mode is allowed to make, over a computed set and a
semantic solution set. -/
def allowedClaim (o : ClaimMode) (computed solutions : Set ℚ) : Prop :=
  match o with
  | .completeMode => computed = solutions
  | .partialMode => computed ⊆ solutions
  | .envelopeMode => solutions ⊆ computed

/-- C07(a): each mode's claim is exactly its mode contract. -/
theorem complete_requires_equality (computed solutions : Set ℚ)
    (h : allowedClaim .completeMode computed solutions) : computed = solutions := h

theorem partial_requires_subset (computed solutions : Set ℚ)
    (h : allowedClaim .partialMode computed solutions) : computed ⊆ solutions := h

theorem envelope_requires_outer (computed solutions : Set ℚ)
    (h : allowedClaim .envelopeMode computed solutions) : solutions ⊆ computed := h

/-- C07(b) adverse: a strict-subset witness forbids the equality claim —
a partial result is never displayed as complete. -/
theorem partial_never_displayed_complete (computed solutions : Set ℚ)
    (hstrict : ∃ x, x ∈ solutions ∧ ¬ (x ∈ computed))
    (hsub : computed ⊆ solutions) :
    ¬ (computed = solutions) := by
  intro heq
  obtain ⟨x, hx, hxc⟩ := hstrict
  rw [heq] at hx
  exact hxc (hsub hx)

/-- C07(c): no empirical label without a verification certificate. -/
def empiricalLabel (verified : Bool) : String → Option String :=
  fun lab => if verified then some lab else none

theorem no_empirical_label_unverified (lab : String)
    (h : empiricalLabel false lab = some lab) : False := by
  simp only [empiricalLabel] at h
  rw [if_neg (by simp)] at h
  simp at h

end JurisLean.FullMath.Composition
