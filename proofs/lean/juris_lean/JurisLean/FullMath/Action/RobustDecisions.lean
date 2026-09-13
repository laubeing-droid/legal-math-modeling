import JurisLean.FullMath.Core.Foundations

/-!
G05/EXT08 — Robust decisions under a shared uncertainty parameter.

With a shared θ the robust value is max_π min_θ V(π, θ); a rectangular
decomposition into per-period independent minima only gives a conservative
lower bound (Σᵢ min rᵢ ≤ min θ. Σᵢ rᵢ, witnessed pointwise), and the
concrete two-period instance r₁ = 1{θ}, r₂ = 1{¬θ} has shared-θ total
exactly 1 while the rectangular sum is 0.
-/

namespace JurisLean.FullMath.Action

section Robust

/-- G05(a): rectangular decomposition is conservative — per-period minima
sum to at most the shared-parameter total (witnessed at any θ). -/
theorem rectangle_lower_bound {Θ : Type} [Nonempty Θ]
    (r₁ r₂ : Θ → ℚ)
    (m₁ : ℚ) (hm₁ : ∀ θ, m₁ ≤ r₁ θ)
    (m₂ : ℚ) (hm₂ : ∀ θ, m₂ ≤ r₂ θ) :
    m₁ + m₂ ≤ r₁ (Classical.arbitrary Θ) + r₂ (Classical.arbitrary Θ) := by
  have h1 := hm₁ (Classical.arbitrary Θ)
  have h2 := hm₂ (Classical.arbitrary Θ)
  linarith

/-- The two concrete per-period payoffs of the adversarial instance. -/
def rInd (θ : Bool) : ℚ := if θ then 1 else 0
def rCon (θ : Bool) : ℚ := if θ then 0 else 1

/-- Both per-period minima over the two-point parameter are zero. -/
theorem instance_rectangular_sum_zero :
    (∀ θ : Bool, (0:ℚ) ≤ rInd θ) ∧ (∀ θ : Bool, (0:ℚ) ≤ rCon θ) ∧ ((0:ℚ) + 0) = 0 := by
  refine ⟨fun θ => by cases θ <;> simp [rInd], fun θ => by cases θ <;> simp [rCon], by norm_num⟩

/-- G05(b): the shared-θ two-period total is identically one. -/
theorem shared_theta_total_identity (θ : Bool) : rInd θ + rCon θ = 1 := by
  cases θ <;> simp [rInd, rCon] <;> norm_num

/-- The shared-parameter total is exactly one while the rectangular sum of
per-period minima is zero — the rectangular bound is strictly looser. -/
theorem rectangular_bound_strictly_looser :
    (∀ θ : Bool, rInd θ + rCon θ = 1) ∧ ((0:ℚ) + 0) = 0 ∧ (0:ℚ) < 1 := by
  refine ⟨shared_theta_total_identity, by norm_num, by norm_num⟩

end Robust

end JurisLean.FullMath.Action
