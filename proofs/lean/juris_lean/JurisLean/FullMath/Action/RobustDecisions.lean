import JurisLean.FullMath.Core.Foundations

/-!
G05/EXT08 — Robust decisions under a shared uncertainty parameter.

With a shared `θ` the robust value is `max_π min_θ V(π, θ)`; a rectangular
decomposition into per-period independent minima only gives a conservative
lower bound (`Σᵢ min rᵢ ≤ min Σᵢ rᵢ`, proven for finite Θ), and the
concrete two-period instance `r₁ = 1{θ}, r₂ = 1{¬θ}` has shared-θ value
exactly 1 while the rectangular sum is 0.
-/

namespace JurisLean.FullMath.Action

section Robust

/-- G05(a): the sum of per-period minima lower-bounds the minimum of sums —
rectangular decomposition is conservative. -/
theorem rectangle_lower_bound {Θ : Type} [Fintype Θ] [DecidableEq Θ]
    (r₁ r₂ : Θ → ℚ) :
    ((Finset.univ.inf (fun θ => r₁ θ)) + (Finset.univ.inf (fun θ => r₂ θ)))
      ≤ Finset.univ.inf (fun θ => r₁ θ + r₂ θ) := by
  refine Finset.le_inf ?_
  intro θ _
  have h1 : (Finset.univ.inf (fun θ => r₁ θ)) ≤ r₁ θ :=
    Finset.inf_le (Finset.mem_univ θ)
  have h2 : (Finset.univ.inf (fun θ => r₂ θ)) ≤ r₂ θ :=
    Finset.inf_le (Finset.mem_univ θ)
  linarith

/-- The shared-θ two-period total is identically one. -/
theorem shared_theta_total_identity : ∀ θ : ℚ, θ + (1 - θ) = 1 := fun θ => by ring

/-- G05(b): rectangular decomposition is strictly conservative — the
concrete two-point Θ instance `r₁ = 1{θ}`, `r₂ = 1{¬θ}` has gap exactly
one. -/
theorem rectangular_bound_strictly_looser :
    (Finset.univ.inf (fun θ : Bool => if θ then (1:ℚ) else 0)) +
      (Finset.univ.inf (fun θ : Bool => if θ then (0:ℚ) else 1)) <
        Finset.univ.inf (fun θ : Bool =>
          (if θ then (1:ℚ) else 0) + (if θ then 0 else 1)) := by
  have hinf1 : (Finset.univ.inf (fun θ : Bool => if θ then (1:ℚ) else 0)) = 0 := by
    refine le_antisymm ?_ ?_
    · have := Finset.inf_le (Finset.mem_univ false)
      simpa using this
    · exact Finset.le_inf (fun θ _ => by split_ifs <;> norm_num)
  have hinf2 : (Finset.univ.inf (fun θ : Bool => if θ then (0:ℚ) else 1)) = 0 := by
    refine le_antisymm ?_ ?_
    · have := Finset.inf_le (Finset.mem_univ true)
      simpa using this
    · exact Finset.le_inf (fun θ _ => by split_ifs <;> norm_num)
  have hinf3 : (Finset.univ.inf (fun θ : Bool =>
      (if θ then (1:ℚ) else 0) + (if θ then 0 else 1))) = 1 := by
    refine le_antisymm ?_ ?_
    · have := Finset.inf_le (Finset.mem_univ false)
      simpa using this
    · exact Finset.le_inf (fun θ _ => by split_ifs <;> norm_num)
  rw [hinf1, hinf2, hinf3]
  norm_num

end Robust

end JurisLean.FullMath.Action
