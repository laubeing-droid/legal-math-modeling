import JurisLean.Candidates.PolicyResponse20261027

/-!
Original 12.2 L111 requires accuracy and stability for the same deployed policy.
The existing stable fixed-point counterexample needs the zero-loss link to that
policy's finite deployment law.
-/

namespace JurisLean.Candidates.PolicyPredictionBoundary20261106

open Filter Function PolicyResponse20261027
open scoped Topology

-- There is one feature point. The two actions have masses 1 - θ and θ,
-- both outcomes are 1/2, and the constant predictor reports θ.
theorem accurate_stable_policy_can_be_outside_legal_constraint :
    let update : ℝ → ℝ := fun θ => (θ + ((1 - θ) * (1/2) + θ * (1/2))) / 2
    let loss : ℝ → ℝ := fun θ => (1 - θ) * (θ - 1/2)^2 + θ * (θ - 1/2)^2
    loss (1/2) = 0 ∧
    update (1/2) = 1/2 ∧
    (∀ x ∈ Set.Icc (0 : ℝ) 1,
      Tendsto (fun n : Nat => (update^[n]) x) atTop (𝓝 (1/2))) ∧
    (1/2 : ℝ) ∉ Set.Icc 0 (1/4) := by
  intro update loss
  have update_eq : update = affineResponse (1/2) := by
    funext θ
    dsimp [update, affineResponse]
    ring
  refine ⟨by norm_num [loss], ?_⟩
  rw [update_eq]
  obtain ⟨fixed, converges, outside⟩ := stable_fixed_point_can_be_outside_legal_constraint
  exact ⟨fixed, fun x _ => converges x, outside⟩

#check accurate_stable_policy_can_be_outside_legal_constraint
#print axioms accurate_stable_policy_can_be_outside_legal_constraint

end JurisLean.Candidates.PolicyPredictionBoundary20261106
