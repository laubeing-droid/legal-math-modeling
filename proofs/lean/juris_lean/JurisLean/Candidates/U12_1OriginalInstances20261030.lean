import JurisLean.Candidates.U12_1CausalPolicyBridge20261030
import JurisLean.Candidates.U11_1OriginalInstances20261030

/-!
Blockers: original 12.3 L121 asks for the sharp interval for real bounded
outcomes; original 12.6 L153 and L155 ask for a behavior-only impossibility
proof and a proxy-gain / true-outcome-loss witness. These three short
consequences reuse the existing causal model, authority countermodel and
indicator. They do not change the policy, measurement or permission APIs.
-/

namespace JurisLean.Candidates.U12_1OriginalInstances20261030

open JurisLean.Candidates.Final20261021

-- The conditional-mean calculation in the original question is over reals.
-- The existing same-log endpoint worlds separately establish attainability.
theorem original12_3_real_support_range (value : ℝ) :
    (∃ theta : ℝ, (0 ≤ theta ∧ theta ≤ 1) ∧
      value = theta / 2 + 3 / 20) ↔
    3 / 20 ≤ value ∧ value ≤ 13 / 20 := by
  constructor
  · rintro ⟨theta, ⟨lower, upper⟩, rfl⟩
    constructor <;> linarith
  · rintro ⟨lower, upper⟩
    refine ⟨2 * (value - 3 / 20), ⟨?_, ?_⟩, ?_⟩ <;> linarith

-- Even a recoverer given the complete common causal model cannot recover
-- both external permission sets without the missing institutional input.
theorem original12_6_behavior_only_cannot_recover_both
    (recover : Behavior.CausalModel → Bool → Prop) :
    ¬ (∀ law action : Bool,
      recover Behavior.m1 action ↔ (law = true ∨ action = false)) := by
  intro correct
  have witness :=
    U11_1OriginalInstances20261030.original11_6_same_behavior_different_constraints
  have commonAnswer := (correct true true).mpr witness.2.2.1
  exact witness.2.2.2 ((correct false true).mp commonAnswer)

-- False/true are the two actions; the original target is held fixed while
-- the selected action changes. The two distinct measurements are not merged.
theorem original12_6_proxy_gain_true_loss :
    let proxy : Bool → ℚ := Behavior.indicator
    let trueOutcome : Bool → ℚ := fun action => Behavior.indicator (!action)
    proxy false = 0 ∧ proxy true = 1 ∧
      trueOutcome false = 1 ∧ trueOutcome true = 0 ∧
      proxy true - proxy false = 1 ∧
      trueOutcome true - trueOutcome false = -1 := by
  norm_num [Behavior.indicator]

end JurisLean.Candidates.U12_1OriginalInstances20261030
