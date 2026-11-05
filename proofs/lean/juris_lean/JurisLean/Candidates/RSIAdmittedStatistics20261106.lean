import JurisLean.Candidates.Final20261021.RSI

/-!
Original 13.1 L95 needs one instance where a personal update changes
a case judgment through admitted statistical evidence while the rule
package and mechanism remain fixed.
-/

namespace JurisLean.Candidates.RSIAdmittedStatistics20261106

open JurisLean.Candidates.Final20261021
open JurisLean.Candidates.Final20261021.RSI

private def owner : PartyId := ⟨1⟩

private def checkpoint (version : Nat) (score : ℚ) : Checkpoint :=
  { principal := owner, task := 1, target := 1, feature := 1, ruleVersion := 1
    mechanism := 1, scope := 1, version := version, bytes := []
    prediction := score, evidence := ⟨version⟩ }

private def initial : State :=
  { mechanism := 1, rules := 1
    personal := fun who => if who = owner then some (checkpoint 1 (2 / 5)) else none
    data := [], logs := [] }

private def updated : State :=
  prepareUpdate initial (.personal owner (checkpoint 2 (3 / 5)))

-- The admission input is supplied externally for this fixed case and statistic.
-- The fixed rule package allows that statistic through only with a matching value.
private def statisticalInput (state : State) (admitted : Option ℚ) : Option ℚ :=
  match state.personal owner, admitted with
  | some report, some value =>
      if state.rules = 1 ∧ report.prediction = value then some value else none
  | _, _ => none

private def caseValue (_ _ : Nat) (evidence : Option ℚ) : Option Bool :=
  evidence.map (fun value => decide ((1 / 2 : ℚ) < value))

theorem admitted_statistics_change_case_value_under_fixed_rules :
    updated.mechanism = initial.mechanism ∧
    updated.rules = initial.rules ∧
    proposed_rule_service caseValue initial (statisticalInput initial (some (2 / 5))) =
      some false ∧
    proposed_rule_service caseValue updated (statisticalInput updated (some (3 / 5))) =
      some true ∧
    proposed_rule_service caseValue initial (statisticalInput initial none) = none ∧
    proposed_rule_service caseValue updated (statisticalInput updated none) = none := by
  have frame := u13_2_personal_frame initial owner (checkpoint 2 (3 / 5))
  refine ⟨frame.2.1, frame.1, ?_⟩
  simp [proposed_rule_service, caseValue, statisticalInput, initial, updated,
    prepareUpdate, updatePersonal, checkpoint] <;> decide +kernel

#check admitted_statistics_change_case_value_under_fixed_rules
#print axioms admitted_statistics_change_case_value_under_fixed_rules

end JurisLean.Candidates.RSIAdmittedStatistics20261106
