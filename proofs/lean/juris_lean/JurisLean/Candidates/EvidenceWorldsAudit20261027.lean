import JurisLean.Candidates.EvidenceWorlds20261027

#check JurisLean.Candidates.EvidenceWorlds20261027.constrained_membership
#print axioms JurisLean.Candidates.EvidenceWorlds20261027.constrained_membership
#check JurisLean.Candidates.EvidenceWorlds20261027.additional_constraints_only_remove_worlds
#print axioms JurisLean.Candidates.EvidenceWorlds20261027.additional_constraints_only_remove_worlds
#check JurisLean.Candidates.EvidenceWorlds20261027.faithful_evidence_retains_actual_world
#print axioms JurisLean.Candidates.EvidenceWorlds20261027.faithful_evidence_retains_actual_world
#check JurisLean.Candidates.EvidenceWorlds20261027.all_positive_and_negative_iff_empty
#print axioms JurisLean.Candidates.EvidenceWorlds20261027.all_positive_and_negative_iff_empty
#check JurisLean.Candidates.EvidenceWorlds20261027.world_incompatible_iff_empty
#print axioms JurisLean.Candidates.EvidenceWorlds20261027.world_incompatible_iff_empty
#check JurisLean.Candidates.EvidenceWorlds20261027.world_supported_iff_nonempty_universal
#print axioms JurisLean.Candidates.EvidenceWorlds20261027.world_supported_iff_nonempty_universal
#check JurisLean.Candidates.EvidenceWorlds20261027.world_opposed_iff_nonempty_universal
#print axioms JurisLean.Candidates.EvidenceWorlds20261027.world_opposed_iff_nonempty_universal
#check JurisLean.Candidates.EvidenceWorlds20261027.world_insufficient_iff_both_possibilities
#print axioms JurisLean.Candidates.EvidenceWorlds20261027.world_insufficient_iff_both_possibilities
#check JurisLean.Candidates.EvidenceWorlds20261027.supported_world_judgment_needs_actual_membership
#print axioms JurisLean.Candidates.EvidenceWorlds20261027.supported_world_judgment_needs_actual_membership
#check JurisLean.Candidates.EvidenceWorlds20261027.source_to_world_truth_is_conditional
#print axioms JurisLean.Candidates.EvidenceWorlds20261027.source_to_world_truth_is_conditional
#check JurisLean.Candidates.EvidenceWorlds20261027.output_world_label_reads_actual_filtered_worlds
#print axioms JurisLean.Candidates.EvidenceWorlds20261027.output_world_label_reads_actual_filtered_worlds
#check JurisLean.Candidates.EvidenceWorlds20261027.adding_evidence_is_monotone_in_information_bits
#print axioms JurisLean.Candidates.EvidenceWorlds20261027.adding_evidence_is_monotone_in_information_bits
#check JurisLean.Candidates.EvidenceWorlds20261027.compatible_pair_membership
#print axioms JurisLean.Candidates.EvidenceWorlds20261027.compatible_pair_membership
#check JurisLean.Candidates.EvidenceWorlds20261027.filtering_never_invents_legal_world_pair
#print axioms JurisLean.Candidates.EvidenceWorlds20261027.filtering_never_invents_legal_world_pair

open JurisLean.Candidates.Final20261021
open JurisLean.Candidates.Final20261021.EvidenceProcedure
open JurisLean.Candidates.EvidenceWorlds20261027

namespace JurisLean.Candidates.EvidenceWorlds20261027.Audit

def positive : EvidenceItem := ⟨⟨1⟩, 0, .yes, true, true⟩
def negative : EvidenceItem := ⟨⟨2⟩, 0, .yes, true, false⟩
def unknownAdmission : EvidenceItem := ⟨⟨3⟩, 0, .unknown, true, false⟩
def valuation (world : Bool) (query : Nat) : Bool := if query = 0 then world else !world
def universe : List Bool := [false, true]
def run (items : List EvidenceItem) := viewEvidence universe valuation 0 items

theorem credible_but_inadmissible_has_no_constraint :
    judgment 0 [{ positive with admissibility := .no }] = .insufficient ∧
      constrained universe valuation [{ positive with admissibility := .no }] = universe := by decide

theorem opposing_usable_directions_empty_classical_worlds :
    judgment 0 [positive, negative] = .incompatible ∧
      constrained universe valuation [positive, negative] = [] ∧
      worldJudgment (constrained universe valuation [positive, negative]) valuation 0 = .incompatible := by decide

theorem adding_credible_evidence_can_destroy_determinacy :
    judgment 0 [positive] = .supported ∧
      judgment 0 [positive, negative] = .incompatible ∧
      worldJudgment (constrained universe valuation [positive]) valuation 0 = .supported ∧
      worldJudgment (constrained universe valuation [positive, negative]) valuation 0 = .incompatible := by decide

theorem admissible_is_not_source_truth :
    false ∈ universe ∧ judgment 0 [positive] = .supported ∧
      worldJudgment (constrained universe valuation [positive]) valuation 0 = .supported ∧
      valuation false 0 = false := by decide

theorem actual_world_coverage_is_necessary :
    worldJudgment [true] valuation 0 = .supported ∧
      (∀ e ∈ ([] : List EvidenceItem), usable e.query e = true → valuation false e.query = e.supports) ∧
      false ∉ ([true] : List Bool) ∧ valuation false 0 = false := by decide

theorem marginal_coordinates_do_not_justify_cartesian_completion :
    (0 : Nat) ∈ [0, 1] ∧ false ∈ [true, false] ∧
      ((0, false) : Nat × Bool) ∉ [(0, true), (1, false)] := by decide

/-- info: true -/
#guard_msgs in
#eval decide ((run []).evidenceJudgment = Judgment.insufficient ∧
  (run []).possibleWorlds = universe ∧ (run []).possibleWorldJudgment = Judgment.insufficient ∧
  (run []).pending = [])

/-- info: true -/
#guard_msgs in
#eval decide ((run [positive]).evidenceJudgment = Judgment.supported ∧
  (run [positive]).possibleWorlds = [true] ∧ (run [positive]).possibleWorldJudgment = Judgment.supported)

/-- info: true -/
#guard_msgs in
#eval decide ((run [negative]).evidenceJudgment = Judgment.opposed ∧
  (run [negative]).possibleWorlds = [false] ∧ (run [negative]).possibleWorldJudgment = Judgment.opposed)

/-- info: true -/
#guard_msgs in
#eval decide ((run [positive, negative]).evidenceJudgment = Judgment.incompatible ∧
  (run [positive, negative]).possibleWorlds = [] ∧
  (run [positive, negative]).possibleWorldJudgment = Judgment.incompatible)

/-- info: true -/
#guard_msgs in
#eval decide ((run [{ positive with admissibility := .no }]).evidenceJudgment = Judgment.insufficient ∧
  (run [{ positive with admissibility := .no }]).possibleWorlds = universe)

/-- info: true -/
#guard_msgs in
#eval decide ((run [unknownAdmission]).evidenceJudgment = Judgment.insufficient ∧
  (run [unknownAdmission]).possibleWorlds = universe ∧
  (run [unknownAdmission]).pending = [SourceRef.mk 3])

/-- info: true -/
#guard_msgs in
#eval decide ((run [{ positive with credibleUnderPolicy := false }]).evidenceJudgment = Judgment.insufficient ∧
  (run [{ positive with credibleUnderPolicy := false }]).possibleWorlds = universe)

/-- info: true -/
#guard_msgs in
#eval decide ((run [{ positive with query := 1 }]).evidenceJudgment = Judgment.insufficient ∧
  (run [{ positive with query := 1 }]).possibleWorlds = [false] ∧
  (run [{ positive with query := 1 }]).possibleWorldJudgment = Judgment.opposed)

/-- info: true -/
#guard_msgs in
#eval decide ((viewEvidence [] valuation 0 [positive]).evidenceJudgment = Judgment.supported ∧
  (viewEvidence [] valuation 0 [positive]).possibleWorldJudgment = Judgment.incompatible)

/-- info: true -/
#guard_msgs in
#eval decide ((run [{ positive with query := 1 }, { negative with query := 1 }]).evidenceJudgment =
  Judgment.insufficient ∧
  (run [{ positive with query := 1 }, { negative with query := 1 }]).possibleWorldJudgment =
  Judgment.incompatible)

/-- info: true -/
#guard_msgs in
#eval decide ((run [positive, unknownAdmission]).possibleWorldJudgment = Judgment.supported ∧
  (run [positive, unknownAdmission]).pending = [SourceRef.mk 3])

/-- info: true -/
#guard_msgs in
#eval decide ((run [positive, positive]).possibleWorlds = (run [positive]).possibleWorlds)

/-- info: true -/
#guard_msgs in
#eval decide (compatibleWorlds [(0, true), (1, false)] (fun (_ : Nat) => valuation) (fun _ => []) =
  [(0, true), (1, false)])

/-- info: true -/
#guard_msgs in
#eval decide (compatibleWorlds [(0, true), (1, false)] (fun (_ : Nat) => valuation)
  (fun branch => if branch = 0 then [positive] else [negative]) = [(0, true), (1, false)])

/-- info: true -/
#guard_msgs in
#eval decide (compatibleWorlds [(0, true), (1, false)] (fun (_ : Nat) => valuation)
  (fun _ => [positive]) = [(0, true)])

/-- info: true -/
#guard_msgs in
#eval decide (evidenceBits 0 [positive] = (true, false) ∧
  evidenceBits 0 [positive, negative] = (true, true))

end JurisLean.Candidates.EvidenceWorlds20261027.Audit

#check JurisLean.Candidates.EvidenceWorlds20261027.Audit.credible_but_inadmissible_has_no_constraint
#print axioms JurisLean.Candidates.EvidenceWorlds20261027.Audit.credible_but_inadmissible_has_no_constraint
#check JurisLean.Candidates.EvidenceWorlds20261027.Audit.opposing_usable_directions_empty_classical_worlds
#print axioms JurisLean.Candidates.EvidenceWorlds20261027.Audit.opposing_usable_directions_empty_classical_worlds
#check JurisLean.Candidates.EvidenceWorlds20261027.Audit.adding_credible_evidence_can_destroy_determinacy
#print axioms JurisLean.Candidates.EvidenceWorlds20261027.Audit.adding_credible_evidence_can_destroy_determinacy
#check JurisLean.Candidates.EvidenceWorlds20261027.Audit.admissible_is_not_source_truth
#print axioms JurisLean.Candidates.EvidenceWorlds20261027.Audit.admissible_is_not_source_truth
#check JurisLean.Candidates.EvidenceWorlds20261027.Audit.actual_world_coverage_is_necessary
#print axioms JurisLean.Candidates.EvidenceWorlds20261027.Audit.actual_world_coverage_is_necessary
#check JurisLean.Candidates.EvidenceWorlds20261027.Audit.marginal_coordinates_do_not_justify_cartesian_completion
#print axioms JurisLean.Candidates.EvidenceWorlds20261027.Audit.marginal_coordinates_do_not_justify_cartesian_completion

