import JurisLean.Candidates.TemporalInterpretationAudit20261027

namespace JurisLean.Candidates.TemporalBoundary20261103

open JurisLean.Candidates.Final20261021
open JurisLean.Candidates.TemporalInterpretation20261027
open JurisLean.Candidates.TemporalInterpretation20261027.Audit

-- Frozen 08.2 L107: the inequalities do not even imply publication by
-- evaluation. The second witness uses only the existing interval completion:
-- B has commenced at evaluation 6, but the fact at 5 still selects A.
-- This does not define the general external App predicate from date fields.
theorem publication_commencement_and_fact_date_are_separate :
    knownPublicationOrder
      (⟨⟨0⟩, ⟨4⟩, ⟨1⟩, ⟨2⟩⟩ : PublicationObservation) ∧
    ¬ ((4 : Int) ≤ 2) ∧
    ((4 : Int) ≤ 6 ∧ (6 : Int) ≤ 6 ∧ ¬ ((6 : Int) ≤ 5)) ∧
    selectVersion
      { gamma with lawDate := ⟨5⟩, knowledgeCutoff := ⟨6⟩, recordCutoff := ⟨6⟩ }
      (completion 6) [8, 9] intervalApp = .known 8 ∧
    selectVersion
      { gamma with lawDate := ⟨6⟩, knowledgeCutoff := ⟨6⟩, recordCutoff := ⟨6⟩ }
      (completion 6) [8, 9] intervalApp = .known 9 := by
  decide +kernel

-- Frozen 08.2 L109: Query is the whole declared question language, not a
-- sample list and not the unrelated finite matter set Q in the frozen plan.
-- Equality below is equality of entire answer functions. No enumeration or
-- single finite decision procedure for an infinite language is assumed.
theorem whole_query_profile_compression_iff {E Query Answer : Type} [DecidableEq Answer]
    (events : List E) (options : E → List Nat)
    (answer : Nat → E → Query → Answer) (chosen : Nat) :
    (∀ questions : List Query,
      checkLossless events questions options answer chosen = true) ↔
      (∀ event ∈ events, options event ≠ [] ∧
        ∀ version ∈ options event, answer version event = answer chosen event) := by
  constructor
  · intro checks event member
    have emptyChecked :=
      (finite_lossless_reflection events ([] : List Query) options answer chosen).mp
        (checks [])
    refine ⟨(emptyChecked event member).1, ?_⟩
    intro version selected
    funext query
    have singletonChecked :=
      (finite_lossless_reflection events [query] options answer chosen).mp
        (checks [query])
    exact (singletonChecked event member).2 version selected query (by simp)
  · intro profiles questions
    apply (finite_lossless_reflection events questions options answer chosen).mpr
    intro event member
    refine ⟨(profiles event member).1, ?_⟩
    intro version selected query _
    exact congrFun ((profiles event member).2 version selected) query

-- Frozen 08.2 L109: all questions of this explicitly finite Bool language
-- have the same answers while the candidate version labels are different.
-- This countermodel does not restrict the generic Query in the theorem above.
theorem all_query_answers_need_not_preserve_version_labels :
    (∀ questions : List Bool,
      checkLossless ([()] : List Unit) questions (fun _ => [8, 9])
        (fun _ _ _ => false) 8 = true) ∧
    9 ∈ ([8, 9] : List Nat) ∧ (9 : Nat) ≠ 8 := by
  refine ⟨?_, by decide +kernel, by decide +kernel⟩
  apply (whole_query_profile_compression_iff ([()] : List Unit)
    (fun _ => [8, 9]) (fun (_ : Nat) (_ : Unit) (_ : Bool) => false) 8).mpr
  intro event member
  refine ⟨by simp, ?_⟩
  intro version selected
  rfl

end JurisLean.Candidates.TemporalBoundary20261103

#check JurisLean.Candidates.TemporalBoundary20261103.publication_commencement_and_fact_date_are_separate
#print axioms JurisLean.Candidates.TemporalBoundary20261103.publication_commencement_and_fact_date_are_separate
#check JurisLean.Candidates.TemporalBoundary20261103.whole_query_profile_compression_iff
#print axioms JurisLean.Candidates.TemporalBoundary20261103.whole_query_profile_compression_iff
#check JurisLean.Candidates.TemporalBoundary20261103.all_query_answers_need_not_preserve_version_labels
#print axioms JurisLean.Candidates.TemporalBoundary20261103.all_query_answers_need_not_preserve_version_labels

#check JurisLean.Candidates.TemporalInterpretation20261027.legal_applicability_requires_faithful_interpretation
#print axioms JurisLean.Candidates.TemporalInterpretation20261027.legal_applicability_requires_faithful_interpretation

#check JurisLean.Candidates.TemporalInterpretation20261027.visible_records_preserve_key_consistency
#print axioms JurisLean.Candidates.TemporalInterpretation20261027.visible_records_preserve_key_consistency

#check JurisLean.Candidates.TemporalInterpretation20261027.cut_and_selection_commute_under_locality
#print axioms JurisLean.Candidates.TemporalInterpretation20261027.cut_and_selection_commute_under_locality

#check JurisLean.Candidates.TemporalInterpretation20261027.latest_start_is_correct_in_ordered_interval_model
#print axioms JurisLean.Candidates.TemporalInterpretation20261027.latest_start_is_correct_in_ordered_interval_model

#check JurisLean.Candidates.TemporalInterpretation20261027.single_success_is_exact
#print axioms JurisLean.Candidates.TemporalInterpretation20261027.single_success_is_exact

#check JurisLean.Candidates.TemporalInterpretation20261027.selection_success_contract
#print axioms JurisLean.Candidates.TemporalInterpretation20261027.selection_success_contract

#check JurisLean.Candidates.TemporalInterpretation20261027.successful_version_is_applicable
#print axioms JurisLean.Candidates.TemporalInterpretation20261027.successful_version_is_applicable

#check JurisLean.Candidates.TemporalInterpretation20261027.visible_set_is_permutation_invariant
#print axioms JurisLean.Candidates.TemporalInterpretation20261027.visible_set_is_permutation_invariant

#check JurisLean.Candidates.TemporalInterpretation20261027.selection_is_permutation_invariant
#print axioms JurisLean.Candidates.TemporalInterpretation20261027.selection_is_permutation_invariant

#check JurisLean.Candidates.TemporalInterpretation20261027.selection_stable_after_invisible_append
#print axioms JurisLean.Candidates.TemporalInterpretation20261027.selection_stable_after_invisible_append

#check JurisLean.Candidates.TemporalInterpretation20261027.unknown_time_retains_each_completion
#print axioms JurisLean.Candidates.TemporalInterpretation20261027.unknown_time_retains_each_completion

#check JurisLean.Candidates.TemporalInterpretation20261027.nonempty_constraint_refinement_preserves_must
#print axioms JurisLean.Candidates.TemporalInterpretation20261027.nonempty_constraint_refinement_preserves_must

#check JurisLean.Candidates.TemporalInterpretation20261027.must_truth_requires_actual_world_membership
#print axioms JurisLean.Candidates.TemporalInterpretation20261027.must_truth_requires_actual_world_membership

#check JurisLean.Candidates.TemporalInterpretation20261027.finite_lossless_reflection
#print axioms JurisLean.Candidates.TemporalInterpretation20261027.finite_lossless_reflection

#check JurisLean.Candidates.TemporalInterpretation20261027.labels_preserved_implies_all_answers
#print axioms JurisLean.Candidates.TemporalInterpretation20261027.labels_preserved_implies_all_answers

#check JurisLean.Candidates.TemporalInterpretation20261027.timed_compiler_consumes_selected_version
#print axioms JurisLean.Candidates.TemporalInterpretation20261027.timed_compiler_consumes_selected_version

#check JurisLean.Candidates.TemporalInterpretation20261027.timed_compilation_has_actual_app_and_closure
#print axioms JurisLean.Candidates.TemporalInterpretation20261027.timed_compilation_has_actual_app_and_closure

#check JurisLean.Candidates.TemporalInterpretation20261027.temporal_source_rule_semantic_composition
#print axioms JurisLean.Candidates.TemporalInterpretation20261027.temporal_source_rule_semantic_composition

#check JurisLean.Candidates.TemporalInterpretation20261027.Audit.publication_does_not_identify_applicable_version
#print axioms JurisLean.Candidates.TemporalInterpretation20261027.Audit.publication_does_not_identify_applicable_version

#check JurisLean.Candidates.TemporalInterpretation20261027.Audit.global_latest_version_loses_first_event
#print axioms JurisLean.Candidates.TemporalInterpretation20261027.Audit.global_latest_version_loses_first_event

#check JurisLean.Candidates.TemporalInterpretation20261027.Audit.cut_and_selection_need_not_commute
#print axioms JurisLean.Candidates.TemporalInterpretation20261027.Audit.cut_and_selection_need_not_commute

#check JurisLean.Candidates.TemporalInterpretation20261027.Audit.raising_cut_need_not_narrow_candidates
#print axioms JurisLean.Candidates.TemporalInterpretation20261027.Audit.raising_cut_need_not_narrow_candidates

#check JurisLean.Candidates.TemporalInterpretation20261027.Audit.time_cut_alone_does_not_choose_law
#print axioms JurisLean.Candidates.TemporalInterpretation20261027.Audit.time_cut_alone_does_not_choose_law

#check JurisLean.Candidates.TemporalInterpretation20261027.Audit.preserving_one_answer_need_not_preserve_labels_or_all_answers
#print axioms JurisLean.Candidates.TemporalInterpretation20261027.Audit.preserving_one_answer_need_not_preserve_labels_or_all_answers
