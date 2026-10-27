import JurisLean.Candidates.TemporalInterpretation20261027

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

open JurisLean.Candidates.Final20261021
open JurisLean.Candidates.Final20261021.Temporal
open JurisLean.Candidates.SourceCompilation20261027
open JurisLean.Candidates.CompilerProvenance20261027
open JurisLean.Candidates.TemporalInterpretation20261027

namespace JurisLean.Candidates.TemporalInterpretation20261027.Audit

def gamma : Gamma := ⟨⟨1⟩, 1, 1, "synthetic", 3, 7, 8, ⟨5⟩, ⟨20⟩, ⟨20⟩, 1, 1, 1⟩
def record (id version : Nat) (start : Int) (stop : Option Int) (recorded known : Int) : VersionRecord :=
  ⟨⟨id⟩, version, "synthetic", 3, ⟨start⟩, stop.map LawDate.mk, ⟨recorded⟩, ⟨known⟩⟩
def history := [record 1 8 0 (some 10) 0 0, record 2 9 10 none 0 0]
def atDate (date : Int) := { gamma with lawDate := ⟨date⟩ }
def selectAt (date : Int) := selectVersion (atDate date) history [8, 9] intervalApp

-- Same publication=4, old-effective=0, fact=5, evaluation=6 inequalities.
-- Completing B's effective date as 4 or 10 gives distinct applicable versions.
def completion (bEffective : Int) :=
  [record 1 8 0 (some bEffective) 0 0, record 2 9 bEffective none 4 4]

theorem publication_does_not_identify_applicable_version :
    (0 : Int) < 4 ∧ (0 : Int) ≤ 5 ∧ (5 : Int) ≤ 6 ∧
    selectVersion { gamma with knowledgeCutoff := ⟨6⟩, recordCutoff := ⟨6⟩ }
      (completion 4) [8, 9] intervalApp = .known 9 ∧
    selectVersion { gamma with knowledgeCutoff := ⟨6⟩, recordCutoff := ⟨6⟩ }
      (completion 10) [8, 9] intervalApp = .known 8 := by decide

theorem global_latest_version_loses_first_event :
    selectAt 5 = .known 8 ∧ selectAt 12 = .known 9 ∧ selectAt 20 = .known 9 ∧
      selectAt 5 ≠ selectAt 12 := by decide

-- The same fixed App gives the late exception priority when visible.
def exceptionApp : App := fun _ records v =>
  if ∃ e ∈ records, e.id = ⟨2⟩ then
    if v = 9 then .yes else .no
  else if v = 8 then .yes else .no
def lateHistory := [record 1 8 0 none 1 1, record 2 9 0 none 3 3]
def early := { gamma with recordCutoff := ⟨2⟩, knowledgeCutoff := ⟨2⟩ }
def later := { gamma with recordCutoff := ⟨3⟩, knowledgeCutoff := ⟨3⟩ }

def selectFullThenFilter (g : Gamma) (h : List VersionRecord) : Result Nat :=
  match selectFrom g h.toFinset [8, 9] exceptionApp with
  | .known v => if ∃ e ∈ visibleSet g h, e.version = v then .known v else .unknown .missingEvidence
  | .unknown e => .unknown e
  | .rejected e => .rejected e
  | .conflict l r => .conflict l r

theorem cut_and_selection_need_not_commute :
    selectVersion early lateHistory [8, 9] exceptionApp = .known 8 ∧
      selectFullThenFilter early lateHistory = .unknown .missingEvidence := by decide

theorem raising_cut_need_not_narrow_candidates :
    candidates early (visibleSet early lateHistory) [8, 9] exceptionApp = [8] ∧
    candidates later (visibleSet later lateHistory) [8, 9] exceptionApp = [9] ∧
    ¬ (∀ v ∈ candidates later (visibleSet later lateHistory) [8, 9] exceptionApp,
      v ∈ candidates early (visibleSet early lateHistory) [8, 9] exceptionApp) := by decide

theorem time_cut_alone_does_not_choose_law :
    selectVersion early lateHistory [8, 9] (fun _ _ v => if v = 8 then .yes else .no) = .known 8 ∧
    selectVersion early lateHistory [8, 9] (fun _ _ v => if v = 9 then .yes else .no) = .known 9 := by decide

def partial : PartialVersion := ⟨⟨2⟩, 9, "synthetic", 3, ⟨0⟩, none, ⟨1⟩, none⟩
def options (_ : Unit) : List Nat := [8, 9]
def sameAnswer (v : Nat) (_ : Unit) (q : Bool) : Nat := if q then v else 0

theorem preserving_one_answer_need_not_preserve_labels_or_all_answers :
    checkLossless [()] [false] options sameAnswer 8 = true ∧
      9 ∈ options () ∧ (9 : Nat) ≠ 8 ∧
      checkLossless [()] [false, true] options sameAnswer 8 = false := by decide

def material : MaterialSnapshot := ⟨gamma, 2, 3, [⟨⟨1⟩, 0, 0, "synthetic primitive atom 1"⟩]⟩
def quoted {A : Type} (a : A) : Quoted A := ⟨⟨⟨1⟩, 0, 2, 3⟩, a⟩
def view : ConsumedView :=
  { record := quoted ⟨⟨0, 1, 2, 1, .normScope⟩, 3, true⟩
    relations := [], ledger := [], payments := [], initialHistory := [], historyEvents := []
    objects := [quoted (⟨1⟩, .relation ⟨9⟩)]
    observed := quoted (⟨1⟩, ⟨9⟩), atoms := [quoted 1] }
def catalog : List InterpretationRow := [⟨material, 0, view⟩]
def rule : RuleUse := ⟨50, 8, ⟨[1], 2⟩⟩
def nodes : List Node := [.leaf ⟨⟨1⟩, 0, 7, 1⟩, .fire rule [0]]
def run (h : List VersionRecord) (app : App) : Result TimedCompilation :=
  compileTimed material h [8, 9] app 0 catalog [rule] (fun _ _ => true) nodes 1 2
def isKnown : Result TimedCompilation → Bool
  | .known _ => true
  | _ => false

/-- info: true -/
#guard_msgs in
#eval decide (selectAt 5 = (Result.known 8 : Result Nat) ∧
  selectAt 12 = (Result.known 9 : Result Nat) ∧ selectAt 10 = (Result.known 9 : Result Nat))

/-- info: true -/
#guard_msgs in
#eval decide (selectVersion gamma history.reverse [8, 9] intervalApp = selectAt 5)

/-- info: true -/
#guard_msgs in
#eval decide ((visibleSet gamma [record 1 8 0 none 0 0, record 2 9 0 none 0 0]).card = 2)

/-- info: true -/
#guard_msgs in
#eval decide (selectVersion gamma [record 1 8 0 none 0 0, record 2 9 0 none 0 0] [8, 9] intervalApp =
  (Result.conflict 8 9 : Result Nat))

/-- info: true -/
#guard_msgs in
#eval decide (selectVersion gamma [record 1 8 0 none 0 0, record 1 9 0 none 0 0] [8, 9] intervalApp =
  (Result.rejected Error.observationBindingMismatch : Result Nat))

/-- info: true -/
#guard_msgs in
#eval decide (selectVersion gamma history [8, 8, 9] intervalApp =
  (Result.rejected Error.versionConflict : Result Nat))

/-- info: true -/
#guard_msgs in
#eval decide (selectVersion gamma history [8, 9]
  (fun _ _ v => if v = 8 then Applicable.yes else Applicable.unknown) =
  (Result.unknown Error.applicabilityUnknown : Result Nat))

/-- info: true -/
#guard_msgs in
#eval decide (selectVersion gamma history [] intervalApp = (Result.unknown Error.missingEvidence : Result Nat))

/-- info: true -/
#guard_msgs in
#eval decide (selectVersion gamma [] [8, 9] intervalApp = (Result.unknown Error.missingEvidence : Result Nat))

/-- info: true -/
#guard_msgs in
#eval decide (selectVersion early lateHistory [8, 9] exceptionApp = (Result.known 8 : Result Nat) ∧
  selectVersion later lateHistory [8, 9] exceptionApp = (Result.known 9 : Result Nat))

/-- info: true -/
#guard_msgs in
#eval decide (knownAtAlternatives early [record 1 8 0 none 1 1] [8, 9] exceptionApp partial [⟨1⟩, ⟨3⟩] =
  [(Result.known 9 : Result Nat), (Result.known 8 : Result Nat)])

/-- info: true -/
#guard_msgs in
#eval decide (knownAtAlternatives early [record 1 8 0 none 1 1] [8, 9] exceptionApp partial [] =
  [(Result.unknown Error.missingEvidence : Result Nat)])

/-- info: true -/
#guard_msgs in
#eval decide (knownAtAlternatives early [record 1 8 0 none 1 1] [8, 9] exceptionApp
  { partial with knownAt := some ⟨3⟩ } [⟨1⟩] = [(Result.known 8 : Result Nat)])

/-- info: true -/
#guard_msgs in
#eval !checkLossless [()] [false] (fun _ => []) sameAnswer 8

/-- info: true -/
#guard_msgs in
#eval decide (checkLossless [()] [false] options sameAnswer 8 = true ∧
  checkLossless [()] [false, true] options sameAnswer 8 = false)

/-- info: true -/
#guard_msgs in
#eval match run history intervalApp with
  | .known out => decide (out.selectedVersion = 8 ∧ out.compiled.source.material.gamma = gamma ∧
      out.compiled.evidence.atom = 2 ∧ 2 ∈ out.compiled.closure)
  | _ => false

/-- info: true -/
#guard_msgs in
#eval !isKnown (run history (fun _ _ _ => .unknown))

/-- info: true -/
#guard_msgs in
#eval !isKnown (run history (fun _ _ v => if v = 9 then .yes else .no))

/-- info: true -/
#guard_msgs in
#eval !isKnown (compileTimed material history [8, 9] intervalApp 0 catalog [rule]
  (fun _ _ => false) nodes 1 2)

/-- info: true -/
#guard_msgs in
#eval !isKnown (compileTimed material history [8, 9] (fun _ _ _ => .unknown)
  0 catalog [rule] (fun _ _ => true) [.leaf ⟨⟨1⟩, 0, 7, 1⟩] 0 1)

/-- info: true -/
#guard_msgs in
#eval !isKnown (compileTimed { material with gamma := { gamma with lawDate := ⟨12⟩ } }
  history [8, 9] intervalApp 0 catalog [rule] (fun _ _ => true) nodes 1 2)

/-- info: true -/
#guard_msgs in
#eval !isKnown (run [record 1 8 0 none 0 0, record 2 9 0 none 0 0] intervalApp)

end JurisLean.Candidates.TemporalInterpretation20261027.Audit

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

