import JurisLean.Candidates.SourcePolicyExhaustionAudit20261103
import JurisLean.Candidates.SourceHornBoundaryAudit20261103
import JurisLean.Candidates.FiniteLegalValidationAudit20261027
import JurisLean.Candidates.TemporalInterpretationAudit20261027
import JurisLean.Candidates.ProcedureClosureAudit20261027

/-!
Frozen original 08.7, lines 139 and 141: carry the supplied event-time
coordinate into the existing bounded inspection call and instantiate one
finite dependency ordering. The supplied App retains its own legal-version
argument; this connection does not prove that App faithfully interprets the
event time. The snapshot does not infer event time from source history, identify
the key below with a complete semantic input, or assert RawProcess termination.
-/

namespace JurisLean.Candidates.DependencySnapshot20261103

open JurisLean.Candidates.Final20261021
open JurisLean.Candidates.Final20261021.EvidenceProcedure
open JurisLean.Candidates.Final20261021.Temporal
open JurisLean.Candidates.FiniteLegalValidation20261027
open JurisLean.Candidates.ProcedureClosure20261027
open JurisLean.Candidates.SourceCompilation20261027
open JurisLean.Candidates.TemporalInterpretation20261027
open JurisLean.Candidates.CompilerProvenance20261027

/-- One finite inspection bundle; event time is supplied independently. -/
structure InspectionSnapshot where
  bound : BoundData
  eventFactTime : Nat
  temporalHistory : List VersionRecord

/-- Only the three requested coordinates; this is not a full semantic identity. -/
def inspectionKey (snapshot : InspectionSnapshot) : Gamma × (Nat × Nat) :=
  (snapshot.bound.source.material.gamma,
    (snapshot.eventFactTime, snapshot.bound.policy.version))

theorem successful_binding_and_inspection_preserve_snapshot_inputs {W : Type}
    (snapshot : InspectionSnapshot) (view : ExtractedView)
    (supplements : List Supplement) (policies : List ProcessPolicy)
    (boundAccepted : bindAdditional view supplements policies = .known snapshot.bound)
    (versions : List Nat) (appAtEventTime : Nat → App) (rules : List RuleUse)
    (ruleGate : Gamma → RuleUse → Bool) (modelWorlds : List W)
    (truth : W → Nat → Bool) :
    let report := inspectBound snapshot.bound snapshot.temporalHistory versions
      (appAtEventTime snapshot.eventFactTime) rules ruleGate modelWorlds truth
    report.bound.source = view ∧
      report.bound.source.material.gamma = view.material.gamma ∧
      report.selected = selectVersion snapshot.bound.source.material.gamma
        snapshot.temporalHistory versions (appAtEventTime snapshot.eventFactTime) ∧
      report.horn = selectedHorn snapshot.bound.source report.selected rules ruleGate
        (eligibleFacts snapshot.bound) ∧
      report.procedure = checkProcess snapshot.bound.policy.required
        (processInput snapshot.bound.supplement.process snapshot.bound.policy) ∧
      snapshot.bound.policy.gamma = view.material.gamma ∧
      snapshot.bound.policy.version = snapshot.bound.supplement.policyVersion := by
  have binding := bound_data_keeps_exact_source_and_independent_policy
    view supplements policies snapshot.bound boundAccepted
  rcases binding with ⟨sourceBound, _, _, _, _, _, gammaBound, revisionBound⟩
  refine ⟨sourceBound, ?_, rfl, rfl, rfl, gammaBound, revisionBound⟩
  exact congrArg (fun extracted : ExtractedView => extracted.material.gamma) sourceBound

theorem inspection_key_eq_iff_coordinates_equal
    (left right : InspectionSnapshot) :
    inspectionKey left = inspectionKey right ↔
      left.bound.source.material.gamma = right.bound.source.material.gamma ∧
      left.eventFactTime = right.eventFactTime ∧
      left.bound.policy.version = right.bound.policy.version := by
  simp [inspectionKey, Prod.mk.injEq]

inductive DependencyStage where
  | material
  | entity
  | followupProgram
  deriving DecidableEq

def dependencyRank : DependencyStage → Nat
  | .material => 0
  | .entity => 1
  | .followupProgram => 2

/-- Edges point from a consumer to a prerequisite. -/
def stageDepends : DependencyStage → DependencyStage → Prop
  | .entity, .material => True
  | .followupProgram, .entity => True
  | .followupProgram, .material => True
  | _, _ => False

private theorem stage_dependency_strictly_lowers_rank (consumer prerequisite : DependencyStage)
    (edge : stageDepends consumer prerequisite) :
    dependencyRank prerequisite < dependencyRank consumer := by
  cases consumer <;> cases prerequisite <;>
    simp [stageDepends, dependencyRank] at * <;> omega

theorem finite_material_entity_program_dependencies_have_no_infinite_chain :
    ¬ ∃ path : Nat → DependencyStage, ∀ k,
      stageDepends (path k) (path (k + 1)) :=
  JurisLean.Candidates.ProcedureClosure20261027.strict_rank_excludes_infinite_execution
    dependencyRank stageDepends stage_dependency_strictly_lowers_rank

end JurisLean.Candidates.DependencySnapshot20261103

#check JurisLean.Candidates.DependencySnapshot20261103.successful_binding_and_inspection_preserve_snapshot_inputs
#print axioms JurisLean.Candidates.DependencySnapshot20261103.successful_binding_and_inspection_preserve_snapshot_inputs
#check JurisLean.Candidates.DependencySnapshot20261103.inspection_key_eq_iff_coordinates_equal
#print axioms JurisLean.Candidates.DependencySnapshot20261103.inspection_key_eq_iff_coordinates_equal
#check JurisLean.Candidates.DependencySnapshot20261103.finite_material_entity_program_dependencies_have_no_infinite_chain
#print axioms JurisLean.Candidates.DependencySnapshot20261103.finite_material_entity_program_dependencies_have_no_infinite_chain

#check JurisLean.Candidates.Final20261021.Acceptance.a_u09_three_observations
#print axioms JurisLean.Candidates.Final20261021.Acceptance.a_u09_three_observations
#check JurisLean.Candidates.SourceHornBoundary20261103.same_source_completed_countermodels
#print axioms JurisLean.Candidates.SourceHornBoundary20261103.same_source_completed_countermodels
#check JurisLean.Candidates.ProcedureClosure20261027.Audit.four_judgment_process_products_are_distinct
#print axioms JurisLean.Candidates.ProcedureClosure20261027.Audit.four_judgment_process_products_are_distinct
#check JurisLean.Candidates.TemporalInterpretation20261027.Audit.global_latest_version_loses_first_event
#print axioms JurisLean.Candidates.TemporalInterpretation20261027.Audit.global_latest_version_loses_first_event
#check JurisLean.Candidates.FiniteLegalValidation20261027.family_retains_each_branch_including_failures
#print axioms JurisLean.Candidates.FiniteLegalValidation20261027.family_retains_each_branch_including_failures
#check JurisLean.Candidates.FiniteLegalValidation20261027.validator_consumes_actual_bound_source
#print axioms JurisLean.Candidates.FiniteLegalValidation20261027.validator_consumes_actual_bound_source
#check JurisLean.Candidates.FiniteLegalValidation20261027.inspected_horn_is_applicable_and_complete
#print axioms JurisLean.Candidates.FiniteLegalValidation20261027.inspected_horn_is_applicable_and_complete
#check JurisLean.Candidates.PolicyExhaustion20261103.actual_bound_valid_policy_exhaustion
#print axioms JurisLean.Candidates.PolicyExhaustion20261103.actual_bound_valid_policy_exhaustion
#check JurisLean.Candidates.TemporalInterpretation20261027.selection_success_contract
#print axioms JurisLean.Candidates.TemporalInterpretation20261027.selection_success_contract
#check JurisLean.Candidates.Final20261021.Compiler.u03_2_relative_completeness
#print axioms JurisLean.Candidates.Final20261021.Compiler.u03_2_relative_completeness
