import JurisLean.Seams.AdjudicationBridge
import JurisLean.Candidates.ProcedureClosureAudit20261027
import JurisLean.Candidates.FiniteLegalValidation20261027

/-!
Frozen 08.5, lines 127 and 129. Existing definitions are retained.
The finite counter adds the executable opportunity missing from the old
empty-policy counter. Validity uses the independent normative process policy
and the actual context/version-selection result.
-/

namespace JurisLean.Candidates.PolicyExhaustion20261103

open JurisLean.Candidates.Final20261021
open JurisLean.Candidates.Final20261021.Temporal
open JurisLean.Candidates.Final20261021.EvidenceProcedure
open JurisLean.Candidates.FiniteLegalValidation20261027
open JurisLean.Seams.AdjudicationBridge

def counterAAF : DungAAF :=
  { args := {"claim"}, attacks := ∅ }

def counterPolicy : TerminalPolicy counterAAF :=
  { admissibleSupport := fun _ => false
    conclusive := ∅
    presumed := ∅
    obstructed := ∅
    contraryEvidence := ∅ }

/-- The independent normative scope in the single L127 countermodel. -/
def counterRequired : List Nat := [1]

/-- Only the unfinished required operation 1 has an executable step. -/
def counterExecution (finished : Bool) (opportunity : Nat) : Option Bool :=
  if finished then none else if opportunity ∈ counterRequired then some true else none

-- L127 needs every round, not a finite test prefix.
private theorem counter_rounds_empty (n : Nat) :
    rounds counterPolicy n = (∅, ∅) := by
  induction n with
  | zero => simp [rounds, baseSet, counterPolicy]
  | succ n ih =>
      change
        (adoptedStep counterPolicy (rounds counterPolicy n).1
          (rejectedStep counterPolicy (rounds counterPolicy n).1 (rounds counterPolicy n).2),
          rejectedStep counterPolicy (rounds counterPolicy n).1 (rounds counterPolicy n).2) = (∅, ∅)
      simp only [ih]
      simp [adoptedStep, rejectedStep, counterPolicy]

-- L127: the old counter omitted an actual executable-step witness.
theorem declared_finality_misses_one_executable_requirement :
    counterRequired = [1] ∧
    counterAAF.args = {"claim"} ∧
    finalUndetermined counterPolicy "claim" ∧
    (finalUndetermined counterPolicy "claim" ↔
      KernelV3.FullyExhausted (exhaustionOf counterPolicy "claim")) ∧
    KernelV3.FullyExhausted (exhaustionOf counterPolicy "claim") ∧
    counterExecution false 1 = some true ∧
    (∀ o : Nat, (∃ after : Bool, counterExecution false o = some after) ↔ o = 1) ∧
    ¬ (∀ o ∈ counterRequired, counterExecution false o = none) := by
  have undecided : finalUndetermined counterPolicy "claim" := by
    constructor
    · rintro ⟨n, member⟩
      simpa [counter_rounds_empty n] using member
    · rintro ⟨n, member⟩
      simpa [counter_rounds_empty n] using member
  have relative := final_undetermined_iff_exhausted counterPolicy "claim"
  have full := relative.mp undecided
  have uniqueExecutable :
      ∀ o : Nat, (∃ after : Bool, counterExecution false o = some after) ↔ o = 1 := by
    intro o
    by_cases same : o = 1
    · subst o
      simp [counterExecution, counterRequired]
    · simp [counterExecution, counterRequired, same]
  have stillOpen : ¬ (∀ o ∈ counterRequired, counterExecution false o = none) := by
    intro closed
    have impossible := closed 1 (by simp [counterRequired])
    simpa [counterExecution, counterRequired] using impossible
  exact ⟨rfl, rfl, undecided, relative, full, rfl, uniqueExecutable, stillOpen⟩

/--
L129's branch retains the whole Gamma and the actual version-selection result.
The independent normative policy supplies the required scope and all three
trusted registries. No exhaustion or final-result assertion is a validity field.
Pending records need not already be complete.
-/
structure ValidPolicy (raw : RawProcess) (norm : ProcessPolicy)
    (branch : Gamma × Result Nat) : Prop where
  contextBound : norm.gamma = branch.1
  branchResolved : branch.2 = .known norm.version
  versionBound : norm.version = branch.1.normVersion
  primitiveChecks :
    ProcedureClosure20261027.validPolicy norm.required (processInput raw norm) = true
  completedDependencies :
    ∀ o ∈ raw.records, o.id ∈ raw.domain →
      ((o.executedReceipt.any fun r => decide (r ∈ norm.validExecutions)) ||
       (o.waivedBy.any fun r => decide (r ∈ norm.validWaivers))) = true →
      ∀ d ∈ o.dependencies,
        ∃ dep ∈ raw.records,
          dep.id = d ∧ d ∈ raw.domain ∧ dep.rank < o.rank ∧
            terminal (processInput raw norm) d = true

-- L129 needs the actual bound/selector instance, not an arbitrary Result.
theorem actual_bound_valid_policy_exhaustion {W : Type}
    (bound : BoundData) (history : List VersionRecord) (versions : List Nat)
    (app : TemporalInterpretation20261027.App)
    (rules : List CompilerProvenance20261027.RuleUse)
    (ruleGate : Gamma → CompilerProvenance20261027.RuleUse → Bool)
    (modelWorlds : List W) (truth : W → Nat → Bool)
    (valid : ValidPolicy bound.supplement.process bound.policy
      (bound.source.material.gamma,
        TemporalInterpretation20261027.selectVersion
          bound.source.material.gamma history versions app))
    (done : exhausted (processInput bound.supplement.process bound.policy) = true) :
    (inspectBound bound history versions app rules ruleGate modelWorlds truth).procedure =
        .known .closedLawfully ∧
      ∀ o ∈ bound.policy.required,
        terminal (processInput bound.supplement.process bound.policy) o = true := by
  have closed :
      ProcedureClosure20261027.checkProcess bound.policy.required
        (processInput bound.supplement.process bound.policy) = .known .closedLawfully :=
    (ProcedureClosure20261027.checked_closed_iff_valid_and_exhausted _ _).mpr
      ⟨valid.primitiveChecks, done⟩
  exact ⟨closed,
    inspected_closed_process_exhausts_independent_requirements
      bound history versions app rules ruleGate modelWorlds truth closed⟩

end JurisLean.Candidates.PolicyExhaustion20261103

#check JurisLean.KernelV3.FullyExhausted
#check JurisLean.Seams.AdjudicationBridge.exhaustionOf
#check JurisLean.Seams.AdjudicationBridge.finalUndetermined
#check JurisLean.Candidates.PolicyExhaustion20261103.ValidPolicy

#check JurisLean.Seams.AdjudicationBridge.final_undetermined_iff_exhausted
#print axioms JurisLean.Seams.AdjudicationBridge.final_undetermined_iff_exhausted
#check JurisLean.Candidates.ProcedureClosure20261027.Audit.vacuous_policy_exhaustion_misses_independent_requirement
#print axioms JurisLean.Candidates.ProcedureClosure20261027.Audit.vacuous_policy_exhaustion_misses_independent_requirement
#check JurisLean.Candidates.ProcedureClosure20261027.exhaustion_transfers_under_coverage
#print axioms JurisLean.Candidates.ProcedureClosure20261027.exhaustion_transfers_under_coverage
#check JurisLean.Candidates.ProcedureClosure20261027.reverse_exhaustion_needs_no_extra_domain
#print axioms JurisLean.Candidates.ProcedureClosure20261027.reverse_exhaustion_needs_no_extra_domain
#check JurisLean.Candidates.FiniteLegalValidation20261027.bound_data_keeps_exact_source_and_independent_policy
#print axioms JurisLean.Candidates.FiniteLegalValidation20261027.bound_data_keeps_exact_source_and_independent_policy
#check JurisLean.Candidates.FiniteLegalValidation20261027.selected_horn_cannot_rewrite_original_context
#print axioms JurisLean.Candidates.FiniteLegalValidation20261027.selected_horn_cannot_rewrite_original_context
#check JurisLean.Candidates.FiniteLegalValidation20261027.inspected_closed_process_exhausts_independent_requirements
#print axioms JurisLean.Candidates.FiniteLegalValidation20261027.inspected_closed_process_exhausts_independent_requirements
#check JurisLean.Candidates.PolicyExhaustion20261103.declared_finality_misses_one_executable_requirement
#print axioms JurisLean.Candidates.PolicyExhaustion20261103.declared_finality_misses_one_executable_requirement
#check JurisLean.Candidates.PolicyExhaustion20261103.actual_bound_valid_policy_exhaustion
#print axioms JurisLean.Candidates.PolicyExhaustion20261103.actual_bound_valid_policy_exhaustion
