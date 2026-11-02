import JurisLean.Candidates.SourceFinalBridgeAudit20261102
import JurisLean.Candidates.SourceFiniteStageAudit20261102
import JurisLean.Candidates.Final20261021.Acceptance
import JurisLean.Candidates.U03DebtClosureAudit20261027
import JurisLean.Candidates.TemporalInterpretation20261027

namespace JurisLean.Candidates.SourceHornBoundary20261103

open JurisLean.Candidates.Final20261021
open JurisLean.Candidates.SourceCompilation20261027
open JurisLean.Candidates.SourceStages20261027
open JurisLean.Candidates.SourceFinalBridge20261102
open JurisLean.Candidates.CompilerProvenance20261027

-- Frozen 08.1 L103: finite countermodels only; the declarations below are
-- synthetic legal meanings, not assertions of any actual statute or payment.
-- Atom 1 is the supplied payment assertion, 3 the legal conclusion, and 4
-- a positive witness that the exception does not apply.
def boundaryCatalog : List InterpretationRow := [⟨stageMaterial, 0, stageView⟩]
def encodedRule : RuleUse := ⟨50, stageGamma.normVersion, ⟨[1], 3⟩⟩
def declaredExceptionRule : Compiler.Rule Nat := ⟨[1, 4], 3⟩
def boundaryGate : Gamma → RuleUse → Bool := fun _ _ => true
def boundaryNodes : List Node :=
  [.leaf ⟨⟨1⟩, 0, 7, 1⟩, .fire encodedRule [0]]
def boundaryCompile : Result CompiledView :=
  compileView stageMaterial 0 boundaryCatalog [encodedRule] boundaryGate boundaryNodes 1 3
def otherVersion : Gamma :=
  { stageGamma with normVersion := stageGamma.normVersion + 1 }
def paidOnlyTruth (a : Nat) : Prop := a = 1
def paidAndConclusionTruth (a : Nat) : Prop := a = 1 ∨ a = 3
def noPaymentTruth (_ : Nat) : Prop := False

-- Reuse the accepted source/frame and 10,7,7 arithmetic; the new obligation
-- is internal completion with each independently failed external premise.
theorem same_source_completed_countermodels :
    ∃ out, ∃ compiled : CompiledView,
      sourceModel JurisLean.Seams.UnifiedInstance.instanceM
        stageMaterial 0 boundaryCatalog = .ok out ∧
      boundaryCompile = .known compiled ∧
      compiled.source = out.1.source ∧
      compiled.source.material.gamma = stageGamma ∧
      3 ∈ compiled.closure ∧
      Compiler.closed (activeRules stageGamma [encodedRule] boundaryGate)
        compiled.closure = true ∧
      (out.1.stages.afterFirst.state.debt.amount.value = (3 : ℚ) ∧
        out.1.stages.afterSecond.state.debt.amount.value = (0 : ℚ)) ∧
      activeRules stageGamma [encodedRule] boundaryGate = [encodedRule.rule] ∧
      (encodedRule.rule ≠ declaredExceptionRule ∧
        Compiler.Models (fun a => a ∈ ([1] : List Nat))
          (fun r => r ∈ [declaredExceptionRule]) paidOnlyTruth ∧
        ¬ paidOnlyTruth 3) ∧
      (Compiler.Models (fun a => a ∈ ([1] : List Nat))
          (fun r => r ∈ activeRules stageGamma [encodedRule] boundaryGate)
          paidAndConclusionTruth ∧
        activeRules otherVersion [encodedRule] boundaryGate = [] ∧
        Compiler.Models (fun a => a ∈ ([1] : List Nat))
          (fun r => r ∈ activeRules otherVersion [encodedRule] boundaryGate)
          paidOnlyTruth ∧
        ¬ paidOnlyTruth 3) ∧
      (Compiler.Models (fun _ : Nat => False)
          (fun r => r ∈ activeRules stageGamma [encodedRule] boundaryGate)
          noPaymentTruth ∧
        ¬ noPaymentTruth 1 ∧ ¬ noPaymentTruth 3) := by
  obtain ⟨out, mu, modelAccepted, _⟩ :=
    source_model_joint_bridge_nonempty_and_faithfulness_needed
  obtain ⟨frame, staged, _, _, _, firstAmount, finalAmount, _⟩ :=
    finite_stage_compatible_counterexample
  have modelStages := (public_model_consumes_the_actual_stage_frame
    JurisLean.Seams.UnifiedInstance.instanceM stageMaterial 0
      boundaryCatalog out modelAccepted).1
  have stagedPublic : sourceStages stageMaterial 0 boundaryCatalog = .known frame := staged
  have sameFrame : out.1 = frame :=
    Result.known.inj (modelStages.symm.trans stagedPublic)
  have computed :
      (match boundaryCompile with
       | .known value => decide (value.source.material.gamma = stageGamma)
       | _ => false) = true := by decide +kernel
  obtain ⟨compiled, compilerAccepted⟩ :
      ∃ compiled : CompiledView, boundaryCompile = .known compiled := by
    cases result : boundaryCompile with
    | known value => exact ⟨value, rfl⟩
    | unknown e => simp [result] at computed
    | rejected e => simp [result] at computed
    | conflict l r => simp [result] at computed
  have contextEq : compiled.source.material.gamma = stageGamma :=
    of_decide_eq_true (by simpa only [compilerAccepted] using computed)
  have flow := compiler_reads_actual_extracted_output
    stageMaterial 0 boundaryCatalog [encodedRule] boundaryGate boundaryNodes 1 3
      compiled compilerAccepted
  have extracted := (public_consumer_reads_actual_extraction
    stageMaterial 0 boundaryCatalog out.1 modelStages).1
  have sourceEq : compiled.source = out.1.source :=
    Result.known.inj (flow.1.symm.trans extracted)
  have queryMem := (actual_compilation_enters_finite_closure
    stageMaterial 0 boundaryCatalog [encodedRule] boundaryGate boundaryNodes 1 3
      compiled compilerAccepted).1
  have closureClosed :
      Compiler.closed (activeRules compiled.source.material.gamma [encodedRule] boundaryGate)
        compiled.closure = true := by
    rw [flow.2.2]
    exact Compiler.u03_2_closed_at_finite_fuel _ _ _ (Nat.le_refl _)
  refine ⟨out, compiled, modelAccepted, compilerAccepted, sourceEq, contextEq,
    queryMem, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [contextEq] using closureClosed
  · exact ⟨by simpa only [sameFrame] using firstAmount,
      by simpa only [sameFrame] using finalAmount⟩
  · simp [activeRules, encodedRule, boundaryGate]
  · simp [Compiler.Models, encodedRule, declaredExceptionRule, paidOnlyTruth]
  · simp [Compiler.Models, activeRules, encodedRule, boundaryGate, otherVersion,
      stageGamma, paidAndConclusionTruth, paidOnlyTruth]
  · simp [Compiler.Models, activeRules, encodedRule, boundaryGate, noPaymentTruth]

-- Both finite worlds admit the observed payment. Only the positive atom 4,
-- together with fact faithfulness, rules out the world in which the exception
-- actually occurs. An empty exception file supplies no such atom.
def exceptionTruth (exceptionOccurs : Bool) (a : Nat) : Prop :=
  a = 1 ∨ (exceptionOccurs = false ∧ (a = 4 ∨ a = 3))

theorem positive_exception_witness_is_not_absence :
    (3 ∉ Compiler.proposed_rule_input [declaredExceptionRule] 2 [1] ∧
      3 ∈ Compiler.proposed_rule_input [declaredExceptionRule] 2 [1, 4]) ∧
    (Compiler.closed [declaredExceptionRule]
        (Compiler.proposed_rule_input [declaredExceptionRule] 2 [1]) = true ∧
      Compiler.closed [declaredExceptionRule]
        (Compiler.proposed_rule_input [declaredExceptionRule] 2 [1, 4]) = true) ∧
    (∀ exceptionOccurs : Bool,
      Compiler.Models (fun a => a ∈ ([1] : List Nat))
        (fun r => r ∈ [declaredExceptionRule]) (exceptionTruth exceptionOccurs)) ∧
    (∀ a ∈ ([1] : List Nat), exceptionTruth true a) ∧
    ¬ exceptionTruth true 4 ∧ ¬ exceptionTruth true 3 ∧
    (∀ a ∈ ([1, 4] : List Nat), exceptionTruth false a) ∧
    (∀ exceptionOccurs : Bool,
      (∀ a ∈ ([1, 4] : List Nat), exceptionTruth exceptionOccurs a) →
        exceptionOccurs = false) ∧
    exceptionTruth false 3 := by
  refine ⟨Acceptance.n03_missing_exception_is_not_positive_witness, ?_, ?_⟩
  · decide +kernel
  · simp [Compiler.Models, declaredExceptionRule, exceptionTruth]

end JurisLean.Candidates.SourceHornBoundary20261103

#check JurisLean.Candidates.CompilerProvenance20261027.u03_1_checked_provenance_sound
#print axioms JurisLean.Candidates.CompilerProvenance20261027.u03_1_checked_provenance_sound
#check JurisLean.Candidates.CompilerProvenance20261027.u03_1_checked_provenance_acyclic
#print axioms JurisLean.Candidates.CompilerProvenance20261027.u03_1_checked_provenance_acyclic
#check JurisLean.Candidates.CompilerProvenance20261027.u03_1_provenance_consumed_by_finite_closure
#print axioms JurisLean.Candidates.CompilerProvenance20261027.u03_1_provenance_consumed_by_finite_closure
#check JurisLean.Candidates.CompilerProvenance20261027.u03_1_provenance_semantic_composition
#print axioms JurisLean.Candidates.CompilerProvenance20261027.u03_1_provenance_semantic_composition
#check JurisLean.Candidates.Final20261021.Compiler.u03_1_common_facts_closure_subset_robust
#print axioms JurisLean.Candidates.Final20261021.Compiler.u03_1_common_facts_closure_subset_robust
#check JurisLean.Candidates.Final20261021.Compiler.u03_1_robust_query_strictly_beyond_common_facts
#print axioms JurisLean.Candidates.Final20261021.Compiler.u03_1_robust_query_strictly_beyond_common_facts
#check JurisLean.Candidates.Final20261021.Compiler.exists_closed_fuel_le_carrier
#print axioms JurisLean.Candidates.Final20261021.Compiler.exists_closed_fuel_le_carrier
#check JurisLean.Candidates.Final20261021.Compiler.u03_2_closed_at_finite_fuel
#print axioms JurisLean.Candidates.Final20261021.Compiler.u03_2_closed_at_finite_fuel
#check JurisLean.Candidates.Final20261021.Compiler.u03_2_bounded_executable_closure_complete
#print axioms JurisLean.Candidates.Final20261021.Compiler.u03_2_bounded_executable_closure_complete
#check JurisLean.Candidates.Final20261021.Compiler.u03_2_computed_at_carrier_iff
#print axioms JurisLean.Candidates.Final20261021.Compiler.u03_2_computed_at_carrier_iff
#check JurisLean.Candidates.Final20261021.Compiler.u03_2_robust_queries_exact
#print axioms JurisLean.Candidates.Final20261021.Compiler.u03_2_robust_queries_exact
#check JurisLean.Candidates.Final20261021.Compiler.u03_2_empty_interpretations_rejected
#print axioms JurisLean.Candidates.Final20261021.Compiler.u03_2_empty_interpretations_rejected
#check JurisLean.Candidates.SourceCompilation20261027.compiler_reads_actual_extracted_output
#print axioms JurisLean.Candidates.SourceCompilation20261027.compiler_reads_actual_extracted_output
#check JurisLean.Candidates.SourceCompilation20261027.actual_compilation_enters_finite_closure
#print axioms JurisLean.Candidates.SourceCompilation20261027.actual_compilation_enters_finite_closure
#check JurisLean.Candidates.SourceCompilation20261027.interpreted_material_to_query
#print axioms JurisLean.Candidates.SourceCompilation20261027.interpreted_material_to_query

#check JurisLean.Candidates.TemporalInterpretation20261027.legal_applicability_requires_faithful_interpretation
#print axioms JurisLean.Candidates.TemporalInterpretation20261027.legal_applicability_requires_faithful_interpretation
#check JurisLean.Candidates.TemporalInterpretation20261027.selection_success_contract
#print axioms JurisLean.Candidates.TemporalInterpretation20261027.selection_success_contract
#check JurisLean.Candidates.TemporalInterpretation20261027.successful_version_is_applicable
#print axioms JurisLean.Candidates.TemporalInterpretation20261027.successful_version_is_applicable

#check JurisLean.Candidates.Final20261021.Compiler.u03_1_relative_soundness
#print axioms JurisLean.Candidates.Final20261021.Compiler.u03_1_relative_soundness
#check JurisLean.Candidates.SourceHornBoundary20261103.same_source_completed_countermodels
#print axioms JurisLean.Candidates.SourceHornBoundary20261103.same_source_completed_countermodels
#check JurisLean.Candidates.SourceHornBoundary20261103.positive_exception_witness_is_not_absence
#print axioms JurisLean.Candidates.SourceHornBoundary20261103.positive_exception_witness_is_not_absence
#check JurisLean.Candidates.Final20261021.Acceptance.n03_missing_exception_is_not_positive_witness
#print axioms JurisLean.Candidates.Final20261021.Acceptance.n03_missing_exception_is_not_positive_witness

#check JurisLean.Candidates.SourceStages20261027.finite_stage_compatible_counterexample
#print axioms JurisLean.Candidates.SourceStages20261027.finite_stage_compatible_counterexample
#check JurisLean.Candidates.SourceFinalBridge20261102.source_model_joint_semantic_quantity
#print axioms JurisLean.Candidates.SourceFinalBridge20261102.source_model_joint_semantic_quantity
#check JurisLean.Candidates.SourceFinalBridge20261102.source_model_joint_bridge_nonempty_and_faithfulness_needed
#print axioms JurisLean.Candidates.SourceFinalBridge20261102.source_model_joint_bridge_nonempty_and_faithfulness_needed
