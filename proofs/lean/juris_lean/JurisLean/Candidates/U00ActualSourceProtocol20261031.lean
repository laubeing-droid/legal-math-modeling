import JurisLean.Candidates.U07_2JointObject20261029
import JurisLean.Candidates.U10_1RefreshRuleProtocol20261030

noncomputable section

namespace JurisLean.Candidates.U00ActualSourceProtocol20261031

open JurisLean.Candidates.Final20261021
open JurisLean.Seams
open JurisLean.Candidates.SourceCompilation20261027
open JurisLean.Candidates.SourceStages20261027
open JurisLean.Candidates.U07_2JointObject20261029
open JurisLean.Candidates.FiniteLegalValidation20261027
open JurisLean.Candidates.LegalActionDomain20261027
open JurisLean.Candidates.U10_1RefreshRuleProtocol20261030

/-!
CI_NOT_RUN.

The missing U00 edge is source identity between the actual U07 producer and
the current U10 rule consumer. Both calls use the same anchor, parse branch,
and interpretation catalogue. The equality of the consumed source is derived
from actual extraction and binding calls, rather than supplied as a premise.

A failed source call returns its original failure. A successful source call
runs the existing protocol and retains its complete ProtocolRun, including a
stopped/unknown continuation. Success below refers explicitly to continued=true.
The selected norm version is the checked refreshed version; nothing identifies
background.norms with the newly selected norms.
-/

def sourceThenProtocol {V R W : Type} [DecidableEq R]
    (background : UnifiedModel V R) (grants : List Authorization.Grant)
    (before : Ledger.Handle) (change : Pipeline.RefreshInput)
    (input : LegalInput W) (branch : Nat) (meaning : ActionMeaning)
    (renewals : List (RenewalRequest W)) :
    Except (Result Unit)
      ((SourceFrame × UnifiedModel V RelationId) × ProtocolRun) :=
  match sourceModel background input.anchor branch input.catalog with
  | .error failure => .error failure
  | .ok sourceOut =>
      .ok (sourceOut,
        refreshEvaluateContinue grants before change input branch meaning renewals)

/-- Every source failure, including unknown/conflict, is returned unchanged. -/
theorem source_failure_is_retained {V R W : Type} [DecidableEq R]
    (background : UnifiedModel V R) (grants : List Authorization.Grant)
    (before : Ledger.Handle) (change : Pipeline.RefreshInput)
    (input : LegalInput W) (branch : Nat) (meaning : ActionMeaning)
    (renewals : List (RenewalRequest W)) (failure : Result Unit)
    (failed : sourceModel background input.anchor branch input.catalog = .error failure) :
    sourceThenProtocol background grants before change input branch meaning renewals =
      .error failure := by
  simp [sourceThenProtocol, failed]

private lemma sourceThenProtocol_actual_calls {V R W : Type} [DecidableEq R]
    (background : UnifiedModel V R) (grants : List Authorization.Grant)
    (before : Ledger.Handle) (change : Pipeline.RefreshInput)
    (input : LegalInput W) (branch : Nat) (meaning : ActionMeaning)
    (renewals : List (RenewalRequest W))
    (sourceOut : SourceFrame × UnifiedModel V RelationId) (run : ProtocolRun)
    (called : sourceThenProtocol background grants before change input branch meaning renewals =
      .ok (sourceOut, run)) :
    sourceModel background input.anchor branch input.catalog = .ok sourceOut ∧
      run = refreshEvaluateContinue grants before change input branch meaning renewals := by
  cases produced : sourceModel background input.anchor branch input.catalog with
  | error failure => simp [sourceThenProtocol, produced] at called
  | ok actual =>
      have pairEq : actual = sourceOut ∧
          refreshEvaluateContinue grants before change input branch meaning renewals = run := by
        simpa only [sourceThenProtocol, produced, Except.ok.injEq, Prod.mk.injEq] using called
      exact ⟨by simpa only [pairEq.1] using produced, pairEq.2.symm⟩

/-- The actual producer's joint source is the source read by the current rule consumer. -/
theorem successful_joint_source_is_actual_current_rule_input
    {V R W : Type} [DecidableEq R]
    (background : UnifiedModel V R) (grants : List Authorization.Grant)
    (before : Ledger.Handle) (change : Pipeline.RefreshInput)
    (input : LegalInput W) (branch : Nat) (meaning : ActionMeaning)
    (renewals : List (RenewalRequest W))
    (sourceOut : SourceFrame × UnifiedModel V RelationId) (run : ProtocolRun)
    (called : sourceThenProtocol background grants before change input branch meaning renewals =
      .ok (sourceOut, run))
    (continued : run.continued = true) :
    ∃ x : JointObject, ∃ after : Ledger.Handle, ∃ bound : BoundData, ∃ horn : HornReport,
      suppliedLayers sourceOut = jointLayers background x ∧
      JointContract background input.anchor branch input.catalog x ∧
      bound.source = sourceOut.1.source ∧
      Pipeline.refresh grants before change = .known after ∧
      evaluateCurrentRules after input branch = .known (bound, horn) ∧
      after.state.env = .known horn.selectedVersion ∧
      horn.selectedVersion = after.gamma.normVersion ∧
      input.anchor.gamma = after.gamma ∧ input.history = after.state.normHistory ∧
      horn = fullHorn sourceOut.1.source horn.selectedVersion input.rules input.ruleGate
        (eligibleFacts bound) ∧
      Trace.Step before after ∧
      (∀ final : Ledger.Handle, Trace.Invariant before →
        run.payment.current = some final →
        Trace.Path before final ∧ Trace.Invariant final ∧
          before.state.used ⊆ final.state.used) := by
  obtain ⟨produced, runActual⟩ := sourceThenProtocol_actual_calls
    background grants before change input branch meaning renewals sourceOut run called
  have started :
      (refreshEvaluateContinue grants before change input branch meaning renewals).continued = true := by
    simpa only [runActual] using continued
  obtain ⟨x, sameLayers, joint⟩ := actual_source_has_joint_object
    background input.anchor branch input.catalog sourceOut produced
  obtain ⟨after, bound, horn, procedure, refreshed, evaluated, environment, version,
      full, anchor, history, meaningGamma, permissions, process, closed,
      payment, frame, step⟩ :=
    continued_protocol_refines_actual_calls grants before change input branch meaning renewals started
  have staged := (public_model_consumes_the_actual_stage_frame
    background input.anchor branch input.catalog sourceOut produced).1
  have extractedSource := (public_consumer_reads_actual_extraction
    input.anchor branch input.catalog sourceOut.1 staged).1
  have flow := evaluated_rules_use_actual_environment after input branch bound horn evaluated
  obtain ⟨view, extractedView, admitted⟩ := flow.2.2.1
  have viewSame : view = sourceOut.1.source :=
    Result.known.inj (extractedView.symm.trans extractedSource)
  have boundSource : bound.source = sourceOut.1.source :=
    (bound_data_keeps_exact_source_and_independent_policy
      view input.supplements input.policies bound admitted).1.trans viewSame
  refine ⟨x, after, bound, horn, sameLayers, joint, boundSource,
    refreshed, evaluated, environment, version, anchor, history, ?_, step, ?_⟩
  · simpa only [boundSource] using full
  · intro final initial reported
    have reportedActual :
        (refreshEvaluateContinue grants before change input branch meaning renewals).payment.current =
          some final := by
      simpa only [runActual] using reported
    exact reported_protocol_post_has_actual_path grants before final change input branch meaning
      renewals initial reportedActual

end JurisLean.Candidates.U00ActualSourceProtocol20261031

#print axioms JurisLean.Candidates.U00ActualSourceProtocol20261031.source_failure_is_retained
#print axioms JurisLean.Candidates.U00ActualSourceProtocol20261031.successful_joint_source_is_actual_current_rule_input
