import JurisLean.Candidates.Final20261021.Pipeline

namespace JurisLean.Candidates.U02_1ActualPipeline20261029

open JurisLean.Candidates.Final20261021

/-- The missing U02.1 execution premise: actual acknowledged outputs of the
    existing payment/refresh pipeline preserve the declared state invariant.
    The opening-state premise is discharged below from frozen section 14. -/
theorem actual_payment_pipeline_preserves_invariant
    (initial final : Ledger.Handle) (first second : PaymentRequest)
    (grants : List Authorization.Grant) (mode : Ledger.Submission)
    (change : Option Pipeline.RefreshInput)
    (valid : Trace.Invariant initial)
    (reported : (Pipeline.executePayments initial first second grants mode change).current = some final) :
    Trace.Invariant final := by
  cases firstRun : Ledger.consume_ext initial initial first
      (Authorization.authorized grants initial.gamma first.payload.payer 0 first.payload.normVersion
        (.relation first.payload.relation) (some first.payload)) .submit with
  | committed receipt firstPost =>
      have validFirst : Trace.Invariant firstPost := Trace.step_preserves
        (Trace.u10_2_committed_executor_is_step initial initial first _ .submit receipt firstPost firstRun) valid
      cases change with
      | none =>
          apply Trace.u10_2_known_executor_post_preserves firstPost firstPost second
            (Authorization.authorized grants firstPost.gamma second.payload.payer 0 second.payload.normVersion
              (.relation second.payload.relation) (some second.payload)) mode final validFirst
          simpa only [Pipeline.executePayments, firstRun, Pipeline.finishPayment_current] using reported
      | some refresh =>
          cases refreshed : Pipeline.refresh grants firstPost refresh with
          | known prepared =>
              have validPrepared : Trace.Invariant prepared := Trace.step_preserves
                (Pipeline.u10_1_authorized_refresh_is_step grants firstPost prepared refresh refreshed) validFirst
              apply Trace.u10_2_known_executor_post_preserves prepared prepared second
                (Authorization.authorized grants prepared.gamma second.payload.payer 0 second.payload.normVersion
                  (.relation second.payload.relation) (some second.payload)) mode final validPrepared
              simpa only [Pipeline.executePayments, firstRun, refreshed, Pipeline.finishPayment_current] using reported
          | unknown e =>
              have same : firstPost = final := by
                simpa only [Pipeline.executePayments, firstRun, refreshed, Option.some.injEq] using reported
              simpa only [← same] using validFirst
          | rejected e =>
              have same : firstPost = final := by
                simpa only [Pipeline.executePayments, firstRun, refreshed, Option.some.injEq] using reported
              simpa only [← same] using validFirst
          | conflict left right =>
              have same : firstPost = final := by
                simpa only [Pipeline.executePayments, firstRun, refreshed, Option.some.injEq] using reported
              simpa only [← same] using validFirst
  | replay receipt =>
      have same : initial = final := by
        simpa only [Pipeline.executePayments, firstRun, Pipeline.finishPayment, Option.some.injEq] using reported
      simpa only [← same] using valid
  | rejectedNoCommit attempt reason =>
      have same : initial = final := by
        simpa only [Pipeline.executePayments, firstRun, Pipeline.finishPayment, Option.some.injEq] using reported
      simpa only [← same] using valid
  | conflict registered requested =>
      have same : initial = final := by
        simpa only [Pipeline.executePayments, firstRun, Pipeline.finishPayment, Option.some.injEq] using reported
      simpa only [← same] using valid
  | unknownCommit key attempt =>
      have impossible : (none : Option Ledger.Handle) = some final := by
        simpa only [Pipeline.executePayments, firstRun, Pipeline.finishPayment] using reported
      cases impossible
  | pending reason =>
      have same : initial = final := by
        simpa only [Pipeline.executePayments, firstRun, Pipeline.finishPayment, Option.some.injEq] using reported
      simpa only [← same] using valid

/-- The exact gate expression used by `Pipeline.runClosed`, without replacing
    its permitted-world lists or its original Bool successor/invariant table. -/
def pipelineGate (i : Pipeline.Input) (derived : List Nat) : List Nat :=
  Harness.proposed_harness_gate (W := Bool) (S := Bool)
    (fun _ => true)
    (fun world _ action => decide (action ∈ if world then i.world1Actions else i.world0Actions))
    (fun _ _ _ after => after) (fun _ after => after) true
    (if i.permissionAtom ∈ derived then i.world0Actions else [])

/-- Mathematical projection of the actual state, with the original table's
    `true` precisely reflecting the existing full state invariant. -/
noncomputable def stateProjection (h : Ledger.Handle) : Bool := by
  classical
  exact decide (Trace.Invariant h)

/-- The actual closed pipeline supplies both the checked action and the
    concrete poststate. No successor-membership premise is assumed. The
    original nonnegative opening-debt condition is frozen section 14's d0≥0. -/
theorem actual_closed_pipeline_refines_gate
    (i : Pipeline.Input) (p1 p2 : PaymentPayload) (derived : List Nat)
    (world : Bool) (selected : Decision.DecisionIR) (final : Ledger.Handle)
    (opening : 0 ≤ i.debt.amount.value)
    (decision : (Pipeline.runClosed i p1 p2 derived).decision = some selected)
    (reported : (Pipeline.runClosed i p1 p2 derived).payment.current = some final) :
    selected.action.id ∈ (if world then i.world1Actions else i.world0Actions) ∧
      selected.action.execution = [p1, p2] ∧ Trace.Invariant final ∧ stateProjection final = true := by
  have choiceAdmission (prediction : Result Calibration.BoundPrediction)
      (values : List Decision.DecisionIR) (picked : Decision.DecisionIR)
      (chosen : (match prediction with
        | .known _ => Decision.proposed_decision (pipelineGate i derived) values
        | _ => none) = some picked) : picked.action.id ∈ pipelineGate i derived := by
    cases prediction with
    | known value => exact (Decision.u06_3_decision_respects_allowed (pipelineGate i derived) values picked chosen).1
    | unknown e => cases chosen
    | rejected e => cases chosen
    | conflict left right => cases chosen
  let initial : Ledger.Handle :=
    let base := Trace.initial i.view.gamma i.debt
    { base with state := { base.state with
      normHistory := i.normHistory,
      env := Temporal.proposed_applicability i.view.gamma i.normHistory } }
  have initialValid : Trace.Invariant initial := by
    rcases Trace.initial_invariant i.view.gamma i.debt opening with ⟨quantity, cash, _, coherent⟩
    exact ⟨quantity, cash, rfl, coherent⟩
  have initialProjection : stateProjection initial = true := by
    simpa only [stateProjection, decide_eq_true_eq] using initialValid
  unfold Pipeline.runClosed at decision reported
  dsimp only at decision reported
  -- Generalize the actual chosen option, retaining its defining equation.
  -- This avoids splitting an inner prediction match instead of the control flow.
  generalize choiceDefinition :
    (match
      (match Learning.proposed_fit_contract i.fitExpected i.fitSupplied,
        RSI.proposed_checkpoint_service
          ⟨i.oldModel.scope.principal, i.fitExpected.task, i.fitExpected.target,
            i.fitExpected.featureVersion, i.view.gamma.normVersion,
            i.view.gamma.mechanismVersion, i.oldModel.model.scope⟩
          (some i.oldModel.model) none none none with
      | .known _, .known model =>
          if model.version = i.fitExpected.modelVersion then
            Calibration.proposed_calibration_support_gate i.fitExpected i.calibration i.riskLimit i.supported
          else .unknown .scopeMismatch
      | _, _ => .unknown .targetMismatch) with
    | .known _ => Decision.proposed_decision
        (Harness.proposed_harness_gate (W := Bool) (S := Bool)
          (fun _ => true)
          (fun world _ action => decide (action ∈ if world then i.world1Actions else i.world0Actions))
          (fun _ _ _ after => after) (fun _ after => after) true
          (if i.permissionAtom ∈ derived then i.world0Actions else []))
        (i.alternatives.filterMap fun a =>
          match Decision.evaluate i.view.gamma i.utility i.utilityVersion i.riskLimit a with
          | .known value => some value
          | _ => none)
    | _ => none) = choice at decision reported
  cases choice with
  | none => simp [Pipeline.stop] at reported
  | some picked =>
      by_cases payloadMatches : picked.action.execution = [p1, p2]
      · simp [payloadMatches] at decision reported
        cases environment : Temporal.proposed_applicability i.view.gamma i.normHistory with
        | known version =>
            by_cases currentVersion : version = i.view.gamma.normVersion
            · simp [environment, currentVersion] at decision reported
              have same : picked = selected := by simpa using decision
              subst picked
              have admitted : selected.action.id ∈ pipelineGate i derived :=
                choiceAdmission _ _ selected choiceDefinition
              have validFinal : Trace.Invariant final :=
                actual_payment_pipeline_preserves_invariant initial final
                  ⟨i.firstKey, ⟨1⟩, p1, .yes, Pipeline.interpretPayment i.view p1⟩
                  ⟨i.secondKey, ⟨2⟩, p2, .yes, Pipeline.interpretPayment i.view p2⟩
                  i.grants i.secondSubmission i.secondRefresh initialValid reported
              have actualStep : stateProjection final = true := by
                simpa only [stateProjection, decide_eq_true_eq] using validFinal
              have safe := ((Harness.u02_3_finite_gate_enumeration (W := Bool) (S := Bool)
                (fun _ => true)
                (fun w _ action => decide (action ∈ if w then i.world1Actions else i.world0Actions))
                (fun _ _ _ after => after) (fun _ after => after) true
                (if i.permissionAtom ∈ derived then i.world0Actions else []) selected.action.id).mp admitted).2
              have atActual := Harness.u02_1_gate_sound_under_Ke
                (fun (_ : Bool) => true = true)
                (fun w (_ : Bool) action =>
                  decide (action ∈ if w then i.world1Actions else i.world0Actions) = true)
                (fun (_ : Bool) (_ : Bool) (_ : Nat) after => after = true)
                (fun (_ : Bool) after => after = true)
                (stateProjection initial) (stateProjection final) selected.action.id world rfl
                (by simpa only [initialProjection] using safe) actualStep
              refine ⟨?_, payloadMatches, validFinal, atActual.2⟩
              simpa only [decide_eq_true_eq] using atActual.1
            · simp [environment, currentVersion, Pipeline.stop] at reported
        | unknown e => simp [environment, Pipeline.stop] at reported
        | rejected e => simp [environment, Pipeline.stop] at reported
        | conflict left right => simp [environment, Pipeline.stop] at reported
      · simp [payloadMatches, Pipeline.stop] at reported

/-- The public pipeline, including actual source binding and rule checking,
    reaches the same gate refinement. The checked full payment list is read
    back from the actual bindings, rather than supplied as an assumption. -/
theorem actual_pipeline_refines_gate
    (i : Pipeline.Input) (world : Bool) (selected : Decision.DecisionIR)
    (final : Ledger.Handle) (opening : 0 ≤ i.debt.amount.value)
    (decision : (Pipeline.run i).decision = some selected)
    (reported : (Pipeline.run i).payment.current = some final) :
    selected.action.id ∈ (if world then i.world1Actions else i.world0Actions) ∧
      Trace.Invariant final ∧ stateProjection final = true ∧
      ∃ p1 p2,
        Representation.proposed_common_model i.view i.firstIndex = .known p1 ∧
        Representation.proposed_common_model i.view i.secondIndex = .known p2 ∧
        selected.action.execution = [p1, p2] := by
  cases firstBinding : Representation.proposed_common_model i.view i.firstIndex <;>
    cases secondBinding : Representation.proposed_common_model i.view i.secondIndex <;>
    cases factChecking : Pipeline.checkFacts i.supportTable i.facts <;>
    simp only [Pipeline.run, firstBinding, secondBinding, factChecking] at decision reported
  all_goals try { simp only [Pipeline.stop, reduceCtorEq] at reported }
  rename_i p1 p2 facts
  cases closure : Compiler.proposed_checked_rule_input i.rules i.closureFuel facts with
  | known derived =>
      have bound := actual_closed_pipeline_refines_gate i p1 p2 derived world selected final opening
        (by simpa only [Pipeline.runBound, closure] using decision)
        (by simpa only [Pipeline.runBound, closure] using reported)
      exact ⟨bound.1, bound.2.2.1, bound.2.2.2, p1, p2, rfl, rfl, bound.2.1⟩
  | unknown e => simp only [Pipeline.runBound, closure, Pipeline.stop, reduceCtorEq] at reported
  | rejected e => simp only [Pipeline.runBound, closure, Pipeline.stop, reduceCtorEq] at reported
  | conflict left right => simp only [Pipeline.runBound, closure, Pipeline.stop, reduceCtorEq] at reported

-- Finite declared examples for original question 02.1: schema checking,
-- action identity, and the norm-context version have different contracts.
def schemaAccept (_action : Bool) : Bool := true
def normAllows (context action : Bool) : Bool := decide (action = context)
def writeState (action _before : Bool) : Bool := action

/-- All three original finite counterexamples, plus the manuscript's common
    idle and empty-successor boundaries. These do not refute the conditional
    gate theorem: each failure removes one of its required connections. -/
theorem finite_failure_and_completion_boundaries :
    (schemaAccept false = true ∧ normAllows true false = false) ∧
    (normAllows true true = true ∧ writeState true false = true ∧
      writeState false false = false ∧ normAllows true false = false) ∧
    (normAllows true true = true ∧ normAllows false true = false) ∧
    (¬ ∃ action : Option Bool, ∀ world : Bool, action = some world) ∧
    (∀ world : Bool, (none : Option Bool) = none ∨ (none : Option Bool) = some world) ∧
    Harness.Safe (fun (_ : Bool) => True)
      (fun (_ : Bool) (_ : Bool) (_ : Bool) => True)
      (fun (_ : Bool) (_ : Bool) (_ : Bool) (_ : Bool) => False)
      (fun (_ : Bool) (_ : Bool) => False) false false ∧
    ¬ ∃ after : Bool, (fun (_ : Bool) (_ : Bool) (_ : Bool) (_ : Bool) => False)
      false false false after := by
  refine ⟨⟨rfl, rfl⟩, ⟨rfl, rfl, rfl, rfl⟩, ⟨rfl, rfl⟩, ?_, ?_, ?_, ?_⟩
  · rintro ⟨action, allWorlds⟩
    have impossible : (false : Bool) = true :=
      Option.some.inj ((allWorlds false).symm.trans (allWorlds true))
    cases impossible
  · intro world
    exact Or.inl rfl
  · intro world possible
    refine ⟨True.intro, ?_⟩
    intro after impossible
    exact impossible
  · rintro ⟨after, impossible⟩
    exact impossible

#check actual_payment_pipeline_preserves_invariant
#print axioms actual_payment_pipeline_preserves_invariant
#check actual_closed_pipeline_refines_gate
#print axioms actual_closed_pipeline_refines_gate
#check actual_pipeline_refines_gate
#print axioms actual_pipeline_refines_gate
#check finite_failure_and_completion_boundaries
#print axioms finite_failure_and_completion_boundaries
#check Harness.u02_1_gate_sound_under_Ke
#print axioms Harness.u02_1_gate_sound_under_Ke
#check Harness.u02_3_finite_gate_enumeration
#print axioms Harness.u02_3_finite_gate_enumeration
#check Decision.u06_3_decision_respects_allowed
#print axioms Decision.u06_3_decision_respects_allowed
#check Trace.initial_invariant
#print axioms Trace.initial_invariant
#check Trace.step_preserves
#print axioms Trace.step_preserves
#check Trace.u10_2_committed_executor_is_step
#print axioms Trace.u10_2_committed_executor_is_step
#check Trace.u10_2_known_executor_post_preserves
#print axioms Trace.u10_2_known_executor_post_preserves
#check Pipeline.u10_1_authorized_refresh_is_step
#print axioms Pipeline.u10_1_authorized_refresh_is_step

end JurisLean.Candidates.U02_1ActualPipeline20261029
