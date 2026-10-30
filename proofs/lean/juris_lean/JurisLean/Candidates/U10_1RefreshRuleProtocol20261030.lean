/-
CI_NOT_RUN.

Blocks master U10.1 L311--313: the actual successful refresh environment is
passed to the existing selectedHorn/fullHorn evaluator before the finite
instruction tail is called. Every successful internal refresh repeats these
checks with an explicit new continuation request. Source Gamma and history are checked, not
rewritten. Existing rule semantics, executors and trace/invariant proofs are
reused; only necessary control-flow and path-composition connections are added.

The supplied ActionMeaning is an external normative premise contract. These
checks do not establish its legal truth from its SourceRef. The computed local
precondition checks its current Gamma, derived permission atoms and required
procedure closure. Payment identity, payload scope, current authorization and
consumption checks are still performed by the existing actual tail executor;
refresh alone does not imply that a later payment will commit.

Only this finite payment/refresh composition is claimed. UnknownCommit still
has no certain poststate. No new global termination or general-protocol claim.
-/

import JurisLean.Candidates.LegalActionDomain20261027

namespace JurisLean.Candidates.U10_1RefreshRuleProtocol20261030

open JurisLean.Candidates.Final20261021
open JurisLean.Candidates.SourceCompilation20261027
open JurisLean.Candidates.FiniteLegalValidation20261027
open JurisLean.Candidates.LegalActionDomain20261027
open JurisLean.Candidates.DecisionTrajectoryConsumer20261027
open JurisLean.Candidates.ProcedureClosure20261027

/-- Existing source extraction and evidence admission feed the actual current
environment directly to the existing versioned rule evaluator. -/
def evaluateCurrentRules {W : Type} (current : Ledger.Handle)
    (input : LegalInput W) (branch : Nat) : Result (BoundData × HornReport) :=
  if input.anchor.gamma = current.gamma ∧ input.history = current.state.normHistory then
    match extractView input.anchor branch input.catalog with
    | .known view =>
        match bindAdditional view input.supplements input.policies with
        | .known bound =>
            match selectedHorn bound.source current.state.env input.rules input.ruleGate
                (eligibleFacts bound) with
            | .known out => .known (bound, out)
            | .unknown e => .unknown e
            | .rejected e => .rejected e
            | .conflict l r => .conflict l r
        | .unknown e => .unknown e
        | .rejected e => .rejected e
        | .conflict l r => .conflict l r
    | .unknown e => .unknown e
    | .rejected e => .rejected e
    | .conflict l r => .conflict l r
  else .rejected .scopeMismatch

/-- These are actual checks of the declared local law-step precondition, not
assumptions that the desired executor validation or a commit has succeeded. -/
private def checkNext (current : Ledger.Handle) (meaning : ActionMeaning)
    (bound : BoundData) (out : HornReport) : Result Unit :=
  if meaning.gamma ≠ current.gamma then .rejected .scopeMismatch
  else if meaning.permissionAtoms.all (fun a => decide (a ∈ out.closure)) = false then
    .unknown .notIdentified
  else
    match checkProcess bound.policy.required (processInput bound.supplement.process bound.policy) with
    | .known procedure =>
        if meaning.requiresClosed = true ∧ procedure ≠ .closedLawfully then
          .unknown .openMissingOpportunity
        else .known ()
    | .unknown e => .unknown e
    | .rejected e => .rejected e
    | .conflict l r => .conflict l r

structure ProtocolRun where
  evaluation : Result (BoundData × HornReport)
  /-- Initial tail entry; later internal checks may still stop that tail. -/
  continued : Bool
  payment : Pipeline.PaymentRun

private def stopAt (current : Ledger.Handle) (evaluation : Result (BoundData × HornReport))
    (exit : Pipeline.Exit) (reason : Error) : ProtocolRun :=
  ⟨evaluation, false, ⟨exit, some current, [], [reason]⟩⟩

/-- One existing explicit request for each successful internal refresh. -/
abbrev RenewalRequest (W : Type) := LegalInput W × Nat × ActionMeaning

def checkRenewal {W : Type} (current : Ledger.Handle)
    (steps : List Instruction) : List (RenewalRequest W) → Result (List (RenewalRequest W))
  | [] => .unknown .missingEvidence
  | (input, branch, meaning) :: remaining =>
      match evaluateCurrentRules current input branch with
      | .known (bound, out) =>
          if meaning.steps = steps then
            match checkNext current meaning bound out with
            | .known _ => .known remaining
            | .unknown e => .unknown e
            | .rejected e => .rejected e
            | .conflict l r => .conflict l r
          else .rejected .scopeMismatch
      | .unknown e => .unknown e
      | .rejected e => .rejected e
      | .conflict l r => .conflict l r

/-- Each payment is run exactly once by the existing single-step interpreter.
Every successful internal refresh rechecks the new actual poststate against an
explicit current request; fresh requests permit internal version changes. -/
def checkedTail {W : Type} (grants : List Authorization.Grant)
    (current : Ledger.Handle) (steps : List Instruction)
    (renewals : List (RenewalRequest W)) : Pipeline.PaymentRun :=
  match steps with
  | [] => ⟨.success, some current, [], []⟩
  | .pay request mode :: rest =>
      let one := runTrajectory grants current [.pay request mode]
      match one.exit, one.current with
      | .success, some actualPost =>
          let tail := checkedTail grants actualPost rest renewals
          {tail with outcomes := one.outcomes ++ tail.outcomes,
            obligations := one.obligations ++ tail.obligations}
      | _, _ => one
  | .refresh change :: rest =>
      match Pipeline.refresh grants current change with
      | .known actualPost =>
          if rest = [] then ⟨.success, some actualPost, [], []⟩
          else
            match checkRenewal actualPost rest renewals with
            | .known remaining => checkedTail grants actualPost rest remaining
            | .unknown e => ⟨.undecided, some actualPost, [], [e]⟩
            | .rejected e => ⟨.rejected, some actualPost, [], [e]⟩
            | .conflict _ _ => ⟨.undecided, some actualPost, [], [.versionConflict]⟩
      | .unknown e => ⟨.undecided, some current, [], [e]⟩
      | .rejected e => ⟨.rejected, some current, [], [e]⟩
      | .conflict _ _ => ⟨.undecided, some current, [], [.versionConflict]⟩

private def continueAt {W : Type} (grants : List Authorization.Grant)
    (current : Ledger.Handle) (input : LegalInput W) (branch : Nat)
    (meaning : ActionMeaning) (renewals : List (RenewalRequest W)) : ProtocolRun :=
  let evaluated := evaluateCurrentRules current input branch
  match evaluated with
  | .known (bound, out) =>
      match checkNext current meaning bound out with
      | .known _ => ⟨evaluated, true, checkedTail grants current meaning.steps renewals⟩
      | .unknown e => stopAt current evaluated .undecided e
      | .rejected e => stopAt current evaluated .rejected e
      | .conflict _ _ => stopAt current evaluated .undecided .versionConflict
  | .unknown e => stopAt current evaluated .undecided e
  | .rejected e => stopAt current evaluated .rejected e
  | .conflict _ _ => stopAt current evaluated .undecided .versionConflict

/-- Actual refresh, actual rule evaluation, checked continuation. Every stopped
rule/precondition branch keeps the already committed refresh poststate. -/
def refreshEvaluateContinue {W : Type} (grants : List Authorization.Grant)
    (before : Ledger.Handle) (change : Pipeline.RefreshInput)
    (input : LegalInput W) (branch : Nat) (meaning : ActionMeaning)
    (renewals : List (RenewalRequest W)) : ProtocolRun :=
  match Pipeline.refresh grants before change with
  | .known actualPost => continueAt grants actualPost input branch meaning renewals
  | .unknown e => stopAt before (.unknown e) .undecided e
  | .rejected e => stopAt before (.rejected e) .rejected e
  | .conflict l r => stopAt before (.conflict l r) .undecided .versionConflict

/-- Blocks the missing real rule-input edge: the actual env is the selection
argument; source/facts come from the actual checked source/admission calls. -/
theorem evaluated_rules_use_actual_environment {W : Type} (current : Ledger.Handle)
    (input : LegalInput W) (branch : Nat) (bound : BoundData) (out : HornReport)
    (accepted : evaluateCurrentRules current input branch = .known (bound, out)) :
    input.anchor.gamma = current.gamma ∧ input.history = current.state.normHistory ∧
      (∃ view, extractView input.anchor branch input.catalog = .known view ∧
        bindAdditional view input.supplements input.policies = .known bound) ∧
      bound.source.material.gamma = current.gamma ∧
      selectedHorn bound.source current.state.env input.rules input.ruleGate
        (eligibleFacts bound) = .known out ∧
      current.state.env = .known out.selectedVersion ∧
      out.selectedVersion = current.gamma.normVersion ∧
      out = fullHorn bound.source out.selectedVersion input.rules input.ruleGate
        (eligibleFacts bound) := by
  by_cases aligned : input.anchor.gamma = current.gamma ∧ input.history = current.state.normHistory
  · cases extracted : extractView input.anchor branch input.catalog with
    | unknown e => simp [evaluateCurrentRules, aligned, extracted] at accepted
    | rejected e => simp [evaluateCurrentRules, aligned, extracted] at accepted
    | conflict l r => simp [evaluateCurrentRules, aligned, extracted] at accepted
    | known view =>
        cases admitted : bindAdditional view input.supplements input.policies with
        | unknown e => simp [evaluateCurrentRules, aligned, extracted, admitted] at accepted
        | rejected e => simp [evaluateCurrentRules, aligned, extracted, admitted] at accepted
        | conflict l r => simp [evaluateCurrentRules, aligned, extracted, admitted] at accepted
        | known actualBound =>
            cases evaluated : selectedHorn actualBound.source current.state.env input.rules
                input.ruleGate (eligibleFacts actualBound) with
            | unknown e => simp [evaluateCurrentRules, aligned, extracted, admitted, evaluated] at accepted
            | rejected e => simp [evaluateCurrentRules, aligned, extracted, admitted, evaluated] at accepted
            | conflict l r => simp [evaluateCurrentRules, aligned, extracted, admitted, evaluated] at accepted
            | known actualOut =>
                have same : (actualBound, actualOut) = (bound, out) :=
                  Result.known.inj (by
                    simpa only [evaluateCurrentRules, if_pos aligned, extracted, admitted, evaluated]
                      using accepted)
                cases same
                have material := (extracted_view_is_exact_selected_payload
                  input.anchor branch input.catalog view extracted).1
                have source := (bound_data_keeps_exact_source_and_independent_policy
                  view input.supplements input.policies actualBound admitted).1
                have sameGamma : actualBound.source.material.gamma = current.gamma := by
                  rw [source, material, aligned.1]
                have flow := selected_horn_cannot_rewrite_original_context actualBound.source
                  current.state.env input.rules input.ruleGate (eligibleFacts actualBound) actualOut evaluated
                exact ⟨aligned.1, aligned.2, ⟨view, extracted, admitted⟩, sameGamma,
                  evaluated, flow.1, by simpa only [sameGamma] using flow.2.1, flow.2.2⟩
  · simp [evaluateCurrentRules, aligned] at accepted

private theorem checkNext_known (current : Ledger.Handle) (meaning : ActionMeaning)
    (bound : BoundData) (out : HornReport)
    (accepted : checkNext current meaning bound out = .known ()) :
    meaning.gamma = current.gamma ∧ (∀ a ∈ meaning.permissionAtoms, a ∈ out.closure) ∧
      ∃ procedure,
        checkProcess bound.policy.required (processInput bound.supplement.process bound.policy) =
          .known procedure ∧
        (meaning.requiresClosed = true → procedure = .closedLawfully) := by
  by_cases sameGamma : meaning.gamma = current.gamma
  · cases permissions : meaning.permissionAtoms.all (fun a => decide (a ∈ out.closure)) with
    | false => simp [checkNext, sameGamma, permissions] at accepted
    | true =>
        cases checked : checkProcess bound.policy.required
            (processInput bound.supplement.process bound.policy) with
        | unknown e => simp [checkNext, sameGamma, permissions, checked] at accepted
        | rejected e => simp [checkNext, sameGamma, permissions, checked] at accepted
        | conflict l r => simp [checkNext, sameGamma, permissions, checked] at accepted
        | known procedure =>
            by_cases blocked : meaning.requiresClosed = true ∧ procedure ≠ .closedLawfully
            · simp [checkNext, sameGamma, permissions, checked, blocked] at accepted
            · refine ⟨sameGamma, ?_, procedure, checked, ?_⟩
              · simpa only [List.all_eq_true, decide_eq_true_eq] using permissions
              · intro required
                by_contra notClosed
                exact blocked ⟨required, notClosed⟩
  · simp [checkNext, sameGamma] at accepted

private theorem checkRenewal_known {W : Type} (current : Ledger.Handle)
    (steps : List Instruction) (renewals remaining : List (RenewalRequest W))
    (checked : checkRenewal current steps renewals = .known remaining) :
    ∃ input branch meaning bound out,
      renewals = (input, branch, meaning) :: remaining ∧ meaning.steps = steps ∧
      evaluateCurrentRules current input branch = .known (bound, out) ∧
      checkNext current meaning bound out = .known () := by
  cases renewals with
  | nil => simp [checkRenewal] at checked
  | cons request rest =>
      rcases request with ⟨input, branch, meaning⟩
      cases evaluated : evaluateCurrentRules current input branch with
      | unknown e => simp [checkRenewal, evaluated] at checked
      | rejected e => simp [checkRenewal, evaluated] at checked
      | conflict l r => simp [checkRenewal, evaluated] at checked
      | known pair =>
          rcases pair with ⟨bound, out⟩
          by_cases sameTail : meaning.steps = steps
          · cases ready : checkNext current meaning bound out with
            | unknown e => simp [checkRenewal, evaluated, sameTail, ready] at checked
            | rejected e => simp [checkRenewal, evaluated, sameTail, ready] at checked
            | conflict l r => simp [checkRenewal, evaluated, sameTail, ready] at checked
            | known unit =>
                cases unit
                have same : rest = remaining := Result.known.inj (by
                  simpa only [checkRenewal, evaluated, if_pos sameTail, ready] using checked)
                subst remaining
                exact ⟨input, branch, meaning, bound, out, rfl, sameTail, evaluated, ready⟩
          · simp [checkRenewal, evaluated, sameTail] at checked

/-- Master L313 at every internal refresh, with the original instruction suffix
checked against a new explicit meaning, without relabelling old premises. -/
theorem internal_refresh_rechecks_before_continuation {W : Type}
    (grants : List Authorization.Grant) (before after : Ledger.Handle)
    (change : Pipeline.RefreshInput) (steps : List Instruction)
    (renewals remaining : List (RenewalRequest W))
    (nonempty : steps ≠ [])
    (refreshed : Pipeline.refresh grants before change = .known after)
    (renewed : checkRenewal after steps renewals = .known remaining) :
    ∃ input branch meaning bound out procedure,
      renewals = (input, branch, meaning) :: remaining ∧ meaning.steps = steps ∧
      evaluateCurrentRules after input branch = .known (bound, out) ∧
      input.anchor.gamma = after.gamma ∧ input.history = after.state.normHistory ∧
      after.state.env = .known out.selectedVersion ∧ out.selectedVersion = after.gamma.normVersion ∧
      out = fullHorn bound.source out.selectedVersion input.rules input.ruleGate (eligibleFacts bound) ∧
      meaning.gamma = after.gamma ∧ (∀ a ∈ meaning.permissionAtoms, a ∈ out.closure) ∧
      checkProcess bound.policy.required (processInput bound.supplement.process bound.policy) =
        .known procedure ∧
      (meaning.requiresClosed = true → procedure = .closedLawfully) ∧
      checkedTail grants before (.refresh change :: steps) renewals =
        checkedTail grants after steps remaining := by
  obtain ⟨input, branch, meaning, bound, out, requests, sameTail, evaluated, ready⟩ :=
    checkRenewal_known after steps renewals remaining renewed
  have flow := evaluated_rules_use_actual_environment after input branch bound out evaluated
  obtain ⟨sameGamma, permissions, procedure, process, closed⟩ :=
    checkNext_known after meaning bound out ready
  refine ⟨input, branch, meaning, bound, out, procedure, requests, sameTail, evaluated,
    flow.1, flow.2.1, flow.2.2.2.2.2.1, flow.2.2.2.2.2.2.1,
    flow.2.2.2.2.2.2.2, sameGamma, permissions, process, closed, ?_⟩
  simp only [checkedTail, refreshed, if_neg nonempty, renewed]

private theorem continueAt_started {W : Type} (grants : List Authorization.Grant)
    (current : Ledger.Handle) (input : LegalInput W) (branch : Nat) (meaning : ActionMeaning)
    (renewals : List (RenewalRequest W))
    (started : (continueAt grants current input branch meaning renewals).continued = true) :
    ∃ bound out, evaluateCurrentRules current input branch = .known (bound, out) ∧
      checkNext current meaning bound out = .known () ∧
      (continueAt grants current input branch meaning renewals).payment =
        checkedTail grants current meaning.steps renewals := by
  cases evaluated : evaluateCurrentRules current input branch with
  | unknown e => simp [continueAt, evaluated, stopAt] at started
  | rejected e => simp [continueAt, evaluated, stopAt] at started
  | conflict l r => simp [continueAt, evaluated, stopAt] at started
  | known pair =>
      rcases pair with ⟨bound, out⟩
      cases checked : checkNext current meaning bound out with
      | unknown e => simp [continueAt, evaluated, checked, stopAt] at started
      | rejected e => simp [continueAt, evaluated, checked, stopAt] at started
      | conflict l r => simp [continueAt, evaluated, checked, stopAt] at started
      | known unit =>
          cases unit
          exact ⟨bound, out, evaluated, checked, by simp only [continueAt, evaluated, checked]⟩

private theorem continueAt_stopped {W : Type} (grants : List Authorization.Grant)
    (current : Ledger.Handle) (input : LegalInput W) (branch : Nat) (meaning : ActionMeaning)
    (renewals : List (RenewalRequest W))
    (stopped : (continueAt grants current input branch meaning renewals).continued = false) :
    (continueAt grants current input branch meaning renewals).payment.current = some current := by
  cases evaluated : evaluateCurrentRules current input branch with
  | unknown e => simp only [continueAt, evaluated, stopAt]
  | rejected e => simp only [continueAt, evaluated, stopAt]
  | conflict l r => simp only [continueAt, evaluated, stopAt]
  | known pair =>
      rcases pair with ⟨bound, out⟩
      cases checked : checkNext current meaning bound out with
      | unknown e => simp only [continueAt, evaluated, checked, stopAt]
      | rejected e => simp only [continueAt, evaluated, checked, stopAt]
      | conflict l r => simp only [continueAt, evaluated, checked, stopAt]
      | known unit => simp [continueAt, evaluated, checked] at stopped

private theorem refresh_success_post (grants : List Authorization.Grant)
    (before after : Ledger.Handle) (change : Pipeline.RefreshInput)
    (published : Pipeline.refresh grants before change = .known after) :
    after = ⟨change.gamma, before.revision + 1, {before.state with
      normHistory := before.state.normHistory ++ [change.event],
      env := Temporal.proposed_applicability change.gamma (before.state.normHistory ++ [change.event])}⟩ := by
  unfold Pipeline.refresh at published
  split at published
  next mismatch => cases published
  next sameCase =>
    split at published
    next unauthorized => cases published
    next authorized => exact (Result.known.inj published).symm

/-- Blocks the missing composed Post/Frame-to-next-Pre connection. All local
rule/procedure premises below are obtained from actual checks. Remaining
payment premises are rechecked by the unchanged actual runTrajectory executor. -/
theorem continued_protocol_refines_actual_calls {W : Type} (grants : List Authorization.Grant)
    (before : Ledger.Handle) (change : Pipeline.RefreshInput)
    (input : LegalInput W) (branch : Nat) (meaning : ActionMeaning)
    (renewals : List (RenewalRequest W))
    (started : (refreshEvaluateContinue grants before change input branch meaning renewals).continued = true) :
    ∃ after bound out procedure,
      Pipeline.refresh grants before change = .known after ∧
      evaluateCurrentRules after input branch = .known (bound, out) ∧
      after.state.env = .known out.selectedVersion ∧
      out.selectedVersion = after.gamma.normVersion ∧
      out = fullHorn bound.source out.selectedVersion input.rules input.ruleGate (eligibleFacts bound) ∧
      input.anchor.gamma = after.gamma ∧ input.history = after.state.normHistory ∧
      meaning.gamma = after.gamma ∧ (∀ a ∈ meaning.permissionAtoms, a ∈ out.closure) ∧
      checkProcess bound.policy.required (processInput bound.supplement.process bound.policy) =
        .known procedure ∧
      (meaning.requiresClosed = true → procedure = .closedLawfully) ∧
      (refreshEvaluateContinue grants before change input branch meaning renewals).payment =
        checkedTail grants after meaning.steps renewals ∧
      {after.state with normHistory := before.state.normHistory, env := before.state.env} = before.state ∧
      Trace.Step before after := by
  cases refreshed : Pipeline.refresh grants before change with
  | unknown e => simp [refreshEvaluateContinue, refreshed, stopAt] at started
  | rejected e => simp [refreshEvaluateContinue, refreshed, stopAt] at started
  | conflict l r => simp [refreshEvaluateContinue, refreshed, stopAt] at started
  | known after =>
      have continued : (continueAt grants after input branch meaning renewals).continued = true := by
        simpa only [refreshEvaluateContinue, refreshed] using started
      obtain ⟨bound, out, evaluated, checked, tail⟩ :=
        continueAt_started grants after input branch meaning renewals continued
      have flow := evaluated_rules_use_actual_environment after input branch bound out evaluated
      obtain ⟨sameGamma, permissions, procedure, process, closed⟩ :=
        checkNext_known after meaning bound out checked
      have frame : {after.state with normHistory := before.state.normHistory,
          env := before.state.env} = before.state := by
        rw [refresh_success_post grants before after change refreshed]
      refine ⟨after, bound, out, procedure, refreshed, evaluated, flow.2.2.2.2.2.1,
        flow.2.2.2.2.2.2.1, flow.2.2.2.2.2.2.2, flow.1, flow.2.1,
        sameGamma, permissions, process, closed, ?_, frame, ?_⟩
      · simpa only [refreshEvaluateContinue, refreshed] using tail
      · exact Pipeline.u10_1_authorized_refresh_is_step grants before after change refreshed

/-- A stopped initial rule/procedure phase does not roll back or hide an already
committed refresh, nor pretend that its old environment is still current. -/
theorem stopped_protocol_keeps_committed_refresh {W : Type} (grants : List Authorization.Grant)
    (before after : Ledger.Handle) (change : Pipeline.RefreshInput)
    (input : LegalInput W) (branch : Nat) (meaning : ActionMeaning)
    (renewals : List (RenewalRequest W))
    (refreshed : Pipeline.refresh grants before change = .known after)
    (stopped : (refreshEvaluateContinue grants before change input branch meaning renewals).continued = false) :
    (refreshEvaluateContinue grants before change input branch meaning renewals).payment.current = some after := by
  have halted : (continueAt grants after input branch meaning renewals).continued = false := by
    simpa only [refreshEvaluateContinue, refreshed] using stopped
  simpa only [refreshEvaluateContinue, refreshed] using
    continueAt_stopped grants after input branch meaning renewals halted

private theorem append_actual_paths {before middle final : Ledger.Handle}
    (first : Trace.Path before middle) (second : Trace.Path middle final) :
    Trace.Path before final := by
  induction first generalizing final with
  | nil => exact second
  | cons edge rest ih => exact .cons edge (ih second)

private theorem checkedTail_has_actual_path {W : Type} (grants : List Authorization.Grant)
    (current final : Ledger.Handle) (steps : List Instruction)
    (renewals : List (RenewalRequest W))
    (reported : (checkedTail grants current steps renewals).current = some final) :
    Trace.Path current final := by
  induction steps generalizing current renewals with
  | nil =>
      have same : current = final := by
        simpa only [checkedTail, Option.some.injEq] using reported
      subst final
      exact .nil current
  | cons instruction rest ih =>
      cases instruction with
      | pay request mode =>
          cases exited : (runTrajectory grants current [.pay request mode]).exit with
          | success =>
              cases post : (runTrajectory grants current [.pay request mode]).current with
              | none => simp [checkedTail, exited, post] at reported
              | some actualPost =>
                  have tailPost : (checkedTail grants actualPost rest renewals).current = some final := by
                    simpa only [checkedTail, exited, post] using reported
                  exact append_actual_paths
                    (every_reported_post_has_an_actual_path grants [.pay request mode]
                      current actualPost post)
                    (ih actualPost renewals tailPost)
          | rejected =>
              have onePost : (runTrajectory grants current [.pay request mode]).current = some final := by
                simpa only [checkedTail, exited] using reported
              exact every_reported_post_has_an_actual_path grants [.pay request mode] current final onePost
          | undecided =>
              have onePost : (runTrajectory grants current [.pay request mode]).current = some final := by
                simpa only [checkedTail, exited] using reported
              exact every_reported_post_has_an_actual_path grants [.pay request mode] current final onePost
      | refresh change =>
          cases refreshed : Pipeline.refresh grants current change with
          | unknown e =>
              have same : current = final := by
                simpa only [checkedTail, refreshed, Option.some.injEq] using reported
              subst final
              exact .nil current
          | rejected e =>
              have same : current = final := by
                simpa only [checkedTail, refreshed, Option.some.injEq] using reported
              subst final
              exact .nil current
          | conflict l r =>
              have same : current = final := by
                simpa only [checkedTail, refreshed, Option.some.injEq] using reported
              subst final
              exact .nil current
          | known actualPost =>
              have edge := Pipeline.u10_1_authorized_refresh_is_step grants current actualPost change refreshed
              by_cases empty : rest = []
              · have same : actualPost = final := by
                  simpa only [checkedTail, refreshed, if_pos empty, Option.some.injEq] using reported
                subst final
                exact .cons edge (.nil actualPost)
              · cases renewed : checkRenewal actualPost rest renewals with
                | known remaining =>
                    have tailPost : (checkedTail grants actualPost rest remaining).current = some final := by
                      simpa only [checkedTail, refreshed, if_neg empty, renewed] using reported
                    exact .cons edge (ih actualPost remaining tailPost)
                | unknown e =>
                    have same : actualPost = final := by
                      simpa only [checkedTail, refreshed, if_neg empty, renewed, Option.some.injEq] using reported
                    subst final
                    exact .cons edge (.nil actualPost)
                | rejected e =>
                    have same : actualPost = final := by
                      simpa only [checkedTail, refreshed, if_neg empty, renewed, Option.some.injEq] using reported
                    subst final
                    exact .cons edge (.nil actualPost)
                | conflict l r =>
                    have same : actualPost = final := by
                      simpa only [checkedTail, refreshed, if_neg empty, renewed, Option.some.injEq] using reported
                    subst final
                    exact .cons edge (.nil actualPost)

/-- Only the new refresh edge is composed with the existing actual-tail path
theorem. The closed finite trace and invariant proofs are reused unchanged. -/
theorem reported_protocol_post_has_actual_path {W : Type} (grants : List Authorization.Grant)
    (before final : Ledger.Handle) (change : Pipeline.RefreshInput)
    (input : LegalInput W) (branch : Nat) (meaning : ActionMeaning)
    (renewals : List (RenewalRequest W))
    (initial : Trace.Invariant before)
    (reported : (refreshEvaluateContinue grants before change input branch meaning renewals).payment.current = some final) :
    Trace.Path before final ∧ Trace.Invariant final ∧ before.state.used ⊆ final.state.used := by
  have path : Trace.Path before final := by
    cases refreshed : Pipeline.refresh grants before change with
    | unknown e =>
        have same : before = final := by
          simpa only [refreshEvaluateContinue, refreshed, stopAt, Option.some.injEq] using reported
        subst final
        exact .nil before
    | rejected e =>
        have same : before = final := by
          simpa only [refreshEvaluateContinue, refreshed, stopAt, Option.some.injEq] using reported
        subst final
        exact .nil before
    | conflict l r =>
        have same : before = final := by
          simpa only [refreshEvaluateContinue, refreshed, stopAt, Option.some.injEq] using reported
        subst final
        exact .nil before
    | known after =>
        have step := Pipeline.u10_1_authorized_refresh_is_step grants before after change refreshed
        cases started : (continueAt grants after input branch meaning renewals).continued with
        | false =>
            have current := continueAt_stopped grants after input branch meaning renewals started
            have same : after = final := by
              have exactPost : (continueAt grants after input branch meaning renewals).payment.current = some final := by
                simpa only [refreshEvaluateContinue, refreshed] using reported
              exact Option.some.inj (current.symm.trans exactPost)
            subst final
            exact .cons step (.nil after)
        | true =>
            obtain ⟨bound, out, evaluated, checked, tail⟩ :=
              continueAt_started grants after input branch meaning renewals started
            have tailPost : (checkedTail grants after meaning.steps renewals).current = some final := by
              simpa only [refreshEvaluateContinue, refreshed, tail] using reported
            exact .cons step
              (checkedTail_has_actual_path grants after final meaning.steps renewals tailPost)
  exact ⟨path, Trace.u10_2_finite_trace_composition path initial, Trace.used_monotone_path path⟩

end JurisLean.Candidates.U10_1RefreshRuleProtocol20261030
