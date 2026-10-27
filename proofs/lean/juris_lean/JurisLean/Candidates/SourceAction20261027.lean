import JurisLean.Candidates.SourceOpening20261027

/-!
The first business episode consumes the actual source opening. Each payment
instruction selects a bound row from that finite source window; callers supply
attempts and submission outcomes, never replacement payment keys or payloads.
Quotes are checked against these instructions without rewriting any payoff,
cost, context or execution field. Failed quote bindings remain in the result.

Legal meanings, grants, outcome identification, measurement attestations and
sampling assumptions remain independent inputs. A known outer result means the
consumer ran, not that its decision, payment, measurement or feedback succeeded.
No unknown commit is resolved here and no structural stage is a commit receipt.
-/

namespace JurisLean.Candidates.SourceAction20261027

open JurisLean.Candidates.Final20261021
open JurisLean.Candidates.SourceStages20261027
open JurisLean.Candidates.FiniteLegalValidation20261027
open JurisLean.Candidates.IntervalDecisionConsumer20261027
open JurisLean.Candidates.DecisionTrajectoryConsumer20261027
open JurisLean.Candidates.LegalActionDomain20261027
open JurisLean.Candidates.LoadedLegalConsumer20261027
open JurisLean.Candidates.AdaptiveRoundLedger20261027
open JurisLean.Candidates.BusinessFeedbackLoop20261027
open JurisLean.Candidates.SourceOpening20261027

inductive PaymentSlot where
  | first | second
  deriving DecidableEq, Repr

def boundRow (frame : SourceFrame) : PaymentSlot → BoundPayment
  | .first => frame.first
  | .second => frame.second

structure PaymentCall where
  slot : PaymentSlot
  attempt : AttemptId
  submission : Ledger.Submission
  deriving DecidableEq, Repr

def sourceApplicable {W : Type} (opening : SharedOpening W) (row : BoundPayment) : Applicable :=
  if opening.handle.state.env = .known row.payment.value.payload.normVersion ∧
      opening.branches.all (fun branch => decide
        (branch.legal.selected = .known row.payment.value.payload.normVersion)) then .yes
  else .unknown

def paymentRequest {W : Type} (opening : SharedOpening W) (call : PaymentCall) : PaymentRequest :=
  let row := boundRow opening.anchor.frame call.slot
  ⟨row.payment.value.key, call.attempt, row.payment.value.payload,
    sourceApplicable opening row, some row.payment.value.key⟩

def instructions {W : Type} (opening : SharedOpening W) (calls : List PaymentCall) : List Instruction :=
  calls.map fun call => .pay (paymentRequest opening call) call.submission

theorem source_request_keeps_actual_key_payload_and_identity {W : Type}
    (opening : SharedOpening W) (call : PaymentCall) :
    let row := boundRow opening.anchor.frame call.slot
    (paymentRequest opening call).key = row.payment.value.key ∧
    (paymentRequest opening call).payload = row.payment.value.payload ∧
    (paymentRequest opening call).interpretedPayment = some row.payment.value.key ∧
    (paymentRequest opening call).attempt = call.attempt := ⟨rfl, rfl, rfl, rfl⟩

theorem applicable_request_requires_actual_environment_and_all_versions {W : Type}
    (opening : SharedOpening W) (call : PaymentCall) :
    (paymentRequest opening call).applicable = .yes ↔
      opening.handle.state.env = .known (paymentRequest opening call).payload.normVersion ∧
      ∀ branch ∈ opening.branches,
        branch.legal.selected = .known (paymentRequest opening call).payload.normVersion := by
  simp [paymentRequest, sourceApplicable, List.all_eq_true]

theorem instruction_payloads_are_source_rows_in_call_order {W : Type}
    (opening : SharedOpening W) (calls : List PaymentCall) :
    paymentPayloads (instructions opening calls) =
      calls.map (fun call => (boundRow opening.anchor.frame call.slot).payment.value.payload) := by
  induction calls with
  | nil => rfl
  | cons call rest ih => simpa only [instructions, List.map_cons, paymentPayloads, paymentRequest] using
      congrArg (List.cons (boundRow opening.anchor.frame call.slot).payment.value.payload) ih

structure PlanSpec where
  quote : BinaryQuote
  calls : List PaymentCall
  deriving DecidableEq, Repr

def bindPlan {W : Type} (opening : SharedOpening W) (spec : PlanSpec) : Result Proposal :=
  let steps := instructions opening spec.calls
  if spec.quote.gamma = opening.handle.gamma ∧ paymentPayloads steps = spec.quote.execution then
    .known ⟨spec.quote, steps⟩
  else .rejected .scopeMismatch

theorem bound_plan_preserves_entire_quote_and_source_instructions {W : Type}
    (opening : SharedOpening W) (spec : PlanSpec) (proposal : Proposal)
    (accepted : bindPlan opening spec = .known proposal) :
    proposal.quote = spec.quote ∧ proposal.steps = instructions opening spec.calls ∧
      spec.quote.gamma = opening.handle.gamma ∧
      spec.quote.execution = spec.calls.map
        (fun call => (boundRow opening.anchor.frame call.slot).payment.value.payload) := by
  unfold bindPlan at accepted
  split at accepted
  · rename_i checked
    cases accepted
    exact ⟨rfl, rfl, checked.1,
      checked.2.symm.trans (instruction_payloads_are_source_rows_in_call_order opening spec.calls)⟩
  · cases accepted

def planResults {W : Type} (opening : SharedOpening W) (specs : List PlanSpec) :
    List (PlanSpec × Result Proposal) := specs.map fun spec => (spec, bindPlan opening spec)

def usablePlans (rows : List (PlanSpec × Result Proposal)) : List Proposal :=
  rows.filterMap fun row => match row.2 with
    | .known proposal => some proposal
    | _ => none

theorem usable_plan_has_an_actual_source_spec {W : Type}
    (opening : SharedOpening W) (specs : List PlanSpec) (proposal : Proposal)
    (member : proposal ∈ usablePlans (planResults opening specs)) :
    ∃ spec ∈ specs, bindPlan opening spec = .known proposal := by
  obtain ⟨row, present, selected⟩ := List.mem_filterMap.mp member
  obtain ⟨spec, included, same⟩ := List.mem_map.mp present
  subst row
  cases bound : bindPlan opening spec with
  | unknown e => simp [bound] at selected
  | rejected e => simp [bound] at selected
  | conflict a b => simp [bound] at selected
  | known actual =>
      have equal : actual = proposal := by simpa [bound] using selected
      exact ⟨spec, included, by simpa [equal] using bound⟩

structure ActionSettings (W : Type) (m : Nat) where
  model : ActionModel W Ledger.Handle
  plans : List PlanSpec
  request : DecisionRequest m
  calibration : CalibrationPacket m
  calibrationCatalog : List (CalibrationPacket m)
  radius : ℚ
  exponent : Nat
  utility : ℚ → ℚ
  grants : List Authorization.Grant

def actionInput {W : Type} {m : Nat} (legal : LegalInput W)
    (settings : ActionSettings W m) (rows : List (PlanSpec × Result Proposal)) : ActionInput W m :=
  ⟨legal, settings.model, usablePlans rows, settings.request, settings.calibration,
    settings.calibrationCatalog, settings.radius, settings.exponent, settings.utility, settings.grants⟩

structure Completed (W : Type) (m : Nat) where
  opening : SharedOpening W
  plans : List (PlanSpec × Result Proposal)
  initial : State m
  episode : Episode W m

structure Run (W : Type) (m : Nat) where
  inspection : Result (List (Nat × Result (ValidationReport W)))
  outcome : Result (Completed W m)

def run {W : Type} {m : Nat} (legal : LegalInput W) (learning : RoundState m)
    (settings : ActionSettings W m) (measurement : MeasurementInput m)
    (policy : PolicyInput m) (feedback : FeedbackInput m) : Run W m :=
  ⟨legal.inspect, match openingFor legal with
    | .known opening =>
        let rows := planResults opening settings.plans
        match initialState opening learning with
        | .known initial => .known ⟨opening, rows, initial,
            BusinessFeedbackLoop20261027.episode initial (actionInput legal settings rows)
              measurement policy feedback⟩
        | .unknown e => .unknown e
        | .rejected e => .rejected e
        | .conflict a b => .conflict a b
    | .unknown e => .unknown e
    | .rejected e => .rejected e
    | .conflict a b => .conflict a b⟩

theorem source_run_keeps_inspection_even_on_failure {W : Type} {m : Nat}
    (legal : LegalInput W) (learning : RoundState m) (settings : ActionSettings W m)
    (measurement : MeasurementInput m) (policy : PolicyInput m) (feedback : FeedbackInput m) :
    (run legal learning settings measurement policy feedback).inspection = legal.inspect := rfl

theorem completed_run_consumes_actual_opening_and_plans {W : Type} {m : Nat}
    (legal : LegalInput W) (learning : RoundState m) (settings : ActionSettings W m)
    (measurement : MeasurementInput m) (policy : PolicyInput m) (feedback : FeedbackInput m)
    (out : Completed W m)
    (completed : (run legal learning settings measurement policy feedback).outcome = .known out) :
    openingFor legal = .known out.opening ∧ initialState out.opening learning = .known out.initial ∧
      out.plans = planResults out.opening settings.plans ∧
      out.episode = BusinessFeedbackLoop20261027.episode out.initial
        (actionInput legal settings out.plans) measurement policy feedback := by
  cases opened : openingFor legal with
  | unknown e => simp [run, opened] at completed
  | rejected e => simp [run, opened] at completed
  | conflict a b => simp [run, opened] at completed
  | known opening =>
      cases initialized : initialState opening learning with
      | unknown e => simp [run, opened, initialized] at completed
      | rejected e => simp [run, opened, initialized] at completed
      | conflict a b => simp [run, opened, initialized] at completed
      | known initial =>
          simp only [run, opened, initialized, Result.known.injEq] at completed
          subst out
          exact ⟨rfl, initialized, rfl, rfl⟩

theorem selected_source_plan_has_actual_spec_and_legal_validation {W : Type} {m : Nat}
    (legal : LegalInput W) (learning : RoundState m) (settings : ActionSettings W m)
    (measurement : MeasurementInput m) (policy : PolicyInput m) (feedback : FeedbackInput m)
    (out : Completed W m) (actual : LoadedRun W m) (proposal : Proposal)
    (completed : (run legal learning settings measurement policy feedback).outcome = .known out)
    (called : out.episode.action.run = some actual)
    (chosen : actual.execution.proposal = some proposal) :
    ∃ spec ∈ settings.plans, bindPlan out.opening spec = .known proposal ∧
      ∃ branches, legal.inspect = .known branches ∧
        accepts settings.model legal.truth out.opening.handle legal.anchor.gamma branches proposal = true := by
  have connected := completed_run_consumes_actual_opening_and_plans legal learning settings measurement
    policy feedback out completed
  have initial := initialized_state_keeps_supplied_learner_and_actual_opening
    out.opening learning out.initial connected.2.1
  rw [connected.2.2.2] at called
  obtain ⟨before, reported, executed, _⟩ := actual_action_reads_current_handle_and_loaded_state
    out.initial (actionInput legal settings out.plans) actual called
  have same : before = out.opening.handle := Option.some.inj (reported.symm.trans initial.2.1)
  subst before
  rw [executed] at chosen
  obtain ⟨branches, inspected, member, accepted⟩ := loaded_run_uses_actual_legal_validation
    legal settings.model (usablePlans out.plans) out.initial.learning settings.request settings.calibration
    settings.calibrationCatalog settings.radius settings.exponent settings.utility settings.grants
    out.opening.handle proposal chosen
  rw [connected.2.2.1] at member
  obtain ⟨spec, included, bound⟩ := usable_plan_has_an_actual_source_spec out.opening settings.plans proposal member
  exact ⟨spec, included, bound, branches, inspected, accepted⟩

theorem source_episode_and_finite_continuation_preserve_invariants {W : Type} {m : Nat}
    (legal : LegalInput W) (learning : RoundState m) (settings : ActionSettings W m)
    (measurement : MeasurementInput m) (policy : PolicyInput m) (feedback : FeedbackInput m)
    (out : Completed W m) (commands : List (Command W m))
    (completed : (run legal learning settings measurement policy feedback).outcome = .known out)
    (budget : roundSpent learning ≤ learning.limit) :
    KnownBusinessInvariant (commands.foldl step out.episode.continuation.post) ∧
      (commands.foldl step out.episode.continuation.post).learning.limit = learning.limit ∧
      roundSpent (commands.foldl step out.episode.continuation.post).learning ≤ learning.limit := by
  have connected := completed_run_consumes_actual_opening_and_plans legal learning settings measurement
    policy feedback out completed
  have started : start legal learning = .known out.initial := by
    simp only [start, connected.1, connected.2.1]
  have valid := source_initialized_state_has_proved_known_invariant legal learning out.initial started
  rw [connected.2.2.2]
  exact arbitrary_finite_commands_start_from_actual_source legal learning out.initial
    (.episode (actionInput legal settings out.plans) measurement policy feedback :: commands) started budget

end JurisLean.Candidates.SourceAction20261027
