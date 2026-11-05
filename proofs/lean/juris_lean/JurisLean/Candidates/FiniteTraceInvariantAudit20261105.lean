import JurisLean.Candidates.PartialStepGateAudit20261105

namespace JurisLean.Candidates.FiniteTraceInvariantAudit20261105

open JurisLean.Candidates.Final20261021
open JurisLean.Candidates.Final20261021.Acceptance
open JurisLean.Candidates.AuthorizationClosureAudit20261104

-- Frozen 10.5 L133: keep the existing numeric/cash/selector/receipt invariant.
-- The missing conjuncts are fixed business fields and the actual executor
-- contracts at the current Handle. They are proved, not supplied as I assumptions.
-- This is the fixed Trace/consume_ext/refresh model, not every legal operation.
def stableFields (h : Ledger.Handle) :=
  (h.gamma.caseId, h.state.debt.relation, h.state.debt.obligor,
    h.state.debt.creditor, h.state.debt.amount.tag, h.state.debt.metadata,
    h.state.formations)

def BoundRequest (before reference : Ledger.Handle) (req : PaymentRequest) : Prop :=
  reference = before ∧
  (req.payload.caseId = before.gamma.caseId ∧
    req.payload.caseRevision = before.gamma.caseRevision ∧
    req.payload.relation = before.state.debt.relation ∧
    req.payload.payer = before.state.debt.obligor ∧
    req.payload.payee = before.state.debt.creditor ∧
    req.payload.factDate = before.gamma.lawDate) ∧
  req.payload.amount.tag = before.state.debt.amount.tag ∧
  req.payload.normVersion = before.gamma.normVersion ∧
  before.state.env = .known before.gamma.normVersion

-- No new gate: extract the checks already made by validationError.
theorem ready_binds_current_fields (before reference : Ledger.Handle)
    (req : PaymentRequest) (permission : Bool)
    (ready : Ledger.validationError before reference req permission = none) :
    BoundRequest before reference req := by
  unfold Ledger.validationError at ready
  split_ifs at ready with hprev hid hunknown hno hscope htag hversion henv
    hformation hpermission hnegative hused hcash <;> try cases ready
  simp only [not_or, not_not] at hprev hscope htag hversion henv
  exact ⟨hprev, hscope, htag, hversion, henv⟩

theorem step_preserves_fixed_fields {before after : Ledger.Handle}
    (step : Trace.Step before after) : stableFields after = stableFields before := by
  cases step with
  | pay req permission fresh ready nonneg => rfl
  | accrue amount nonneg => rfl
  | principal amount nonneg => rfl
  | writeoff amount nonneg bound => rfl
  | refresh gamma event grants actor authorized sameCase =>
      simpa only [stableFields, sameCase]
  | reject => rfl

theorem path_preserves_fixed_fields {before after : Ledger.Handle}
    (path : Trace.Path before after) : stableFields after = stableFields before := by
  induction path with
  | nil h => rfl
  | cons step rest ih => exact ih.trans (step_preserves_fixed_fields step)

def PaymentGate (before : Ledger.Handle) : Prop :=
  ∀ (reference : Ledger.Handle) (req : PaymentRequest) (permission : Bool)
    (mode : Ledger.Submission) (receipt : Ledger.Receipt) (after : Ledger.Handle),
    Ledger.consume_ext before reference req permission mode = .committed receipt after →
    BoundRequest before reference req

-- This is at-most-once for the supplied model identity. The already-proved
-- source identity bridge keeps its explicit samePaymentId and Trace.Path inputs.
def SingleConsumption (before : Ledger.Handle) : Prop :=
  ∀ (reference after later laterReference : Ledger.Handle)
    (req next : PaymentRequest) (permission permissionNext : Bool)
    (mode modeNext : Ledger.Submission) (receipt : Ledger.Receipt),
    Ledger.consume_ext before reference req permission mode = .committed receipt after →
    Trace.Path after later → next.key = req.key →
    ∀ nextReceipt nextPost,
      Ledger.consume_ext later laterReference next permissionNext modeNext ≠
        .committed nextReceipt nextPost

-- Draft flags do not issue authority. submitDraft is the actual refresh call,
-- and Granted checks the supplied catalog in the old/current Handle context.
def NormGate (before : Ledger.Handle) : Prop :=
  ∀ (catalog : List Authorization.Grant) (change : Pipeline.RefreshInput)
    (after : Ledger.Handle),
    Pipeline.refresh catalog before change = .known after →
    Granted catalog before ⟨change, false, false⟩

theorem local_executor_contracts (before : Ledger.Handle) :
    PaymentGate before ∧ SingleConsumption before ∧ NormGate before := by
  refine ⟨?_, ?_, ?_⟩
  · intro reference req permission mode receipt after committed
    obtain ⟨_, _, ready, _, _⟩ :=
      Ledger.consume_committed_origin before reference req permission mode receipt after committed
    exact ready_binds_current_fields before reference req permission ready
  · exact Trace.u09_1_actual_trace_at_most_once before
  · intro catalog change after published
    exact (actual_refresh_requires_old_authority catalog before after
      ⟨change, false, false⟩ published).1

-- I contains state facts and one-step/trace safety contracts instantiated at
-- the current Handle. Authority is not replaced by a snapshot equality.
def I (current : Ledger.Handle) : Prop :=
  Trace.Invariant current ∧ stableFields current = stableFields opening ∧
  PaymentGate current ∧ SingleConsumption current ∧ NormGate current

theorem initial_i : I opening :=
  ⟨a_opening_invariant, rfl, local_executor_contracts opening⟩

theorem step_preserves_i {before after : Ledger.Handle}
    (step : Trace.Step before after) (initial : I before) : I after := by
  rcases initial with ⟨numeric, frame, _⟩
  exact ⟨Trace.step_preserves step numeric,
    (step_preserves_fixed_fields step).trans frame, local_executor_contracts after⟩

-- Existing numeric induction is reused; only the missing field frame needed
-- a path induction. Any actual intermediate state has such an actual prefix.
theorem finite_prefix_i (current : Ledger.Handle)
    (prefixPath : Trace.Path opening current) : I current :=
  ⟨Trace.u10_2_finite_trace_composition prefixPath a_opening_invariant,
    path_preserves_fixed_fields prefixPath, local_executor_contracts current⟩

-- The premise is the output of the existing real protocol, not an asserted
-- legal trace or an assumed invariant of its final state.
theorem actual_reported_protocol_post_i {W : Type}
    (catalog : List Authorization.Grant) (final : Ledger.Handle)
    (change : Pipeline.RefreshInput)
    (input : JurisLean.Candidates.LegalActionDomain20261027.LegalInput W)
    (branch : Nat)
    (meaning : JurisLean.Candidates.LegalActionDomain20261027.ActionMeaning)
    (renewals : List (JurisLean.Candidates.U10_1RefreshRuleProtocol20261030.RenewalRequest W))
    (reported : (JurisLean.Candidates.U10_1RefreshRuleProtocol20261030.refreshEvaluateContinue
      catalog opening change input branch meaning renewals).payment.current = some final) :
    I final := by
  exact finite_prefix_i final
    (JurisLean.Candidates.U10_1RefreshRuleProtocol20261030.reported_protocol_post_has_actual_path
      catalog opening final change input branch meaning renewals a_opening_invariant reported).1

-- L137 is a non-inference boundary. Same forms does not determine outstanding
-- quantity. claim : Applicable remains unknown here; it is not a judgment of
-- a real legal entitlement. Other effects require their own explicit rule.
theorem forms_do_not_determine_quantity :
    Ledger.forms opening.state debt.relation = true ∧
    Ledger.forms post2.state debt.relation = true ∧
    Ledger.quantity opening.state debt.relation = some 10 ∧
    Ledger.quantity post2.state debt.relation = some 0 ∧
    Ledger.quantity opening.state debt.relation ≠ Ledger.quantity post2.state debt.relation ∧
    opening.state.claim = .unknown ∧ post2.state.claim = .unknown ∧
    post2.state.procedure = .open ∧ post2.state.paid = 14 ∧ post2.state.surplus = 4 := by
  decide +kernel

#check ready_binds_current_fields
#print axioms ready_binds_current_fields
#check step_preserves_fixed_fields
#print axioms step_preserves_fixed_fields
#check path_preserves_fixed_fields
#print axioms path_preserves_fixed_fields
#check local_executor_contracts
#print axioms local_executor_contracts
#check initial_i
#print axioms initial_i
#check step_preserves_i
#print axioms step_preserves_i
#check finite_prefix_i
#print axioms finite_prefix_i
#check actual_reported_protocol_post_i
#print axioms actual_reported_protocol_post_i
#check forms_do_not_determine_quantity
#print axioms forms_do_not_determine_quantity
#check a_opening_invariant
#print axioms a_opening_invariant
#check Trace.step_preserves
#print axioms Trace.step_preserves
#check Trace.u10_2_finite_trace_composition
#print axioms Trace.u10_2_finite_trace_composition
#check Trace.u09_1_actual_trace_at_most_once
#print axioms Trace.u09_1_actual_trace_at_most_once
#check actual_refresh_requires_old_authority
#print axioms actual_refresh_requires_old_authority
#check JurisLean.Candidates.U10_1RefreshRuleProtocol20261030.reported_protocol_post_has_actual_path
#print axioms JurisLean.Candidates.U10_1RefreshRuleProtocol20261030.reported_protocol_post_has_actual_path
#check Ledger.forms_preserved_by_performance
#print axioms Ledger.forms_preserved_by_performance
#check Ledger.performance_metadata
#print axioms Ledger.performance_metadata
#check a_u09_continuous_10_7_7
#print axioms a_u09_continuous_10_7_7
#check n_non_continuous_consume
#print axioms n_non_continuous_consume
#check n_poststate_name_not_binding
#print axioms n_poststate_name_not_binding
#check JurisLean.Candidates.SourcePaymentIdentity20261103.sourced_calls_with_same_payment_id_are_at_most_once
#print axioms JurisLean.Candidates.SourcePaymentIdentity20261103.sourced_calls_with_same_payment_id_are_at_most_once

end JurisLean.Candidates.FiniteTraceInvariantAudit20261105