import JurisLean.Candidates.Final20261021.Pipeline
import JurisLean.Candidates.DecisionTrajectoryConsumer20261027
import JurisLean.Candidates.ParametricAllocationAudit20261104
import JurisLean.Seams.UnifiedNeedlesS0S1

/-!
Frozen original 10.7 L149/L151/L153 preparation only. CI_NOT_RUN; PARTIAL.
L149: actual finite business projection, payment effect connection and non-stutter.
L151: actual refresh projection with explicit execution/query Gamma parameters.
L153: independent-history codec and bad intermediate-authority counterexamples.
Reuse Ledger.consume_committed_origin; do not replace any closed core theorem.
Scope: fixed pay/refresh/replay/reject instructions only. Dropped State fields
have no preservation claim in this fragment. No external legal truth is proved.
The fixed interpreter lifting retains the supplied grants throughout; payment
and refresh legality are independent predicates on projected fields. A reported
post does not imply success: known failures can stop at the unchanged state.
unknownCommit has no reported post and is not assigned a successful stutter.
-/

namespace JurisLean.Candidates.RepresentationRefinementAudit20261105

open JurisLean.Candidates.Final20261021

/-- A genuine projection, omitting procedure/judgment and other unused fields. -/
structure BusinessView where
  gamma : Gamma
  revision : Nat
  debt : DebtRecord
  formations : List RelationId
  allocated : ℚ
  paid : ℚ
  surplus : ℚ
  cash : List CashEvent
  used : Finset PaymentId
  receipts : List Ledger.Receipt
  history : List Temporal.VersionRecord
  env : Result Nat

def project (h : Ledger.Handle) : BusinessView :=
  ⟨h.gamma, h.revision, h.state.debt, h.state.formations,
    h.state.allocated, h.state.paid, h.state.surplus, h.state.cash,
    h.state.used, h.state.receipts, h.state.normHistory, h.state.env⟩

def Ref (h : Ledger.Handle) (s : BusinessView) : Prop := project h = s

-- Explicit field effect, not an existential image of a concrete execution.
def payEffect (s : BusinessView) (req : PaymentRequest) : BusinessView :=
  let k := min req.payload.amount.value s.debt.amount.value
  let receipt : Ledger.Receipt :=
    ⟨req.key, req.payload, s.revision, s.revision + 1,
      s.debt.amount.value, s.debt.amount.value - k, k, req.payload.amount.value - k⟩
  { s with
    revision := s.revision + 1
    debt := { s.debt with amount := { s.debt.amount with value := s.debt.amount.value - k } }
    allocated := s.allocated + k
    paid := s.paid + req.payload.amount.value
    surplus := s.surplus + (req.payload.amount.value - k)
    cash := s.cash ++ [⟨req.payload.cashId, req.payload.source,
      req.payload.payer, req.payload.payee, req.payload.amount⟩]
    used := insert req.key s.used
    receipts := s.receipts ++ [receipt] }

theorem project_commit (before : Ledger.Handle) (req : PaymentRequest) :
    project (Ledger.commitPayment before req).2 = payEffect (project before) req := rfl

/-- Authority calculation remains the actual call's supplied catalog, not a
new assumption asserting abstract simulation or observation agreement. -/
theorem actual_payment_projects (grants : List Authorization.Grant)
    (before after : Ledger.Handle) (req : PaymentRequest)
    (mode : Ledger.Submission) (receipt : Ledger.Receipt)
    (success : Ledger.consume_ext before before req
      (Authorization.authorized grants before.gamma req.payload.payer 0
        req.payload.normVersion (.relation req.payload.relation) (some req.payload))
      mode = .committed receipt after) :
    project after = payEffect (project before) req := by
  obtain ⟨_, _, _, _, post⟩ := Ledger.consume_committed_origin before before req
    (Authorization.authorized grants before.gamma req.payload.payer 0
      req.payload.normVersion (.relation req.payload.relation) (some req.payload))
    mode receipt after success
  rw [post]
  exact project_commit before req

theorem pay_effect_receipt_length (s : BusinessView) (req : PaymentRequest) :
    (payEffect s req).receipts.length = s.receipts.length + 1 := by
  simp [payEffect]

/-- Includes zero-amount payment: receipt observation forbids a hidden stutter. -/
theorem pay_effect_not_stutter (s : BusinessView) (req : PaymentRequest) :
    payEffect s req ≠ s := by
  intro same
  have lengths := congrArg (fun v : BusinessView => v.receipts.length) same
  rw [pay_effect_receipt_length] at lengths
  omega

def refreshEffect (s : BusinessView) (g : Gamma)
    (e : Temporal.VersionRecord) : BusinessView :=
  { s with gamma := g, revision := s.revision + 1,
    history := s.history ++ [e],
    env := Temporal.proposed_applicability g (s.history ++ [e]) }

theorem actual_refresh_projects (grants : List Authorization.Grant)
    (before after : Ledger.Handle) (change : Pipeline.RefreshInput)
    (published : Pipeline.refresh grants before change = .known after) :
    project after = refreshEffect (project before) change.gamma change.event := by
  unfold Pipeline.refresh at published
  split at published
  · cases published
  · split at published
    · cases published
    · cases published
      rfl

/-- A historical query keeps its own context; no claim that an appended event
is invisible or that revocation universally commutes with old queries. -/
def queryAt (q : Gamma) (s : BusinessView) : Result Nat :=
  Temporal.proposed_applicability q s.history

theorem historical_query_parameter (q next : Gamma) (s : BusinessView)
    (e : Temporal.VersionRecord) :
    queryAt q (refreshEffect s next e) =
      Temporal.proposed_applicability q (s.history ++ [e]) := rfl

/-- All explicitly required observations are retained literally by the
projection, including attribution through complete cash/receipt payloads. -/
theorem actual_observation_projection (h : Ledger.Handle) :
    (project h).cash = h.state.cash ∧
    (project h).used = h.state.used ∧
    (project h).receipts = h.state.receipts ∧
    (project h).gamma = h.gamma ∧
    (project h).history = h.state.normHistory ∧
    (project h).env = h.state.env := ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

-- Same finite boundary checks, expressed only on abstract fields. The caller
-- uses the current state as previous_output_ref; no stale-reference claim.
def payError (s : BusinessView) (req : PaymentRequest) (permission : Bool) : Option Error :=
  if req.interpretedPayment ≠ some req.key then some .identityUnknown
  else if req.applicable = .unknown then some .applicabilityUnknown
  else if req.applicable = .no then some .notApplicable
  else if req.payload.caseId ≠ s.gamma.caseId ∨
      req.payload.caseRevision ≠ s.gamma.caseRevision ∨
      req.payload.relation ≠ s.debt.relation ∨
      req.payload.payer ≠ s.debt.obligor ∨ req.payload.payee ≠ s.debt.creditor ∨
      req.payload.factDate ≠ s.gamma.lawDate then some .scopeMismatch
  else if req.payload.amount.tag ≠ s.debt.amount.tag then some .unitBindingMissing
  else if req.payload.normVersion ≠ s.gamma.normVersion then some .scopeMismatch
  else if s.env ≠ .known s.gamma.normVersion then some .scopeMismatch
  else if s.debt.relation ∉ s.formations then some .notApplicable
  else if permission = false then some .authorityUnresolved
  else if req.payload.amount.value < 0 then some .unsupported
  else if req.key ∈ s.used then some .duplicateCash
  else if s.cash.any (fun e => e.id == req.payload.cashId) then some .duplicateCash
  else none

def permissionAt (grants : List Authorization.Grant) (s : BusinessView)
    (req : PaymentRequest) : Bool :=
  Authorization.authorized grants s.gamma req.payload.payer 0
    req.payload.normVersion (.relation req.payload.relation) (some req.payload)

inductive LegalStep (grants : List Authorization.Grant) : BusinessView → BusinessView → Prop where
  | pay (s : BusinessView) (req : PaymentRequest)
      (fresh : s.receipts.find? (fun r => r.key == req.key) = none)
      (ready : payError s req (permissionAt grants s req) = none) :
      LegalStep grants s (payEffect s req)
  | refresh (s : BusinessView) (change : Pipeline.RefreshInput)
      (sameCase : change.gamma.caseId = s.gamma.caseId)
      (authority : Authorization.authorized grants s.gamma change.actor 1
        change.event.version (.document change.event.version) none (some change.gamma) = true) :
      LegalStep grants s (refreshEffect s change.gamma change.event)

inductive LegalPath (grants : List Authorization.Grant) : BusinessView → BusinessView → Prop where
  | nil (s : BusinessView) : LegalPath grants s s
  | cons {s t u : BusinessView} : LegalStep grants s t →
      LegalPath grants t u → LegalPath grants s u

theorem actual_payment_legal (grants : List Authorization.Grant)
    (before after : Ledger.Handle) (req : PaymentRequest)
    (mode : Ledger.Submission) (receipt : Ledger.Receipt)
    (success : Ledger.consume_ext before before req (permissionAt grants (project before) req)
      mode = .committed receipt after) : LegalStep grants (project before) (project after) := by
  obtain ⟨_, fresh, ready, _, post⟩ := Ledger.consume_committed_origin before before req
    (permissionAt grants (project before) req) mode receipt after success
  rw [post, project_commit]
  apply LegalStep.pay
  · exact fresh
  · simpa [payError, project, Ledger.validationError] using ready

theorem actual_refresh_legal (grants : List Authorization.Grant)
    (before after : Ledger.Handle) (change : Pipeline.RefreshInput)
    (published : Pipeline.refresh grants before change = .known after) :
    LegalStep grants (project before) (project after) := by
  rw [actual_refresh_projects grants before after change published]
  by_cases same : change.gamma.caseId = before.gamma.caseId
  · cases authority : Authorization.authorized grants before.gamma change.actor 1
      change.event.version (.document change.event.version) none (some change.gamma) with
    | false => simp [Pipeline.refresh, same, authority] at published
    | true => exact .refresh (project before) change same authority
  · simp [Pipeline.refresh, same] at published

open JurisLean.Candidates.DecisionTrajectoryConsumer20261027

/-- Fixed actual interpreter only. Induction follows its real branches, so the
authorization catalog is never reconstructed from a bare Trace.Path. -/
theorem actual_finite_trace_projects (grants : List Authorization.Grant)
    (steps : List Instruction) (initial final : Ledger.Handle)
    (reported : (runTrajectory grants initial steps).current = some final) :
    LegalPath grants (project initial) (project final) := by
  induction steps generalizing initial with
  | nil =>
      have same : initial = final := by simpa [runTrajectory] using reported
      subst final
      exact .nil _
  | cons step rest ih =>
      cases step with
      | pay req mode =>
          cases executed : Ledger.consume_ext initial initial req
              (Authorization.authorized grants initial.gamma req.payload.payer 0 req.payload.normVersion
                (.relation req.payload.relation) (some req.payload)) mode with
          | committed receipt actualPost =>
              exact .cons (actual_payment_legal grants initial actualPost req mode receipt executed)
                (ih actualPost (by simpa only [runTrajectory, executed] using reported))
          | replay receipt =>
              exact ih initial (by simpa only [runTrajectory, executed] using reported)
          | unknownCommit key attempt =>
              simp [runTrajectory, executed, Pipeline.finishPayment] at reported
          | rejectedNoCommit attempt e =>
              have same : initial = final := by
                simpa [runTrajectory, executed, Pipeline.finishPayment] using reported
              subst final
              exact .nil _
          | conflict registered requested =>
              have same : initial = final := by
                simpa [runTrajectory, executed, Pipeline.finishPayment] using reported
              subst final
              exact .nil _
          | pending e =>
              have same : initial = final := by
                simpa [runTrajectory, executed, Pipeline.finishPayment] using reported
              subst final
              exact .nil _
      | refresh change =>
          cases refreshed : Pipeline.refresh grants initial change with
          | known actualPost =>
              exact .cons (actual_refresh_legal grants initial actualPost change refreshed)
                (ih actualPost (by simpa only [runTrajectory, refreshed] using reported))
          | unknown e =>
              have same : initial = final := by simpa [runTrajectory, refreshed] using reported
              subst final
              exact .nil _
          | rejected e =>
              have same : initial = final := by simpa [runTrajectory, refreshed] using reported
              subst final
              exact .nil _
          | conflict x y =>
              have same : initial = final := by simpa [runTrajectory, refreshed] using reported
              subst final
              exact .nil _

/-- Explicit no-post boundary; reconciliation lies outside this finite proof. -/
theorem unknown_commit_has_no_reported_post (grants : List Authorization.Grant)
    (before : Ledger.Handle) (req : PaymentRequest) (mode : Ledger.Submission)
    (rest : List Instruction) (key : PaymentId) (attempt : AttemptId)
    (unknown : Ledger.consume_ext before before req (permissionAt grants (project before) req)
      mode = .unknownCommit key attempt) :
    (runTrajectory grants before (.pay req mode :: rest)).current = none := by
  have executed : Ledger.consume_ext before before req
      (Authorization.authorized grants before.gamma req.payload.payer 0 req.payload.normVersion
        (.relation req.payload.relation) (some req.payload)) mode =
      .unknownCommit key attempt := unknown
  simp only [runTrajectory, executed, Pipeline.finishPayment]

-- A bad candidate writes a genuine commitPayment effect without invoking the
-- authorized executor, then arbitrarily restores the initial Handle. These
-- are candidate writes, NOT a claim of actual legal steps or lawful rollback.
def goodCandidate : List Ledger.Handle := [Acceptance.opening]
def badCandidate : List Ledger.Handle :=
  [Acceptance.opening, Acceptance.post1, Acceptance.opening]

theorem same_terminal_misses_intermediate_authority :
    goodCandidate.head? = badCandidate.head? ∧
    goodCandidate.getLast? = badCandidate.getLast? ∧
    LegalPath [] (project Acceptance.opening) (project Acceptance.opening) ∧
    Acceptance.post1 ∈ badCandidate ∧
    project Acceptance.post1 = payEffect (project Acceptance.opening) (Acceptance.request 1) ∧
    (project Acceptance.post1).receipts.length =
      (project Acceptance.opening).receipts.length + 1 ∧
    permissionAt [] (project Acceptance.opening) (Acceptance.request 1) = false := by
  refine ⟨rfl, rfl, .nil _, ?_, ?_, ?_, ?_⟩
  · simp [badCandidate]
  · exact project_commit Acceptance.opening (Acceptance.request 1)
  · rw [show project Acceptance.post1 =
      payEffect (project Acceptance.opening) (Acceptance.request 1) from
        project_commit Acceptance.opening (Acceptance.request 1)]
    exact pay_effect_receipt_length _ _
  · rfl

open JurisLean.Seams.UnifiedNeedlesS0S1

/-- Counterexample to a codec-only acceptance rule, not to the actual executor.
The existing codec theorem is reused, while independent histories disagree. -/
theorem codec_does_not_constrain_independent_history (record : CaseRecord) :
    caseFragment.dec (caseFragment.enc record) = record ∧
    (record, ([] : List Nat)).1 = (record, [1]).1 ∧
    (record, ([] : List Nat)).2 ≠ (record, [1]).2 := by
  refine ⟨caseFragment_roundTrip record, rfl, ?_⟩
  simp

end JurisLean.Candidates.RepresentationRefinementAudit20261105

-- 13 own declarations + 3 necessary reused evidence targets. CI_NOT_RUN.
#check JurisLean.Candidates.RepresentationRefinementAudit20261105.project_commit
#print axioms JurisLean.Candidates.RepresentationRefinementAudit20261105.project_commit
#check JurisLean.Candidates.RepresentationRefinementAudit20261105.actual_payment_projects
#print axioms JurisLean.Candidates.RepresentationRefinementAudit20261105.actual_payment_projects
#check JurisLean.Candidates.RepresentationRefinementAudit20261105.pay_effect_receipt_length
#print axioms JurisLean.Candidates.RepresentationRefinementAudit20261105.pay_effect_receipt_length
#check JurisLean.Candidates.RepresentationRefinementAudit20261105.pay_effect_not_stutter
#print axioms JurisLean.Candidates.RepresentationRefinementAudit20261105.pay_effect_not_stutter
#check JurisLean.Candidates.RepresentationRefinementAudit20261105.actual_refresh_projects
#print axioms JurisLean.Candidates.RepresentationRefinementAudit20261105.actual_refresh_projects
#check JurisLean.Candidates.RepresentationRefinementAudit20261105.historical_query_parameter
#print axioms JurisLean.Candidates.RepresentationRefinementAudit20261105.historical_query_parameter
#check JurisLean.Candidates.RepresentationRefinementAudit20261105.actual_observation_projection
#print axioms JurisLean.Candidates.RepresentationRefinementAudit20261105.actual_observation_projection
#check JurisLean.Candidates.RepresentationRefinementAudit20261105.actual_payment_legal
#print axioms JurisLean.Candidates.RepresentationRefinementAudit20261105.actual_payment_legal
#check JurisLean.Candidates.RepresentationRefinementAudit20261105.actual_refresh_legal
#print axioms JurisLean.Candidates.RepresentationRefinementAudit20261105.actual_refresh_legal
#check JurisLean.Candidates.RepresentationRefinementAudit20261105.actual_finite_trace_projects
#print axioms JurisLean.Candidates.RepresentationRefinementAudit20261105.actual_finite_trace_projects
#check JurisLean.Candidates.RepresentationRefinementAudit20261105.unknown_commit_has_no_reported_post
#print axioms JurisLean.Candidates.RepresentationRefinementAudit20261105.unknown_commit_has_no_reported_post
#check JurisLean.Candidates.RepresentationRefinementAudit20261105.same_terminal_misses_intermediate_authority
#print axioms JurisLean.Candidates.RepresentationRefinementAudit20261105.same_terminal_misses_intermediate_authority
#check JurisLean.Candidates.RepresentationRefinementAudit20261105.codec_does_not_constrain_independent_history
#print axioms JurisLean.Candidates.RepresentationRefinementAudit20261105.codec_does_not_constrain_independent_history
#check JurisLean.Candidates.ParametricAllocationAudit20261104.l163_equal_total_does_not_fix_identity
#print axioms JurisLean.Candidates.ParametricAllocationAudit20261104.l163_equal_total_does_not_fix_identity
#check JurisLean.Seams.UnifiedNeedlesS0S1.caseFragment_roundTrip
#print axioms JurisLean.Seams.UnifiedNeedlesS0S1.caseFragment_roundTrip
#check JurisLean.Candidates.Final20261021.Ledger.consume_committed_origin
#print axioms JurisLean.Candidates.Final20261021.Ledger.consume_committed_origin
