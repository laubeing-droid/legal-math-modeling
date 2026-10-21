import JurisLean.Candidates.Final20261021.Progress
import JurisLean.Candidates.Final20261021.Transactions
import JurisLean.Seams.UnifiedQuantLedger

namespace JurisLean.Candidates.Final20261021.Ledger

structure Receipt where
  key : PaymentId
  payload : PaymentPayload
  beforeRevision : Nat
  afterRevision : Nat
  beforeDebt : ℚ
  afterDebt : ℚ
  allocated : ℚ
  remainder : ℚ
  deriving DecidableEq, Repr

structure RestDebt where
  relation : RelationId
  obligor : PartyId
  creditor : PartyId
  amount : Amount
  eligible : Bool
  claimEvidence : SourceRef
  eligibilityEvidence : Option SourceRef
  deriving DecidableEq, Repr

structure State where
  debt : DebtRecord
  formations : List RelationId
  judgment : Judgment
  procedure : Procedure
  claim : Applicable
  executionEligible : Bool
  initialDebt : ℚ
  newDebt : ℚ
  accrual : ℚ
  allocated : ℚ
  writtenOff : ℚ
  paid : ℚ
  surplus : ℚ
  cash : List CashEvent
  used : Finset PaymentId
  receipts : List Receipt
  rest : Option RestDebt
  refundCash : List CashEvent
  normHistory : List Temporal.VersionRecord
  env : Result Nat
  deriving DecidableEq, Repr

abbrev Handle := PostStateHandle State

def balance (s : State) : ℚ := s.debt.amount.value
def forms (s : State) (r : RelationId) : Bool := decide (r ∈ s.formations)

-- Absence of a formed relation is None, distinct from some zero.
def quantity (s : State) (r : RelationId) : Option ℚ :=
  if r = s.debt.relation ∧ r ∈ s.formations then some (balance s) else none

def Conserves (s : State) : Prop :=
  0 ≤ balance s ∧ 0 ≤ s.newDebt ∧ 0 ≤ s.accrual ∧ 0 ≤ s.allocated ∧
  0 ≤ s.writtenOff ∧ 0 ≤ s.paid ∧ 0 ≤ s.surplus ∧
  balance s = s.initialDebt + s.newDebt + s.accrual - s.allocated - s.writtenOff ∧
  s.paid = s.allocated + s.surplus

def performance (s : State) (p : PaymentPayload) : State :=
  let k := min p.amount.value (balance s)
  { s with
    debt := { s.debt with amount := { s.debt.amount with value := balance s - k } }
    allocated := s.allocated + k
    paid := s.paid + p.amount.value
    surplus := s.surplus + (p.amount.value - k)
    cash := s.cash ++ [⟨p.cashId, p.source, p.payer, p.payee, p.amount⟩] }

theorem forms_preserved_by_performance (s : State) (p : PaymentPayload) (r : RelationId) :
    forms (performance s p) r = forms s r := rfl

theorem performance_metadata (s : State) (p : PaymentPayload) :
    (performance s p).debt.relation = s.debt.relation ∧
    (performance s p).debt.obligor = s.debt.obligor ∧
    (performance s p).debt.creditor = s.debt.creditor ∧
    (performance s p).debt.amount.tag = s.debt.amount.tag ∧
    (performance s p).debt.metadata = s.debt.metadata ∧
    (performance s p).judgment = s.judgment ∧
    (performance s p).procedure = s.procedure ∧
    (performance s p).claim = s.claim := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem u09_1_quantity_conservation (s : State) (p : PaymentPayload)
    (hs : Conserves s) (hp : 0 ≤ p.amount.value) : Conserves (performance s p) := by
  rcases hs with ⟨hd, hn, ha, hk, hw, hc, hu, he, hf⟩
  have hkn : 0 ≤ min p.amount.value (balance s) := le_min hp hd
  have hkp := min_le_left p.amount.value (balance s)
  have hkd := min_le_right p.amount.value (balance s)
  dsimp [Conserves, performance, balance] at *
  refine ⟨?_, hn, ha, ?_, hw, ?_, ?_, ?_, ?_⟩ <;> linarith

def afterPayments (s : State) : List PaymentPayload → State
  | [] => s
  | p :: ps => afterPayments (performance s p) ps

theorem u09_1_continuous_consume (s : State) (ps : List PaymentPayload)
    (hs : Conserves s) (hp : ∀ p ∈ ps, 0 ≤ p.amount.value) :
    Conserves (afterPayments s ps) := by
  induction ps generalizing s with
  | nil => exact hs
  | cons p ps ih =>
      exact ih (performance s p) (u09_1_quantity_conservation s p hs (hp p (by simp)))
        (fun p h => hp p (by simp [h]))

def accrue (s : State) (a : ℚ) : State :=
  { s with debt := { s.debt with amount := { s.debt.amount with value := balance s + a } }
           accrual := s.accrual + a }

def addPrincipal (s : State) (n : ℚ) : State :=
  { s with debt := { s.debt with amount := { s.debt.amount with value := balance s + n } }
           newDebt := s.newDebt + n }

def writeOff (s : State) (w : ℚ) : State :=
  { s with debt := { s.debt with amount := { s.debt.amount with value := balance s - w } }
           writtenOff := s.writtenOff + w }

theorem accrue_conserves (s : State) (a : ℚ) (hs : Conserves s) (ha : 0 ≤ a) :
    Conserves (accrue s a) := by
  rcases hs with ⟨hd, hn, hi, hk, hw, hc, hu, he, hf⟩
  dsimp [Conserves, accrue, balance] at *
  refine ⟨?_, hn, ?_, hk, hw, hc, hu, ?_, hf⟩ <;> linarith

theorem principal_conserves (s : State) (n : ℚ) (hs : Conserves s) (hnn : 0 ≤ n) :
    Conserves (addPrincipal s n) := by
  rcases hs with ⟨hd, hn, hi, hk, hw, hc, hu, he, hf⟩
  dsimp [Conserves, addPrincipal, balance] at *
  refine ⟨?_, ?_, hi, hk, hw, hc, hu, ?_, hf⟩ <;> linarith

theorem writeoff_conserves (s : State) (w : ℚ) (hs : Conserves s)
    (hw : 0 ≤ w) (hwd : w ≤ balance s) : Conserves (writeOff s w) := by
  rcases hs with ⟨hd, hn, hi, hk, hW, hc, hu, he, hf⟩
  dsimp [Conserves, writeOff, balance] at *
  refine ⟨?_, hn, hi, hk, ?_, hc, hu, ?_, hf⟩ <;> linarith

theorem u09_3_accrual_not_cash (s : State) (a : ℚ) :
    (accrue s a).cash = s.cash ∧ (accrue s a).paid = s.paid ∧
    (accrue s a).refundCash = s.refundCash := ⟨rfl, rfl, rfl⟩

theorem u09_3_general_allocation {I : Type} (items : Finset I) (d k : I → ℚ) (p : ℚ)
    (legalBounds : ∀ i ∈ items, 0 ≤ k i ∧ k i ≤ d i)
    (budget : ∑ i ∈ items, k i ≤ p) :
    (∀ i ∈ items, 0 ≤ d i - k i ∧ d i - k i ≤ d i) ∧
    (∑ i ∈ items, d i) = (∑ i ∈ items, (d i - k i)) + ∑ i ∈ items, k i ∧
    0 ≤ p - ∑ i ∈ items, k i := by
  refine ⟨?_, ?_, sub_nonneg.mpr budget⟩
  · intro i hi
    obtain ⟨hn, hb⟩ := legalBounds i hi
    constructor <;> linarith
  · rw [Finset.sum_sub_distrib]
    ring

theorem weak_allocation_not_maximal :
    (0 : ℚ) ≤ 0 ∧ 0 ≤ 1 ∧ (0 : ℚ) ≤ 1 ∧ min (1 - 0 : ℚ) (1 - 0) ≠ 0 := by norm_num

theorem u09_2_cash_conservation {A : Type} [Fintype A]
    (events : List (A → ℚ)) (balanced : ∀ e ∈ events, ∑ a, e a = 0) :
    (events.map (fun e => ∑ a, e a)).sum = 0 := by
  induction events with
  | nil => simp
  | cons e es ih =>
      have he := balanced e (by simp)
      have hs := ih (fun e h => balanced e (by simp [h]))
      simp [he, hs]

def lookupReceipt (s : State) (key : PaymentId) : Option Receipt :=
  s.receipts.find? (fun r => r.key == key)

def validationError (prev previous_output_ref : Handle) (req : PaymentRequest)
    (permission : Bool) : Option Error :=
  if previous_output_ref ≠ prev then some .prestateRequired
  else if req.interpretedPayment ≠ some req.key then some .identityUnknown
  else if req.applicable = .unknown then some .applicabilityUnknown
  else if req.applicable = .no then some .notApplicable
  else if req.payload.caseId ≠ prev.gamma.caseId ∨
      req.payload.caseRevision ≠ prev.gamma.caseRevision ∨
      req.payload.relation ≠ prev.state.debt.relation ∨
      req.payload.payer ≠ prev.state.debt.obligor ∨
      req.payload.payee ≠ prev.state.debt.creditor then some .scopeMismatch
  else if req.payload.amount.tag ≠ prev.state.debt.amount.tag then some .unitBindingMissing
  else if req.payload.normVersion ≠ prev.gamma.normVersion then some .scopeMismatch
  else if permission = false then some .authorityUnresolved
  else if req.payload.amount.value < 0 then some .unsupported
  else if req.key ∈ prev.state.used then some .duplicateCash
  else if prev.state.cash.any (fun e => e.id == req.payload.cashId) then some .duplicateCash
  else none

def commitPayment (prev : Handle) (req : PaymentRequest) : Receipt × Handle :=
  let k := min req.payload.amount.value (balance prev.state)
  let s := performance prev.state req.payload
  let receipt : Receipt := ⟨req.key, req.payload, prev.revision, prev.revision + 1,
    balance prev.state, balance s, k, req.payload.amount.value - k⟩
  (receipt, ⟨prev.gamma, prev.revision + 1,
    { s with used := insert req.key s.used, receipts := s.receipts ++ [receipt] }⟩)

inductive Submission where
  | submit | rejectedBeforeSubmit | unknownCommit
  deriving DecidableEq, Repr

inductive Outcome where
  | committed (receipt : Receipt) (post : Handle)
  | replay (receipt : Receipt)
  | rejectedNoCommit (attempt : AttemptId) (reason : Error)
  | conflict (registered requested : PaymentPayload)
  | unknownCommit (key : PaymentId) (attempt : AttemptId)
  deriving DecidableEq, Repr

def Outcome.post (before : Handle) : Outcome → Option Handle
  | .committed _ h => some h
  | .unknownCommit _ _ => none
  | _ => some before

-- Resolve stable business identity before admitting a genuinely new effect.
-- UnknownCommit is client knowledge; it carries no definite server poststate.
def consume_ext (prev previous_output_ref : Handle) (req : PaymentRequest)
    (permission : Bool) (submission : Submission) : Outcome :=
  match lookupReceipt prev.state req.key with
  | some receipt =>
      if receipt.payload = req.payload then .replay receipt
      else .conflict receipt.payload req.payload
  | none =>
      match submission with
      | .unknownCommit => .unknownCommit req.key req.attempt
      | .rejectedBeforeSubmit => .rejectedNoCommit req.attempt .unsupported
      | .submit =>
          match validationError prev previous_output_ref req permission with
          | some reason => .rejectedNoCommit req.attempt reason
          | none =>
              let committed := commitPayment prev req
              .committed committed.1 committed.2

theorem u09_writeU_on_committed_applicable (prev : Handle) (req : PaymentRequest) :
    req.key ∈ (commitPayment prev req).2.state.used ∧
    (commitPayment prev req).2.state.used = insert req.key prev.state.used := by
  simp [commitPayment, performance]

theorem u09_committed_path (prev previous_output_ref : Handle) (req : PaymentRequest)
    (permission : Bool) (fresh : lookupReceipt prev.state req.key = none)
    (ready : validationError prev previous_output_ref req permission = none) :
    consume_ext prev previous_output_ref req permission .submit =
      .committed (commitPayment prev req).1 (commitPayment prev req).2 := by
  simp [consume_ext, fresh, ready]

theorem u09_zero_pay_yes_in_U (prev : Handle) (req : PaymentRequest)
    (zero : req.payload.amount.value = 0) (hd : 0 ≤ balance prev.state) :
    req.key ∈ (commitPayment prev req).2.state.used ∧
    balance (commitPayment prev req).2.state = balance prev.state := by
  constructor
  · exact (u09_writeU_on_committed_applicable prev req).1
  · simp [commitPayment, performance, balance, zero, min_eq_left hd]

theorem u09_unknown_has_no_certain_poststate (prev previous_output_ref : Handle)
    (req : PaymentRequest) (permission : Bool)
    (fresh : lookupReceipt prev.state req.key = none) :
    (consume_ext prev previous_output_ref req permission .unknownCommit).post prev = none := by
  simp [consume_ext, fresh, Outcome.post]

theorem u09_unknown_keeps_key (prev previous_output_ref : Handle) (req : PaymentRequest)
    (permission : Bool) (fresh : lookupReceipt prev.state req.key = none) :
    consume_ext prev previous_output_ref req permission .unknownCommit =
      .unknownCommit req.key req.attempt := by simp [consume_ext, fresh]

theorem u09_replay_stable (prev previous_output_ref : Handle) (req : PaymentRequest)
    (permission : Bool) (submission : Submission) (r : Receipt)
    (registered : lookupReceipt prev.state req.key = some r) (same : r.payload = req.payload) :
    consume_ext prev previous_output_ref req permission submission = .replay r := by
  simp [consume_ext, registered, same]

structure RestClaimWitness where
  relation : RelationId
  obligor : PartyId
  creditor : PartyId
  amount : Amount
  evidence : SourceRef
  deriving DecidableEq, Repr

def RestClaim (s : State) (w : RestClaimWitness) : Result State :=
  if w.relation = s.debt.relation ∨ w.relation ∈ s.formations ∨ w.amount.value < 0
    then .rejected .scopeMismatch
  else .known { s with rest := some ⟨w.relation, w.obligor, w.creditor, w.amount,
      false, w.evidence, none⟩, formations := s.formations ++ [w.relation] }

def ExecEligible (s : State) (relation : RelationId) (evidence : SourceRef) : Result State :=
  match s.rest with
  | none => .unknown .missingEvidence
  | some r =>
      if r.relation = relation then
        .known { s with rest := some { r with eligible := true, eligibilityEvidence := some evidence } }
      else .rejected .scopeMismatch

def RestPay (s : State) (event : CashEvent) : Result State :=
  match s.rest with
  | none => .rejected .prematureCash
  | some r =>
      if r.eligible = false then .rejected .autoFullRefund
      else if event.amount.tag ≠ r.amount.tag ∨ event.payer ≠ r.obligor ∨
        event.payee ≠ r.creditor ∨ event.amount.value < 0 then .rejected .unitBindingMissing
      else if (s.cash ++ s.refundCash).any (fun e => e.id == event.id) then .rejected .duplicateCash
      else .known { s with
        rest := some { r with amount := { r.amount with value :=
          r.amount.value - min event.amount.value r.amount.value } }
        refundCash := s.refundCash ++ [event] }

theorem rest_claim_no_cash (s : State) (w : RestClaimWitness) (after : State)
    (h : RestClaim s w = .known after) : after.cash = s.cash ∧ after.refundCash = s.refundCash := by
  unfold RestClaim at h
  split at h
  · cases h
  · cases h
    exact ⟨rfl, rfl⟩

theorem rest_eligibility_no_cash (s : State) (r : RelationId) (e : SourceRef) (after : State)
    (h : ExecEligible s r e = .known after) :
    after.cash = s.cash ∧ after.refundCash = s.refundCash ∧ after.used = s.used := by
  unfold ExecEligible at h
  split at h
  · cases h
  · split at h
    · cases h
      exact ⟨rfl, rfl, rfl⟩
    · cases h

def auditPerformanceLayers (before after : State) : Result Unit :=
  if after.formations = before.formations ∧ after.claim = before.claim ∧
    after.executionEligible = before.executionEligible ∧ after.procedure = before.procedure then
    .known () else .rejected .layerCollapse

-- Reuse the old general list theorem, not its fixed Master example.
theorem baseline_afterStream (ps : List ℚ)
    (items : List JurisLean.Seams.UnifiedQuantLedger.LedgerItem)
    (nonneg : ∀ it ∈ items, 0 ≤ it.amount) (payments : ∀ p ∈ ps, 0 ≤ p) :
    JurisLean.Seams.UnifiedQuantLedger.outstanding
      (JurisLean.Seams.UnifiedQuantLedger.afterStream ps items) =
      max (JurisLean.Seams.UnifiedQuantLedger.outstanding items - ps.sum) 0 :=
  JurisLean.Seams.UnifiedQuantLedger.outstanding_afterStream ps items nonneg payments

end JurisLean.Candidates.Final20261021.Ledger
