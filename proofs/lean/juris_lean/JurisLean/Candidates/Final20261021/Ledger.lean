import JurisLean.Candidates.Final20261021.Interfaces
import JurisLean.Candidates.Final20261021.Temporal
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
  deriving DecidableEq

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

def cashTotal (s : State) : ℚ := (s.cash.map (fun e => e.amount.value)).sum
def CashConsistent (s : State) : Prop := cashTotal s = s.paid

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

theorem performance_cash_consistent (s : State) (p : PaymentPayload)
    (h : CashConsistent s) : CashConsistent (performance s p) := by
  simpa [CashConsistent, cashTotal, performance, List.map_append, List.sum_append] using
    congrArg (fun q : ℚ => q + p.amount.value) h

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

def cashVector {A : Type} (events : List (A → ℚ)) (a : A) : ℚ :=
  (events.map (fun e => e a)).sum

theorem u09_2_cash_by_account {A : Type} [Fintype A] (events : List (A → ℚ))
    (balanced : ∀ e ∈ events, ∑ a, e a = 0) : ∑ a, cashVector events a = 0 := by
  induction events with
  | nil => simp [cashVector]
  | cons e es ih =>
      have he := balanced e (by simp)
      have hs := ih (fun e h => balanced e (by simp [h]))
      change (∑ a, (e a + cashVector es a)) = 0
      rw [Finset.sum_add_distrib, he, hs, add_zero]

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
      req.payload.payee ≠ prev.state.debt.creditor ∨
      req.payload.factDate ≠ prev.gamma.lawDate then some .scopeMismatch
  else if req.payload.amount.tag ≠ prev.state.debt.amount.tag then some .unitBindingMissing
  else if req.payload.normVersion ≠ prev.gamma.normVersion then some .scopeMismatch
  else if prev.state.env ≠ .known prev.gamma.normVersion then some .scopeMismatch
  else if prev.state.debt.relation ∉ prev.state.formations then some .notApplicable
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

def ReceiptArithmetic (r : Receipt) : Prop :=
  r.afterRevision = r.beforeRevision + 1 ∧
  r.beforeDebt = r.afterDebt + r.allocated ∧
  r.payload.amount.value = r.allocated + r.remainder

-- This is an independently checkable state invariant. Historical receipts are
-- checked against their own transitions, not the current aggregate balance.
def ReceiptCoherent (s : State) : Prop :=
  (∀ key, key ∈ s.used ↔ ∃ r ∈ s.receipts, r.key = key) ∧
  (∀ r ∈ s.receipts, ReceiptArithmetic r) ∧
  (∀ r ∈ s.receipts, ∀ t ∈ s.receipts, r.key = t.key → r = t) ∧
  (∀ r ∈ s.receipts,
    (⟨r.payload.cashId, r.payload.source, r.payload.payer,
      r.payload.payee, r.payload.amount⟩ : CashEvent) ∈ s.cash)

theorem committed_receipt_arithmetic (prev : Handle) (req : PaymentRequest) :
    ReceiptArithmetic (commitPayment prev req).1 := by
  refine ⟨rfl, ?_, ?_⟩ <;> dsimp [commitPayment, performance, balance] <;> ring

theorem commit_receipt_coherent (prev : Handle) (req : PaymentRequest)
    (coherent : ReceiptCoherent prev.state) (unused : req.key ∉ prev.state.used) :
    ReceiptCoherent (commitPayment prev req).2.state := by
  rcases coherent with ⟨keys, arithmetic, unique, backed⟩
  let receipt := (commitPayment prev req).1
  have receiptKey : receipt.key = req.key := rfl
  have fresh : ∀ r ∈ prev.state.receipts, r.key ≠ req.key := by
    intro r hr same
    exact unused ((keys req.key).mpr ⟨r, hr, same⟩)
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro key
    change key ∈ insert req.key prev.state.used ↔
      ∃ r ∈ prev.state.receipts ++ [receipt], r.key = key
    constructor
    · intro used
      rcases Finset.mem_insert.mp used with same | old
      · exact ⟨receipt, List.mem_append.mpr (Or.inr (by simp)), receiptKey.trans same.symm⟩
      · obtain ⟨r, hr, hk⟩ := (keys key).mp old
        exact ⟨r, List.mem_append.mpr (Or.inl hr), hk⟩
    · rintro ⟨r, hr, hk⟩
      rcases List.mem_append.mp hr with old | new
      · exact Finset.mem_insert.mpr (Or.inr ((keys key).mpr ⟨r, old, hk⟩))
      · have same : r = receipt := List.mem_singleton.mp new
        subst r
        exact Finset.mem_insert.mpr (Or.inl (hk.symm.trans receiptKey))
  · intro r hr
    change r ∈ prev.state.receipts ++ [receipt] at hr
    rcases List.mem_append.mp hr with old | new
    · exact arithmetic r old
    · have same : r = receipt := List.mem_singleton.mp new
      subst r
      exact committed_receipt_arithmetic prev req
  · intro r hr t ht sameKey
    change r ∈ prev.state.receipts ++ [receipt] at hr
    change t ∈ prev.state.receipts ++ [receipt] at ht
    rcases List.mem_append.mp hr with oldR | newR <;>
      rcases List.mem_append.mp ht with oldT | newT
    · exact unique r oldR t oldT sameKey
    · have ht' : t = receipt := List.mem_singleton.mp newT
      exact False.elim (fresh r oldR (sameKey.trans ((congrArg Receipt.key ht').trans receiptKey)))
    · have hr' : r = receipt := List.mem_singleton.mp newR
      exact False.elim (fresh t oldT (sameKey.symm.trans ((congrArg Receipt.key hr').trans receiptKey)))
    · exact (List.mem_singleton.mp newR).trans (List.mem_singleton.mp newT).symm
  · intro r hr
    change r ∈ prev.state.receipts ++ [receipt] at hr
    change (⟨r.payload.cashId, r.payload.source, r.payload.payer,
      r.payload.payee, r.payload.amount⟩ : CashEvent) ∈ prev.state.cash ++
      [⟨req.payload.cashId, req.payload.source, req.payload.payer,
        req.payload.payee, req.payload.amount⟩]
    rcases List.mem_append.mp hr with old | new
    · exact List.mem_append.mpr (Or.inl (backed r old))
    · have same : r = receipt := List.mem_singleton.mp new
      subst r
      exact List.mem_append.mpr (Or.inr (by simp [receipt, commitPayment]))

inductive Submission where
  | submit | rejectedBeforeSubmit | unknownCommit
  deriving DecidableEq, Repr

inductive Outcome where
  | committed (receipt : Receipt) (post : Handle)
  | replay (receipt : Receipt)
  | rejectedNoCommit (attempt : AttemptId) (reason : Error)
  | conflict (registered requested : PaymentPayload)
  | unknownCommit (key : PaymentId) (attempt : AttemptId)
  | pending (reason : Error)
  deriving DecidableEq

def Outcome.post (before : Handle) : Outcome → Option Handle
  | .committed _ h => some h
  | .unknownCommit _ _ => none
  | _ => some before

-- Acknowledged U is not a claim about the unobserved server state.
def Outcome.acknowledgedUsed (before : Handle) (outcome : Outcome) : Finset PaymentId :=
  match outcome.post before with | some h => h.state.used | none => before.state.used

theorem noncommit_does_not_write_U (before : Handle) (outcome : Outcome)
    (noncommit : ∀ receipt post, outcome ≠ .committed receipt post) :
    outcome.acknowledgedUsed before = before.state.used := by
  cases outcome with
  | committed receipt post => exact False.elim (noncommit receipt post rfl)
  | replay receipt => rfl
  | rejectedNoCommit attempt reason => rfl
  | conflict registered requested => rfl
  | unknownCommit key attempt => rfl
  | pending reason => rfl

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
          | some .identityUnknown => .pending .identityUnknown
          | some .applicabilityUnknown => .pending .applicabilityUnknown
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
  · change balance prev.state - min req.payload.amount.value (balance prev.state) = balance prev.state
    rw [zero, min_eq_left hd, sub_zero]

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

theorem guard_none_iff (p : Prop) [Decidable p] (error : Error) (next : Option Error) :
    (if p then some error else next) = none ↔ ¬p ∧ next = none := by
  by_cases hp : p
  · rw [if_pos hp]
    constructor
    · intro impossible
      cases impossible
    · rintro ⟨notp, _⟩
      exact False.elim (notp hp)
  · rw [if_neg hp]
    exact ⟨fun h => ⟨hp, h⟩, fun h => h.2⟩

theorem validation_none_fields (prev previous_output_ref : Handle)
    (req : PaymentRequest) (permission : Bool)
    (ready : validationError prev previous_output_ref req permission = none) :
    previous_output_ref = prev ∧ req.interpretedPayment = some req.key ∧
      req.applicable = .yes ∧ 0 ≤ req.payload.amount.value ∧ req.key ∉ prev.state.used := by
  unfold validationError at ready
  simp only [guard_none_iff] at ready
  rcases ready with ⟨reference, identity, notUnknown, notNo, scope, tag, norm,
    environment, formed, authorized, nonnegative, unused, cash, done⟩
  have yes : req.applicable = .yes := by
    cases ha : req.applicable with
    | yes => rfl
    | no => exact False.elim (notNo ha)
    | unknown => exact False.elim (notUnknown ha)
  exact ⟨not_ne_iff.mp reference, not_ne_iff.mp identity, yes,
    le_of_not_gt nonnegative, unused⟩

theorem ready_requires_identity_and_applicability (prev previous_output_ref : Handle)
    (req : PaymentRequest) (permission : Bool)
    (ready : validationError prev previous_output_ref req permission = none) :
    req.applicable = .yes ∧ req.interpretedPayment = some req.key ∧
    0 ≤ req.payload.amount.value := by
  have fields := validation_none_fields prev previous_output_ref req permission ready
  exact ⟨fields.2.2.1, fields.2.1, fields.2.2.2.1⟩

theorem ready_requires_unused (prev previous_output_ref : Handle)
    (req : PaymentRequest) (permission : Bool)
    (ready : validationError prev previous_output_ref req permission = none) :
    req.key ∉ prev.state.used := by
  exact (validation_none_fields prev previous_output_ref req permission ready).2.2.2.2

theorem ready_requires_actual_output (prev previous_output_ref : Handle)
    (req : PaymentRequest) (permission : Bool)
    (ready : validationError prev previous_output_ref req permission = none) :
    previous_output_ref = prev := by
  exact (validation_none_fields prev previous_output_ref req permission ready).1

theorem consume_committed_origin (prev previous_output_ref : Handle)
    (req : PaymentRequest) (permission : Bool) (submission : Submission)
    (r : Receipt) (post : Handle)
    (success : consume_ext prev previous_output_ref req permission submission = .committed r post) :
    submission = .submit ∧ lookupReceipt prev.state req.key = none ∧
      validationError prev previous_output_ref req permission = none ∧
      r = (commitPayment prev req).1 ∧ post = (commitPayment prev req).2 := by
  cases hs : lookupReceipt prev.state req.key with
  | some old =>
      by_cases same : old.payload = req.payload <;>
        simp [consume_ext, hs, same] at success
  | none =>
      cases submission with
      | unknownCommit => simp [consume_ext, hs] at success
      | rejectedBeforeSubmit => simp [consume_ext, hs] at success
      | submit =>
          cases he : validationError prev previous_output_ref req permission with
          | some e => cases e <;> simp [consume_ext, hs, he] at success
          | none =>
              simp only [consume_ext, hs, he] at success
              cases success
              exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem consume_committed_receipts (prev previous_output_ref : Handle)
    (req : PaymentRequest) (permission : Bool) (submission : Submission)
    (r : Receipt) (post : Handle) (coherent : ReceiptCoherent prev.state)
    (success : consume_ext prev previous_output_ref req permission submission = .committed r post) :
    ReceiptCoherent post.state ∧ ReceiptArithmetic r := by
  obtain ⟨_, _, ready, hr, hp⟩ :=
    consume_committed_origin prev previous_output_ref req permission submission r post success
  rw [hp, hr]
  exact ⟨commit_receipt_coherent prev req coherent
    (ready_requires_unused prev previous_output_ref req permission ready),
    committed_receipt_arithmetic prev req⟩

theorem consume_success_is_gated (prev previous_output_ref : Handle)
    (req : PaymentRequest) (permission : Bool) (submission : Submission)
    (r : Receipt) (post : Handle)
    (success : consume_ext prev previous_output_ref req permission submission = .committed r post) :
    req.applicable = .yes ∧ req.interpretedPayment = some req.key ∧
      req.key ∈ post.state.used := by
  cases hs : lookupReceipt prev.state req.key with
  | some old =>
      by_cases same : old.payload = req.payload <;>
        simp [consume_ext, hs, same] at success
  | none =>
      cases submission with
      | unknownCommit => simp [consume_ext, hs] at success
      | rejectedBeforeSubmit => simp [consume_ext, hs] at success
      | submit =>
          cases he : validationError prev previous_output_ref req permission with
          | some e =>
              cases e <;> simp [consume_ext, hs, he] at success
          | none =>
              simp only [consume_ext, hs, he] at success
              cases success
              obtain ⟨app, identity, amount⟩ :=
                ready_requires_identity_and_applicability prev previous_output_ref req permission he
              exact ⟨app, identity, (u09_writeU_on_committed_applicable prev req).1⟩

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
        rest := some { r with
          amount := { r.amount with value := r.amount.value - min event.amount.value r.amount.value } },
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

-- Acceptance-side audits for proposed reports; these are not middleware.
def auditUnknownReport (before reported : State) : Result Unit :=
  if reported.used = before.used then .known () else .rejected .burnedByUnknown

def auditAccrualReport (before reported : State) : Result Unit :=
  if reported.cash = before.cash ∧ reported.refundCash = before.refundCash ∧
      reported.paid = before.paid then .known () else .rejected .accrualCashCollapse

def auditReceipt (receipt : Receipt) (reported : State) : Result Unit :=
  if balance reported = receipt.afterDebt ∧
      receipt.beforeDebt = receipt.afterDebt + receipt.allocated ∧
      receipt.payload.amount.value = receipt.allocated + receipt.remainder then .known ()
  else .rejected .stateConservationMismatch

def displayMinor (amount : Amount) (exponent : Nat) (rounding : Option (ℚ → Int)) : Result Int :=
  match rounding with
  | none => .unknown .roundingBasisMissing
  | some policy => .known (policy (amount.value * (10 : ℚ)^exponent))

-- Reuse the old general list theorem, not its fixed Master example.
theorem baseline_afterStream (ps : List ℚ)
    (items : List JurisLean.Seams.UnifiedQuantLedger.LedgerItem)
    (nonneg : ∀ it ∈ items, 0 ≤ it.amount) (payments : ∀ p ∈ ps, 0 ≤ p) :
    JurisLean.Seams.UnifiedQuantLedger.outstanding
      (JurisLean.Seams.UnifiedQuantLedger.afterStream ps items) =
      max (JurisLean.Seams.UnifiedQuantLedger.outstanding items - ps.sum) 0 :=
  JurisLean.Seams.UnifiedQuantLedger.outstanding_afterStream ps items nonneg payments

theorem balance_performance_clamp (s : State) (p : PaymentPayload) :
    balance (performance s p) = max (balance s - p.amount.value) 0 := by
  change balance s - min p.amount.value (balance s) = max (balance s - p.amount.value) 0
  rcases le_total p.amount.value (balance s) with hp | hd
  · rw [min_eq_left hp, max_eq_left (sub_nonneg.mpr hp)]
  · rw [min_eq_right hd, sub_self, max_eq_right (sub_nonpos.mpr hd)]

theorem u09_1_afterPayments_clamp (s : State) (ps : List PaymentPayload)
    (nonneg : 0 ≤ balance s) (payments : ∀ p ∈ ps, 0 ≤ p.amount.value) :
    balance (afterPayments s ps) = max (balance s - (ps.map fun p => p.amount.value).sum) 0 := by
  induction ps generalizing s with
  | nil => simp [afterPayments, max_eq_left nonneg]
  | cons p ps ih =>
      have tailNonneg : ∀ q ∈ ps, 0 ≤ q.amount.value :=
        fun q hq => payments q (List.mem_cons_of_mem _ hq)
      have mappedNonneg : ∀ q ∈ ps.map (fun p => p.amount.value), 0 ≤ q := by
        intro q hq
        obtain ⟨payload, hp, same⟩ := List.mem_map.mp hq
        rw [← same]
        exact tailNonneg payload hp
      have nextNonneg : 0 ≤ balance (performance s p) := by
        rw [balance_performance_clamp]
        exact le_max_right _ _
      change balance (afterPayments (performance s p) ps) = _
      rw [ih (performance s p) nextNonneg tailNonneg, balance_performance_clamp]
      simpa only [List.map_cons, List.sum_cons] using
        JurisLean.Seams.UnifiedQuantLedger.clamp_clamp (balance s) p.amount.value
          (ps.map fun p => p.amount.value).sum (List.sum_nonneg mappedNonneg)

-- The only bridge premise is the initial quantitative projection. The final
-- equality follows from two independent general list recursions; it is not
-- assumed for each transition, and it supplies no legal-interpretation claim.
theorem u09_1_scalar_vector_stream_refinement (s : State) (ps : List PaymentPayload)
    (items : List JurisLean.Seams.UnifiedQuantLedger.LedgerItem)
    (itemsNonneg : ∀ it ∈ items, 0 ≤ it.amount)
    (paymentsNonneg : ∀ p ∈ ps, 0 ≤ p.amount.value)
    (initialProjection : balance s = JurisLean.Seams.UnifiedQuantLedger.outstanding items) :
    balance (afterPayments s ps) = JurisLean.Seams.UnifiedQuantLedger.outstanding
      (JurisLean.Seams.UnifiedQuantLedger.afterStream (ps.map fun p => p.amount.value) items) := by
  have mappedNonneg : ∀ q ∈ ps.map (fun p => p.amount.value), 0 ≤ q := by
    intro q hq
    obtain ⟨p, hp, same⟩ := List.mem_map.mp hq
    rw [← same]
    exact paymentsNonneg p hp
  have nonneg : 0 ≤ balance s := by
    rw [initialProjection]
    exact JurisLean.Seams.UnifiedQuantLedger.outstanding_nonneg items itemsNonneg
  rw [u09_1_afterPayments_clamp s ps nonneg paymentsNonneg,
    baseline_afterStream _ items itemsNonneg mappedNonneg, initialProjection]

end JurisLean.Candidates.Final20261021.Ledger
