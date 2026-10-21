import JurisLean.Candidates.Final20261021.Ledger

namespace JurisLean.Candidates.Final20261021.Trace

def Invariant (h : Ledger.Handle) : Prop :=
  Ledger.Conserves h.state ∧
  Ledger.CashConsistent h.state ∧
  h.state.env = Temporal.proposed_applicability h.gamma h.state.normHistory ∧
  Ledger.ReceiptCoherent h.state

-- Complete concrete opening state of section 14, not an assumed I(S0).
def initial (g : Gamma) (debt : DebtRecord) : Ledger.Handle :=
  ⟨g, 0, { debt := debt, formations := [debt.relation], judgment := .insufficient,
    procedure := .open, claim := .unknown, executionEligible := false,
    initialDebt := debt.amount.value, newDebt := 0, accrual := 0, allocated := 0,
    writtenOff := 0, paid := 0, surplus := 0, cash := [], used := ∅,
    receipts := [], rest := none, refundCash := [], normHistory := [],
    env := Temporal.proposed_applicability g [] }⟩

theorem initial_invariant (g : Gamma) (debt : DebtRecord) (nonneg : 0 ≤ debt.amount.value) :
    Invariant (initial g debt) := by
  constructor
  · simpa [initial, Ledger.Conserves, Ledger.balance] using nonneg
  · refine ⟨rfl, rfl, ?_⟩
    simp [Ledger.ReceiptCoherent, initial]

def correctStep (s0 : Ledger.Handle) (p1 p2 : PaymentRequest)
    (permit1 permit2 : Bool) (mode2 : Ledger.Submission) : Ledger.Outcome × Option Ledger.Outcome :=
  let out1 := Ledger.consume_ext s0 s0 p1 permit1 .submit
  match out1 with
  | .committed _ previous_output_ref =>
      (out1, some (Ledger.consume_ext previous_output_ref previous_output_ref p2 permit2 mode2))
  | _ => (out1, none)

-- Context is part of the actual state. Refresh publishes history, Gamma, env
-- together; neither a stale environment nor a replay of S0 is a trace edge.
inductive Step : Ledger.Handle → Ledger.Handle → Prop where
  | pay (h : Ledger.Handle) (req : PaymentRequest) (p : Bool)
      (newKey : Ledger.lookupReceipt h.state req.key = none)
      (ready : Ledger.validationError h h req p = none)
      (amount : 0 ≤ req.payload.amount.value) : Step h (Ledger.commitPayment h req).2
  | accrue (h : Ledger.Handle) (a : ℚ) (ha : 0 ≤ a) :
      Step h { h with revision := h.revision + 1, state := Ledger.accrue h.state a }
  | principal (h : Ledger.Handle) (n : ℚ) (hn : 0 ≤ n) :
      Step h { h with revision := h.revision + 1, state := Ledger.addPrincipal h.state n }
  | writeoff (h : Ledger.Handle) (w : ℚ) (hw : 0 ≤ w) (bound : w ≤ Ledger.balance h.state) :
      Step h { h with revision := h.revision + 1, state := Ledger.writeOff h.state w }
  | refresh (h : Ledger.Handle) (g : Gamma) (e : Temporal.VersionRecord)
      (grants : List Authorization.Grant) (actor : PartyId)
      (authorized : Authorization.authorized grants h.gamma actor 1 e.version
        (.document e.version) none (some g) = true)
      (sameCase : g.caseId = h.gamma.caseId) :
      Step h ⟨g, h.revision + 1, { h.state with normHistory := h.state.normHistory ++ [e],
        env := Temporal.proposed_applicability g (h.state.normHistory ++ [e]) }⟩
  | reject (h : Ledger.Handle) : Step h h

theorem step_preserves {s t : Ledger.Handle} (step : Step s t) (hs : Invariant s) :
    Invariant t := by
  rcases hs with ⟨numeric, cash, fresh, coherent⟩
  cases step with
  | pay h req p hk ready amount =>
      exact ⟨Ledger.u09_1_quantity_conservation h.state req.payload numeric amount,
        Ledger.performance_cash_consistent h.state req.payload cash, fresh,
        Ledger.commit_receipt_coherent h req coherent (Ledger.ready_requires_unused h h req p ready)⟩
  | accrue h a ha => exact ⟨Ledger.accrue_conserves h.state a numeric ha, cash, fresh, coherent⟩
  | principal h n hn => exact ⟨Ledger.principal_conserves h.state n numeric hn, cash, fresh, coherent⟩
  | writeoff h w hw bound => exact ⟨Ledger.writeoff_conserves h.state w numeric hw bound, cash, fresh, coherent⟩
  | refresh h g e grants actor auth same => exact ⟨numeric, cash, rfl, coherent⟩
  | reject h => exact ⟨numeric, cash, fresh, coherent⟩

-- The actual executor, rather than an independently asserted pay transition,
-- supplies every premise of the abstract step constructor.
theorem u10_2_committed_executor_is_step (before previous_output_ref : Ledger.Handle)
    (req : PaymentRequest) (permission : Bool) (mode : Ledger.Submission)
    (receipt : Ledger.Receipt) (after : Ledger.Handle)
    (committed : Ledger.consume_ext before previous_output_ref req permission mode =
      .committed receipt after) : Step before after := by
  obtain ⟨_, fresh, ready, _, post⟩ :=
    Ledger.consume_committed_origin before previous_output_ref req permission mode receipt after committed
  have same := Ledger.ready_requires_actual_output before previous_output_ref req permission ready
  subst previous_output_ref
  rw [post]
  exact .pay before req permission fresh ready
    (Ledger.ready_requires_identity_and_applicability before before req permission ready).2.2

theorem u10_2_known_executor_post_preserves (before previous_output_ref : Ledger.Handle)
    (req : PaymentRequest) (permission : Bool) (mode : Ledger.Submission)
    (after : Ledger.Handle) (initial : Invariant before)
    (reported : (Ledger.consume_ext before previous_output_ref req permission mode).post before = some after) :
    Invariant after := by
  have frame (same : some before = some after) : Invariant after := by
    cases same
    exact initial
  cases execution : Ledger.consume_ext before previous_output_ref req permission mode with
  | committed receipt post =>
      have same : post = after := by simpa [execution, Ledger.Outcome.post] using reported
      subst after
      exact step_preserves
        (u10_2_committed_executor_is_step before previous_output_ref req permission mode receipt post execution)
        initial
  | unknownCommit key attempt => simp [execution, Ledger.Outcome.post] at reported
  | replay receipt => exact frame (by simpa [execution, Ledger.Outcome.post] using reported)
  | rejectedNoCommit attempt reason => exact frame (by simpa [execution, Ledger.Outcome.post] using reported)
  | conflict registered requested => exact frame (by simpa [execution, Ledger.Outcome.post] using reported)
  | pending reason => exact frame (by simpa [execution, Ledger.Outcome.post] using reported)

inductive Path : Ledger.Handle → Ledger.Handle → Prop where
  | nil (h : Ledger.Handle) : Path h h
  | cons {s t u : Ledger.Handle} : Step s t → Path t u → Path s u

theorem used_monotone_step {s t : Ledger.Handle} (step : Step s t) :
    s.state.used ⊆ t.state.used := by
  cases step with
  | pay h req p hk ready amount =>
      intro key used
      change key ∈ insert req.key h.state.used
      exact Finset.mem_insert.mpr (Or.inr used)
  | accrue h a ha => exact fun _ used => used
  | principal h n hn => exact fun _ used => used
  | writeoff h w hw bound => exact fun _ used => used
  | refresh h g e grants actor auth same => exact fun _ used => used
  | reject h => exact fun _ used => used

theorem used_monotone_path {s t : Ledger.Handle} (path : Path s t) :
    s.state.used ⊆ t.state.used := by
  induction path with
  | nil h => exact fun _ used => used
  | cons step rest ih => exact fun _ used => ih (used_monotone_step step used)

theorem u09_1_actual_trace_at_most_once (s ref after later laterRef : Ledger.Handle)
    (req next : PaymentRequest) (permission permissionNext : Bool)
    (mode modeNext : Ledger.Submission) (receipt : Ledger.Receipt)
    (committed : Ledger.consume_ext s ref req permission mode = .committed receipt after)
    (intervening : Path after later) (sameKey : next.key = req.key) :
    ∀ r post, Ledger.consume_ext later laterRef next permissionNext modeNext ≠ .committed r post := by
  intro r post second
  have burned := (Ledger.consume_success_is_gated s ref req permission mode receipt after committed).2.2
  have stillUsed := used_monotone_path intervening burned
  obtain ⟨_, _, ready, _, _⟩ :=
    Ledger.consume_committed_origin later laterRef next permissionNext modeNext r post second
  have unused := Ledger.ready_requires_unused later laterRef next permissionNext ready
  rw [sameKey] at unused
  exact unused stillUsed

theorem u10_2_finite_trace_composition {s t : Ledger.Handle} (path : Path s t)
    (initial : Invariant s) : Invariant t := by
  induction path with
  | nil h => exact initial
  | cons step rest ih => exact ih (step_preserves step initial)

theorem from_concrete_initial (g : Gamma) (debt : DebtRecord)
    (nonneg : 0 ≤ debt.amount.value) (final : Ledger.Handle)
    (path : Path (initial g debt) final) : Invariant final :=
  u10_2_finite_trace_composition path (initial_invariant g debt nonneg)

end JurisLean.Candidates.Final20261021.Trace
