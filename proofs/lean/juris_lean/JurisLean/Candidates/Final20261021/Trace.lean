import JurisLean.Candidates.Final20261021.Ledger

namespace JurisLean.Candidates.Final20261021.Trace

def Invariant (h : Ledger.Handle) : Prop :=
  Ledger.Conserves h.state ∧
  Ledger.CashConsistent h.state ∧
  h.state.env = Temporal.proposed_applicability h.gamma h.state.normHistory

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
  · exact ⟨rfl, rfl⟩

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
  rcases hs with ⟨numeric, cash, fresh⟩
  cases step with
  | pay h req p hk ready amount =>
      exact ⟨Ledger.u09_1_quantity_conservation h.state req.payload numeric amount,
        Ledger.performance_cash_consistent h.state req.payload cash, fresh⟩
  | accrue h a ha => exact ⟨Ledger.accrue_conserves h.state a numeric ha, cash, fresh⟩
  | principal h n hn => exact ⟨Ledger.principal_conserves h.state n numeric hn, cash, fresh⟩
  | writeoff h w hw bound => exact ⟨Ledger.writeoff_conserves h.state w numeric hw bound, cash, fresh⟩
  | refresh h g e grants actor auth same => exact ⟨numeric, cash, rfl⟩
  | reject h => exact ⟨numeric, cash, fresh⟩

inductive Path : Ledger.Handle → Ledger.Handle → Prop where
  | nil (h : Ledger.Handle) : Path h h
  | cons {s t u : Ledger.Handle} : Step s t → Path t u → Path s u

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
