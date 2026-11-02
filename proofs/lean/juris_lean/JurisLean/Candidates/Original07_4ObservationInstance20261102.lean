import JurisLean.Candidates.SourceRepresentation20261027
import JurisLean.Candidates.Final20261021.Ledger

/-!
Original 07.4 instance: the existing generic representation results are kept
unchanged. This finite observation family reads a supplied accounting history
through the existing commit function; it does not choose an encoding or assert
that a production encoding is adequate or that requests are legally admissible.
-/

namespace JurisLean.Candidates.Original07_4ObservationInstance20261102

open JurisLean.Candidates.Final20261021
open JurisLean.Candidates.Final20261021.Ledger
open JurisLean.Candidates.SourceRepresentation20261027

abbrev ActualHistory := Ledger.Handle × List PaymentRequest

inductive ActualObservation where
  | identity
  | allocations
  | stageBalances
  | terminalBalance

abbrev PaymentIdentityObservation := PaymentId × PaymentPayload × Option ObjectId
abbrev IdentityObservation :=
  Gamma × Nat × RelationId × PartyId × PartyId × List PaymentIdentityObservation
abbrev ActualObservationValue :=
  Sum IdentityObservation (Sum (List Amount) (Sum (List Amount) Amount))

def commitTrace (initial : Ledger.Handle) : List PaymentRequest → List (Ledger.Receipt × Ledger.Handle)
  | [] => []
  | request :: rest =>
      let step := Ledger.commitPayment initial request
      step :: commitTrace step.2 rest

def stageBalances (history : ActualHistory) : List Amount :=
  history.1.state.debt.amount ::
    (commitTrace history.1 history.2).map (fun step => step.2.state.debt.amount)

def terminalBalance (history : ActualHistory) : Amount :=
  (stageBalances history).getLast (by simp [stageBalances])

def actualRead (mu : SourceRef → Option ObjectId) :
    ActualObservation → ActualHistory → ActualObservationValue
  | .identity, history =>
      .inl (history.1.gamma, history.1.revision,
        history.1.state.debt.relation, history.1.state.debt.obligor,
        history.1.state.debt.creditor,
        (commitTrace history.1 history.2).map
          (fun step => (step.1.key, step.1.payload, mu step.1.payload.source)))
  | .allocations, history =>
      .inr (.inl ((commitTrace history.1 history.2).map
        (fun step => ⟨step.1.allocated, step.1.payload.amount.tag⟩)))
  | .stageBalances, history => .inr (.inr (.inl (stageBalances history)))
  | .terminalBalance, history => .inr (.inr (.inr (terminalBalance history)))

/-- A concrete finite counterexample: a left inverse need not be a right inverse. -/
theorem unit_bool_retraction_not_reflection :
    ∃ e : Unit → Bool, ∃ d : Bool → Unit,
      (∀ u, d (e u) = u) ∧ ¬ Function.Surjective e ∧
        Function.comp e d ≠ (id : Bool → Bool) := by
  refine ⟨(fun _ : Unit => false), ?_⟩
  refine ⟨(fun _ : Bool => ()), ?_⟩
  constructor
  · intro u
    cases u
    rfl
  constructor
  · intro surj
    obtain ⟨u, hu⟩ := surj true
    have nohit :=
      JurisLean.Candidates.SourceRepresentation20261027.preservation_without_reflection |>.2.2
    exact nohit ⟨u, by simpa using hu⟩
  · intro rightInverse
    have atTrue := congrFun rightInverse true
    have impossible : false = true := by simpa [Function.comp] using atTrue
    cases impossible

end JurisLean.Candidates.Original07_4ObservationInstance20261102