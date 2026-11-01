import JurisLean.Candidates.U06_1OriginalCashIdentityInstances20261101
import JurisLean.Candidates.U06_2EquilibriumTransfer20261030
import Mathlib

/-!
Original 06.7 L137 finite witness. The terminal cash events have explicit
identities, payer/payee fields, real gross amounts, and payment dates. The
synthetic tag and common valuation context are fixed inputs; a payment date is
not a valuation date. The second-round discount is a preference applied to
cash, not a second cash fee. This connects actual Q1 event accounting to the
existing W4 abstract terminal utility without changing that ledger.
-/

noncomputable section
open JurisLean.Candidates.Final20261021
open JurisLean.Candidates.U06_1OriginalCashIdentityInstances20261101
open JurisLean.Candidates.U06_2EquilibriumTransfer20261030
open scoped BigOperators

namespace JurisLean.Candidates.U06_7OriginalCashBargainBridge20261102

local instance : DecidableEq RealCashEvent := Classical.decEq _

def terminalCode : BargainTerminal → Nat
  | .accept0 first => if first then 1 else 0
  | .accept1 first second => 2 + (if first then 2 else 0) + (if second then 1 else 0)
  | .failure first second => 6 + (if first then 2 else 0) + (if second then 1 else 0)

def terminalEventId (z : BargainTerminal) (recipient : Bool) : EventId :=
  ⟨2 * terminalCode z + (if recipient then 1 else 0)⟩

def terminalParty (recipient : Bool) : PartyId := if recipient then ⟨2⟩ else ⟨1⟩

/-- Local synthetic marker only; it is not an evidence reference or T113 input. -/
def bargainSyntheticSource : SourceRef := ⟨6707⟩

def terminalGross (z : BargainTerminal) (recipient : Bool) : ℝ :=
  ((if recipient then (bargainLedger z).grossB else (bargainLedger z).grossA : ℚ) : ℝ)

def terminalPaymentDate : BargainTerminal → LawDate
  | .accept0 _ => ⟨0⟩
  | .accept1 _ _ => ⟨1⟩
  | .failure _ _ => ⟨1⟩

def terminalCashEvent (z : BargainTerminal) (recipient : Bool) : RealCashEvent :=
  ⟨terminalEventId z recipient, bargainSyntheticSource, ⟨0⟩,
    terminalParty recipient, terminalGross z recipient, cashTag, terminalPaymentDate z⟩

def terminalCashEvents : BargainTerminal → List RealCashEvent
  | .accept0 first => [terminalCashEvent (.accept0 first) false,
      terminalCashEvent (.accept0 first) true]
  | .accept1 first second => [terminalCashEvent (.accept1 first second) false,
      terminalCashEvent (.accept1 first second) true]
  | .failure _ _ => []

def terminalCashSet (z : BargainTerminal) : Finset RealCashEvent :=
  (terminalCashEvents z).toFinset

def terminalCashNet (z : BargainTerminal) (recipient : Bool) : ℝ :=
  netCash (terminalCashSet z) (terminalParty recipient)

def terminalCashPreference (z : BargainTerminal) (recipient : Bool) : ℝ :=
  match z with
  | .accept0 _ => terminalCashNet z recipient
  | .accept1 _ _ => (bParamsDemo.delta : ℝ) * terminalCashNet z recipient
  | .failure _ _ => 0

/-- The two terminal payments are distinct by their event IDs. Consequently
`terminalCashSet` meets the unique-ID premise of Q1's event-sum reindexing API. -/
theorem terminal_cash_event_ids_nodup (z : BargainTerminal) :
    ((terminalCashEvents z).map RealCashEvent.id).Nodup := by
  cases z with
  | accept0 first => cases first <;>
      norm_num [terminalCashEvents, terminalCashEvent, terminalEventId, terminalCode]
  | accept1 first second => cases first <;> cases second <;>
      norm_num [terminalCashEvents, terminalCashEvent, terminalEventId, terminalCode]
  | failure first second => cases first <;> cases second <;>
      norm_num [terminalCashEvents, terminalCashEvent, terminalEventId, terminalCode]

/-- The event list records exactly the gross W4 transfer to each recipient. -/
theorem terminal_cash_net_is_gross (z : BargainTerminal) (recipient : Bool) :
    terminalCashNet z recipient = terminalGross z recipient := by
  cases z with
  | accept0 first =>
      cases first <;> cases recipient <;>
        norm_num [terminalCashNet, terminalCashSet, terminalCashEvents,
          terminalCashEvent, terminalEventId, terminalCode, terminalParty,
          terminalGross, terminalPaymentDate, netCash, cashFlow, bargainLedger,
          bargainX, bargainY, bParamsDemo, cashTag]
  | accept1 first second =>
      cases first <;> cases second <;> cases recipient <;>
        norm_num [terminalCashNet, terminalCashSet, terminalCashEvents,
          terminalCashEvent, terminalEventId, terminalCode, terminalParty,
          terminalGross, terminalPaymentDate, netCash, cashFlow, bargainLedger,
          bargainX, bargainY, bParamsDemo, cashTag]
  | failure first second =>
      cases first <;> cases second <;> cases recipient <;>
        norm_num [terminalCashNet, terminalCashSet, terminalCashEvents,
          terminalCashEvent, terminalEventId, terminalCode, terminalParty,
          terminalGross, terminalPaymentDate, netCash, cashFlow, bargainLedger,
          bargainX, bargainY, bParamsDemo, cashTag]

/-- The cash ledger plus the existing time preference yields the W4 abstract
terminal utility. Delayed utility loss is derived from `delta`; it is not a
cash event or an assumed monetary charge. -/
theorem terminal_cash_utility_matches_w4 (z : BargainTerminal) (recipient : Bool) :
    terminalCashPreference z recipient = bargainAbstractTerminalPay z recipient := by
  calc
    terminalCashPreference z recipient = bargainLedgerPay z recipient := by
      cases z with
      | accept0 first =>
          cases first <;> cases recipient <;>
            norm_num [terminalCashPreference, terminal_cash_net_is_gross,
              terminalGross, bargainLedgerPay, bargainLedger, bargainX, bParamsDemo]
      | accept1 first second =>
          cases first <;> cases second <;> cases recipient <;>
            norm_num [terminalCashPreference, terminal_cash_net_is_gross,
              terminalGross, bargainLedgerPay, bargainLedger, bargainY, bParamsDemo,
              bargain_delay_loss_formula]
      | failure first second =>
          cases first <;> cases second <;> cases recipient <;>
            norm_num [terminalCashPreference, terminal_cash_net_is_gross,
              terminalGross, bargainLedgerPay, bargainLedger]
    _ = bargainAbstractTerminalPay z recipient := bargain_ledger_payoff_eq z recipient
end JurisLean.Candidates.U06_7OriginalCashBargainBridge20261102