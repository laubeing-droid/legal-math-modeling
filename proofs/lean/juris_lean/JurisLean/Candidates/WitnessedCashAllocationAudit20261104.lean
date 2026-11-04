import JurisLean.Candidates.Final20261021.Trace
import JurisLean.Seams.InstitutionalEffects

/-!
新增义务：仅连接冻结09.6 L179中任意给定合法k到同一实际State的quantity/cash后态，
并给出L181反例与L183分层frame边界；不扩张原题语义。
PREP_NOT_COMPILED / PARTIAL_09_6。这里的数值边界是外部Theta/适用事实给出的输入证据，
本稿只证明给定证据如何作用到同一个State；不定义法律默认、不证明现实现金发生或协议接受。
-/

namespace JurisLean.Candidates.WitnessedCashAllocationAudit20261104

open JurisLean.Candidates.Final20261021

/-- allocationPost把外部给定的k作用到同一State，现金事件仍来自同一p。 -/
def allocationPost (s : Ledger.State) (p : PaymentPayload) (k : ℚ) : Ledger.State :=
  { s with
    debt := { s.debt with amount := { s.debt.amount with value := Ledger.balance s - k } }
    allocated := s.allocated + k
    paid := s.paid + p.amount.value
    surplus := s.surplus + (p.amount.value - k)
    cash := s.cash ++ [⟨p.cashId, p.source, p.payer, p.payee, p.amount⟩] }

/-- 生产模型已有performance只是k=min这一实例，不表示任意Theta已被执行。 -/
theorem performance_is_min_allocation (s : Ledger.State) (p : PaymentPayload) :
    Ledger.performance s p = allocationPost s p (min p.amount.value (Ledger.balance s)) := rfl

/-- 对新构造的State，除数量/分配/付款/余额外，恰列出实际未改的记录字段。 -/
theorem allocationPost_record_frame (s : Ledger.State) (p : PaymentPayload) (k : ℚ) :
    (allocationPost s p k).formations = s.formations ∧
    (allocationPost s p k).debt.relation = s.debt.relation ∧
    (allocationPost s p k).debt.obligor = s.debt.obligor ∧
    (allocationPost s p k).debt.creditor = s.debt.creditor ∧
    (allocationPost s p k).debt.amount.tag = s.debt.amount.tag ∧
    (allocationPost s p k).debt.metadata = s.debt.metadata ∧
    (allocationPost s p k).executionEligible = s.executionEligible ∧
    (allocationPost s p k).judgment = s.judgment ∧
    (allocationPost s p k).procedure = s.procedure ∧
    (allocationPost s p k).claim = s.claim ∧
    (allocationPost s p k).initialDebt = s.initialDebt ∧
    (allocationPost s p k).newDebt = s.newDebt ∧
    (allocationPost s p k).accrual = s.accrual ∧
    (allocationPost s p k).writtenOff = s.writtenOff ∧
    (allocationPost s p k).used = s.used ∧
    (allocationPost s p k).receipts = s.receipts ∧
    (allocationPost s p k).rest = s.rest ∧
    (allocationPost s p k).refundCash = s.refundCash ∧
    (allocationPost s p k).normHistory = s.normHistory ∧
    (allocationPost s p k).env = s.env := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Cash consistency transfers conditionally by reusing the existing performance theorem. -/
theorem allocationPost_cash_consistent (s : Ledger.State) (p : PaymentPayload) (k : ℚ)
    (h : Ledger.CashConsistent s) : Ledger.CashConsistent (allocationPost s p k) := by
  have hp := Ledger.performance_cash_consistent s p h
  simpa [Ledger.CashConsistent, Ledger.cashTotal, allocationPost, Ledger.performance] using hp

/--
`hq` supplies the current quantity at r; `hkMin` records the externally supplied allocation k
within the local numeric bounds. This arithmetic update does not establish real cash occurrence,
legal recognition, or acceptance by the payment protocol; no postcondition is assumed.
-/
theorem arbitrary_k_same_state_update
    (s : Ledger.State) (p : PaymentPayload) (r : RelationId) (d k : ℚ)
    (hq : Ledger.quantity s r = some d)
    (hd : 0 ≤ d) (ha : 0 ≤ p.amount.value) (hk0 : 0 ≤ k)
    (hkMin : k ≤ min p.amount.value d) :
    (Ledger.quantity (allocationPost s p k) r = some (d - k) ∧
      (0 ≤ Ledger.balance (allocationPost s p k) ∧
        Ledger.balance s = Ledger.balance (allocationPost s p k) + k ∧
        0 ≤ p.amount.value - k) ∧
      ( (allocationPost s p k).allocated = s.allocated + k ∧
        (allocationPost s p k).paid = s.paid + p.amount.value ∧
        (allocationPost s p k).surplus = s.surplus + (p.amount.value - k) ∧
        Ledger.cashTotal (allocationPost s p k) = Ledger.cashTotal s + p.amount.value ∧
        (allocationPost s p k).cash = s.cash ++
          [⟨p.cashId, p.source, p.payer, p.payee, p.amount⟩] )) := by
  have hqFacts : r = s.debt.relation ∧ r ∈ s.formations ∧ Ledger.balance s = d := by
    unfold Ledger.quantity at hq
    by_cases hcond : r = s.debt.relation ∧ r ∈ s.formations
    · simp [hcond] at hq
      exact ⟨hcond.1, hcond.2, hq⟩
    · simp [hcond] at hq
  have hkDebt : k ≤ d := le_trans hkMin (min_le_right _ _)
  have hkPaid : k ≤ p.amount.value := le_trans hkMin (min_le_left _ _)
  have hgeneral := Ledger.u09_3_general_allocation
    (items := (Finset.univ : Finset Unit))
    (d := fun _ => d) (k := fun _ => k) (p := p.amount.value)
    (by
      intro i hi
      cases i
      exact ⟨hk0, hkDebt⟩)
    (by simpa using hkPaid)
  have hsingle := hgeneral.1 () (by simp)
  have hrem : 0 ≤ d - k := hsingle.1
  have hdecomp : d = (d - k) + k := by simpa using hgeneral.2.1
  have hunused : 0 ≤ p.amount.value - k := by simpa using hgeneral.2.2
  have hpostBalance : Ledger.balance (allocationPost s p k) = d - k := by
    simp [Ledger.balance, allocationPost, hqFacts.2.2]
  have hpostQuantity : Ledger.quantity (allocationPost s p k) r = some (d - k) := by
    simp [Ledger.quantity, allocationPost, Ledger.balance, hqFacts.1,
      hqFacts.2.1, hqFacts.2.2]
  refine ⟨hpostQuantity, ?_, ?_⟩
  · constructor
    · rw [hpostBalance]
      exact hrem
    · constructor
      · rw [hqFacts.2.2, hpostBalance]
        exact hdecomp
      · exact hunused
  · exact ⟨rfl, rfl, rfl,
      by simp [Ledger.cashTotal, allocationPost, List.map_append, List.sum_append],
      rfl⟩

/-- Toy type-level input: zero debt with no formed relation, and one linked cash payload of 6. -/
def toyTag : AmountTag := ⟨"toy", "toy-unit", 0⟩
def toyZeroDebt (relation : RelationId) (obligor creditor : PartyId) (metadata : String) : DebtRecord :=
  ⟨relation, obligor, creditor, ⟨0, toyTag⟩, metadata⟩
def toyFourDebt (relation : RelationId) (obligor creditor : PartyId) (metadata : String) : DebtRecord :=
  ⟨relation, obligor, creditor, ⟨4, toyTag⟩, metadata⟩
def toyCashSix (g : Gamma) (relation : RelationId) (payer payee : PartyId)
    (source : SourceRef) (cashId : EventId) : PaymentPayload :=
  ⟨g.caseId, g.caseRevision, relation, payer, payee, ⟨6, toyTag⟩,
    source, cashId, g.normVersion, g.lawDate⟩
def unformedToyOpening (g : Gamma) (relation : RelationId) (obligor creditor : PartyId)
    (metadata : String) : Ledger.Handle :=
  let h := Trace.initial g (toyZeroDebt relation obligor creditor metadata)
  { h with state := { h.state with formations := [] } }
def unformedToyPost (g : Gamma) (relation : RelationId) (obligor creditor : PartyId)
    (metadata : String) (source : SourceRef) (cashId : EventId) : Ledger.State :=
  Ledger.performance (unformedToyOpening g relation obligor creditor metadata).state
    (toyCashSix g relation obligor creditor source cashId)
def formedToyPost (g : Gamma) (relation : RelationId) (obligor creditor : PartyId)
    (metadata : String) (source : SourceRef) (cashId : EventId) : Ledger.State :=
  Ledger.performance (Trace.initial g (toyFourDebt relation obligor creditor metadata)).state
    (toyCashSix g relation obligor creditor source cashId)
def toyCashEvent (g : Gamma) (relation : RelationId) (obligor creditor : PartyId)
    (source : SourceRef) (cashId : EventId) : CashEvent :=
  ⟨cashId, source, obligor, creditor, (toyCashSix g relation obligor creditor source cashId).amount⟩

/-- L181: the same raw State has no formed quantity while its given cash event totals six. -/
theorem unformed_option_none_cash_six
    (g : Gamma) (relation : RelationId) (obligor creditor : PartyId)
    (metadata : String) (source : SourceRef) (cashId : EventId) :
    let pre := (unformedToyOpening g relation obligor creditor metadata).state
    let post := unformedToyPost g relation obligor creditor metadata source cashId
    Ledger.quantity pre relation = none ∧ Ledger.quantity post relation = none ∧
    Ledger.balance post = 0 ∧ post.allocated = 0 ∧ post.paid = 6 ∧
    Ledger.cashTotal pre = 0 ∧ Ledger.cashTotal post = 6 ∧ post ≠ pre ∧
    post.cash = [toyCashEvent g relation obligor creditor source cashId] ∧
    post.newDebt = 0 ∧ post.rest = none ∧ post.refundCash = [] ∧
    Ledger.Conserves post ∧ Ledger.CashConsistent post := by
  dsimp
  let h0 := Trace.initial g (toyZeroDebt relation obligor creditor metadata)
  have h0inv : Trace.Invariant h0 :=
    Trace.initial_invariant g (toyZeroDebt relation obligor creditor metadata) (by simp [toyZeroDebt, toyTag])
  have hpreInv : Trace.Invariant (unformedToyOpening g relation obligor creditor metadata) := by
    rcases h0inv with ⟨hc, hcash, henv, hreceipt⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa [unformedToyOpening, Trace.initial, toyZeroDebt, toyTag,
        Ledger.Conserves, Ledger.balance] using hc
    · simpa [unformedToyOpening, Trace.initial, toyZeroDebt, toyTag,
        Ledger.CashConsistent, Ledger.cashTotal] using hcash
    · simpa [unformedToyOpening, Trace.initial, toyZeroDebt, toyTag] using henv
    · simpa [unformedToyOpening, Trace.initial, toyZeroDebt, toyTag,
        Ledger.ReceiptCoherent] using hreceipt
  have hcPost : Ledger.Conserves
      (unformedToyPost g relation obligor creditor metadata source cashId) :=
    Ledger.u09_1_quantity_conservation _ _ hpreInv.1 (by norm_num [toyCashSix])
  have hcashPost : Ledger.CashConsistent
      (unformedToyPost g relation obligor creditor metadata source cashId) :=
    Ledger.performance_cash_consistent _ _ hpreInv.2.1
  have hpreCash : Ledger.cashTotal
      (unformedToyOpening g relation obligor creditor metadata).state = 0 := by
    simp [unformedToyOpening, Trace.initial, toyZeroDebt, toyTag, Ledger.cashTotal]
  have hpostCash : Ledger.cashTotal
      (unformedToyPost g relation obligor creditor metadata source cashId) = 6 := by
    norm_num [unformedToyPost, unformedToyOpening, toyCashSix, toyZeroDebt,
      toyTag, Trace.initial, Ledger.performance, Ledger.balance, Ledger.cashTotal]
  have hpostNePre : unformedToyPost g relation obligor creditor metadata source cashId ≠
      (unformedToyOpening g relation obligor creditor metadata).state := by
    intro h
    have htot := congrArg Ledger.cashTotal h
    rw [hpostCash, hpreCash] at htot
    norm_num at htot
  refine ⟨?_, ?_, ?_, ?_, ?_, hpreCash, hpostCash, hpostNePre,
    ?_, ?_, ?_, ?_, hcPost, hcashPost⟩ <;>
    simp [unformedToyOpening, unformedToyPost, toyCashSix, toyZeroDebt, toyTag,
      Trace.initial, Ledger.performance, Ledger.quantity, Ledger.balance,
      Ledger.cashTotal, toyCashEvent]

/-- L181: formed debt 4 with the same cash input 6 allocates 4 and preserves cash 6. -/
theorem formed_four_cash_six_allocates_four
    (g : Gamma) (relation : RelationId) (obligor creditor : PartyId)
    (metadata : String) (source : SourceRef) (cashId : EventId) :
    Ledger.quantity (formedToyPost g relation obligor creditor metadata source cashId) relation = some 0 ∧
    Ledger.balance (formedToyPost g relation obligor creditor metadata source cashId) = 0 ∧
    (formedToyPost g relation obligor creditor metadata source cashId).allocated = 4 ∧
    (formedToyPost g relation obligor creditor metadata source cashId).paid = 6 ∧
    (formedToyPost g relation obligor creditor metadata source cashId).surplus = 2 ∧
    Ledger.cashTotal (formedToyPost g relation obligor creditor metadata source cashId) = 6 ∧
    (formedToyPost g relation obligor creditor metadata source cashId).cash =
      [toyCashEvent g relation obligor creditor source cashId] := by
  norm_num [formedToyPost, toyCashSix, toyFourDebt, toyTag, Trace.initial,
      Ledger.performance, Ledger.quantity, Ledger.balance, Ledger.cashTotal, toyCashEvent]

/-
Scope boundary: `JurisLean.Seams.InstitutionalEffects.next_performance_is_identity`
returns identity only for its relation `Ledger Rel`. Existing `Final20261021.Ledger.forms_preserved_by_performance`
and `performance_metadata` are reusable for the min instance. Neither implies full State identity,
that cash did not occur, or that all external legal rights/eligibility remain unchanged.
-/

end JurisLean.Candidates.WitnessedCashAllocationAudit20261104

#check JurisLean.Candidates.WitnessedCashAllocationAudit20261104.allocationPost
#check JurisLean.Candidates.Final20261021.Ledger.quantity
#check JurisLean.Candidates.WitnessedCashAllocationAudit20261104.performance_is_min_allocation
#print axioms JurisLean.Candidates.WitnessedCashAllocationAudit20261104.performance_is_min_allocation
#check JurisLean.Candidates.WitnessedCashAllocationAudit20261104.allocationPost_record_frame
#print axioms JurisLean.Candidates.WitnessedCashAllocationAudit20261104.allocationPost_record_frame
#check JurisLean.Candidates.WitnessedCashAllocationAudit20261104.allocationPost_cash_consistent
#print axioms JurisLean.Candidates.WitnessedCashAllocationAudit20261104.allocationPost_cash_consistent
#check JurisLean.Candidates.WitnessedCashAllocationAudit20261104.arbitrary_k_same_state_update
#print axioms JurisLean.Candidates.WitnessedCashAllocationAudit20261104.arbitrary_k_same_state_update
#check JurisLean.Candidates.WitnessedCashAllocationAudit20261104.unformed_option_none_cash_six
#print axioms JurisLean.Candidates.WitnessedCashAllocationAudit20261104.unformed_option_none_cash_six
#check JurisLean.Candidates.WitnessedCashAllocationAudit20261104.formed_four_cash_six_allocates_four
#print axioms JurisLean.Candidates.WitnessedCashAllocationAudit20261104.formed_four_cash_six_allocates_four
