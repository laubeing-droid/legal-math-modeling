import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.List.OfFn
import JurisLean.Candidates.Final20261021.Acceptance
import JurisLean.Candidates.SingleDebtStreamAudit20261103

namespace JurisLean.Candidates.ParametricAllocationAudit20261104

open JurisLean.Candidates.Final20261021
open JurisLean.Seams.UnifiedQuantLedger
open scoped BigOperators

abbrev AllocationRowBinding (items : List LedgerItem) :=
  Fin items.length → DebtRecord → LedgerItem → Prop

abbrev AllocationPaymentIdentity :=
  DebtRecord → PaymentPayload → Prop

/- L165: applicable theta receives the actual state, debt, payment, time, version, and facts. -/
abbrev AllocationThetaRule :=
  List LedgerItem → DebtRecord → PaymentPayload → LawDate → Nat → List SourceRef → Prop

structure AllocationCertificate
    (items : List LedgerItem)
    (payment : PaymentPayload)
    (rowBinding : AllocationRowBinding items)
    (paymentIdentity : AllocationPaymentIdentity)
    (theta : AllocationThetaRule)
    (time : LawDate)
    (version : Nat) where
  sourceDebt : Fin items.length → DebtRecord
  facts : Fin items.length → List SourceRef
  allocation : Fin items.length → ℚ
  externalRowIdentity : ∀ i,
    rowBinding i (sourceDebt i) (items.get i)
  sourceAmountAndUnit : ∀ i,
    (sourceDebt i).amount.value = (items.get i).amount ∧
      (sourceDebt i).amount.tag = payment.amount.tag
  paymentIdentityEvidence : ∀ i,
    0 < allocation i → paymentIdentity (sourceDebt i) payment
  thetaEvidence : ∀ i,
    0 < allocation i → theta items (sourceDebt i) payment time version (facts i)
  bounds : ∀ i, 0 ≤ allocation i ∧ allocation i ≤ (items.get i).amount
  budget : (∑ i, allocation i) ≤ payment.amount.value

abbrev AllocTheta
    (items : List LedgerItem)
    (payment : PaymentPayload)
    (rowBinding : AllocationRowBinding items)
    (paymentIdentity : AllocationPaymentIdentity)
    (theta : AllocationThetaRule)
    (time : LawDate)
    (version : Nat) :=
  Option (AllocationCertificate items payment rowBinding paymentIdentity theta time version)

def applyAllocationVector
    (items : List LedgerItem)
    (allocation : Fin items.length → ℚ) : List LedgerItem :=
  List.ofFn (fun i : Fin items.length =>
    let item := items.get i
    { item with amount := item.amount - allocation i })

def allocatedRow
    (items : List LedgerItem)
    (allocation : Fin items.length → ℚ)
    (i : Fin items.length) : LedgerItem :=
  (applyAllocationVector items allocation)[i.val]'(by
    simpa [applyAllocationVector] using i.isLt)

def applyAllocTheta
    {items : List LedgerItem}
    {payment : PaymentPayload}
    {rowBinding : AllocationRowBinding items}
    {paymentIdentity : AllocationPaymentIdentity}
    {theta : AllocationThetaRule}
    {time : LawDate}
    {version : Nat}
    (output : AllocTheta items payment rowBinding paymentIdentity theta time version) :
    Option (List LedgerItem) :=
  output.map fun certificate => applyAllocationVector items certificate.allocation

/- L167: all time, rule, and fact inputs are explicit; no formula is selected here. -/
structure AccrualTerms where
  base : Amount
  rateParameters : List ℚ
  feeParameters : List Amount
  timeQuantity : ℚ
  timeUnit : String

abbrev AccrualFormula := Ledger.State → LawDate → LawDate → AccrualTerms → Amount
abbrev AccrualRounding := ℚ → ℚ
abbrev AccrualEffectiveness := Ledger.State → LawDate → LawDate → AccrualTerms → Prop
abbrev AccrualFactCondition :=
  Ledger.State → LawDate → LawDate → AccrualTerms → AccrualFormula → AccrualRounding → Prop

structure AccrualCertificate
    (state : Ledger.State)
    (t0 t1 : LawDate)
    (formula : AccrualFormula)
    (rounding : AccrualRounding)
    (effective : AccrualEffectiveness)
    (factsValid : AccrualFactCondition) where
  terms : AccrualTerms
  resultUnitMatches : (formula state t0 t1 terms).tag = state.debt.amount.tag
  effectiveEvidence : effective state t0 t1 terms
  factsEvidence : factsValid state t0 t1 terms formula rounding

abbrev AccrueTheta
    (state : Ledger.State)
    (t0 t1 : LawDate)
    (formula : AccrualFormula)
    (rounding : AccrualRounding)
    (effective : AccrualEffectiveness)
    (factsValid : AccrualFactCondition) :=
  Option (AccrualCertificate state t0 t1 formula rounding effective factsValid)

def applyAccrueTheta
    {state : Ledger.State}
    {t0 t1 : LawDate}
    {formula : AccrualFormula}
    {rounding : AccrualRounding}
    {effective : AccrualEffectiveness}
    {factsValid : AccrualFactCondition}
    (output : AccrueTheta state t0 t1 formula rounding effective factsValid) :
    Option Ledger.State :=
  output.map fun certificate =>
    Ledger.accrue state (rounding (formula state t0 t1 certificate.terms).value)

theorem certified_allocation_updates_actual_list
    {items : List LedgerItem}
    {payment : PaymentPayload}
    {rowBinding : AllocationRowBinding items}
    {paymentIdentity : AllocationPaymentIdentity}
    {theta : AllocationThetaRule}
    {time : LawDate}
    {version : Nat}
    (certificate : AllocationCertificate items payment rowBinding paymentIdentity theta time version) :
    applyAllocTheta (some certificate) =
        some (applyAllocationVector items certificate.allocation) ∧
      (applyAllocationVector items certificate.allocation).length = items.length ∧
      (∀ i : Fin items.length,
        JurisLean.Candidates.SingleDebtStream20261103.sameItemFrameLe
          (allocatedRow items certificate.allocation i) (items.get i)) ∧
      (∀ i : Fin items.length,
        0 ≤ (allocatedRow items certificate.allocation i).amount) ∧
      outstanding items = outstanding (applyAllocationVector items certificate.allocation) +
          ∑ i : Fin items.length, certificate.allocation i ∧
      0 ≤ payment.amount.value - ∑ i : Fin items.length, certificate.allocation i ∧
      payment.amount.value =
        (∑ i : Fin items.length, certificate.allocation i) +
          (payment.amount.value - ∑ i : Fin items.length, certificate.allocation i) ∧
      (∀ i : Fin items.length,
        (certificate.sourceDebt i).amount.value = (items.get i).amount ∧
          (certificate.sourceDebt i).amount.tag = payment.amount.tag) := by
  have core := Ledger.u09_3_general_allocation
    (Finset.univ : Finset (Fin items.length))
    (fun j => (items.get j).amount) certificate.allocation payment.amount.value
    (by
      intro j _
      exact certificate.bounds j)
    certificate.budget
  have preSum : outstanding items = ∑ i : Fin items.length, (items.get i).amount := by
    calc
      outstanding items = (items.map LedgerItem.amount).sum := rfl
      _ = ((List.ofFn items.get).map LedgerItem.amount).sum := by rw [List.ofFn_get]
      _ = ∑ i : Fin items.length, (items.get i).amount := by
        simp only [List.map_ofFn, List.sum_ofFn, Function.comp_apply]
  have postSum :
      outstanding (applyAllocationVector items certificate.allocation) =
        ∑ i : Fin items.length, ((items.get i).amount - certificate.allocation i) := by
    simp [outstanding, liAmounts, applyAllocationVector, List.map_ofFn,
      List.sum_ofFn, Function.comp_apply]
  have lengthEq : (applyAllocationVector items certificate.allocation).length = items.length := by
    simp [applyAllocationVector]
  have fullFrame : ∀ i : Fin items.length,
      JurisLean.Candidates.SingleDebtStream20261103.sameItemFrameLe
        (allocatedRow items certificate.allocation i) (items.get i) := by
    intro i
    simp only [allocatedRow, applyAllocationVector, List.getElem_ofFn,
      JurisLean.Candidates.SingleDebtStream20261103.sameItemFrameLe]
    obtain ⟨halloc, _⟩ := certificate.bounds i
    exact ⟨rfl, rfl, rfl, rfl, rfl, by linarith⟩
  have postNonnegative : ∀ i : Fin items.length,
      0 ≤ (allocatedRow items certificate.allocation i).amount := by
    intro i
    obtain ⟨_, hbound⟩ := certificate.bounds i
    simp only [allocatedRow, applyAllocationVector, List.getElem_ofFn]
    linarith
  rcases core with ⟨_, sumDecomposition, unusedNonnegative⟩
  have listDecomposition :
      outstanding items = outstanding (applyAllocationVector items certificate.allocation) +
          ∑ i : Fin items.length, certificate.allocation i := by
    rw [postSum, preSum]
    simpa using sumDecomposition
  refine ⟨rfl, lengthEq, fullFrame, postNonnegative, listDecomposition,
    unusedNonnegative, ?_, ?_⟩
  · ring
  · exact certificate.sourceAmountAndUnit

theorem accrue_theta_output_is_actual_accrual
    {state : Ledger.State}
    {t0 t1 : LawDate}
    {formula : AccrualFormula}
    {rounding : AccrualRounding}
    {effective : AccrualEffectiveness}
    {factsValid : AccrualFactCondition}
    (output : AccrueTheta state t0 t1 formula rounding effective factsValid) :
    applyAccrueTheta output =
      output.map fun certificate =>
        Ledger.accrue state (rounding (formula state t0 t1 certificate.terms).value) := rfl

theorem actual_accrual_balance_and_non_cash (state : Ledger.State) (amount : ℚ) :
    Ledger.balance (Ledger.accrue state amount) = Ledger.balance state + amount ∧
      (Ledger.accrue state amount).cash = state.cash ∧
      (Ledger.accrue state amount).paid = state.paid ∧
      (Ledger.accrue state amount).refundCash = state.refundCash ∧
      (Ledger.accrue state amount).debt.amount.tag = state.debt.amount.tag := by
  exact ⟨rfl, (Ledger.u09_3_accrual_not_cash state amount).1,
    (Ledger.u09_3_accrual_not_cash state amount).2.1,
    (Ledger.u09_3_accrual_not_cash state amount).2.2, rfl⟩

theorem synthetic_accrual_increases_balance_without_payment :
    Ledger.balance (Ledger.accrue Acceptance.opening.state 1) = 11 ∧
      (Ledger.accrue Acceptance.opening.state 1).cash = Acceptance.opening.state.cash ∧
      (Ledger.accrue Acceptance.opening.state 1).paid = Acceptance.opening.state.paid ∧
      (Ledger.accrue Acceptance.opening.state 1).refundCash =
        Acceptance.opening.state.refundCash := by
  refine ⟨?_, (Ledger.u09_3_accrual_not_cash Acceptance.opening.state 1).1,
    (Ledger.u09_3_accrual_not_cash Acceptance.opening.state 1).2.1,
    (Ledger.u09_3_accrual_not_cash Acceptance.opening.state 1).2.2⟩
  norm_num [Ledger.balance, Ledger.accrue, Acceptance.opening, Acceptance.debt,
    Acceptance.tag, JurisLean.Candidates.Final20261021.Trace.initial]

/- L163: compare actual greedy afterPay on the fixed list and its reversal. -/
def twoEqualItems : List LedgerItem :=
  [ ⟨1, .principal, .contractStip, 10, .claimed, 5⟩
  , ⟨2, .principal, .contractStip, 20, .claimed, 5⟩ ]

def forwardAfterPay : List LedgerItem := afterPay 5 twoEqualItems
def reversedAfterPay : List LedgerItem := afterPay 5 twoEqualItems.reverse

theorem l163_equal_total_does_not_fix_identity :
    forwardAfterPay.map (fun item => (item.ident, item.amount)) = [(1, 0), (2, 5)] ∧
      reversedAfterPay.map (fun item => (item.ident, item.amount)) = [(2, 0), (1, 5)] ∧
      outstanding forwardAfterPay = 5 ∧ outstanding reversedAfterPay = 5 := by
  norm_num [forwardAfterPay, reversedAfterPay, twoEqualItems, afterPay,
    outstanding, liAmounts]

end JurisLean.Candidates.ParametricAllocationAudit20261104

#check JurisLean.Candidates.ParametricAllocationAudit20261104.AllocTheta
#check JurisLean.Candidates.ParametricAllocationAudit20261104.AccrueTheta
#check JurisLean.Candidates.ParametricAllocationAudit20261104.certified_allocation_updates_actual_list
#check JurisLean.Candidates.ParametricAllocationAudit20261104.accrue_theta_output_is_actual_accrual
#check JurisLean.Candidates.ParametricAllocationAudit20261104.actual_accrual_balance_and_non_cash
#check JurisLean.Candidates.ParametricAllocationAudit20261104.synthetic_accrual_increases_balance_without_payment
#check JurisLean.Candidates.ParametricAllocationAudit20261104.l163_equal_total_does_not_fix_identity
#print axioms JurisLean.Candidates.ParametricAllocationAudit20261104.certified_allocation_updates_actual_list
#print axioms JurisLean.Candidates.ParametricAllocationAudit20261104.accrue_theta_output_is_actual_accrual
#print axioms JurisLean.Candidates.ParametricAllocationAudit20261104.actual_accrual_balance_and_non_cash
#print axioms JurisLean.Candidates.ParametricAllocationAudit20261104.synthetic_accrual_increases_balance_without_payment
#print axioms JurisLean.Candidates.ParametricAllocationAudit20261104.l163_equal_total_does_not_fix_identity
#check JurisLean.Candidates.Final20261021.Ledger.u09_3_general_allocation
#check JurisLean.Candidates.Final20261021.Ledger.u09_3_accrual_not_cash
#check JurisLean.Candidates.SingleDebtStream20261103.afterPay_preserves_full_frame_and_pointwise_order
#check JurisLean.Seams.UnifiedQuantLedger.allocsOf_sum_add_remaining
#check JurisLean.Seams.UnifiedQuantLedger.allocsOf_sum_eq_min
#check JurisLean.Seams.UnifiedQuantLedger.outstanding_afterPay
#check JurisLean.Seams.UnifiedQuantLedger.afterPay_amounts_nonneg
#print axioms JurisLean.Candidates.Final20261021.Ledger.u09_3_general_allocation
#print axioms JurisLean.Candidates.Final20261021.Ledger.u09_3_accrual_not_cash
#print axioms JurisLean.Candidates.SingleDebtStream20261103.afterPay_preserves_full_frame_and_pointwise_order
#print axioms JurisLean.Seams.UnifiedQuantLedger.allocsOf_sum_add_remaining
#print axioms JurisLean.Seams.UnifiedQuantLedger.allocsOf_sum_eq_min
#print axioms JurisLean.Seams.UnifiedQuantLedger.outstanding_afterPay
#print axioms JurisLean.Seams.UnifiedQuantLedger.afterPay_amounts_nonneg
