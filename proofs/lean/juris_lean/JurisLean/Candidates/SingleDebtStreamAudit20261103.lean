import JurisLean.Seams.UnifiedQuantLedger
import JurisLean.Candidates.Final20261021.Ledger
import JurisLean.Candidates.Final20261021.Acceptance

/-!
Frozen original 09.1 lines 145 and 147, and 09.2 lines 151 and 153.
The results below connect the existing quantity recursion to the existing
single-debt ledger fixtures. Rationals do not encode units; equal units remain
an external precondition for interpreting these operations as one quantity.
The frame result concerns the stored non-amount LedgerItem fields only; it
does not assign legal meaning to ClaimStatus.
-/

namespace JurisLean.Candidates.SingleDebtStream20261103

open JurisLean.Candidates.Final20261021
open JurisLean.Candidates.Final20261021.Acceptance
open JurisLean.Candidates.Final20261021.Ledger
open JurisLean.Seams.UnifiedQuantLedger
open JurisLean.Seams.UnifiedQuantities

-- Frozen 09.1 L145: the one-step min decomposition, including the exact
-- positive-part identities and the complementary-slackness zero.
theorem min_payment_step_nine_laws (d p : ℚ) (hd : 0 ≤ d) (hp : 0 ≤ p) :
    (0 ≤ min p d ∧ min p d ≤ d) ∧
    min p d ≤ p ∧
    0 ≤ d - min p d ∧
    0 ≤ p - min p d ∧
    d = min p d + (d - min p d) ∧
    p = min p d + (p - min p d) ∧
    d - min p d = max (d - p) 0 ∧
    p - min p d = max (p - d) 0 ∧
    min (d - min p d) (p - min p d) = 0 := by
  refine ⟨⟨le_min hp hd, min_le_right p d⟩, min_le_left p d,
    sub_nonneg.mpr (min_le_right p d),
    sub_nonneg.mpr (min_le_left p d), by ring, by ring, ?_, ?_, ?_⟩
  · rcases le_total p d with hpd | hdp
    · rw [min_eq_left hpd, max_eq_left (sub_nonneg.mpr hpd)]
    · rw [min_eq_right hdp, max_eq_right (sub_nonpos.mpr hdp)]
      simp
  · rcases le_total p d with hpd | hdp
    · rw [min_eq_left hpd, max_eq_right (sub_nonpos.mpr hpd)]
      simp
    · rw [min_eq_right hdp, max_eq_left (sub_nonneg.mpr hdp)]
  · rcases le_total p d with hpd | hdp
    · rw [min_eq_left hpd]
      simp only [sub_self]
      exact min_eq_right (sub_nonneg.mpr hpd)
    · rw [min_eq_right hdp]
      simp only [sub_self]
      exact min_eq_left (sub_nonneg.mpr hdp)

def sameItemFrameLe (after before : LedgerItem) : Prop :=
  after.ident = before.ident ∧
  after.kind = before.kind ∧
  after.basis = before.basis ∧
  after.beneficiary = before.beneficiary ∧
  after.status = before.status ∧
  after.amount ≤ before.amount

-- Frozen 09.2 L151: this is the standard product order over the fixed
-- non-amount frame and the amount coordinate; nonnegativity is not built into
-- the relation, so it remains reflexive even on signed records.
theorem sameItemFrameLe_is_partial_order :
    (∀ item, sameItemFrameLe item item) ∧
    (∀ first second third,
      sameItemFrameLe first second → sameItemFrameLe second third →
        sameItemFrameLe first third) ∧
    (∀ first second,
      sameItemFrameLe first second → sameItemFrameLe second first → first = second) := by
  refine ⟨?_, ?_, ?_⟩
  · intro item
    exact ⟨rfl, rfl, rfl, rfl, rfl, le_rfl⟩
  · intro first second third h12 h23
    rcases h12 with ⟨id12, kind12, basis12, beneficiary12, status12, amount12⟩
    rcases h23 with ⟨id23, kind23, basis23, beneficiary23, status23, amount23⟩
    exact ⟨id12.trans id23, kind12.trans kind23, basis12.trans basis23,
      beneficiary12.trans beneficiary23, status12.trans status23,
      le_trans amount12 amount23⟩
  · intro first second h12 h21
    rcases h12 with ⟨id12, kind12, basis12, beneficiary12, status12, amount12⟩
    rcases h21 with ⟨id21, kind21, basis21, beneficiary21, status21, amount21⟩
    have amountEq : first.amount = second.amount := le_antisymm amount12 amount21
    cases first
    cases second
    simp_all [sameItemFrameLe, amountEq]

-- Frozen 09.1 L147 and 09.2 L151: on a fixed nonnegative item list, each
-- recursive payment keeps every record in position and can only lower amount.
theorem afterPay_preserves_full_frame_and_pointwise_order
    (items : List LedgerItem) (p : ℚ) (hp : 0 ≤ p)
    (hnn : ∀ item ∈ items, 0 ≤ item.amount) :
    List.Forall₂ sameItemFrameLe (afterPay p items) items := by
  induction items generalizing p with
  | nil => simp [afterPay]
  | cons item rest ih =>
      have headFrame :
          sameItemFrameLe
            { item with amount := item.amount - min p item.amount } item := by
        unfold sameItemFrameLe
        refine ⟨rfl, rfl, rfl, rfl, rfl, ?_⟩
        have hm : 0 ≤ min p item.amount := le_min hp (hnn item (by simp))
        linarith
      have hpTail : 0 ≤ p - min p item.amount :=
        sub_nonneg.mpr (min_le_left p item.amount)
      have hnnTail : ∀ x ∈ rest, 0 ≤ x.amount := by
        intro x hx
        exact hnn x (List.mem_cons_of_mem _ hx)
      simpa [afterPay] using
        (List.Forall₂.cons headFrame (ih (p - min p item.amount) hpTail hnnTail))

def negativePaymentItem : LedgerItem :=
  ⟨1, .principal, .contractStip, 2, .supported, 1⟩

-- Frozen 09.1 L145: without the nonnegative-payment premise, the existing
-- quantity recursion permits negative allocation and an increased debt.
theorem negative_payment_breaks_the_one_step_bounds :
    allocsOf (-1) [negativePaymentItem] = [-1] ∧
    afterPay (-1) [negativePaymentItem] =
      [{ negativePaymentItem with amount := 2 }] ∧
    outstanding (afterPay (-1) [negativePaymentItem]) = 2 := by
  norm_num [negativePaymentItem, allocsOf, afterPay, outstanding, liAmounts]

def tenUnitItem : LedgerItem :=
  ⟨1, .principal, .contractStip, 2, .supported, 10⟩

-- A projection of each existing recursive payment step; it does not run a
-- separate payment process.
def streamUnusedPayments : List ℚ → List LedgerItem → List ℚ
  | [], _ => []
  | p :: ps, items =>
      remainingAfter (liAmounts items) p ::
        streamUnusedPayments ps (afterPay p items)

-- Each recursive position is evaluated against the actual prefix ledger
-- reached by the existing afterPay recursion.
def finitePaymentStepLaw : List ℚ → List LedgerItem → Prop
  | [], _ => True
  | p :: ps, items =>
      ((allocsOf p items).sum = min p (outstanding items) ∧
        0 ≤ (allocsOf p items).sum ∧
        (allocsOf p items).sum ≤ outstanding items ∧
        (allocsOf p items).sum ≤ p ∧
        outstanding (afterPay p items) =
          outstanding items - (allocsOf p items).sum ∧
        0 ≤ outstanding (afterPay p items) ∧
        outstanding (afterPay p items) ≤ outstanding items ∧
        remainingAfter (liAmounts items) p = p - (allocsOf p items).sum ∧
        p = (allocsOf p items).sum + remainingAfter (liAmounts items) p ∧
        0 ≤ remainingAfter (liAmounts items) p) ∧
      finitePaymentStepLaw ps (afterPay p items)

-- Frozen 09.2 L151: for every finite nonnegative payment stream, each ai and
-- ui is computed at that stream position from the actual preceding ledger;
-- di is the next actual ledger balance.
theorem finite_payment_steps_follow_actual_prefix
    (ps : List ℚ) (items : List LedgerItem)
    (hnn : ∀ item ∈ items, 0 ≤ item.amount)
    (hps : ∀ p ∈ ps, 0 ≤ p) :
    finitePaymentStepLaw ps items := by
  induction ps generalizing items with
  | nil => simp [finitePaymentStepLaw]
  | cons p ps ih =>
      have hp : 0 ≤ p := hps p (by simp)
      have hpsTail : ∀ q ∈ ps, 0 ≤ q := by
        intro q hq
        exact hps q (List.mem_cons_of_mem _ hq)
      have hnnNext : ∀ item ∈ afterPay p items, 0 ≤ item.amount :=
        afterPay_amounts_nonneg items p
      have hdebt : 0 ≤ outstanding items := outstanding_nonneg items hnn
      have allocationEq :
          (allocsOf p items).sum = min p (outstanding items) :=
        allocsOf_sum_eq_min items p hp hnn
      have allocationNonneg : 0 ≤ (allocsOf p items).sum :=
        List.sum_nonneg (allocsOf_mem_nonneg items p hnn hp)
      have allocationLeDebt : (allocsOf p items).sum ≤ outstanding items := by
        rw [allocationEq]
        exact min_le_right p (outstanding items)
      have allocationLePayment : (allocsOf p items).sum ≤ p :=
        allocsOf_sum_le items p hp
      have stepLaws := min_payment_step_nine_laws
        (outstanding items) p hdebt hp
      rcases stepLaws with
        ⟨⟨_, _⟩, _, _, _, _, _, debtResidual, _, _⟩
      have debtAfter :
          outstanding (afterPay p items) =
            outstanding items - (allocsOf p items).sum := by
        calc
          outstanding (afterPay p items) =
              max (outstanding items - p) 0 :=
            outstanding_afterPay_clamp items p hnn hp
          _ = outstanding items - min p (outstanding items) := debtResidual.symm
          _ = outstanding items - (allocsOf p items).sum := by rw [allocationEq]
      have debtAfterNonneg : 0 ≤ outstanding (afterPay p items) := by
        rw [debtAfter]
        exact sub_nonneg.mpr allocationLeDebt
      have debtAfterLe :
          outstanding (afterPay p items) ≤ outstanding items := by
        rw [debtAfter]
        exact sub_le_self _ allocationNonneg
      have paymentSplit :
          (allocsOf p items).sum + remainingAfter (liAmounts items) p = p :=
        allocsOf_sum_add_remaining items p
      have unusedEq :
          remainingAfter (liAmounts items) p =
            p - (allocsOf p items).sum := by
        linarith
      have unusedNonneg : 0 ≤ remainingAfter (liAmounts items) p :=
        remainingAfter_nonneg (liAmounts items) p hp
      simp only [finitePaymentStepLaw]
      exact ⟨⟨allocationEq, allocationNonneg, allocationLeDebt,
        allocationLePayment, debtAfter, debtAfterNonneg, debtAfterLe,
        unusedEq, paymentSplit.symm, unusedNonneg⟩,
        ih (afterPay p items) hnnNext hpsTail⟩

-- Frozen 09.2 L151: the exact sum split is over actual per-step allocation
-- rows and the derived unused-payment observer.
theorem finite_stream_payments_equal_allocations_plus_unused
    (ps : List ℚ) (items : List LedgerItem) :
    ps.sum = ((streamAllocs ps items).map List.sum).sum +
      (streamUnusedPayments ps items).sum := by
  induction ps generalizing items with
  | nil => simp [streamAllocs, streamUnusedPayments]
  | cons p ps ih =>
      have headSplit := allocsOf_sum_add_remaining items p
      have tailSplit := ih (afterPay p items)
      simp only [streamAllocs, streamUnusedPayments, List.map_cons,
        List.sum_cons]
      linarith

-- Frozen 09.2 L151: the initial outstanding total is the actual final
-- outstanding total plus the sums of the actual allocation rows.
theorem finite_stream_debt_conservation
    (ps : List ℚ) (items : List LedgerItem) :
    outstanding items = outstanding (afterStream ps items) +
      ((streamAllocs ps items).map List.sum).sum := by
  induction ps generalizing items with
  | nil => simp [afterStream, streamAllocs]
  | cons p ps ih =>
      have step := outstanding_afterPay p items
      have tail := ih (afterPay p items)
      simp only [afterStream, streamAllocs, List.map_cons, List.sum_cons]
      linarith

-- Frozen 09.2 L153: the final balance is permutation-invariant for a single
-- nonnegative ledger item, by the existing stream clamp theorem.
theorem single_item_final_balance_invariant_under_payment_permutation
    (ps qs : List ℚ) (item : LedgerItem) (hitem : 0 ≤ item.amount)
    (hps : ∀ p ∈ ps, 0 ≤ p) (permutation : ps.Perm qs) :
    outstanding (afterStream ps [item]) =
      outstanding (afterStream qs [item]) := by
  have hitems : ∀ it ∈ [item], 0 ≤ it.amount := by
    intro it hit
    have same : it = item := List.mem_singleton.mp hit
    subst it
    exact hitem
  have hqs : ∀ p ∈ qs, 0 ≤ p := by
    intro p hp
    exact hps p (permutation.mem_iff.mpr hp)
  rw [outstanding_afterStream ps [item] hitems hps,
    outstanding_afterStream qs [item] hitems hqs,
    permutation.sum_eq]

-- Frozen 09.2 L151/L153: the same ten-unit input is consumed sequentially.
-- The current acceptance fixture and the ledger quantity stream agree at the
-- final balance, while the stream exposes both per-payment allocations and
-- both unused payment residues.
theorem continuous_ten_seven_seven_matches_quantity_stream :
    streamAllocs [7, 7] [tenUnitItem] = [[7], [3]] ∧
    remainingAfter (liAmounts [tenUnitItem]) 7 = 0 ∧
    remainingAfter (liAmounts (afterPay 7 [tenUnitItem])) 7 = 4 ∧
    ([7, 7] : List ℚ).sum =
      ((streamAllocs [7, 7] [tenUnitItem]).map List.sum).sum + [0, 4].sum ∧
    outstanding (afterStream [7, 7] [tenUnitItem]) = 0 ∧
    Ledger.balance Acceptance.post2.state =
      outstanding (afterStream [7, 7] [tenUnitItem]) := by
  have actual := Acceptance.a_u09_continuous_10_7_7
  have streamAllocations :
      streamAllocs [7, 7] [tenUnitItem] = [[7], [3]] := by
    norm_num [tenUnitItem, streamAllocs, afterPay, allocsOf]
  have firstResidue : remainingAfter (liAmounts [tenUnitItem]) 7 = 0 := by
    norm_num [tenUnitItem, liAmounts, remainingAfter]
  have secondResidue :
      remainingAfter (liAmounts (afterPay 7 [tenUnitItem])) 7 = 4 := by
    norm_num [tenUnitItem, liAmounts, afterPay, remainingAfter]
  have finalStream : outstanding (afterStream [7, 7] [tenUnitItem]) = 0 := by
    norm_num [tenUnitItem, outstanding, liAmounts, afterStream, afterPay]
  have totalSplit :
      ([7, 7] : List ℚ).sum =
        ((streamAllocs [7, 7] [tenUnitItem]).map List.sum).sum + [0, 4].sum := by
    rw [streamAllocations]
    norm_num
  refine ⟨streamAllocations, firstResidue, secondResidue, totalSplit,
    finalStream, ?_⟩
  rw [actual.2.1, finalStream]

-- Frozen 09.2 L153: actual 7/3 receipt allocations do not license retaining
-- the original debt as the post-payment state.
def reportedOldDebtAsRemainder : ℚ := Ledger.balance Acceptance.opening.state

theorem seven_three_allocation_report_cannot_keep_old_debt :
    (Ledger.commitPayment Acceptance.opening (Acceptance.request 1)).1.allocated = 7 ∧
    (Ledger.commitPayment Acceptance.post1 (Acceptance.request 2)).1.allocated = 3 ∧
    Ledger.balance Acceptance.opening.state = 10 ∧
    Ledger.balance Acceptance.post2.state = 0 ∧
    (Ledger.commitPayment Acceptance.opening (Acceptance.request 1)).1.allocated +
      (Ledger.commitPayment Acceptance.post1 (Acceptance.request 2)).1.allocated = 10 ∧
    Ledger.balance Acceptance.opening.state ≠ Ledger.balance Acceptance.post2.state ∧
    Ledger.balance Acceptance.opening.state ≠
      reportedOldDebtAsRemainder +
        (Ledger.commitPayment Acceptance.opening (Acceptance.request 1)).1.allocated +
        (Ledger.commitPayment Acceptance.post1 (Acceptance.request 2)).1.allocated := by
  decide +kernel

def paymentOrder12First :=
  Ledger.commitPayment Acceptance.opening (Acceptance.request 1)
def paymentOrder12Second :=
  Ledger.commitPayment paymentOrder12First.2 (Acceptance.request 2)
def paymentOrder21First :=
  Ledger.commitPayment Acceptance.opening (Acceptance.request 2)
def paymentOrder21Second :=
  Ledger.commitPayment paymentOrder21First.2 (Acceptance.request 1)

-- Frozen 09.2 L153: the same two actual payment identities can receive
-- different per-payment allocations when their execution order is reversed,
-- even though the final single-debt balance is the same.
theorem final_balance_order_independent_but_payment_identity_allocation_is_not :
    paymentOrder12Second.2.state.receipts.map (fun r => (r.key, r.allocated)) =
      [ (⟨1⟩, 7), (⟨2⟩, 3) ] ∧
    paymentOrder21Second.2.state.receipts.map (fun r => (r.key, r.allocated)) =
      [ (⟨2⟩, 7), (⟨1⟩, 3) ] ∧
    Ledger.balance paymentOrder12Second.2.state =
      Ledger.balance paymentOrder21Second.2.state ∧
    Ledger.balance paymentOrder12Second.2.state = 0 := by
  decide +kernel

end JurisLean.Candidates.SingleDebtStream20261103

#check JurisLean.Candidates.SingleDebtStream20261103.min_payment_step_nine_laws
#print axioms JurisLean.Candidates.SingleDebtStream20261103.min_payment_step_nine_laws
#check JurisLean.Candidates.SingleDebtStream20261103.afterPay_preserves_full_frame_and_pointwise_order
#print axioms JurisLean.Candidates.SingleDebtStream20261103.afterPay_preserves_full_frame_and_pointwise_order
#check JurisLean.Candidates.SingleDebtStream20261103.negative_payment_breaks_the_one_step_bounds
#print axioms JurisLean.Candidates.SingleDebtStream20261103.negative_payment_breaks_the_one_step_bounds
#check JurisLean.Candidates.SingleDebtStream20261103.sameItemFrameLe_is_partial_order
#print axioms JurisLean.Candidates.SingleDebtStream20261103.sameItemFrameLe_is_partial_order
#check JurisLean.Candidates.SingleDebtStream20261103.finitePaymentStepLaw
#check JurisLean.Candidates.SingleDebtStream20261103.finite_payment_steps_follow_actual_prefix
#print axioms JurisLean.Candidates.SingleDebtStream20261103.finite_payment_steps_follow_actual_prefix
#check JurisLean.Candidates.SingleDebtStream20261103.streamUnusedPayments
#check JurisLean.Candidates.SingleDebtStream20261103.finite_stream_payments_equal_allocations_plus_unused
#print axioms JurisLean.Candidates.SingleDebtStream20261103.finite_stream_payments_equal_allocations_plus_unused
#check JurisLean.Candidates.SingleDebtStream20261103.finite_stream_debt_conservation
#print axioms JurisLean.Candidates.SingleDebtStream20261103.finite_stream_debt_conservation
#check JurisLean.Candidates.SingleDebtStream20261103.single_item_final_balance_invariant_under_payment_permutation
#print axioms JurisLean.Candidates.SingleDebtStream20261103.single_item_final_balance_invariant_under_payment_permutation
#check JurisLean.Candidates.SingleDebtStream20261103.continuous_ten_seven_seven_matches_quantity_stream
#print axioms JurisLean.Candidates.SingleDebtStream20261103.continuous_ten_seven_seven_matches_quantity_stream
#check JurisLean.Candidates.SingleDebtStream20261103.seven_three_allocation_report_cannot_keep_old_debt
#print axioms JurisLean.Candidates.SingleDebtStream20261103.seven_three_allocation_report_cannot_keep_old_debt
#check JurisLean.Candidates.SingleDebtStream20261103.final_balance_order_independent_but_payment_identity_allocation_is_not
#print axioms JurisLean.Candidates.SingleDebtStream20261103.final_balance_order_independent_but_payment_identity_allocation_is_not

#check JurisLean.Candidates.Final20261021.Acceptance.a_u09_continuous_10_7_7
#print axioms JurisLean.Candidates.Final20261021.Acceptance.a_u09_continuous_10_7_7
#check JurisLean.Candidates.Final20261021.Acceptance.n_non_continuous_consume
#print axioms JurisLean.Candidates.Final20261021.Acceptance.n_non_continuous_consume
#check JurisLean.Candidates.Final20261021.Ledger.u09_1_quantity_conservation
#print axioms JurisLean.Candidates.Final20261021.Ledger.u09_1_quantity_conservation
#check JurisLean.Candidates.Final20261021.Ledger.u09_1_scalar_vector_stream_refinement
#print axioms JurisLean.Candidates.Final20261021.Ledger.u09_1_scalar_vector_stream_refinement
#check JurisLean.Candidates.Final20261021.Acceptance.n09_2_state_conservation_mismatch
#print axioms JurisLean.Candidates.Final20261021.Acceptance.n09_2_state_conservation_mismatch
#check JurisLean.Candidates.Final20261021.Ledger.u09_1_afterPayments_clamp
#print axioms JurisLean.Candidates.Final20261021.Ledger.u09_1_afterPayments_clamp
#check JurisLean.Seams.UnifiedQuantities.waterfall_conservation
#print axioms JurisLean.Seams.UnifiedQuantities.waterfall_conservation
#check JurisLean.Seams.UnifiedQuantities.remainingAfter_nonneg
#print axioms JurisLean.Seams.UnifiedQuantities.remainingAfter_nonneg
#check JurisLean.Seams.UnifiedQuantities.waterfall_sum_le
#print axioms JurisLean.Seams.UnifiedQuantities.waterfall_sum_le
#check JurisLean.Seams.UnifiedQuantLedger.waterfall_sum_eq_min
#print axioms JurisLean.Seams.UnifiedQuantLedger.waterfall_sum_eq_min
#check JurisLean.Seams.UnifiedQuantLedger.afterPay_idents
#print axioms JurisLean.Seams.UnifiedQuantLedger.afterPay_idents
#check JurisLean.Seams.UnifiedQuantLedger.afterPay_amounts_nonneg
#print axioms JurisLean.Seams.UnifiedQuantLedger.afterPay_amounts_nonneg
#check JurisLean.Seams.UnifiedQuantLedger.outstanding_afterStream
#print axioms JurisLean.Seams.UnifiedQuantLedger.outstanding_afterStream
#check JurisLean.Seams.UnifiedQuantLedger.streamAllocs_rows_legal
#print axioms JurisLean.Seams.UnifiedQuantLedger.streamAllocs_rows_legal
