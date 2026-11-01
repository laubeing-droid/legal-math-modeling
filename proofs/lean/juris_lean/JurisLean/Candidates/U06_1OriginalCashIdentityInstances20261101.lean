import JurisLean.Candidates.Final20261021.Ledger
import JurisLean.Candidates.Final20261021.Trace
import Mathlib

/-!
Original 06.1 L85/L89-L91 only. Cash events are existing ledger records.
The payload projection does not add a time field: factDate remains on the
payment payload and receipt. Cash additivity is by event identity, not labels.
-/

noncomputable section
open JurisLean.Candidates.Final20261021
open scoped BigOperators

namespace JurisLean.Candidates.U06_1OriginalCashIdentityInstances20261101

/-- The five cash fields actually appended by ledger performance. -/
def payloadCash (p : PaymentPayload) : CashEvent :=
  ⟨p.cashId, p.source, p.payer, p.payee, p.amount⟩

theorem performance_appends_payload_cash (s : Ledger.State) (p : PaymentPayload) :
    (Ledger.performance s p).cash = s.cash ++ [payloadCash p] := rfl

theorem commit_payment_appends_payload_cash (prev : Ledger.Handle) (req : PaymentRequest) :
    (Ledger.commitPayment prev req).2.state.cash =
      prev.state.cash ++ [payloadCash req.payload] ∧
    (Ledger.commitPayment prev req).1.payload.factDate = req.payload.factDate := by
  constructor <;> rfl

/-- Credit minus debit, on the existing event and account identities. -/
def cashFlow (e : CashEvent) (party : PartyId) : ℚ :=
  (if party = e.payee then e.amount.value else 0) -
    (if party = e.payer then e.amount.value else 0)

def netCash (events : Finset CashEvent) (party : PartyId) : ℚ :=
  events.sum fun e => cashFlow e party

def labelCash (labels : Finset String) (resolve : String → CashEvent)
    (party : PartyId) : ℚ :=
  netCash (labels.image resolve) party

/-- A successful existing payment guard rejects a repeated cash ID and
preserves Nodup when the actual ledger append is made. -/
theorem validated_commit_preserves_cash_ids
    (prev previous_output_ref : Ledger.Handle) (req : PaymentRequest)
    (permission : Bool)
    (ready : Ledger.validationError prev previous_output_ref req permission = none)
    (oldNodup : (prev.state.cash.map CashEvent.id).Nodup) :
    req.payload.cashId ∉ prev.state.cash.map CashEvent.id ∧
      ((Ledger.commitPayment prev req).2.state.cash.map CashEvent.id).Nodup := by
  unfold Ledger.validationError at ready
  simp only [Ledger.guard_none_iff] at ready
  rcases ready with ⟨_, _, _, _, _, _, _, _, _, _, _, _, cashGuard, _⟩
  have noRepeatedEvent : ∀ e ∈ prev.state.cash, e.id ≠ req.payload.cashId := by
    intro e he hId
    apply cashGuard
    rw [List.any_eq_true]
    exact ⟨e, he, by simp [hId]⟩
  have freshId : req.payload.cashId ∉ prev.state.cash.map CashEvent.id := by
    intro hmem
    obtain ⟨e, he, hId⟩ := List.mem_map.mp hmem
    exact noRepeatedEvent e he hId
  have appendedNodup :
      (prev.state.cash.map CashEvent.id ++ [req.payload.cashId]).Nodup :=
    (List.nodup_append).2
      ⟨oldNodup, by simp, by
        intro a ha b hb hab
        simp only [List.mem_singleton] at hb
        subst b
        exact freshId (hab ▸ ha)⟩
  refine ⟨freshId, ?_⟩
  change ((prev.state.cash ++ [payloadCash req.payload]).map CashEvent.id).Nodup
  rw [List.map_append]
  simpa [payloadCash] using appendedNodup

/-- Reindex a selected event sum by its unique existing event IDs. The
extension outside the selected image is only a function witness. -/
theorem cash_sum_reindexed_by_id
    (s : Ledger.State) (events : Finset CashEvent) (party : PartyId)
    (selected : ∀ e ∈ events, e ∈ s.cash)
    (cashIdsNodup : (s.cash.map CashEvent.id).Nodup) :
    ∃ valueById : EventId → ℚ,
      (∀ e ∈ events, valueById e.id = cashFlow e party) ∧
      netCash events party = ∑ id ∈ events.image CashEvent.id, valueById id := by
  classical
  let valueById : EventId → ℚ := fun id =>
    if h : id ∈ events.image CashEvent.id then
      cashFlow (Classical.choose (Finset.mem_image.mp h)) party
    else 0
  have idInjectiveOnEvents : ∀ e ∈ events, ∀ f ∈ events,
      e.id = f.id → e = f := by
    intro e he f hf hId
    exact List.inj_on_of_nodup_map (f := CashEvent.id) cashIdsNodup
      (selected e he) (selected f hf) hId
  have chosenValue (e : CashEvent) (he : e ∈ events) :
      valueById e.id = cashFlow e party := by
    have himage : e.id ∈ events.image CashEvent.id :=
      Finset.mem_image.mpr ⟨e, he, rfl⟩
    dsimp [valueById]
    rw [dif_pos himage]
    obtain ⟨f, hf, hId⟩ := Classical.choose_spec (Finset.mem_image.mp himage)
    have hSame : f = e := idInjectiveOnEvents f hf e he hId
    rw [hSame]
  refine ⟨valueById, ?_, ?_⟩
  · exact chosenValue
  · calc
      netCash events party = ∑ e ∈ events, cashFlow e party := rfl
      _ = ∑ e ∈ events, valueById e.id := by
        apply Finset.sum_congr rfl
        intro e he
        exact (chosenValue e he).symm
      _ = ∑ id ∈ events.image CashEvent.id, valueById id := by
        rw [← Finset.sum_image idInjectiveOnEvents]

/-- A bijective label rename with the inverse resolver leaves the represented
event set and its cash unchanged. -/
theorem rename_preserves_cash
    (labels : Finset String) (resolve : String → CashEvent)
    (rename : String ≃ String) (party : PartyId) :
    labelCash (labels.image rename) (resolve ∘ rename.symm) party =
      labelCash labels resolve party := by
  simp [labelCash, Finset.image_image, Function.comp_def]

/-- Re-encoding the IDs of these selected records leaves their cash vector
unchanged, provided the encoding is injective on the selected ID image. -/
theorem event_id_renaming_preserves_cash
    (s : Ledger.State) (events : Finset CashEvent) (party : PartyId)
    (selected : ∀ e ∈ events, e ∈ s.cash)
    (cashIdsNodup : (s.cash.map CashEvent.id).Nodup)
    (rename : EventId → EventId)
    (renameInjective : Set.InjOn rename (↑(events.image CashEvent.id))) :
    netCash (events.image (fun e => {e with id := rename e.id})) party =
      netCash events party := by
  classical
  let renameCash : CashEvent → CashEvent := fun e => {e with id := rename e.id}
  have renameCashInjective : ∀ e ∈ events, ∀ f ∈ events,
      renameCash e = renameCash f → e = f := by
    intro e he f hf hSame
    have hRenamedId := congrArg CashEvent.id hSame
    have hEventId := renameInjective e.id
      (Finset.mem_image.mpr ⟨e, he, rfl⟩) f.id
      (Finset.mem_image.mpr ⟨f, hf, rfl⟩) hRenamedId
    cases e with
    | mk eId eSource ePayer ePayee eAmount =>
      cases f with
      | mk fId fSource fPayer fPayee fAmount =>
        simp only [renameCash, CashEvent.mk.injEq] at hSame ⊢
        exact ⟨hEventId, hSame.2⟩
  change netCash (events.image renameCash) party = netCash events party
  unfold netCash
  rw [Finset.sum_image renameCashInjective]
  apply Finset.sum_congr rfl
  intro e he
  rfl
/-- Adding an alias for an already represented event changes neither the
resolved event set nor its cash. Event equality follows from the ledger's
unique cash-ID condition. -/
theorem alias_preserves_cash
    (s : Ledger.State) (labels : Finset String) (resolve : String → CashEvent)
    (oldLabel newLabel : String) (party : PartyId)
    (cashIdsNodup : (s.cash.map CashEvent.id).Nodup)
    (resolvedLabelsInCash : ∀ label ∈ labels, resolve label ∈ s.cash)
    (oldLabelInLabels : oldLabel ∈ labels)
    (newAliasInCash : resolve newLabel ∈ s.cash)
    (sameEventId : (resolve newLabel).id = (resolve oldLabel).id) :
    labelCash (insert newLabel labels) resolve party = labelCash labels resolve party := by
  have sameEvent : resolve newLabel = resolve oldLabel :=
    List.inj_on_of_nodup_map (f := CashEvent.id) cashIdsNodup
      newAliasInCash (resolvedLabelsInCash oldLabel oldLabelInLabels) sameEventId
  unfold labelCash
  rw [Finset.image_insert, sameEvent]
  exact Finset.insert_eq_of_mem
    (Finset.mem_image.mpr ⟨oldLabel, oldLabelInLabels, rfl⟩)

/-- Cash is additive across two event sets with disjoint event-ID images. -/
theorem disjoint_id_cash_additive
    (s : Ledger.State) (left right : Finset CashEvent) (party : PartyId)
    (leftSelected : ∀ e ∈ left, e ∈ s.cash)
    (rightSelected : ∀ e ∈ right, e ∈ s.cash)
    (cashIdsNodup : (s.cash.map CashEvent.id).Nodup)
    (disjointIds : Disjoint (left.image CashEvent.id) (right.image CashEvent.id)) :
    netCash (left ∪ right) party = netCash left party + netCash right party := by
  have disjointEvents : Disjoint left right := by
    refine Finset.disjoint_left.mpr ?_
    intro e heLeft heRight
    exact (Finset.disjoint_left.mp disjointIds) e.id
      (Finset.mem_image.mpr ⟨e, heLeft, rfl⟩)
      (Finset.mem_image.mpr ⟨e, heRight, rfl⟩)
  unfold netCash
  rw [Finset.sum_union disjointEvents]

def cashAccounts (events : List CashEvent) : Finset PartyId :=
  (events.map CashEvent.payer).toFinset ∪ (events.map CashEvent.payee).toFinset

/-- The actual finite account universe generated by the event endpoints
conserves cash under the admitted U09.2 account-sum theorem. -/
theorem actual_cash_accounts_conserve (events : List CashEvent) (unitTag : AmountTag)
    (sameUnit : ∀ e ∈ events, e.amount.tag = unitTag) :
    ∑ party : {p // p ∈ cashAccounts events},
      Ledger.cashVector
        (events.map fun e => fun account : {p // p ∈ cashAccounts events} =>
          cashFlow e account.val) party = 0 := by
  classical
  let Account := {p // p ∈ cashAccounts events}
  have balanced : ∀ event ∈
      events.map (fun e => fun account : Account => cashFlow e account.val),
      ∑ account : Account, event account = 0 := by
    intro event hEvent
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hEvent
    have payerMem : e.payer ∈ cashAccounts events := by
      unfold cashAccounts
      apply Finset.mem_union_left
      exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨e, he, rfl⟩)
    have payeeMem : e.payee ∈ cashAccounts events := by
      unfold cashAccounts
      apply Finset.mem_union_right
      exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨e, he, rfl⟩)
    let payer : Account := ⟨e.payer, payerMem⟩
    let payee : Account := ⟨e.payee, payeeMem⟩
    have credit :
        (∑ account : Account,
          if account.val = e.payee then e.amount.value else 0) = e.amount.value := by
      refine Finset.sum_eq_single_of_mem payee (Finset.mem_univ _) ?_
      intro account _ hne
      have hval : account.val ≠ e.payee := by
        intro h
        apply hne
        exact Subtype.ext h
      simp [hval]
    have debit :
        (∑ account : Account,
          if account.val = e.payer then e.amount.value else 0) = e.amount.value := by
      refine Finset.sum_eq_single_of_mem payer (Finset.mem_univ _) ?_
      intro account _ hne
      have hval : account.val ≠ e.payer := by
        intro h
        apply hne
        exact Subtype.ext h
      simp [hval]
    change (∑ account : Account, cashFlow e account.val) = 0
    unfold cashFlow
    rw [Finset.sum_sub_distrib, credit, debit]
    ring
  simpa [Ledger.cashVector] using
    (Ledger.u09_2_cash_by_account
      (events.map fun e => fun account : Account => cashFlow e account.val) balanced)

/-- Three concrete labels resolving to one six-unit event are not three
cash events; naïvely summing the labels triples the payment. -/
def sixUnitEvent : CashEvent :=
  ⟨⟨1⟩, ⟨1⟩, ⟨1⟩, ⟨2⟩, ⟨6, ⟨"SYN", "unit", 0⟩⟩⟩

def threeLabels : Finset String := {"one", "two", "three"}

def resolveThreeLabels (_ : String) : CashEvent := sixUnitEvent

theorem three_labels_one_six :
    labelCash threeLabels resolveThreeLabels ⟨2⟩ = 6 ∧
      (threeLabels.sum fun label => cashFlow (resolveThreeLabels label) ⟨2⟩) = 18 := by
  norm_num [labelCash, netCash, threeLabels, resolveThreeLabels, sixUnitEvent, cashFlow]

def cashTag : AmountTag := ⟨"SYN", "unit", 0⟩

def cashGamma : Gamma :=
  { caseId := ⟨1⟩, caseRevision := 0, evidenceVersion := 0, jurisdiction := "SYNTH",
    question := 0, interpretation := 0, normVersion := 0, lawDate := ⟨6⟩,
    knowledgeCutoff := ⟨6⟩, recordCutoff := ⟨6⟩, schemaVersion := 0,
    observationFamily := 0, mechanismVersion := 0 }

def sixDebt : DebtRecord := ⟨⟨1⟩, ⟨1⟩, ⟨2⟩, ⟨6, cashTag⟩, "synthetic debt"⟩

def cashOpening : Ledger.Handle := Trace.initial cashGamma sixDebt

def sixPaymentPayload (id : Nat) : PaymentPayload :=
  ⟨cashGamma.caseId, 0, sixDebt.relation, sixDebt.obligor, sixDebt.creditor,
    ⟨6, cashTag⟩, ⟨id⟩, ⟨id⟩, 0, cashGamma.lawDate⟩

def afterFirstSixPayment : Ledger.State :=
  Ledger.performance cashOpening.state (sixPaymentPayload 1)

def afterTwoSixPayments : Ledger.State :=
  Ledger.performance afterFirstSixPayment (sixPaymentPayload 2)

/-- Two distinct actual six-unit performance events against an initial six-unit
debt preserve the relation while the second payment is recorded as surplus. -/
theorem two_real_six_payments_keep_debt :
    cashOpening.state.cash = [] ∧
    Ledger.balance cashOpening.state = 6 ∧
    (sixPaymentPayload 1).cashId ≠ (sixPaymentPayload 2).cashId ∧
    afterTwoSixPayments.cash.map CashEvent.id = [⟨1⟩, ⟨2⟩] ∧
    Ledger.cashTotal afterTwoSixPayments = 12 ∧
    afterTwoSixPayments.initialDebt = 6 ∧
    afterTwoSixPayments.debt.relation = sixDebt.relation ∧
    Ledger.balance afterTwoSixPayments = 0 ∧
    afterTwoSixPayments.allocated = 6 ∧
    afterTwoSixPayments.surplus = 6 := by
  decide +kernel

end JurisLean.Candidates.U06_1OriginalCashIdentityInstances20261101