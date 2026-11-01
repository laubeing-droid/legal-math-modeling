import JurisLean.Candidates.Final20261021.Ledger
import JurisLean.Candidates.Final20261021.Trace
import Mathlib

/-!
Original 06.1 L83/L85/L89-L91 only. The mathematical cash denotation has real
amounts; the existing rational ledger is connected by an explicit embedding.
The payload projection does not add a time field: factDate remains on the
payment payload and receipt. Cash additivity is by event identity, not labels.
-/

noncomputable section
open JurisLean.Candidates.Final20261021
open scoped BigOperators

namespace JurisLean.Candidates.U06_1OriginalCashIdentityInstances20261101

/-- The original question's cash denotation uses real-valued amounts. -/
structure RealCashEvent where
  id : EventId
  source : SourceRef
  payer : PartyId
  payee : PartyId
  amount : ℝ
  tag : AmountTag
  factDate : LawDate

local instance : DecidableEq RealCashEvent := Classical.decEq _

/-- The five cash fields actually appended by ledger performance. -/
def payloadCash (p : PaymentPayload) : CashEvent :=
  ⟨p.cashId, p.source, p.payer, p.payee, p.amount⟩

/-- A concrete embedding of an existing rational ledger event into the original
real-valued cash denotation, with its externally supplied event date. -/
def fromQCash (date : LawDate) (e : CashEvent) : RealCashEvent :=
  ⟨e.id, e.source, e.payer, e.payee, (e.amount.value : ℝ), e.amount.tag, date⟩

def fromQPayload (p : PaymentPayload) : RealCashEvent :=
  fromQCash p.factDate (payloadCash p)

theorem fromQPayload_preserves_fields (p : PaymentPayload) :
    (fromQPayload p).id = p.cashId ∧
    (fromQPayload p).source = p.source ∧
    (fromQPayload p).payer = p.payer ∧
    (fromQPayload p).payee = p.payee ∧
    (fromQPayload p).amount = (p.amount.value : ℝ) ∧
    (fromQPayload p).tag = p.amount.tag ∧
    (fromQPayload p).factDate = p.factDate := by
  rfl

theorem performance_appends_payload_cash (s : Ledger.State) (p : PaymentPayload) :
    (Ledger.performance s p).cash = s.cash ++ [payloadCash p] := rfl

theorem commit_payment_appends_payload_cash (prev : Ledger.Handle) (req : PaymentRequest) :
    (Ledger.commitPayment prev req).2.state.cash =
      prev.state.cash ++ [payloadCash req.payload] ∧
    (Ledger.commitPayment prev req).1.payload.factDate = req.payload.factDate := by
  constructor <;> rfl

/-- The original real-valued credit-minus-debit cash flow. -/
def cashFlow (e : RealCashEvent) (party : PartyId) : ℝ :=
  (if party = e.payee then e.amount else 0) -
    (if party = e.payer then e.amount else 0)

def netCash (events : Finset RealCashEvent) (party : PartyId) : ℝ :=
  events.sum fun e => cashFlow e party

def labelCash (labels : Finset String) (resolve : String → RealCashEvent)
    (party : PartyId) : ℝ :=
  netCash (labels.image resolve) party

/-- The bounded implementation's existing rational cash flow, kept separate
from the real-valued original denotation. -/
def qCashFlow (e : CashEvent) (party : PartyId) : ℚ :=
  (if party = e.payee then e.amount.value else 0) -
    (if party = e.payer then e.amount.value else 0)

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
        exact freshId ((hab.trans hb) ▸ ha)⟩
  refine ⟨freshId, ?_⟩
  change ((prev.state.cash ++ [payloadCash req.payload]).map CashEvent.id).Nodup
  rw [List.map_append]
  simpa [payloadCash] using appendedNodup

/-- Reindex a selected event sum by its unique existing event IDs. The
extension outside the selected image is only a function witness. -/
theorem cash_sum_reindexed_by_id
    (entries : List RealCashEvent) (events : Finset RealCashEvent) (party : PartyId)
    (selected : ∀ e ∈ events, e ∈ entries)
    (cashIdsNodup : (entries.map RealCashEvent.id).Nodup) :
    ∃ valueById : EventId → ℝ,
      (∀ e ∈ events, valueById e.id = cashFlow e party) ∧
      netCash events party = ∑ id ∈ events.image RealCashEvent.id, valueById id := by
  classical
  let valueById : EventId → ℝ := fun id =>
    if h : id ∈ events.image RealCashEvent.id then
      cashFlow (Classical.choose (Finset.mem_image.mp h)) party
    else 0
  have idInjectiveOnEvents : ∀ e ∈ events, ∀ f ∈ events,
      e.id = f.id → e = f := by
    intro e he f hf hId
    exact List.inj_on_of_nodup_map (f := RealCashEvent.id) cashIdsNodup
      (selected e he) (selected f hf) hId
  have chosenValue (e : RealCashEvent) (he : e ∈ events) :
      valueById e.id = cashFlow e party := by
    have himage : e.id ∈ events.image RealCashEvent.id :=
      Finset.mem_image.mpr ⟨e, he, rfl⟩
    dsimp [valueById]
    rw [dif_pos himage]
    have spec := Classical.choose_spec (Finset.mem_image.mp himage)
    exact congrArg (fun event : RealCashEvent => cashFlow event party)
      (idInjectiveOnEvents (Classical.choose (Finset.mem_image.mp himage))
        spec.1 e he spec.2)
  refine ⟨valueById, ?_, ?_⟩
  · exact chosenValue
  · calc
      netCash events party = ∑ e ∈ events, cashFlow e party := rfl
      _ = ∑ e ∈ events, valueById e.id := by
        apply Finset.sum_congr rfl
        intro e he
        exact (chosenValue e he).symm
      _ = ∑ id ∈ events.image RealCashEvent.id, valueById id := by
        rw [← Finset.sum_image idInjectiveOnEvents]

/-- A bijective label rename with the inverse resolver leaves the represented
event set and its cash unchanged. -/
theorem rename_preserves_cash
    (labels : Finset String) (resolve : String → RealCashEvent)
    (rename : String ≃ String) (party : PartyId) :
    labelCash (labels.image rename) (resolve ∘ rename.symm) party =
      labelCash labels resolve party := by
  simp [labelCash, Finset.image_image, Function.comp_def]

/-- Re-encoding the IDs of these selected records leaves their cash vector
unchanged, provided the encoding is injective on the selected ID image. -/
theorem event_id_renaming_preserves_cash
    (entries : List RealCashEvent) (events : Finset RealCashEvent) (party : PartyId)
    (selected : ∀ e ∈ events, e ∈ entries)
    (cashIdsNodup : (entries.map RealCashEvent.id).Nodup)
    (rename : EventId → EventId)
    (renameInjective : Set.InjOn rename (↑(events.image RealCashEvent.id))) :
    netCash (events.image (fun e => {e with id := rename e.id})) party =
      netCash events party := by
  classical
  let renameCash : RealCashEvent → RealCashEvent := fun e => {e with id := rename e.id}
  have renameCashInjective : ∀ e ∈ events, ∀ f ∈ events,
      renameCash e = renameCash f → e = f := by
    intro e he f hf hSame
    have hRenamedId := congrArg RealCashEvent.id hSame
    have hEventId := renameInjective
      (Finset.mem_image.mpr ⟨e, he, rfl⟩)
      (Finset.mem_image.mpr ⟨f, hf, rfl⟩) hRenamedId
    exact List.inj_on_of_nodup_map (f := RealCashEvent.id) cashIdsNodup
      (selected e he) (selected f hf) hEventId
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
    (entries : List RealCashEvent) (labels : Finset String) (resolve : String → RealCashEvent)
    (oldLabel newLabel : String) (party : PartyId)
    (cashIdsNodup : (entries.map RealCashEvent.id).Nodup)
    (resolvedLabelsInCash : ∀ label ∈ labels, resolve label ∈ entries)
    (oldLabelInLabels : oldLabel ∈ labels)
    (newAliasInCash : resolve newLabel ∈ entries)
    (sameEventId : (resolve newLabel).id = (resolve oldLabel).id) :
    labelCash (insert newLabel labels) resolve party = labelCash labels resolve party := by
  have sameEvent : resolve newLabel = resolve oldLabel :=
    List.inj_on_of_nodup_map (f := RealCashEvent.id) cashIdsNodup
      newAliasInCash (resolvedLabelsInCash oldLabel oldLabelInLabels) sameEventId
  unfold labelCash
  rw [Finset.image_insert, sameEvent]
  rw [Finset.insert_eq_of_mem (Finset.mem_image_of_mem resolve oldLabelInLabels)]

/-- Cash is additive across two event sets with disjoint event-ID images. -/
theorem disjoint_id_cash_additive
    (entries : List RealCashEvent) (left right : Finset RealCashEvent) (party : PartyId)
    (leftSelected : ∀ e ∈ left, e ∈ entries)
    (rightSelected : ∀ e ∈ right, e ∈ entries)
    (cashIdsNodup : (entries.map RealCashEvent.id).Nodup)
    (disjointIds : Disjoint (left.image RealCashEvent.id) (right.image RealCashEvent.id)) :
    netCash (left ∪ right) party = netCash left party + netCash right party := by
  have disjointEvents : Disjoint left right := by
    refine Finset.disjoint_left.mpr ?_
    intro e heLeft heRight
    exact (Finset.disjoint_left.mp disjointIds)
      (Finset.mem_image.mpr ⟨e, heLeft, rfl⟩)
      (Finset.mem_image.mpr ⟨e, heRight, rfl⟩)
  unfold netCash
  rw [Finset.sum_union disjointEvents]

/-- The existing rational ledger's account universe and balance theorem remain
an implementation result, separate from the real-valued original contract. -/
def qCashAccounts (events : List CashEvent) : Finset PartyId :=
  (events.map CashEvent.payer).toFinset ∪ (events.map CashEvent.payee).toFinset

theorem q_ledger_cash_accounts_conserve (events : List CashEvent) :
    ∑ party : {p // p ∈ qCashAccounts events},
      Ledger.cashVector
        (events.map fun e => fun account : {p // p ∈ qCashAccounts events} =>
          qCashFlow e account.val) party = 0 := by
  classical
  let Account := {p // p ∈ qCashAccounts events}
  have balanced : ∀ event ∈ events.map (fun e => fun account : Account => qCashFlow e account.val),
      ∑ account : Account, event account = 0 := by
    intro event hEvent
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hEvent
    have payerMem : e.payer ∈ qCashAccounts events := by
      unfold qCashAccounts
      apply Finset.mem_union_left
      exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨e, he, rfl⟩)
    have payeeMem : e.payee ∈ qCashAccounts events := by
      unfold qCashAccounts
      apply Finset.mem_union_right
      exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨e, he, rfl⟩)
    let payer : Account := ⟨e.payer, payerMem⟩
    let payee : Account := ⟨e.payee, payeeMem⟩
    have credit :
        (∑ account : Account,
          if account.val = e.payee then e.amount.value else 0) = e.amount.value := by
      have single := Finset.sum_eq_single_of_mem
        (s := (Finset.univ : Finset Account))
        (f := fun account : Account =>
          if account.val = e.payee then (e.amount.value : ℚ) else 0)
        payee (Finset.mem_univ payee) (by
          intro account _ hne
          have hval : account.val ≠ e.payee := by
            intro h
            apply hne
            exact Subtype.ext h
          simp [hval])
      simpa [payee] using single
    have debit :
        (∑ account : Account,
          if account.val = e.payer then e.amount.value else 0) = e.amount.value := by
      have single := Finset.sum_eq_single_of_mem
        (s := (Finset.univ : Finset Account))
        (f := fun account : Account =>
          if account.val = e.payer then (e.amount.value : ℚ) else 0)
        payer (Finset.mem_univ payer) (by
          intro account _ hne
          have hval : account.val ≠ e.payer := by
            intro h
            apply hne
            exact Subtype.ext h
          simp [hval])
      simpa [payer] using single
    change (∑ account : Account, qCashFlow e account.val) = 0
    unfold qCashFlow
    rw [Finset.sum_sub_distrib, credit, debit]
    ring
  simpa [Ledger.cashVector] using
    (Ledger.u09_2_cash_by_account
      (events.map fun e => fun account : Account => qCashFlow e account.val) balanced)

/-- The real account universe is the finite set of event endpoints. -/
def realCashAccounts (events : Finset RealCashEvent) : Finset PartyId :=
  events.image RealCashEvent.payer ∪ events.image RealCashEvent.payee

/-- Real cash sums to zero across all accounts present in the selected events.
All events share the declared amount tag; the valuation context is an external
fixed input and is not inferred from payment fact dates. -/
theorem actual_cash_accounts_conserve (events : Finset RealCashEvent) (unitTag : AmountTag)
    (sameUnit : ∀ e ∈ events, e.amount.tag = unitTag) :
    ∑ party : {p // p ∈ realCashAccounts events}, netCash events party.val = 0 := by
  classical
  let Account := {p // p ∈ realCashAccounts events}
  have eventBalanced (e : RealCashEvent) (he : e ∈ events) :
      ∑ account : Account, cashFlow e account.val = 0 := by
    have payerMem : e.payer ∈ realCashAccounts events := by
      apply Finset.mem_union_left
      exact Finset.mem_image.mpr ⟨e, he, rfl⟩
    have payeeMem : e.payee ∈ realCashAccounts events := by
      apply Finset.mem_union_right
      exact Finset.mem_image.mpr ⟨e, he, rfl⟩
    let payer : Account := ⟨e.payer, payerMem⟩
    let payee : Account := ⟨e.payee, payeeMem⟩
    have credit :
        (∑ account : Account,
          if account.val = e.payee then e.amount else 0) = e.amount := by
      have single := Finset.sum_eq_single_of_mem
        (s := (Finset.univ : Finset Account))
        (f := fun account : Account =>
          if account.val = e.payee then (e.amount : ℝ) else 0)
        payee (Finset.mem_univ payee) (by
          intro account _ hne
          have hval : account.val ≠ e.payee := by
            intro h
            apply hne
            exact Subtype.ext h
          simp [hval])
      simpa [payee] using single
    have debit :
        (∑ account : Account,
          if account.val = e.payer then e.amount else 0) = e.amount := by
      have single := Finset.sum_eq_single_of_mem
        (s := (Finset.univ : Finset Account))
        (f := fun account : Account =>
          if account.val = e.payer then (e.amount : ℝ) else 0)
        payer (Finset.mem_univ payer) (by
          intro account _ hne
          have hval : account.val ≠ e.payer := by
            intro h
            apply hne
            exact Subtype.ext h
          simp [hval])
      simpa [payer] using single
    unfold cashFlow
    rw [Finset.sum_sub_distrib, credit, debit]
    ring
  calc
    _ = ∑ account : Account, ∑ e ∈ events, cashFlow e account.val := by
      rfl
    _ = ∑ e ∈ events, ∑ account : Account, cashFlow e account.val := by
      rw [Finset.sum_comm]
    _ = 0 := by
      apply Finset.sum_eq_zero
      intro e he
      exact eventBalanced e he

/-- The existing rational ledger is a concrete instance of the real-valued
denotation after each event is embedded with its externally supplied date. -/
theorem q_ledger_cash_vector_matches_real_cash (events : List CashEvent)
    (idsNodup : (events.map CashEvent.id).Nodup) (dateOf : CashEvent → LawDate)
    (party : PartyId) :
    netCash (events.toFinset.image (fun e => fromQCash (dateOf e) e)) party =
      (Ledger.cashVector (events.map fun e => fun a : PartyId => qCashFlow e a) party : ℝ) := by
  classical
  let qEvents := events.toFinset
  let lift : CashEvent → RealCashEvent := fun e => fromQCash (dateOf e) e
  have liftInjective : ∀ e ∈ qEvents, ∀ f ∈ qEvents, lift e = lift f → e = f := by
    intro e he f hf h
    have hId := congrArg RealCashEvent.id h
    apply List.inj_on_of_nodup_map (f := CashEvent.id) idsNodup
      (List.mem_of_mem_toFinset he) (List.mem_of_mem_toFinset hf)
    exact hId
  have flowCast (e : CashEvent) : cashFlow (lift e) party = (qCashFlow e party : ℝ) := by
    by_cases hp : party = e.payee <;> by_cases hq : party = e.payer <;>
      simp [lift, fromQCash, cashFlow, qCashFlow, hp, hq]
  unfold netCash
  rw [Finset.sum_image liftInjective]
  simp only [flowCast]
  rw [Ledger.cashVector]
  exact_mod_cast (List.sum_toFinset (fun e => qCashFlow e party)
    (List.Nodup.of_map CashEvent.id idsNodup))

/-- Three concrete labels resolving to one six-unit event are not three
cash events; naïvely summing the labels triples the payment. -/
def sixUnitEvent : RealCashEvent :=
  ⟨⟨1⟩, ⟨1⟩, ⟨1⟩, ⟨2⟩, 6, ⟨"SYN", "unit", 0⟩, ⟨6⟩⟩

def threeLabels : Finset String := {"one", "two", "three"}

def resolveThreeLabels (_ : String) : RealCashEvent := sixUnitEvent

theorem three_labels_one_six :
    labelCash threeLabels resolveThreeLabels ⟨2⟩ = 6 ∧
      (threeLabels.sum fun label => cashFlow (resolveThreeLabels label) ⟨2⟩) = 18 := by
  have labelCount : ({"one", "two", "three"} : Finset String).card = 3 := by decide +kernel
  have labelImage : threeLabels.image resolveThreeLabels = {sixUnitEvent} := by
    simp [threeLabels, resolveThreeLabels]
  constructor
  · change netCash (threeLabels.image resolveThreeLabels) ⟨2⟩ = 6
    rw [labelImage]
    norm_num [netCash, sixUnitEvent, cashFlow]
  · norm_num [netCash, threeLabels, resolveThreeLabels, sixUnitEvent, cashFlow, labelCount]

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

/-- The two Q implementation events embed as real events with their supplied
fact dates; account nets are +12 to the payee and -12 to the payer. -/
theorem two_real_six_payment_account_cash :
    netCash (afterTwoSixPayments.cash.toFinset.image
      (fun e => fromQCash cashGamma.lawDate e)) ⟨2⟩ = 12 ∧
    netCash (afterTwoSixPayments.cash.toFinset.image
      (fun e => fromQCash cashGamma.lawDate e)) ⟨1⟩ = -12 := by
  have sourceFacts := two_real_six_payments_keep_debt
  have hIds : (afterTwoSixPayments.cash.map CashEvent.id).Nodup := by
    rw [sourceFacts.2.2.2.1]
    simp
  have hPayee := q_ledger_cash_vector_matches_real_cash afterTwoSixPayments.cash hIds
    (fun _ => cashGamma.lawDate) ⟨2⟩
  have hPayer := q_ledger_cash_vector_matches_real_cash afterTwoSixPayments.cash hIds
    (fun _ => cashGamma.lawDate) ⟨1⟩
  constructor
  · rw [hPayee]
    norm_num [Ledger.cashVector, qCashFlow, afterTwoSixPayments, afterFirstSixPayment,
      Ledger.performance, sixPaymentPayload, cashGamma, cashTag]
  · rw [hPayer]
    norm_num [Ledger.cashVector, qCashFlow, afterTwoSixPayments, afterFirstSixPayment,
      Ledger.performance, sixPaymentPayload, cashGamma, cashTag]

end JurisLean.Candidates.U06_1OriginalCashIdentityInstances20261101
