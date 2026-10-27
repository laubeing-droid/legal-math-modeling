import JurisLean.Candidates.SourceCompilation20261027
import JurisLean.Candidates.SourceRepresentation20261027
import JurisLean.Candidates.Final20261021.Ledger
import JurisLean.Seams.Unified

/-!
Original 07: deterministic full-row binding, a finite formation/two-payment
window, and conditional common models. The quantitative snapshot precedes this
window; earlier history supplies the relation projection, not a reconstructed
cash balance. Structural acceptance does not grant permission or certify the
primitive interpretation. The four stages are mathematical states, not external
commit receipts. The transaction consumer remains Final20261021.Ledger.

The old C1 is global, C3 includes a fixed game, and C4 contains two transitions
from one starting ledger. Those statements are used unchanged. The separate
stage construction below actually passes the first poststate to payment two.
-/

namespace JurisLean.Candidates.SourceStages20261027

open JurisLean.Candidates.Final20261021
open JurisLean.Candidates.SourceCompilation20261027
open JurisLean.Seams

abbrev ResolvedLegalRef (mu : SourceRef → Option LegalObject) :=
  {ref : SourceRef // ∃ object, mu ref = some object}

noncomputable def canonicalLegalKey (mu : SourceRef → Option LegalObject)
    (ref : ResolvedLegalRef mu) : LegalObject := Classical.choose ref.property

theorem canonical_typed_identity_is_exact (mu : SourceRef → Option LegalObject)
    (left right : ResolvedLegalRef mu) :
    canonicalLegalKey mu left = canonicalLegalKey mu right ↔
      ∃ object, mu left.val = some object ∧ mu right.val = some object := by
  have hl : mu left = some (canonicalLegalKey mu left) := Classical.choose_spec left.property
  have hr : mu right = some (canonicalLegalKey mu right) := Classical.choose_spec right.property
  constructor
  · intro same; exact ⟨canonicalLegalKey mu left, hl, by simpa only [same] using hr⟩
  · rintro ⟨object, l, r⟩
    exact (Option.some.inj (hl.symm.trans l)).trans (Option.some.inj (r.symm.trans hr))

theorem typed_identity_equivalence_on_defined_domain (mu : SourceRef → Option LegalObject) :
    Equivalence (fun left right : ResolvedLegalRef mu =>
      ∃ object, mu left.val = some object ∧ mu right.val = some object) := by
  refine ⟨?_, ?_, ?_⟩
  · intro a; exact (canonical_typed_identity_is_exact mu a a).mp rfl
  · intro a b ab
    exact (canonical_typed_identity_is_exact mu b a).mp
      ((canonical_typed_identity_is_exact mu a b).mpr ab).symm
  · intro a b c ab bc
    exact (canonical_typed_identity_is_exact mu a c).mp
      (((canonical_typed_identity_is_exact mu a b).mpr ab).trans
        ((canonical_typed_identity_is_exact mu b c).mpr bc))

theorem undefined_typed_reference_is_not_identified (mu : SourceRef → Option LegalObject)
    (left right : SourceRef) (missing : mu left = none) :
    ¬ ∃ object, mu left = some object ∧ mu right = some object := by
  rintro ⟨object, found, _⟩
  rw [missing] at found
  cases found

structure BoundPayment where
  history : Quoted SourceHistory
  payment : Quoted FullPayment
  debt : Quoted FullDebt
  relation : Quoted DebtRecord

-- First-match selection is only provisional. The independent count checks
-- below reject ambiguous keys, including two byte-for-byte equal rows.
def candidatePayment (view : ExtractedView) (index : Nat) : Option BoundPayment := do
  let history ← view.decoded.historyEvents[index]?
  let key ← match history.value with
    | .payment _ key => some key
    | .formation _ _ => none
  let payment ← view.decoded.payments.find? (fun p => p.value.key == key)
  let debt ← view.decoded.ledger.find? (fun d => d.value.item.ident == payment.value.targetDebt)
  let relation ← view.decoded.relations.find? (fun r => r.value.relation == debt.value.debtRel)
  return ⟨history, payment, debt, relation⟩

def BindingChecks (view : ExtractedView) (b : BoundPayment) : Prop :=
  (view.decoded.payments.filter (fun p => p.value.key == b.payment.value.key)).length = 1 ∧
  (view.decoded.ledger.filter (fun d => d.value.item.ident == b.payment.value.targetDebt)).length = 1 ∧
  (view.decoded.relations.filter (fun r => r.value.relation == b.debt.value.debtRel)).length = 1 ∧
  b.history.value = .payment b.history.citation.source b.payment.value.key ∧
  b.history.citation = b.payment.citation ∧
  b.payment.value.payload.source = b.payment.citation.source ∧
  b.payment.value.payload.caseId = view.material.gamma.caseId ∧
  b.payment.value.payload.caseRevision = view.material.gamma.caseRevision ∧
  b.payment.value.payload.relation = b.debt.value.debtRel ∧
  b.payment.value.payload.payer = b.debt.value.obligor ∧
  b.payment.value.payload.payee.value = b.debt.value.item.beneficiary ∧
  b.payment.value.payload.amount.tag = b.debt.value.unit ∧
  b.payment.value.payload.normVersion = view.material.gamma.normVersion ∧
  b.payment.value.payload.factDate = view.material.gamma.lawDate ∧
  b.relation.value.relation = b.debt.value.debtRel ∧
  b.relation.value.obligor = b.debt.value.obligor ∧
  b.relation.value.creditor.value = b.debt.value.item.beneficiary ∧
  b.relation.value.amount = ⟨b.debt.value.item.amount, b.debt.value.unit⟩ ∧
  0 ≤ b.debt.value.item.amount ∧ 0 ≤ b.payment.value.payload.amount.value

instance (view : ExtractedView) (b : BoundPayment) : Decidable (BindingChecks view b) :=
  inferInstanceAs (Decidable (_ ∧ _))

def bindPayment (view : ExtractedView) (index : Nat) : Result BoundPayment :=
  match candidatePayment view index with
  | none => .unknown .missingEvidence
  | some b => if BindingChecks view b then .known b else .rejected .observationBindingMismatch

theorem successful_binding_reads_actual_rows (view : ExtractedView) (index : Nat)
    (bound : BoundPayment) (success : bindPayment view index = .known bound) :
    candidatePayment view index = some bound ∧ BindingChecks view bound := by
  cases selected : candidatePayment view index with
  | none => simp [bindPayment, selected] at success
  | some b =>
      simp only [bindPayment, selected] at success
      split at success
      next valid => cases success; exact ⟨rfl, valid⟩
      next invalid => cases success

theorem deterministic_binding_data_unique (view : ExtractedView) (index : Nat)
    (left right : BoundPayment)
    (hl : bindPayment view index = .known left)
    (hr : bindPayment view index = .known right) : left = right :=
  Result.known.inj (hl.symm.trans hr)

def sameDebt (left right : FullDebt) : Bool :=
  decide (left.item.ident = right.item.ident ∧ left.item.kind = right.item.kind ∧
    left.item.basis = right.item.basis ∧ left.item.beneficiary = right.item.beneficiary ∧
    left.item.status = right.item.status ∧ left.item.amount = right.item.amount ∧
    left.debtRel = right.debtRel ∧ left.obligor = right.obligor ∧ left.unit = right.unit)

theorem full_debt_comparison_is_exact (left right : FullDebt)
    (checked : sameDebt left right = true) : left = right := by
  cases left with
  | mk li lr lo lu =>
      cases right with
      | mk ri rr ro ru =>
          cases li
          cases ri
          simp_all [sameDebt]

def initialRelations (view : ExtractedView) : InstitutionalEffects.Ledger RelationId :=
  view.decoded.initialHistory.filterMap fun h => match h.value with
    | .formation source relation => some (InstitutionalEffects.formedRecord (toString source.value) relation)
    | .payment _ _ => none

structure Stage where
  relations : InstitutionalEffects.Ledger RelationId
  quantity : FullDebt
  state : Ledger.State

def initialStage (view : ExtractedView) (bound : BoundPayment) : Stage :=
  let history := initialRelations view
  ⟨history, bound.debt.value,
    { debt := bound.relation.value, formations := history.map (fun r => r.rel)
      judgment := .insufficient, procedure := .open, claim := .unknown
      executionEligible := false, initialDebt := bound.relation.value.amount.value
      newDebt := 0, accrual := 0, allocated := 0, writtenOff := 0, paid := 0, surplus := 0
      cash := [], used := ∅, receipts := [], rest := none, refundCash := []
      normHistory := [], env := .unknown .missingEvidence }⟩

def formStage (before : Stage) (source : SourceRef) (relation : RelationId) : Stage :=
  { before with
    relations := InstitutionalEffects.next before.relations (.formative (toString source.value) relation)
    state := { before.state with formations := before.state.formations ++ [relation] } }

def payStage (before : Stage) (payment : PaymentPayload) : Stage :=
  { before with
    quantity := { before.quantity with item := { before.quantity.item with
      amount := before.quantity.item.amount - min payment.amount.value before.quantity.item.amount } }
    state := Ledger.performance before.state payment }

theorem quantity_step_is_existing_ledger_step (before : Stage) (payment : PaymentPayload) :
    [(payStage before payment).quantity.item] =
      UnifiedQuantLedger.afterPay payment.amount.value [before.quantity.item] := rfl

theorem payment_preserves_complete_nonquantity_fields (before : Stage) (payment : PaymentPayload) :
    (payStage before payment).relations = before.relations ∧
    (payStage before payment).quantity.item.ident = before.quantity.item.ident ∧
    (payStage before payment).quantity.item.kind = before.quantity.item.kind ∧
    (payStage before payment).quantity.item.basis = before.quantity.item.basis ∧
    (payStage before payment).quantity.item.beneficiary = before.quantity.item.beneficiary ∧
    (payStage before payment).quantity.item.status = before.quantity.item.status ∧
    (payStage before payment).quantity.debtRel = before.quantity.debtRel ∧
    (payStage before payment).quantity.obligor = before.quantity.obligor ∧
    (payStage before payment).quantity.unit = before.quantity.unit ∧
    (payStage before payment).state.formations = before.state.formations := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem scalar_and_item_projections_commute (before : Stage) (payment : PaymentPayload)
    (initial : before.quantity.item.amount = Ledger.balance before.state) :
    (payStage before payment).quantity.item.amount = Ledger.balance (payStage before payment).state := by
  change before.quantity.item.amount - min payment.amount.value before.quantity.item.amount =
    Ledger.balance before.state - min payment.amount.value (Ledger.balance before.state)
  rw [initial]

structure FourStages where
  beforeFormation : Stage
  afterFormation : Stage
  afterFirst : Stage
  afterSecond : Stage

def buildStages (view : ExtractedView) (first second : BoundPayment)
    (source : SourceRef) (relation : RelationId) : FourStages :=
  let before := initialStage view first
  let formed := formStage before source relation
  let paidFirst := payStage formed first.payment.value.payload
  ⟨before, formed, paidFirst, payStage paidFirst second.payment.value.payload⟩

theorem four_stages_use_actual_previous_output (view : ExtractedView)
    (first second : BoundPayment) (source : SourceRef) (relation : RelationId) :
    let frame := buildStages view first second source relation
    frame.afterFormation = formStage frame.beforeFormation source relation ∧
    frame.afterFirst = payStage frame.afterFormation first.payment.value.payload ∧
    frame.afterSecond = payStage frame.afterFirst second.payment.value.payload ∧
    frame.afterFirst.relations = frame.afterFormation.relations ∧
    frame.afterSecond.relations = frame.afterFirst.relations := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem adjacent_formation_projection (before : Stage) (source : SourceRef)
    (relation observed : RelationId) :
    InstitutionalEffects.forms (formStage before source relation).relations observed ↔
      observed = relation ∨ InstitutionalEffects.forms before.relations observed :=
  InstitutionalEffects.projection_of_append_matches_step _ _ _ _

theorem two_payments_balance_and_cash (view : ExtractedView) (first second : BoundPayment)
    (source : SourceRef) (relation : RelationId)
    (nonnegative : 0 ≤ first.relation.value.amount.value)
    (payOne : 0 ≤ first.payment.value.payload.amount.value)
    (payTwo : 0 ≤ second.payment.value.payload.amount.value) :
    let frame := buildStages view first second source relation
    Ledger.balance frame.afterSecond.state =
      max (first.relation.value.amount.value -
        (first.payment.value.payload.amount.value + second.payment.value.payload.amount.value)) 0 ∧
    Ledger.Conserves frame.afterSecond.state ∧ Ledger.CashConsistent frame.afterSecond.state := by
  let formed := (buildStages view first second source relation).afterFormation.state
  have initial : Ledger.Conserves formed := by
    dsimp [formed, buildStages, initialStage, formStage, Ledger.Conserves, Ledger.balance]
    exact ⟨nonnegative, le_rfl, le_rfl, le_rfl, le_rfl, le_rfl, le_rfl, by ring, by norm_num⟩
  have cash : Ledger.CashConsistent formed := by rfl
  have conserved := Ledger.u09_1_quantity_conservation
    (Ledger.performance formed first.payment.value.payload) second.payment.value.payload
    (Ledger.u09_1_quantity_conservation formed first.payment.value.payload initial payOne) payTwo
  refine ⟨?_, conserved, Ledger.performance_cash_consistent _ _
    (Ledger.performance_cash_consistent _ _ cash)⟩
  have clamp := Ledger.u09_1_afterPayments_clamp formed
    [first.payment.value.payload, second.payment.value.payload] nonnegative
    (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with rfl | rfl; exact payOne; exact payTwo)
  simpa [Ledger.afterPayments, buildStages, payStage, formed, formStage, initialStage,
    Ledger.balance] using clamp

structure SourceFrame where
  source : ExtractedView
  first : BoundPayment
  second : BoundPayment
  formationSource : SourceRef
  formationRelation : RelationId
  stages : FourStages

def frameFromBindings (view : ExtractedView) (first second : BoundPayment) : Result SourceFrame :=
  match view.decoded.historyEvents with
  | [formation, _, _] =>
      match formation.value with
      | .formation source relation =>
          if source = formation.citation.source ∧ relation = first.debt.value.debtRel ∧
              sameDebt first.debt.value second.debt.value = true ∧
              first.relation.value = second.relation.value ∧
              first.payment.value.key ≠ second.payment.value.key ∧
              first.payment.value.payload.cashId ≠ second.payment.value.payload.cashId then
            .known ⟨view, first, second, source, relation, buildStages view first second source relation⟩
          else .rejected .stageFrameMismatch
      | .payment _ _ => .rejected .stageFrameMismatch
  | _ => .rejected .stageFrameMismatch

def stagesFromView (view : ExtractedView) : Result SourceFrame :=
  match bindPayment view 1, bindPayment view 2 with
  | .known first, .known second => frameFromBindings view first second
  | .unknown e, _ | _, .unknown e => .unknown e
  | .rejected e, _ | _, .rejected e => .rejected e
  | .conflict l r, _ | _, .conflict l r => .conflict l r

def sourceStages (material : MaterialSnapshot) (branch : Nat)
    (catalog : List InterpretationRow) : Result SourceFrame :=
  match extractView material branch catalog with
  | .known view => stagesFromView view
  | .unknown e => .unknown e
  | .rejected e => .rejected e
  | .conflict l r => .conflict l r

theorem frame_contains_actual_computed_stages (view : ExtractedView)
    (first second : BoundPayment) (out : SourceFrame)
    (accepted : frameFromBindings view first second = .known out) :
    out.source = view ∧ out.first = first ∧ out.second = second ∧
    out.stages = buildStages view first second out.formationSource out.formationRelation := by
  unfold frameFromBindings at accepted
  split at accepted
  next formation x y =>
    split at accepted
    next source relation =>
      split at accepted
      next valid => cases accepted; exact ⟨rfl, rfl, rfl, rfl⟩
      next invalid => cases accepted
    next source key => cases accepted
  next other => cases accepted

theorem accepted_view_binds_both_actual_payments (view : ExtractedView) (out : SourceFrame)
    (accepted : stagesFromView view = .known out) :
    out.source = view ∧ bindPayment view 1 = .known out.first ∧
    bindPayment view 2 = .known out.second ∧
    out.stages = buildStages view out.first out.second out.formationSource out.formationRelation := by
  cases one : bindPayment view 1 <;> cases two : bindPayment view 2 <;>
    simp only [stagesFromView, one, two] at accepted
  all_goals try cases accepted
  next first second =>
    obtain ⟨hs, hf, ht, stages⟩ := frame_contains_actual_computed_stages _ _ _ _ accepted
    exact ⟨hs, by simpa only [hf] using one, by simpa only [ht] using two,
      by simpa only [hf, ht] using stages⟩

theorem public_consumer_reads_actual_extraction (material : MaterialSnapshot) (branch : Nat)
    (catalog : List InterpretationRow) (out : SourceFrame)
    (accepted : sourceStages material branch catalog = .known out) :
    extractView material branch catalog = .known out.source ∧
      stagesFromView out.source = .known out := by
  cases extracted : extractView material branch catalog with
  | unknown e => simp [sourceStages, extracted] at accepted
  | rejected e => simp [sourceStages, extracted] at accepted
  | conflict l r => simp [sourceStages, extracted] at accepted
  | known view =>
      have stages : stagesFromView view = .known out := by simpa only [sourceStages, extracted] using accepted
      have same := (accepted_view_binds_both_actual_payments view out stages).1
      exact ⟨by simpa only [same] using extracted, by simpa only [same] using stages⟩

theorem successful_source_stages_conserve (material : MaterialSnapshot) (branch : Nat)
    (catalog : List InterpretationRow) (out : SourceFrame)
    (accepted : sourceStages material branch catalog = .known out) :
    Ledger.balance out.stages.afterSecond.state =
      max (out.first.relation.value.amount.value -
        (out.first.payment.value.payload.amount.value + out.second.payment.value.payload.amount.value)) 0 ∧
    Ledger.Conserves out.stages.afterSecond.state ∧ Ledger.CashConsistent out.stages.afterSecond.state ∧
    out.stages.afterSecond.quantity.item.amount = Ledger.balance out.stages.afterSecond.state := by
  have flow := public_consumer_reads_actual_extraction _ _ _ _ accepted
  have bindings := accepted_view_binds_both_actual_payments out.source out flow.2
  have firstChecks := (successful_binding_reads_actual_rows _ _ _ bindings.2.1).2
  have secondChecks := (successful_binding_reads_actual_rows _ _ _ bindings.2.2.1).2
  rcases firstChecks with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, amount, debtNonneg, payOne⟩
  rcases secondChecks with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, payTwo⟩
  have amountValue := congrArg Amount.value amount
  have nonneg : 0 ≤ out.first.relation.value.amount.value := by
    rw [amountValue]
    exact debtNonneg
  rw [bindings.2.2.2]
  have conserved := two_payments_balance_and_cash out.source out.first out.second
    out.formationSource out.formationRelation nonneg payOne payTwo
  refine ⟨conserved.1, conserved.2.1, conserved.2.2, ?_⟩
  apply scalar_and_item_projections_commute
  apply scalar_and_item_projections_commute
  simpa only [buildStages, formStage, initialStage, Ledger.balance] using amountValue.symm

-- A dependent tuple and independent local witnesses are equivalent by choice;
-- a common semantic fiber requires the additional, explicit base agreement.
theorem independent_local_witnesses_iff_tuple {I : Type} (W : I → Type)
    (P : (i : I) → W i → Prop) :
    (∀ i, ∃ w, P i w) ↔ ∃ ws : (i : I) → W i, ∀ i, P i (ws i) := by
  constructor
  · intro h; exact ⟨fun i => Classical.choose (h i), fun i => Classical.choose_spec (h i)⟩
  · rintro ⟨ws, h⟩ i; exact ⟨ws i, h i⟩

theorem compatible_fibers_compose_local_contracts {I B : Type} (W : I → Type)
    (projection : (i : I) → W i → B) (P : (i : I) → W i → Prop) (base : B)
    (fibers : ∀ i, ∃ w, projection i w = base ∧ P i w) :
    ∃ ws : (i : I) → W i, (∀ i, projection i (ws i) = base) ∧ ∀ i, P i (ws i) := by
  obtain ⟨ws, h⟩ := (independent_local_witnesses_iff_tuple W
    (fun i w => projection i w = base ∧ P i w)).mp fibers
  exact ⟨ws, fun i => (h i).1, fun i => (h i).2⟩

theorem nonempty_local_models_can_have_empty_common_fiber :
    (∃ _ : Unit, True) ∧ (∃ _ : Unit, True) ∧
      ¬ ∃ x y : Unit, (fun _ : Unit => (0 : Nat)) x = (fun _ : Unit => (1 : Nat)) y := by
  exact ⟨⟨(), trivial⟩, ⟨(), trivial⟩, by simp⟩

def modelOf {V R : Type} [DecidableEq R] (background : UnifiedModel V R) (frame : SourceFrame)
    (naturalAmount : Nat) : UnifiedModel V RelationId :=
  { norms := background.norms, atom := background.atom
    aaf := background.aaf, pol := background.pol, disputed := background.disputed
    hBaseConflictFree := background.hBaseConflictFree, round := background.round
    hPolicyClosed := background.hPolicyClosed, hBaseInGrounded := background.hBaseInGrounded
    evalDom := background.evalDom, candidate := background.candidate
    hAdmissibleNonempty := background.hAdmissibleNonempty, hCollapse := background.hCollapse
    ledger := frame.stages.beforeFormation.relations
    eventId := toString frame.formationSource.value
    relFormed := frame.formationRelation
    relObserved := frame.source.decoded.observed.value.2
    performEventId := toString frame.first.payment.value.payload.cashId.value
    obligor := toString frame.first.payment.value.payload.payer.value
    performAmount := naturalAmount
    env := background.env, ad := background.ad, hwf := background.hwf
    atDay := background.atDay, production := background.production
    hUnauthorized := background.hUnauthorized
    asOf := background.asOf, past := background.past
    future₁ := background.future₁, future₂ := background.future₂
    hFuture₁ := background.hFuture₁, hFuture₂ := background.hFuture₂, someLate := background.someLate
    weight := background.weight, truthAssessment := background.truthAssessment
    hWeightPos := background.hWeightPos, hWeightTotal := background.hWeightTotal
    contaminated := background.contaminated, observation := background.observation
    caseBurden := background.caseBurden, sanction := background.sanction }

def LegacyContracts {V : Type} (model : UnifiedModel V RelationId) : Prop :=
  UnifiedNonDegenerate ∧ UnifiedInterpretationPreserved V RelationId model ∧
    UnifiedChainCorrespondence V RelationId model ∧ UnifiedFiniteProcessComposition V RelationId model ∧
    UnifiedTimeAndUncertaintyPreserved V RelationId model

theorem fixed_background_preserves_exact_old_contracts {V R : Type} [DecidableEq R]
    (background : UnifiedModel V R) (frame : SourceFrame) (n : Nat) :
    LegacyContracts (modelOf background frame n) ∧
    (modelOf background frame n).candidate = background.candidate ∧
    (modelOf background frame n).norms = background.norms ∧
    (modelOf background frame n).weight = background.weight :=
  ⟨unified_legal_derivation_on_declared_fragment _, rfl, rfl, rfl⟩

theorem exact_nat_bridge_is_unique (amount : ℚ) (m n : Nat)
    (hm : (m : ℚ) = amount) (hn : (n : ℚ) = amount) : m = n := by
  exact_mod_cast hm.trans hn.symm

-- Strong same-case semantics has named decoders for EVERY declared layer.
-- Structural membership of the weak model does not produce these premises.
def StrongSameCase {I X : Type} (W : I → Type) (read : (i : I) → X → W i)
    (x : X) (layers : (i : I) → W i) : Prop := ∀ i, layers i = read i x

theorem same_case_projection_transfers_local_contracts {I X : Type} (W : I → Type)
    (read : (i : I) → X → W i) (P : (i : I) → W i → Prop)
    (x : X) (layers : (i : I) → W i) (same : StrongSameCase W read x layers)
    (localSound : ∀ i, P i (read i x)) : ∀ i, P i (layers i) := by
  intro i
  rw [same i]
  exact localSound i

theorem static_source_semantic_and_quantity_bridge (material : MaterialSnapshot) (branch : Nat)
    (catalog : List InterpretationRow) (out : SourceFrame)
    (mu : SourceRef → Option LegalObject)
    (resolveFaithful : ∀ view, extractView material branch catalog = .known view →
      ∀ ref obj, resolve view.decoded ref = .known obj → mu ref = some obj)
    (accepted : sourceStages material branch catalog = .known out) :
    mu out.source.decoded.observed.value.1 = some (.relation out.source.decoded.observed.value.2) ∧
    (recordOf out.source).key = out.source.decoded.record.value.key ∧
    out.stages.afterSecond = payStage out.stages.afterFirst out.second.payment.value.payload ∧
    SourceRepresentation20261027.quantityDenote
      (SourceRepresentation20261027.encodeQuantity out.stages.afterSecond.state.debt.amount) =
      some out.stages.afterSecond.state.debt.amount := by
  obtain ⟨extracted, staged⟩ := public_consumer_reads_actual_extraction _ _ _ _ accepted
  have bound := accepted_view_binds_both_actual_payments out.source out staged
  refine ⟨resolveFaithful _ extracted _ _ (extracted_observed_reference_resolves _ _ _ _ extracted),
    rfl, ?_, rfl⟩
  rw [bound.2.2.2]
  rfl

end JurisLean.Candidates.SourceStages20261027
