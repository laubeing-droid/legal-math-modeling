import JurisLean.Candidates.U07_2JointObject20261029

namespace JurisLean.Candidates.U07_3FixedBindingAudit20261029

open JurisLean.Candidates.SourceStages20261027
open JurisLean.Candidates.SourceCompilation20261027
open JurisLean.Candidates.U07_2JointObject20261029
open JurisLean.Candidates.Final20261021
open JurisLean.Seams

-- The fixed-binding result below is limited to the projections named in
-- frozen U07.3; it is not a claim about source truth or arbitrary extractors.
def paymentFields {V : Type} (m : UnifiedModel V RelationId) : String × String × Nat :=
  (m.performEventId, m.obligor, m.performAmount)

theorem fixed_binding_model_projection_unique {V R : Type} [DecidableEq R]
    (background : UnifiedModel V R) (view : ExtractedView) (index : Nat)
    (left right : SourceFrame) (nL nR : Nat)
    (hl : bindPayment view index = .known left.first)
    (hr : bindPayment view index = .known right.first)
    (el : (nL : ℚ) = left.first.payment.value.payload.amount.value)
    (er : (nR : ℚ) = right.first.payment.value.payload.amount.value) :
    paymentFields (modelOf background left nL) =
      paymentFields (modelOf background right nR) := by
  have sameBinding := deterministic_binding_data_unique view index left.first right.first hl hr
  have rightOnLeft := er
  rw [← sameBinding] at rightOnLeft
  have sameAmount :=
    exact_nat_bridge_is_unique left.first.payment.value.payload.amount.value nL nR el rightOnLeft
  change
    (toString left.first.payment.value.payload.cashId.value,
      toString left.first.payment.value.payload.payer.value, nL) =
    (toString right.first.payment.value.payload.cashId.value,
      toString right.first.payment.value.payload.payer.value, nR)
  rw [sameBinding, sameAmount]

-- These are genuine UnifiedModel field-loss witnesses, not successful
-- source bindings after changing the payload.
theorem amount_does_not_identify_payment_fields {V : Type}
    (seed : UnifiedModel V RelationId) :
    let a : UnifiedModel V RelationId :=
      {seed with performEventId := "1", obligor := "1", performAmount := 7}
    let b : UnifiedModel V RelationId := {a with performEventId := "2"}
    let c : UnifiedModel V RelationId := {a with obligor := "2"}
    (paymentFields a).2.2 = (paymentFields b).2.2 ∧
      (paymentFields a).1 ≠ (paymentFields b).1 ∧
      (paymentFields a).2.2 = (paymentFields c).2.2 ∧
      (paymentFields a).2.1 ≠ (paymentFields c).2.1 := by
  change (7 : Nat) = 7 ∧ ("1" : String) ≠ "2" ∧
    (7 : Nat) = 7 ∧ ("1" : String) ≠ "2"
  decide

-- Exercise the frozen Representation boundary: annotation is not payload,
-- while a mismatched case or absent history index produces UNKNOWN.
theorem fixed_binding_boundary_examples (gamma : Gamma) (payment : PaymentPayload) :
    let p : PaymentPayload := {payment with caseId := ⟨0⟩}
    let v : JurisLean.Candidates.Final20261021.Representation.SourceView :=
      {gamma := {gamma with caseId := ⟨0⟩, caseRevision := p.caseRevision},
       history := [.performance p],
       objectMap := [(p.source, .relation p.relation)],
       observedRef := p.source,
       observedRelation := p.relation}
    let a : JurisLean.Candidates.Final20261021.Representation.PaymentRow := ⟨p, "note-a"⟩
    let b : JurisLean.Candidates.Final20261021.Representation.PaymentRow := ⟨p, "note-b"⟩
    JurisLean.Candidates.Final20261021.Representation.proposed_common_model v 0 = .known p ∧
      JurisLean.Candidates.Final20261021.Representation.proposed_binding v 0 "note-a" = some a ∧
      JurisLean.Candidates.Final20261021.Representation.proposed_binding v 0 "note-b" = some b ∧
      a.payload = b.payload ∧
      a ≠ b ∧
      JurisLean.Candidates.Final20261021.Representation.proposed_common_model
        {v with gamma := {v.gamma with caseId := ⟨1⟩}} 0 = .unknown .identityUnknown ∧
      JurisLean.Candidates.Final20261021.Representation.proposed_common_model v 1 =
        .unknown .identityUnknown := by
  simp [JurisLean.Candidates.Final20261021.Representation.proposed_common_model,
    JurisLean.Candidates.Final20261021.Representation.proposed_source_view,
    JurisLean.Candidates.Final20261021.Representation.proposed_binding,
    JurisLean.Candidates.Final20261021.Representation.selectedPayload]

-- Interpretations are explicit external reader outputs tied to this material and
-- branch. This covers only the consumed object and complete payment payload
-- components; it does not assert source truth or arbitrary extractor fidelity.
def PayloadInterpretation
    (objectMeaning : MaterialSnapshot → Nat → SourceRef → Option LegalObject)
    (paymentMeaning : MaterialSnapshot → Nat → Citation → PaymentPayload → Prop)
    (material : MaterialSnapshot) (branch : Nat) (decoded : ConsumedView) : Prop :=
  (∀ q ∈ decoded.objects, objectMeaning material branch q.value.1 = some q.value.2) ∧
  (∀ q ∈ decoded.payments, paymentMeaning material branch q.citation q.value.payload)

theorem actual_record_and_binding_interpretation {V R : Type} [DecidableEq R]
    (background : UnifiedModel V R) (material : MaterialSnapshot) (branch : Nat)
    (catalog : List InterpretationRow)
    (out : SourceFrame × UnifiedModel V RelationId)
    (objectMeaning : MaterialSnapshot → Nat → SourceRef → Option LegalObject)
    (paymentMeaning : MaterialSnapshot → Nat → Citation → PaymentPayload → Prop)
    (catalogInterpreted : ∀ row ∈ catalog, row.material = material → row.branch = branch →
      PayloadInterpretation objectMeaning paymentMeaning material branch row.decoded)
    (accepted : sourceModel background material branch catalog = .ok out) :
    ∃ row ∈ catalog, row.material = material ∧ row.branch = branch ∧
      row.decoded = out.1.source.decoded ∧
      (recordOf out.1.source).key = row.decoded.record.value.key ∧
      (recordOf out.1.source).claimedAmount = row.decoded.record.value.claimedAmount ∧
      (recordOf out.1.source).registered = row.decoded.record.value.registered ∧
      objectMeaning material branch out.1.source.decoded.observed.value.1 =
        some (.relation out.1.source.decoded.observed.value.2) ∧
      out.1.first.history.value = .payment out.1.first.history.citation.source out.1.first.payment.value.key ∧
      paymentMeaning material branch out.1.first.history.citation
        out.1.first.payment.value.payload := by
  have resolveMeaning : ∀ (view : ExtractedView),
      extractView material branch catalog = .known view →
      ∀ (ref : SourceRef) (obj : LegalObject),
        resolve view.decoded ref = .known obj →
        objectMeaning material branch ref = some obj := by
    intro view extracted ref obj resolved
    obtain ⟨_, _, _, row, rowIn, rowMaterial, rowBranch, rowPayload⟩ :=
      extracted_view_is_exact_selected_payload material branch catalog view extracted
    have interp : PayloadInterpretation objectMeaning paymentMeaning material branch view.decoded := by
      simpa only [rowPayload] using (catalogInterpreted row rowIn rowMaterial rowBranch)
    have member : obj ∈
        (view.decoded.objects.filter (fun q => decide (q.value.1 = ref))).map
          (fun q => q.value.2) := by
      dsimp only [resolve] at resolved
      generalize valuesEq :
        (view.decoded.objects.filter (fun q => decide (q.value.1 = ref))).map
          (fun q => q.value.2) = values at resolved
      cases values with
      | nil => cases resolved
      | cons a tail =>
        cases tail with
        | nil =>
          cases resolved
          simp
        | cons b more => cases resolved
    obtain ⟨entry, entryIn, entryObj⟩ := List.mem_map.mp member
    have entryInfo := List.mem_filter.mp entryIn
    have entryRef : entry.value.1 = ref := by
      simpa only [decide_eq_true_eq] using entryInfo.2
    simpa only [entryRef, entryObj] using (interp.1 entry entryInfo.1)
  have candidateMember : ∀ (view : ExtractedView) (index : Nat) (bound : BoundPayment),
      candidatePayment view index = some bound → bound.payment ∈ view.decoded.payments := by
    intro view index bound selected
    cases hHistory : view.decoded.historyEvents[index]? with
    | none => simp [candidatePayment, hHistory] at selected
    | some history =>
      cases hValue : history.value with
      | formation source relationId =>
        simp [candidatePayment, hHistory, hValue] at selected
      | payment source key =>
        cases hPay : view.decoded.payments.find? (fun p => p.value.key == key) with
        | none => simp [candidatePayment, hHistory, hValue, hPay] at selected
        | some paymentRow =>
          cases hDebt : view.decoded.ledger.find?
              (fun d => d.value.item.ident == paymentRow.value.targetDebt) with
          | none => simp [candidatePayment, hHistory, hValue, hPay, hDebt] at selected
          | some debtRow =>
            cases hRelation : view.decoded.relations.find?
                (fun r => r.value.relation == debtRow.value.debtRel) with
            | none =>
              simp [candidatePayment, hHistory, hValue, hPay, hDebt, hRelation] at selected
            | some relationRow =>
              have outEq : (⟨history, paymentRow, debtRow, relationRow⟩ : BoundPayment) = bound := by
                simpa [candidatePayment, hHistory, hValue, hPay, hDebt, hRelation] using selected
              have paymentEq : paymentRow = bound.payment := congrArg BoundPayment.payment outEq
              exact paymentEq ▸ (List.mem_of_find?_eq_some hPay)
  have producerFacts := public_model_consumes_the_actual_stage_frame
    background material branch catalog out accepted
  have extracted := public_consumer_reads_actual_extraction
    material branch catalog out.1 producerFacts.1
  obtain ⟨_, _, _, row, rowIn, rowMaterial, rowBranch, rowPayload⟩ :=
    extracted_view_is_exact_selected_payload material branch catalog out.1.source extracted.1
  have interp : PayloadInterpretation objectMeaning paymentMeaning material branch out.1.source.decoded := by
    simpa only [rowPayload] using (catalogInterpreted row rowIn rowMaterial rowBranch)
  have semantic := static_source_semantic_and_quantity_bridge
    material branch catalog out.1 (objectMeaning material branch) resolveMeaning producerFacts.1
  have bound := accepted_view_binds_both_actual_payments out.1.source out.1 extracted.2
  have firstFacts := successful_binding_reads_actual_rows out.1.source 1 out.1.first bound.2.1
  have firstIn := candidateMember out.1.source 1 out.1.first firstFacts.1
  have firstChecks := firstFacts.2
  have sameCitation : out.1.first.history.citation = out.1.first.payment.citation :=
    firstChecks.2.2.2.2.1
  refine ⟨row, rowIn, rowMaterial, rowBranch, rowPayload, ?_, ?_, ?_, semantic.1, ?_, ?_⟩
  · simp only [recordOf, rowPayload]
  · simp only [recordOf, rowPayload]
  · simp only [recordOf, rowPayload]
  · exact firstChecks.2.2.2.1
  · rw [sameCitation]
    exact interp.2 out.1.first.payment firstIn

-- For a fixed background and reader, two successful outputs share the actual
-- extracted view and therefore the actual first-payment binding; the legacy
-- amount casts come from the accepted sourceModel contracts.
theorem actual_source_model_projection_unique {V R : Type} [DecidableEq R]
    (background : UnifiedModel V R) (material : MaterialSnapshot) (branch : Nat)
    (catalog : List InterpretationRow)
    (outL outR : SourceFrame × UnifiedModel V RelationId)
    (acceptedL : sourceModel background material branch catalog = .ok outL)
    (acceptedR : sourceModel background material branch catalog = .ok outR) :
    paymentFields outL.2 = paymentFields outR.2 := by
  obtain ⟨xL, layersL, contractL⟩ :=
    actual_source_has_joint_object background material branch catalog outL acceptedL
  obtain ⟨xR, layersR, contractR⟩ :=
    actual_source_has_joint_object background material branch catalog outR acceptedR
  have frameSourceL : outL.1.source = xL.1.source := by
    have h := congrArg (fun z => z.1) layersL
    simpa only [suppliedLayers, jointLayers] using h
  have frameSourceR : outR.1.source = xR.1.source := by
    have h := congrArg (fun z => z.1) layersR
    simpa only [suppliedLayers, jointLayers] using h
  have jointSource : xL.1.source = xR.1.source :=
    Result.known.inj (contractL.1.1.symm.trans contractR.1.1)
  have sameSource : outL.1.source = outR.1.source :=
    frameSourceL.trans (jointSource.trans frameSourceR.symm)
  have bindL : bindPayment outL.1.source 1 = .known xL.1.first := by
    rw [frameSourceL]
    exact contractL.1.2.1
  have bindR : bindPayment outL.1.source 1 = .known xR.1.first := by
    rw [sameSource, frameSourceR]
    exact contractR.1.2.1
  have castL : (xL.2 : ℚ) = xL.1.first.payment.value.payload.amount.value :=
    contractL.2.1.2
  have castR : (xR.2 : ℚ) = xR.1.first.payment.value.payload.amount.value :=
    contractR.2.1.2
  have modelL : outL.2 = modelOf background xL.1 xL.2 := by
    have h := congrArg (fun z => z.2.2.2.2) layersL
    simpa only [suppliedLayers, jointLayers] using h
  have modelR : outR.2 = modelOf background xR.1 xR.2 := by
    have h := congrArg (fun z => z.2.2.2.2) layersR
    simpa only [suppliedLayers, jointLayers] using h
  rw [modelL, modelR]
  exact fixed_binding_model_projection_unique background outL.1.source 1
    xL.1 xR.1 xL.2 xR.2 bindL bindR castL castR


-- The two catalogs share the exact same material and CaseRecord, but encode
-- different payload interpretations for the same cited source fragment. The
-- reader functions remain explicit external inputs; this does not certify them
-- as true readings of a real source.
theorem same_material_record_do_not_determine_semantics (gamma : Gamma)
    (record : JurisLean.Seams.UnifiedNeedlesS0S1.CaseRecord) (payment : FullPayment) :
    ∃ (s : MaterialSnapshot) (v0 v1 : ExtractedView) (cat0 cat1 : List InterpretationRow)
      (objectMeaning : MaterialSnapshot → Nat → SourceRef → Option LegalObject)
      (paymentMeaning : MaterialSnapshot → Nat → Citation → PaymentPayload → Prop),
      v0.material = s ∧ v1.material = s ∧
      extractView s 0 cat0 = .known v0 ∧ extractView s 0 cat1 = .known v1 ∧
      extractView s 0 (cat0 ++ cat1) = .conflict 0 2 ∧
      recordOf v0 = recordOf v1 ∧
      v0.decoded.payments.map (fun q => q.value.payload) ≠
        v1.decoded.payments.map (fun q => q.value.payload) ∧
      PayloadInterpretation objectMeaning paymentMeaning s 0 v0.decoded ∧
      ¬ PayloadInterpretation objectMeaning paymentMeaning s 0 v1.decoded ∧
      objectMeaning s 0 v1.decoded.observed.value.1 ≠
        some (.relation v1.decoded.observed.value.2) := by
  let ref0 : SourceRef := ⟨0⟩
  let rel0 : RelationId := ⟨0⟩
  let rel1 : RelationId := ⟨1⟩
  let party0 : PartyId := ⟨0⟩
  let party1 : PartyId := ⟨1⟩
  let event0 : EventId := ⟨0⟩
  let event1 : EventId := ⟨1⟩
  let c : Citation := ⟨ref0, 0, 0, 0⟩
  let fragment : Fragment := ⟨ref0, 0, 0, "one source"⟩
  let s : MaterialSnapshot := ⟨gamma, 0, 0, [fragment]⟩
  let p0 : FullPayment :=
    {payment with payload :=
      {payment.payload with
        caseId := gamma.caseId
        caseRevision := gamma.caseRevision
        source := ref0
        relation := rel0
        cashId := event0
        payer := party0}}
  let p1 : FullPayment :=
    {p0 with payload :=
      {p0.payload with
        relation := rel1
        cashId := event1
        payer := party1}}
  let decoded0 : ConsumedView :=
    ⟨⟨c, record⟩, [], [], [⟨c, p0⟩], [], [],
      [⟨c, (ref0, LegalObject.relation rel0)⟩], ⟨c, (ref0, rel0)⟩, []⟩
  let decoded1 : ConsumedView :=
    ⟨⟨c, record⟩, [], [], [⟨c, p1⟩], [], [],
      [⟨c, (ref0, LegalObject.relation rel1)⟩], ⟨c, (ref0, rel1)⟩, []⟩
  let row0 : InterpretationRow := ⟨s, 0, decoded0⟩
  let row1 : InterpretationRow := ⟨s, 0, decoded1⟩
  let objectMeaning : MaterialSnapshot → Nat → SourceRef → Option LegalObject :=
    fun m b r => if m = s ∧ b = 0 ∧ r = ref0 then some (.relation rel0) else none
  let paymentMeaning : MaterialSnapshot → Nat → Citation → PaymentPayload → Prop :=
    fun m b cite payload => m = s ∧ b = 0 ∧ cite = c ∧ payload = p0.payload
  have h0 : extractView s 0 [row0] = .known ⟨s, 0, decoded0⟩ := by
    simp [extractView, matchingRows, viewChecks, citations, citationPresent, resolve,
      s, fragment, c, ref0, rel0, p0, decoded0, row0]
  have h1 : extractView s 0 [row1] = .known ⟨s, 0, decoded1⟩ := by
    simp [extractView, matchingRows, viewChecks, citations, citationPresent, resolve,
      s, fragment, c, ref0, rel1, p0, p1, decoded1, row1]
  have hBoth : extractView s 0 [row0, row1] = .conflict 0 2 := by
    simp [extractView, matchingRows, s, fragment, row0, row1]
  have hPay : p0.payload ≠ p1.payload := by
    intro h
    have bad := congrArg (fun p : PaymentPayload => p.cashId.value) h
    change (0 : Nat) = 1 at bad
    cases bad
  have hInterpret0 : PayloadInterpretation objectMeaning paymentMeaning s 0 decoded0 := by
    simp [PayloadInterpretation, objectMeaning, paymentMeaning, s, ref0, rel0, c, p0, decoded0]
  have hNotInterpret1 :
      ¬ PayloadInterpretation objectMeaning paymentMeaning s 0 decoded1 := by
    intro h
    have hm := h.1 ⟨c, (ref0, LegalObject.relation rel1)⟩ (by simp [decoded1])
    simp [objectMeaning, s, ref0, rel0, rel1] at hm
  have hMuBad :
      objectMeaning s 0 decoded1.observed.value.1 ≠
        some (.relation decoded1.observed.value.2) := by
    simp [objectMeaning, s, ref0, rel0, rel1, decoded1]
  refine ⟨s, ⟨s, 0, decoded0⟩, ⟨s, 0, decoded1⟩, [row0], [row1],
    objectMeaning, paymentMeaning, rfl, rfl, h0, h1, ?_, rfl, ?_,
    hInterpret0, hNotInterpret1, hMuBad⟩
  · exact hBoth
  · intro same
    exact hPay (List.cons.inj same).1


end JurisLean.Candidates.U07_3FixedBindingAudit20261029
#check JurisLean.Candidates.U07_3FixedBindingAudit20261029.fixed_binding_model_projection_unique
#print axioms JurisLean.Candidates.U07_3FixedBindingAudit20261029.fixed_binding_model_projection_unique
#check JurisLean.Candidates.U07_3FixedBindingAudit20261029.amount_does_not_identify_payment_fields
#print axioms JurisLean.Candidates.U07_3FixedBindingAudit20261029.amount_does_not_identify_payment_fields
#check JurisLean.Candidates.U07_3FixedBindingAudit20261029.fixed_binding_boundary_examples
#print axioms JurisLean.Candidates.U07_3FixedBindingAudit20261029.fixed_binding_boundary_examples
#check JurisLean.Candidates.U07_3FixedBindingAudit20261029.actual_record_and_binding_interpretation
#print axioms JurisLean.Candidates.U07_3FixedBindingAudit20261029.actual_record_and_binding_interpretation
#check JurisLean.Candidates.U07_3FixedBindingAudit20261029.actual_source_model_projection_unique
#print axioms JurisLean.Candidates.U07_3FixedBindingAudit20261029.actual_source_model_projection_unique
#check JurisLean.Candidates.U07_3FixedBindingAudit20261029.same_material_record_do_not_determine_semantics
#print axioms JurisLean.Candidates.U07_3FixedBindingAudit20261029.same_material_record_do_not_determine_semantics
#check JurisLean.Candidates.Final20261021.Representation.u07_3_projection_unique_under_fixed_binding
#print axioms JurisLean.Candidates.Final20261021.Representation.u07_3_projection_unique_under_fixed_binding
#check JurisLean.Candidates.SourceStages20261027.deterministic_binding_data_unique
#print axioms JurisLean.Candidates.SourceStages20261027.deterministic_binding_data_unique
#check JurisLean.Candidates.SourceStages20261027.exact_nat_bridge_is_unique
#print axioms JurisLean.Candidates.SourceStages20261027.exact_nat_bridge_is_unique
#check JurisLean.Candidates.U07_2JointObject20261029.actual_source_has_joint_object
#print axioms JurisLean.Candidates.U07_2JointObject20261029.actual_source_has_joint_object
#check JurisLean.Candidates.SourceStages20261027.static_source_semantic_and_quantity_bridge
#print axioms JurisLean.Candidates.SourceStages20261027.static_source_semantic_and_quantity_bridge
#check JurisLean.Candidates.SourceCompilation20261027.extracted_view_is_exact_selected_payload
#print axioms JurisLean.Candidates.SourceCompilation20261027.extracted_view_is_exact_selected_payload
