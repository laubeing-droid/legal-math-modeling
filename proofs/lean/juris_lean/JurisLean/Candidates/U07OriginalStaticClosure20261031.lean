import JurisLean.Candidates.U07_3FixedBindingAudit20261029

namespace JurisLean.Candidates.U07OriginalStaticClosure20261031

open JurisLean.Candidates.Final20261021
open JurisLean.Candidates.SourceCompilation20261027
open JurisLean.Candidates.SourceRepresentation20261027
open JurisLean.Candidates.SourceStages20261027
open JurisLean.Candidates.U07_2JointObject20261029
open JurisLean.Candidates.U07_3FixedBindingAudit20261029
open JurisLean.Seams

/--
Original 07.4 / L283: e : Unit → Bool maps the sole source point to false;
d : Bool → Unit forgets the Boolean. Then d ∘ e = id, but true has no
preimage under e and e (d true) ≠ true.
-/
theorem left_inverse_without_surjectivity_or_right_inverse :
    (∀ r : Unit,
      (fun _ : Bool => ()) ((fun _ : Unit => false) r) = r) ∧
    ¬ Function.Surjective (fun _ : Unit => false) ∧
    (fun _ : Unit => false) ((fun _ : Bool => ()) true) ≠ true := by
  refine ⟨?_, ?_, by decide⟩
  · intro r
    cases r
    rfl
  · intro surjective
    obtain ⟨r, preimageEq⟩ := surjective true
    cases preimageEq

/--
Original 07.8 / L299: one successful actual sourceModel output supplies
the joint object, the existing fixed-background contracts and four stages,
the actual selected record and interpreted first payment, and the exact
tagged quantity at its final stage.

catalogInterpreted is an explicit external semantic contract. This result
does not derive source truth or all background fields from raw materials.
The legacy Nat amount restriction is the existing sourceModel restriction.
-/
theorem actual_producer_joint_static_conditions
    {V R : Type} [DecidableEq R]
    (background : UnifiedModel V R)
    (material : MaterialSnapshot) (branch : Nat)
    (catalog : List InterpretationRow)
    (out : SourceFrame × UnifiedModel V RelationId)
    (objectMeaning :
      MaterialSnapshot → Nat → SourceRef → Option LegalObject)
    (paymentMeaning :
      MaterialSnapshot → Nat → Citation → PaymentPayload → Prop)
    (catalogInterpreted :
      ∀ row ∈ catalog,
        row.material = material →
        row.branch = branch →
        PayloadInterpretation objectMeaning paymentMeaning
          material branch row.decoded)
    (accepted :
      sourceModel background material branch catalog = .ok out) :
    ∃ x : JointObject,
      suppliedLayers out = jointLayers background x ∧
      JointContract background material branch catalog x ∧
      ∃ row ∈ catalog,
        row.material = material ∧
        row.branch = branch ∧
        row.decoded = out.1.source.decoded ∧
        (recordOf out.1.source).key =
          row.decoded.record.value.key ∧
        (recordOf out.1.source).claimedAmount =
          row.decoded.record.value.claimedAmount ∧
        (recordOf out.1.source).registered =
          row.decoded.record.value.registered ∧
        objectMeaning material branch
            out.1.source.decoded.observed.value.1 =
          some (.relation out.1.source.decoded.observed.value.2) ∧
        out.1.first.history.value =
          .payment out.1.first.history.citation.source
            out.1.first.payment.value.key ∧
        paymentMeaning material branch out.1.first.history.citation
          out.1.first.payment.value.payload ∧
        quantityDenote
            (encodeQuantity out.1.stages.afterSecond.state.debt.amount) =
          some out.1.stages.afterSecond.state.debt.amount := by
  obtain ⟨x, layers, joint⟩ :=
    actual_source_has_joint_object
      background material branch catalog out accepted
  obtain ⟨row, member, sameMaterial, sameBranch, sameDecoded,
      recordKey, recordAmount, recordRegistered,
      observedMeaning, actualHistory, actualPaymentMeaning⟩ :=
    actual_record_and_binding_interpretation
      background material branch catalog out
      objectMeaning paymentMeaning catalogInterpreted accepted
  exact ⟨x, layers, joint, row, member,
    sameMaterial, sameBranch, sameDecoded,
    recordKey, recordAmount, recordRegistered,
    observedMeaning, actualHistory, actualPaymentMeaning,
    all_rational_amounts_have_exact_tagged_encoding
      out.1.stages.afterSecond.state.debt.amount⟩

end JurisLean.Candidates.U07OriginalStaticClosure20261031
