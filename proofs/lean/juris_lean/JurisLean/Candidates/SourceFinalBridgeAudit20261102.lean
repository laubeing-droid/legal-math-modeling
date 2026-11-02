import JurisLean.Candidates.SourceStagesAudit20261027
import JurisLean.Candidates.SourceRepresentationAudit20261027
import JurisLean.Candidates.U07_2JointObject20261029

/-!
Frozen original 07.8 L299 needs one same-output static theorem and a joint
nonempty witness. Quantity syntax, exact tagged encoding, the legacy half
counterexample and the actual common-object construction are reused.
D is Final20261021.Amount; encodeQty is encodeQuantity into RationalQty.
readAmount is Amount.value and unit is the unit selector of Amount.tag.
The pair readout below is Option.map of these selectors; the full Amount
roundtrip retains currency, unit and ruleVersion.
-/

namespace JurisLean.Candidates.SourceFinalBridge20261102

open JurisLean.Candidates.Final20261021
open JurisLean.Candidates.SourceCompilation20261027
open JurisLean.Candidates.SourceStages20261027
open JurisLean.Candidates.U07_2JointObject20261029
open JurisLean.Seams

theorem source_model_joint_semantic_quantity {V R : Type} [DecidableEq R]
    (background : UnifiedModel V R) (material : MaterialSnapshot) (branch : Nat)
    (catalog : List InterpretationRow) (out : SourceFrame × UnifiedModel V RelationId)
    (mu : SourceRef → Option LegalObject)
    (resolveFaithful : ∀ view, extractView material branch catalog = .known view →
      ∀ ref obj, resolve view.decoded ref = .known obj → mu ref = some obj)
    (accepted : sourceModel background material branch catalog = .ok out) :
    (∃ x : JointObject, suppliedLayers out = jointLayers background x ∧
      JointContract background material branch catalog x) ∧
    extractView material branch catalog = .known out.1.source ∧
    mu out.1.source.decoded.observed.value.1 =
      some (.relation out.1.source.decoded.observed.value.2) ∧
    recordOf out.1.source = out.1.source.decoded.record.value ∧
    out.1.stages.afterSecond =
      payStage out.1.stages.afterFirst out.1.second.payment.value.payload ∧
    SourceRepresentation20261027.quantityDenote
      (SourceRepresentation20261027.encodeQuantity out.1.stages.afterSecond.state.debt.amount) =
      some out.1.stages.afterSecond.state.debt.amount ∧
    (SourceRepresentation20261027.quantityDenote
      (SourceRepresentation20261027.encodeQuantity out.1.stages.afterSecond.state.debt.amount)).map
      (fun amount => (amount.value, amount.tag.unit)) =
      some (out.1.stages.afterSecond.state.debt.amount.value,
        out.1.stages.afterSecond.state.debt.amount.tag.unit) := by
  have staged := (public_model_consumes_the_actual_stage_frame
    background material branch catalog out accepted).1
  have extracted := public_consumer_reads_actual_extraction
    material branch catalog out.1 staged
  have semantic := static_source_semantic_and_quantity_bridge
    material branch catalog out.1 mu resolveFaithful staged
  refine ⟨actual_source_has_joint_object background material branch catalog out accepted,
    extracted.1, semantic.1, rfl, semantic.2.2.1, semantic.2.2.2, ?_⟩
  exact congrArg
    (fun result : Option Amount => result.map (fun amount => (amount.value, amount.tag.unit)))
    semantic.2.2.2

theorem source_model_joint_bridge_nonempty_and_faithfulness_needed :
    ∃ out (mu : SourceRef → Option LegalObject),
      sourceModel JurisLean.Seams.UnifiedInstance.instanceM
        stageMaterial 0 [⟨stageMaterial, 0, stageView⟩] = .ok out ∧
      (∀ view, extractView stageMaterial 0 [⟨stageMaterial, 0, stageView⟩] = .known view →
        ∀ ref obj, resolve view.decoded ref = .known obj → mu ref = some obj) ∧
      (∃ x : JointObject,
        suppliedLayers out = jointLayers JurisLean.Seams.UnifiedInstance.instanceM x ∧
        JointContract JurisLean.Seams.UnifiedInstance.instanceM
          stageMaterial 0 [⟨stageMaterial, 0, stageView⟩] x) ∧
      (fun _ : SourceRef => (none : Option LegalObject))
          out.1.source.decoded.observed.value.1 ≠
        some (.relation out.1.source.decoded.observed.value.2) := by
  obtain ⟨frame, staged⟩ := nonempty_source_stage_fixture
  have naturalGuard :
      (match runStageView stageView with
      | .known value =>
          match legacyAmount value with
          | .known _ => true
          | _ => false
      | _ => false) = true := by
    decide +kernel
  rw [staged] at naturalGuard
  obtain ⟨n, natural⟩ : ∃ n, legacyAmount frame = .known n := by
    cases computed : legacyAmount frame with
    | known n => exact ⟨n, rfl⟩
    | unknown e => simp [computed] at naturalGuard
    | rejected e => simp [computed] at naturalGuard
    | conflict l r => simp [computed] at naturalGuard
  have stagedPublic :
      sourceStages stageMaterial 0 [⟨stageMaterial, 0, stageView⟩] = .known frame := staged
  let model := modelOf JurisLean.Seams.UnifiedInstance.instanceM frame n
  let out := (frame, model)
  have accepted :
      sourceModel JurisLean.Seams.UnifiedInstance.instanceM
        stageMaterial 0 [⟨stageMaterial, 0, stageView⟩] = .ok out := by
    simp [sourceModel, stagedPublic, checkedModel, natural, out, model]
  have extracted := (public_consumer_reads_actual_extraction
    stageMaterial 0 [⟨stageMaterial, 0, stageView⟩] frame stagedPublic).1
  let mu : SourceRef → Option LegalObject := fun ref =>
    match resolve frame.source.decoded ref with
    | .known obj => some obj
    | _ => none
  have faithful :
      ∀ view, extractView stageMaterial 0 [⟨stageMaterial, 0, stageView⟩] = .known view →
        ∀ ref obj, resolve view.decoded ref = .known obj → mu ref = some obj := by
    intro view hasView ref obj hasResolution
    have same : view = frame.source :=
      Result.known.inj (hasView.symm.trans extracted)
    subst view
    simp [mu, hasResolution]
  refine ⟨out, mu, accepted, faithful, ?_, ?_⟩
  · exact actual_source_has_joint_object JurisLean.Seams.UnifiedInstance.instanceM
      stageMaterial 0 [⟨stageMaterial, 0, stageView⟩] out accepted
  · simp

end JurisLean.Candidates.SourceFinalBridge20261102

#check JurisLean.Candidates.SourceFinalBridge20261102.source_model_joint_semantic_quantity
#print axioms JurisLean.Candidates.SourceFinalBridge20261102.source_model_joint_semantic_quantity
#check JurisLean.Candidates.SourceFinalBridge20261102.source_model_joint_bridge_nonempty_and_faithfulness_needed
#print axioms JurisLean.Candidates.SourceFinalBridge20261102.source_model_joint_bridge_nonempty_and_faithfulness_needed
