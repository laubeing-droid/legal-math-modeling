import JurisLean.Candidates.SourceStages20261027
import JurisLean.Candidates.Final20261021.Representation

/-!
This witness is built only from a successful public `sourceModel` output.
`JointObject` is an ambient product type; the theorem does not claim every
pair is accepted. The background is frozen as `z`: C1 stays global, C3 keeps
its fixed game, and C4 keeps its old fork from the same ledger. The four actual
stages are separately chained so payment two consumes payment one's output.
This is not a real-source-faithfulness claim and adds no semantic premise.
-/

namespace JurisLean.Candidates.U07_2JointObject20261029

open JurisLean.Candidates.SourceStages20261027
open JurisLean.Candidates.SourceCompilation20261027
open JurisLean.Candidates.Final20261021
open JurisLean.Seams

abbrev JointObject := SourceFrame × Nat

def jointLayers {V R : Type} [DecidableEq R]
    (background : UnifiedModel V R) (x : JointObject) :
    ExtractedView × BoundPayment × BoundPayment × FourStages × UnifiedModel V RelationId :=
  (x.1.source, x.1.first, x.1.second,
    buildStages x.1.source x.1.first x.1.second x.1.formationSource x.1.formationRelation,
    modelOf background x.1 x.2)

def suppliedLayers {V : Type}
    (out : SourceFrame × UnifiedModel V RelationId) :
    ExtractedView × BoundPayment × BoundPayment × FourStages × UnifiedModel V RelationId :=
  (out.1.source, out.1.first, out.1.second, out.1.stages, out.2)

def JointContract {V R : Type} [DecidableEq R]
    (background : UnifiedModel V R) (material : MaterialSnapshot) (branch : Nat)
    (catalog : List InterpretationRow) (x : JointObject) : Prop :=
  let f := x.1
  let m := modelOf background f x.2
  (extractView material branch catalog = .known f.source ∧
    bindPayment f.source 1 = .known f.first ∧ bindPayment f.source 2 = .known f.second) ∧
  (f.stages = buildStages f.source f.first f.second f.formationSource f.formationRelation ∧
    (x.2 : ℚ) = f.first.payment.value.payload.amount.value) ∧
  LegacyContracts m ∧
  (m.ledger = f.stages.beforeFormation.relations ∧
    m.eventId = toString f.formationSource.value ∧ m.relFormed = f.formationRelation ∧
    m.relObserved = f.source.decoded.observed.value.2 ∧
    m.performEventId = toString f.first.payment.value.payload.cashId.value ∧
    m.obligor = toString f.first.payment.value.payload.payer.value ∧
    m.performAmount = x.2) ∧
  (m.norms = background.norms ∧ m.candidate = background.candidate ∧
    m.weight = background.weight) ∧
  (f.stages.afterFormation = formStage f.stages.beforeFormation f.formationSource f.formationRelation ∧
    f.stages.afterFirst = payStage f.stages.afterFormation f.first.payment.value.payload ∧
    f.stages.afterSecond = payStage f.stages.afterFirst f.second.payment.value.payload ∧
    f.stages.afterFirst.relations = f.stages.afterFormation.relations ∧
    f.stages.afterSecond.relations = f.stages.afterFirst.relations) ∧
  (Ledger.balance f.stages.afterSecond.state =
      max (f.first.relation.value.amount.value -
        (f.first.payment.value.payload.amount.value + f.second.payment.value.payload.amount.value)) 0 ∧
    Ledger.Conserves f.stages.afterSecond.state ∧ Ledger.CashConsistent f.stages.afterSecond.state ∧
    f.stages.afterSecond.quantity.item.amount = Ledger.balance f.stages.afterSecond.state)

theorem actual_source_has_joint_object {V R : Type} [DecidableEq R]
    (background : UnifiedModel V R) (material : MaterialSnapshot) (branch : Nat)
    (catalog : List InterpretationRow) (out : SourceFrame × UnifiedModel V RelationId)
    (accepted : sourceModel background material branch catalog = .ok out) :
    ∃ x : JointObject, suppliedLayers out = jointLayers background x ∧
      JointContract background material branch catalog x := by
  have producerFacts := public_model_consumes_the_actual_stage_frame
    background material branch catalog out accepted
  have extracted := public_consumer_reads_actual_extraction
    material branch catalog out.1 producerFacts.1
  have bound := accepted_view_binds_both_actual_payments out.1.source out.1 extracted.2
  have conserved := successful_source_stages_conserve material branch catalog out.1 producerFacts.1
  have checked := producerFacts.2.1
  cases amount : legacyAmount out.1 with
  | unknown e => simp [checkedModel, amount] at checked
  | rejected e => simp [checkedModel, amount] at checked
  | conflict l r => simp [checkedModel, amount] at checked
  | known n =>
      have modelEq : modelOf background out.1 n = out.2 := by
        simpa only [checkedModel, amount, Except.ok.injEq] using checked
      refine ⟨(out.1, n), ?_, ?_⟩
      · simp [suppliedLayers, jointLayers, modelEq, bound.2.2.2]
      · dsimp [JointContract]
        refine ⟨⟨extracted.1, bound.2.1, bound.2.2.1⟩,
          ⟨bound.2.2.2, legacy_amount_success_is_exact _ _ amount⟩,
          (fixed_background_preserves_exact_old_contracts background out.1 n).1,
          ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
          ⟨rfl, rfl, rfl⟩, ?_, conserved⟩
        have stages := four_stages_use_actual_previous_output out.1.source out.1.first out.1.second
          out.1.formationSource out.1.formationRelation
        simpa only [bound.2.2.2] using stages

end JurisLean.Candidates.U07_2JointObject20261029

#check JurisLean.Candidates.U07_2JointObject20261029.actual_source_has_joint_object
#print axioms JurisLean.Candidates.U07_2JointObject20261029.actual_source_has_joint_object
#check JurisLean.Candidates.Final20261021.Representation.u07_2_common_fiber_nonempty
#print axioms JurisLean.Candidates.Final20261021.Representation.u07_2_common_fiber_nonempty
#check JurisLean.Candidates.Final20261021.Representation.n07_2_incompatible_fiber
#print axioms JurisLean.Candidates.Final20261021.Representation.n07_2_incompatible_fiber
#check JurisLean.Candidates.SourceStages20261027.public_model_consumes_the_actual_stage_frame
#print axioms JurisLean.Candidates.SourceStages20261027.public_model_consumes_the_actual_stage_frame
#check JurisLean.Candidates.SourceStages20261027.four_stages_use_actual_previous_output
#print axioms JurisLean.Candidates.SourceStages20261027.four_stages_use_actual_previous_output
#check JurisLean.Candidates.SourceStages20261027.successful_source_stages_conserve
#print axioms JurisLean.Candidates.SourceStages20261027.successful_source_stages_conserve
#check JurisLean.Seams.unified_legal_derivation_on_declared_fragment
#print axioms JurisLean.Seams.unified_legal_derivation_on_declared_fragment
