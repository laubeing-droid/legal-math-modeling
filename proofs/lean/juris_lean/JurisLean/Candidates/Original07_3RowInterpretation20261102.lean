import JurisLean.Candidates.U07_3FixedBindingAudit20261029
import JurisLean.Seams.InstitutionalEffects

/-!
Original 07.3's remaining row-semantics bridge is conditional on an external
meaning for a fixed raw event.  This local string-reference row is not the
existing Nat-valued SourceRef, and its interpretation does not certify source
truth or add fields to the existing CaseRecord / ConsumedView.
-/

namespace JurisLean.Candidates.Original07_3RowInterpretation20261102

open JurisLean.Candidates.SourceCompilation20261027
open JurisLean.Candidates.U07_3FixedBindingAudit20261029
open JurisLean.Seams.InstitutionalEffects

inductive EventPayload where
  | formation (rel : JurisLean.Relation)
  | performance (obligor : String) (rel : JurisLean.Relation) (amount : Nat)

structure EventSourceRow where
  source : String
  sourceRef : String
  sourceOrder : Nat
  raw : JurisLean.Event
  payload : EventPayload

def rowSeam (row : EventSourceRow) : SeamEvent JurisLean.Relation :=
  match row.payload with
  | .formation rel => .formative row.raw.eventId rel
  | .performance obligor rel amount =>
      .performance row.raw.eventId obligor rel amount

def Interpretation
    (meaning : MaterialSnapshot → Nat → String → String → JurisLean.Event →
      Option EventPayload)
    (material : MaterialSnapshot) (branch : Nat) (row : EventSourceRow) : Prop :=
  meaning material branch row.source row.sourceRef row.raw = some row.payload

def semanticSeam
    (meaning : MaterialSnapshot → Nat → String → String → JurisLean.Event →
      Option EventPayload)
    (material : MaterialSnapshot) (branch : Nat) (row : EventSourceRow) :
    Option (SeamEvent JurisLean.Relation) :=
  (meaning material branch row.source row.sourceRef row.raw).map fun payload =>
    match payload with
    | .formation rel => .formative row.raw.eventId rel
    | .performance obligor rel amount =>
        .performance row.raw.eventId obligor rel amount

theorem interpretation_rowSeam
    (meaning : MaterialSnapshot → Nat → String → String → JurisLean.Event →
      Option EventPayload)
    (material : MaterialSnapshot) (branch : Nat) (row : EventSourceRow)
    (interpreted : Interpretation meaning material branch row) :
    semanticSeam meaning material branch row = some (rowSeam row) := by
  unfold semanticSeam Interpretation at *
  rw [interpreted]
  rfl

theorem same_raw_event_distinct_row_seams
    (material : MaterialSnapshot) (branch : Nat)
    (record : JurisLean.Seams.UnifiedNeedlesS0S1.CaseRecord) :
    ∃ (meaning : MaterialSnapshot → Nat → String → String → JurisLean.Event →
        Option EventPayload)
      (v0 v1 : JurisLean.Seams.UnifiedNeedlesS0S1.CaseRecord × EventSourceRow),
      v0.1 = v1.1 ∧
      v0.2.source = v1.2.source ∧
      v0.2.sourceRef = v1.2.sourceRef ∧
      v0.2.sourceOrder = v1.2.sourceOrder ∧
      v0.2.raw = v1.2.raw ∧
      v0.2.payload ≠ v1.2.payload ∧
      rowSeam v0.2 ≠ rowSeam v1.2 ∧
      Interpretation meaning material branch v0.2 ∧
      ¬ Interpretation meaning material branch v1.2 := by
  let raw : JurisLean.Event := ⟨"event", 0, "formation"⟩
  let rel0 : JurisLean.Relation :=
    ⟨"r0", [], "", []⟩
  let rel1 : JurisLean.Relation :=
    ⟨"r1", [], "", []⟩
  let row0 : EventSourceRow :=
    ⟨"source", "ref", 0, raw, .formation rel0⟩
  let row1 : EventSourceRow :=
    ⟨"source", "ref", 0, raw, .formation rel1⟩
  let meaning : MaterialSnapshot → Nat → String → String → JurisLean.Event →
      Option EventPayload :=
    fun _ _ _ _ _ => some (.formation rel0)
  have hrel : rel0 ≠ rel1 := by
    intro h
    have hid := congrArg JurisLean.Relation.relationId h
    simp [rel0, rel1] at hid
  have hpayload : row0.payload ≠ row1.payload := by
    intro h
    have hrel' := congrArg
      (fun payload => match payload with
        | EventPayload.formation rel => rel
        | EventPayload.performance _ rel _ => rel) h
    exact hrel hrel'
  have hseam : rowSeam row0 ≠ rowSeam row1 := by
    intro h
    have hrel' := congrArg
      (fun event : SeamEvent JurisLean.Relation =>
        match event with
        | .formative _ rel => rel
        | .terminating _ rel => rel
        | .performance _ _ rel _ => rel
        | .declaratory _ => rel0) h
    have heq : rel0 = rel1 := by
      simpa [rowSeam, row0, row1, raw] using hrel'
    exact hrel heq
  refine ⟨meaning, (record, row0), (record, row1), rfl, rfl, rfl, rfl, rfl,
    hpayload, hseam, ?_, ?_⟩
  · simp [Interpretation, meaning, row0, raw]
  · simp [Interpretation, meaning, row1, raw, hrel]

end JurisLean.Candidates.Original07_3RowInterpretation20261102
