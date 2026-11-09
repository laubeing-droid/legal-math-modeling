import JurisLean.Review20261110.BusinessTransport
import JurisLean.CN.Completion20261105.Execution
import JurisLean.Candidates.U00MeasuredRSIEntry20261031

/-!
Lossless operation logs and event/measurement/record identities are distinct.
The v4 reports relation may be empty or multivalued; no event is manufactured
from a material record. Source only; CI_NOT_RUN until subject-bound evidence.
-/
namespace LegalMath.RemainingClosure.FullEventLog

namespace Tokens
open LegalMath20261110.OccurrenceHistory
variable {A : Type*}

def forget (h : History A Unit) : List A := h.map Occurrence.action

def encodeFrom (past : History A Unit) (actions : List A) : History A Unit :=
  actions.foldl (fun h a => append h a ()) past

def encode (actions : List A) : History A Unit := encodeFrom [] actions

theorem forget_append (h : History A Unit) (a : A) :
    forget (append h a ()) = forget h ++ [a] := by
  simp [forget, append]

theorem forget_encodeFrom (past : History A Unit) (actions : List A) :
    forget (encodeFrom past actions) = forget past ++ actions := by
  induction actions generalizing past with
  | nil => simp [encodeFrom]
  | cons a rest ih =>
      simpa [encodeFrom, List.foldl_cons, forget_append, List.append_assoc] using
        ih (append past a ())

theorem decode_encode (actions : List A) : forget (encode actions) = actions := by
  simpa [encode, forget] using forget_encodeFrom ([] : History A Unit) actions

theorem encode_injective : Function.Injective (@encode A) := by
  intro a b h
  have same := congrArg forget h
  simpa only [decode_encode] using same

def Canonical (h : History A Unit) : Prop := ∃ actions, h = encode actions

theorem encode_decode (h : History A Unit) (canonical : Canonical h) :
    encode (forget h) = h := by
  obtain ⟨actions,rfl⟩ := canonical
  rw [decode_encode]

theorem encode_append (actions : List A) (a : A) :
    encode (actions ++ [a]) = append (encode actions) a () := by
  simp [encode, encodeFrom, List.foldl_append]

theorem encodeFrom_wellFormed (past : History A Unit) (actions : List A)
    (good : WellFormed past) : WellFormed (encodeFrom past actions) := by
  induction actions generalizing past with
  | nil => exact good
  | cons a rest ih =>
      exact ih (append past a ()) (append_wellFormed past a () good)

theorem encode_wellFormed (actions : List A) : WellFormed (encode actions) :=
  encodeFrom_wellFormed [] actions (by simp [WellFormed])

theorem encode_length (actions : List A) : (encode actions).length = actions.length := by
  have h := congrArg List.length (decode_encode actions)
  simpa [forget] using h

theorem fresh_operation_step (actions : List A) (a : A) :
    encode actions <+: encode (actions ++ [a]) ∧
    (encode (actions ++ [a])).length = (encode actions).length + 1 ∧
    fresh (encode actions) ∉ (encode actions).map Occurrence.token := by
  rw [encode_append]
  exact ⟨append_prefix _ _ _, by simp [append], fresh_not_mem _⟩

/-- A readout of the complete decoded log is exactly its source readout. -/
theorem every_readout_preserved {V : Type*} (read : List A → V) (actions : List A) :
    read (forget (encode actions)) = read actions := by rw [decode_encode]

/-- Every report edge is retained separately. Empty, multivalued and unresolved
fibres remain unchanged; no all-cross-pairs Boolean replaces the relation. -/
def encodedReports {R E : Type*} (reports : R → E → Prop)
    (record : Occurrence R Unit) (event : Occurrence E Unit) : Prop :=
  reports record.action event.action

theorem reports_pair_roundtrip {R E : Type*} (reports : R → E → Prop)
    (record : R) (event : E) (recordToken eventToken : Nat) :
    encodedReports reports ⟨recordToken,record,()⟩ ⟨eventToken,event,()⟩ ↔
      reports record event := Iff.rfl

/-- Decoding the entire encoded graph recovers exactly the original edges. -/
theorem reports_roundtrip {R E : Type*} (reports : R → E → Prop)
    (records : List R) (events : List E) :
    (fun z : Occurrence R Unit × Occurrence E Unit => (z.1.action,z.2.action)) ''
      {z | z.1 ∈ encode records ∧ z.2 ∈ encode events ∧ encodedReports reports z.1 z.2} =
    {z : R × E | z.1 ∈ records ∧ z.2 ∈ events ∧ reports z.1 z.2} := by
  ext z
  constructor
  · rintro ⟨⟨r,e⟩,⟨hr,he,hp⟩,rfl⟩
    refine ⟨?_,?_,hp⟩
    · rw [← decode_encode records]
      exact List.mem_map.mpr ⟨r,hr,rfl⟩
    · rw [← decode_encode events]
      exact List.mem_map.mpr ⟨e,he,rfl⟩
  · rintro ⟨hr,he,hp⟩
    rw [← decode_encode records] at hr
    rw [← decode_encode events] at he
    obtain ⟨r,hr,er⟩ := List.mem_map.mp hr
    obtain ⟨e,he,ee⟩ := List.mem_map.mp he
    refine ⟨(r,e),⟨hr,he,?_⟩,Prod.ext er ee⟩
    simpa only [encodedReports,er,ee] using hp

/-- Multivalued reports cannot be replaced by a unique-event decoder. -/
theorem general_reports_need_not_be_single_valued :
    ¬ ∃ f : Unit → Bool, ∀ e : Bool, True → f () = e := by
  rintro ⟨f,h⟩
  have a := h false True.intro
  have b := h true True.intro
  exact Bool.false_ne_true (a.symm.trans b)

end Tokens

namespace CN
open JurisLean.CN.Revision20261101
open JurisLean.CN.Completion20261105

/-- The result type and complete input payload remain part of each command. -/
abbrev PackedCommand := Sigma (fun α : Type => Command α)

def advance (s : Situation) (c : PackedCommand) : Situation :=
  (executeCommand s c.2).after

def replay (initial : Situation) (commands : List PackedCommand) : Situation :=
  commands.foldl advance initial

def commands {a b : Situation} : History a b → List PackedCommand
  | .nil _ => []
  | .snoc h c => commands h ++ [⟨_,c⟩]

theorem replay_commands {a b : Situation} (h : History a b) :
    replay a (commands h) = b := by
  induction h with
  | nil s => rfl
  | snoc h c ih =>
      simpa [commands, replay, List.foldl_append, advance] using
        congrArg (fun s => (executeCommand s c).after) ih

/-- Every actual CN history, not just a numeric projection, roundtrips. -/
theorem complete_history_roundtrip {a b : Situation} (h : History a b) :
    Tokens.forget (Tokens.encode (commands h)) = commands h ∧
    replay a (Tokens.forget (Tokens.encode (commands h))) = b := by
  exact ⟨Tokens.decode_encode _, by rw [Tokens.decode_encode]; exact replay_commands h⟩

theorem complete_history_all_readouts {a b : Situation} (h : History a b)
    {V : Type*} (read : Situation → V) :
    read (replay a (Tokens.forget (Tokens.encode (commands h)))) = read b := by
  rw [(complete_history_roundtrip h).2]

/-- A material record is an operation but does not create a physical event. -/
theorem record_only_counterexample (s : Situation) (i : Ref .material) (raw : Raw i) :
    (executeCommand s (.record i raw)).after.core.state.F = s.core.state.F ∧
    (History.snoc (History.nil s) (.record i raw)).length = 1 := by
  constructor
  · change (recordMaterial s i raw).after.core.state.F = _
    unfold recordMaterial
    split
    · rfl
    · split <;> rfl
  · rfl

theorem record_only_physical_event_count (s : Situation) (i : Ref .material) (raw : Raw i) :
    ((executeCommand s (.record i raw)).after.core.state.F.map (fun e => e.id)).eraseDups.length =
      (s.core.state.F.map (fun e => e.id)).eraseDups.length := by
  rw [(record_only_counterexample s i raw).1]

/-- The actual occurrence consumer is idempotent on an identical event. -/
theorem occurrence_replay_preserves_events (s : Situation) (o : Occurrence)
    (seen : s.core.state.F.find? (fun old => old.id == o.id) = some o) :
    (occurrence s o).after.core.state.F = s.core.state.F := by
  simp [occurrence, seen, quiet]

/-- A genuinely absent occurrence appends once; ordinary records do not. -/
theorem new_occurrence_adds_one (s : Situation) (o : Occurrence)
    (fresh : s.core.state.F.find? (fun old => old.id == o.id) = none) :
    (occurrence s o).after.core.state.F = s.core.state.F ++ [o] ∧
    (occurrence s o).after.core.state.F.length = s.core.state.F.length + 1 := by
  simp [occurrence, fresh, EffectIR.adjust, EffectIR.write]

end CN

namespace Business
open JurisLean.Candidates.Final20261021
open JurisLean.Candidates.MeasuredPolicy20261027
open JurisLean.Candidates.AdaptiveRoundLedger20261027
open JurisLean.Candidates.U00MeasuredRSIEntry20261031
open LegalMath20261110.OccurrenceHistory

/-- Observation, queue and U00 log use the same existing semantic event key. -/
def eventKey {m : Nat} (row : PolicyObservation m) : EventId :=
  row.measured.dictionary.event

theorem u00_event_identity {m : Nat} (row : PolicyObservation m) :
    (policyLog row).event = eventKey row ∧
    (policyLog row).unit = row.measured.dictionary.unit ∧
    (policyLog row).record = row.measured.dictionary.resultRecord ∧
    (policyLog row).targetVersion = row.measured.dictionary.targetVersion ∧
    (policyLog row).mechanismVersion = row.measured.dictionary.context.mechanismVersion :=
  ⟨rfl,rfl,rfl,rfl,rfl⟩

theorem copied_payment_record_counts_once {m : Nat}
    (records : Finset (PolicyObservation m)) (row : PolicyObservation m)
    (seen : eventKey row ∈ records.image eventKey) :
    recordCount eventKey (insert row records) = recordCount eventKey records :=
  record_count_once eventKey records row seen

/-- Encoding preserves both records even when their physical event coincides.
A second valid measurement is not removed by event-level deduplication. -/
theorem measurements_not_collapsed {m : Nat} (first second : PolicyObservation m) :
    Tokens.forget (Tokens.encode [first,second]) = [first,second] ∧
    (Tokens.encode [first,second]).length = 2 :=
  ⟨Tokens.decode_encode _, by rw [Tokens.encode_length]; rfl⟩

theorem complete_business_log_conservation {W : Type} {m : Nat}
    (initial : JurisLean.Candidates.BusinessFeedbackLoop20261027.State m)
    (actions : List (JurisLean.Candidates.BusinessFeedbackLoop20261027.Command W m))
    (legal : JurisLean.Candidates.BusinessFeedbackLoop20261027.KnownBusinessInvariant initial)
    (budget : roundSpent initial.learning ≤ initial.learning.limit) :
    JurisLean.Candidates.BusinessFeedbackLoop20261027.KnownBusinessInvariant
      ((Tokens.forget (Tokens.encode actions)).foldl
        JurisLean.Candidates.BusinessFeedbackLoop20261027.step initial) ∧
    (((Tokens.forget (Tokens.encode actions)).foldl
        JurisLean.Candidates.BusinessFeedbackLoop20261027.step initial).learning.limit =
      initial.learning.limit ∧
    roundSpent ((Tokens.forget (Tokens.encode actions)).foldl
      JurisLean.Candidates.BusinessFeedbackLoop20261027.step initial).learning ≤ initial.learning.limit := by
  rw [Tokens.decode_encode]
  exact JurisLean.Candidates.BusinessFeedbackLoop20261027.arbitrary_finite_commands_consume_actual_posts
    actions initial legal budget

end Business

#print axioms Tokens.decode_encode
#print axioms Tokens.encode_decode
#print axioms Tokens.encode_injective
#print axioms Tokens.encode_wellFormed
#print axioms Tokens.fresh_operation_step
#print axioms Tokens.every_readout_preserved
#print axioms Tokens.reports_roundtrip
#print axioms Tokens.general_reports_need_not_be_single_valued
#print axioms CN.replay_commands
#print axioms CN.complete_history_roundtrip
#print axioms CN.complete_history_all_readouts
#print axioms CN.record_only_counterexample
#print axioms CN.occurrence_replay_preserves_events
#print axioms CN.new_occurrence_adds_one
#print axioms Business.u00_event_identity
#print axioms Business.copied_payment_record_counts_once
#print axioms Business.measurements_not_collapsed
#print axioms Business.complete_business_log_conservation

end LegalMath.RemainingClosure.FullEventLog
