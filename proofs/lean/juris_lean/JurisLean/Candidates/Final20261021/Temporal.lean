import JurisLean.Candidates.Final20261021.Harness

namespace JurisLean.Candidates.Final20261021.Temporal

structure VersionRecord where
  id : EventId
  version : Nat
  jurisdiction : String
  question : Nat
  factFrom : LawDate
  factUntil : Option LawDate
  recordedAt : Instant
  knownAt : Instant
  deriving DecidableEq, Repr

def visible (g : Gamma) (e : VersionRecord) : Bool :=
  decide (e.recordedAt.ticks ≤ g.recordCutoff.ticks ∧
    e.knownAt.ticks ≤ g.knowledgeCutoff.ticks)

def proposed_event_evidence_versions (g : Gamma) (history : List VersionRecord) :=
  history.filter (visible g)

def applies (g : Gamma) (e : VersionRecord) : Bool :=
  decide (e.jurisdiction = g.jurisdiction ∧ e.question = g.question ∧
    e.factFrom.ordinal ≤ g.lawDate.ordinal ∧
    match e.factUntil with | none => True | some d => g.lawDate.ordinal < d.ordinal)

-- This is the declared half-open, non-retroactive finite interval model.
-- General transitions/exceptions remain explicit alternative branch inputs.
def proposed_applicability (g : Gamma) (history : List VersionRecord) : Result Nat :=
  match (proposed_event_evidence_versions g history).filter (applies g) with
  | [e] => .known e.version
  | [] => .unknown .missingEvidence
  | e :: f :: _ => .conflict e.version f.version

theorem u08_1_history_stable_under_append_after_cut
    (g : Gamma) (history extra : List VersionRecord)
    (later : ∀ e ∈ extra, visible g e = false) :
    proposed_event_evidence_versions g (history ++ extra) =
      proposed_event_evidence_versions g history := by
  have empty : extra.filter (visible g) = [] := by
    induction extra with
    | nil => rfl
    | cons e es ih =>
        have he := later e (by simp)
        have hs := ih (fun x hx => later x (by simp [hx]))
        simp [he, hs]
  simp [proposed_event_evidence_versions, List.filter_append, empty]

theorem u08_1_selection_stable (g : Gamma) (h extra : List VersionRecord)
    (later : ∀ e ∈ extra, visible g e = false) :
    proposed_applicability g (h ++ extra) = proposed_applicability g h := by
  unfold proposed_applicability
  rw [u08_1_history_stable_under_append_after_cut g h extra later]

def Compressible {H V Q A : Type} (app : H → V → Prop)
    (answer : V → H → Q → A) (observations : Q → Prop) (chosen : V) : Prop :=
  ∀ h v q, app h v → observations q → answer v h q = answer chosen h q

theorem u08_2_compression_preserves_actual_observations {H V Q A : Type}
    (app : H → V → Prop) (answer : V → H → Q → A) (observations : Q → Prop)
    (chosen : V) (h : Compressible app answer observations chosen)
    (event : H) (v : V) (q : Q) (hv : app event v) (hq : observations q) :
    answer v event q = answer chosen event q := h event v q hv hq

end JurisLean.Candidates.Final20261021.Temporal
