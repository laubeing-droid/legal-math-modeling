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
    e.factFrom.ordinal ≤ g.lawDate.ordinal) &&
    match e.factUntil with
    | none => true
    | some d => decide (g.lawDate.ordinal < d.ordinal)

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

def checkCompression {H V Q A : Type} [Fintype H] [Fintype V] [Fintype Q]
    [DecidableEq A] (app : H → V → Bool) (answer : V → H → Q → A)
    (observations : Q → Bool) (chosen : V) : Bool :=
  decide (∀ h v q, app h v = true → observations q = true →
    answer v h q = answer chosen h q)

theorem u08_2_finite_compression_reflection {H V Q A : Type}
    [Fintype H] [Fintype V] [Fintype Q] [DecidableEq A]
    (app : H → V → Bool) (answer : V → H → Q → A)
    (observations : Q → Bool) (chosen : V) :
    checkCompression app answer observations chosen = true ↔
      Compressible (fun h v => app h v = true) answer (fun q => observations q = true) chosen := by
  simp [checkCompression, Compressible]

end JurisLean.Candidates.Final20261021.Temporal
