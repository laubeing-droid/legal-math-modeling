import JurisLean.Candidates.Final20261021.EvidenceProcedure

/-!
Original 08.4: evidence directions and classical possible worlds have
different meanings. The executable finite-world filter consumes exactly the
admitted, credible literals. Unknown admissibility stays pending. Empty
world sets are incompatible, never certificates of every proposition.
World/source fidelity and legal-branch compatibility are explicit inputs.
-/

namespace JurisLean.Candidates.EvidenceWorlds20261027

open JurisLean.Candidates.Final20261021
open JurisLean.Candidates.Final20261021.EvidenceProcedure

def respects {W : Type} (truth : W → Nat → Bool) (w : W) (e : EvidenceItem) : Bool :=
  decide (usable e.query e = true → truth w e.query = e.supports)

def constrained {W : Type} (universe : List W) (truth : W → Nat → Bool)
    (items : List EvidenceItem) : List W :=
  universe.filter fun w => items.all (respects truth w)

theorem constrained_membership {W : Type} (universe : List W) (truth : W → Nat → Bool)
    (items : List EvidenceItem) (w : W) :
    w ∈ constrained universe truth items ↔
      w ∈ universe ∧ ∀ e ∈ items, usable e.query e = true → truth w e.query = e.supports := by
  simp [constrained, respects, List.all_eq_true]

theorem additional_constraints_only_remove_worlds {W : Type} (universe : List W)
    (truth : W → Nat → Bool) (old next : List EvidenceItem)
    (includesOld : ∀ e ∈ old, e ∈ next) :
    ∀ w ∈ constrained universe truth next, w ∈ constrained universe truth old := by
  intro w member
  have checked := (constrained_membership universe truth next w).mp member
  exact (constrained_membership universe truth old w).mpr
    ⟨checked.1, fun e he => checked.2 e (includesOld e he)⟩

theorem faithful_evidence_retains_actual_world {W : Type} (universe : List W)
    (truth : W → Nat → Bool) (items : List EvidenceItem) (actual : W)
    (covered : actual ∈ universe)
    (faithful : ∀ e ∈ items, usable e.query e = true → truth actual e.query = e.supports) :
    actual ∈ constrained universe truth items :=
  (constrained_membership universe truth items actual).mpr ⟨covered, faithful⟩

def worldJudgment {W : Type} (worlds : List W) (truth : W → Nat → Bool) (query : Nat) : Judgment :=
  classify (worlds.all fun w => truth w query) (worlds.all fun w => !truth w query)

theorem all_positive_and_negative_iff_empty {W : Type} (worlds : List W)
    (truth : W → Nat → Bool) (query : Nat) :
    ((worlds.all fun w => truth w query) = true ∧
      (worlds.all fun w => !truth w query) = true) ↔ worlds = [] := by
  cases worlds with
  | nil => simp
  | cons w rest => cases value : truth w query <;> simp [value]

theorem world_incompatible_iff_empty {W : Type} (worlds : List W)
    (truth : W → Nat → Bool) (query : Nat) :
    worldJudgment worlds truth query = .incompatible ↔ worlds = [] := by
  exact (u08_3_evidence_four_states
    (worlds.all fun w => truth w query) (worlds.all fun w => !truth w query)).2.2.1.trans
      (all_positive_and_negative_iff_empty worlds truth query)

theorem world_supported_iff_nonempty_universal {W : Type} (worlds : List W)
    (truth : W → Nat → Bool) (query : Nat) :
    worldJudgment worlds truth query = .supported ↔
      worlds ≠ [] ∧ ∀ w ∈ worlds, truth w query = true := by
  rw [(u08_3_evidence_four_states
    (worlds.all fun w => truth w query) (worlds.all fun w => !truth w query)).1]
  constructor
  · rintro ⟨positive, negative⟩
    refine ⟨?_, List.all_eq_true.mp positive⟩
    intro empty
    simp [empty] at negative
  · rintro ⟨nonempty, every⟩
    have positive := List.all_eq_true.mpr every
    refine ⟨positive, ?_⟩
    cases negative : (worlds.all fun w => !truth w query) with
    | false => rfl
    | true =>
        exact False.elim (nonempty ((all_positive_and_negative_iff_empty worlds truth query).mp
          ⟨positive, negative⟩))

theorem world_opposed_iff_nonempty_universal {W : Type} (worlds : List W)
    (truth : W → Nat → Bool) (query : Nat) :
    worldJudgment worlds truth query = .opposed ↔
      worlds ≠ [] ∧ ∀ w ∈ worlds, truth w query = false := by
  rw [(u08_3_evidence_four_states
    (worlds.all fun w => truth w query) (worlds.all fun w => !truth w query)).2.1]
  constructor
  · rintro ⟨positive, negative⟩
    refine ⟨?_, ?_⟩
    · intro empty
      simp [empty] at positive
    · simpa using (List.all_eq_true.mp negative)
  · rintro ⟨nonempty, every⟩
    have negative : (worlds.all fun w => !truth w query) = true := by
      simpa [List.all_eq_true] using every
    refine ⟨?_, negative⟩
    cases positive : (worlds.all fun w => truth w query) with
    | false => rfl
    | true =>
        exact False.elim (nonempty ((all_positive_and_negative_iff_empty worlds truth query).mp
          ⟨positive, negative⟩))

theorem world_insufficient_iff_both_possibilities {W : Type} (worlds : List W)
    (truth : W → Nat → Bool) (query : Nat) :
    worldJudgment worlds truth query = .insufficient ↔
      (∃ w ∈ worlds, truth w query = true) ∧ (∃ w ∈ worlds, truth w query = false) := by
  rw [(u08_3_evidence_four_states
    (worlds.all fun w => truth w query) (worlds.all fun w => !truth w query)).2.2.2]
  simp only [List.all_eq_false]
  constructor
  · rintro ⟨⟨no, noMember, noValue⟩, ⟨yes, yesMember, yesValue⟩⟩
    refine ⟨⟨yes, yesMember, ?_⟩, ⟨no, noMember, ?_⟩⟩
    · cases value : truth yes query <;> simp_all
    · cases value : truth no query <;> simp_all
  · rintro ⟨⟨yes, yesMember, yesValue⟩, ⟨no, noMember, noValue⟩⟩
    exact ⟨⟨no, noMember, by simp [noValue]⟩, ⟨yes, yesMember, by simp [yesValue]⟩⟩

theorem supported_world_judgment_needs_actual_membership {W : Type}
    (worlds : List W) (truth : W → Nat → Bool) (query : Nat) (actual : W)
    (belongs : actual ∈ worlds) (supported : worldJudgment worlds truth query = .supported) :
    truth actual query = true :=
  ((world_supported_iff_nonempty_universal worlds truth query).mp supported).2 actual belongs

theorem source_to_world_truth_is_conditional {W : Type} (universe : List W)
    (truth : W → Nat → Bool) (items : List EvidenceItem) (query : Nat) (actual : W)
    (covered : actual ∈ universe)
    (faithful : ∀ e ∈ items, usable e.query e = true → truth actual e.query = e.supports)
    (supported : worldJudgment (constrained universe truth items) truth query = .supported) :
    truth actual query = true :=
  supported_world_judgment_needs_actual_membership _ truth query actual
    (faithful_evidence_retains_actual_world universe truth items actual covered faithful) supported

def pendingSources (query : Nat) (items : List EvidenceItem) : List SourceRef :=
  (items.filter fun e => decide (e.query = query ∧ e.admissibility = .unknown)).map EvidenceItem.source

structure EvidenceView (W : Type) where
  evidenceJudgment : Judgment
  possibleWorlds : List W
  possibleWorldJudgment : Judgment
  pending : List SourceRef

def viewEvidence {W : Type} (universe : List W) (truth : W → Nat → Bool)
    (query : Nat) (items : List EvidenceItem) : EvidenceView W :=
  let worlds := constrained universe truth items
  ⟨judgment query items, worlds, worldJudgment worlds truth query, pendingSources query items⟩

theorem output_world_label_reads_actual_filtered_worlds {W : Type} (universe : List W)
    (truth : W → Nat → Bool) (query : Nat) (items : List EvidenceItem) :
    (viewEvidence universe truth query items).possibleWorldJudgment = .supported ↔
      (viewEvidence universe truth query items).possibleWorlds ≠ [] ∧
      ∀ w ∈ (viewEvidence universe truth query items).possibleWorlds, truth w query = true :=
  world_supported_iff_nonempty_universal _ _ _

def evidenceBits (query : Nat) (items : List EvidenceItem) : Bool × Bool :=
  (items.any fun e => usable query e && e.supports,
    items.any fun e => usable query e && !e.supports)

def KnowledgeLe (older newer : Bool × Bool) : Prop :=
  (older.1 = true → newer.1 = true) ∧ (older.2 = true → newer.2 = true)

theorem adding_evidence_is_monotone_in_information_bits (query : Nat)
    (old extra : List EvidenceItem) :
    KnowledgeLe (evidenceBits query old) (evidenceBits query (old ++ extra)) := by
  constructor <;> intro recorded <;> simp_all [evidenceBits, List.any_append]

-- Each pair is an explicitly compatible legal interpretation / factual world.
-- No Cartesian completion, vote or probability weighting is performed.
def compatibleWorlds {L W : Type} (allowed : List (L × W))
    (truth : L → W → Nat → Bool) (items : L → List EvidenceItem) : List (L × W) :=
  allowed.filter fun pair => (items pair.1).all (respects (truth pair.1) pair.2)

theorem compatible_pair_membership {L W : Type} (allowed : List (L × W))
    (truth : L → W → Nat → Bool) (items : L → List EvidenceItem) (pair : L × W) :
    pair ∈ compatibleWorlds allowed truth items ↔ pair ∈ allowed ∧
      ∀ e ∈ items pair.1, usable e.query e = true → truth pair.1 pair.2 e.query = e.supports := by
  simp [compatibleWorlds, respects, List.all_eq_true]

theorem filtering_never_invents_legal_world_pair {L W : Type} (allowed : List (L × W))
    (truth : L → W → Nat → Bool) (items : L → List EvidenceItem) (pair : L × W)
    (retained : pair ∈ compatibleWorlds allowed truth items) : pair ∈ allowed :=
  ((compatible_pair_membership allowed truth items pair).mp retained).1

end JurisLean.Candidates.EvidenceWorlds20261027

