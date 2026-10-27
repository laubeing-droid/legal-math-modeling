import JurisLean.Candidates.Final20261021.Temporal
import JurisLean.Candidates.SourceCompilation20261027
import Mathlib.Data.Finset.Dedup

/-!
Original 08.2/08.3 and the temporal edge of 08.7. A finite version catalog
is an explicit input. App interprets the visible records under the same Gamma;
it is not inferred from publication dates or a latest-version heuristic.
Unknown applicability is retained. Successful selection gates the actual
source compiler before any leaf or rule can be accepted as a legal result.
-/

namespace JurisLean.Candidates.TemporalInterpretation20261027

open JurisLean.Candidates.Final20261021
open JurisLean.Candidates.Final20261021.Temporal
open JurisLean.Candidates.SourceCompilation20261027
open JurisLean.Candidates.CompilerProvenance20261027

abbrev App := Gamma → Finset VersionRecord → Nat → Applicable

def visibleSet (g : Gamma) (history : List VersionRecord) : Finset VersionRecord :=
  (proposed_event_evidence_versions g history).toFinset

-- Identical copies are idempotent; different records with one stable ID conflict.
def KeyConsistent (records : Finset VersionRecord) : Prop :=
  ∀ e ∈ records, ∀ f ∈ records, e.id = f.id → e = f

instance (records : Finset VersionRecord) : Decidable (KeyConsistent records) :=
  inferInstanceAs (Decidable (∀ e ∈ records, ∀ f ∈ records, e.id = f.id → e = f))

def candidates (g : Gamma) (records : Finset VersionRecord) (versions : List Nat)
    (app : App) : List Nat :=
  versions.filter fun v => decide (app g records v = .yes)

def pending (g : Gamma) (records : Finset VersionRecord) (versions : List Nat)
    (app : App) : List Nat :=
  versions.filter fun v => decide (app g records v = .unknown)

def single : List Nat → Result Nat
  | [] => .unknown .missingEvidence
  | [v] => .known v
  | v :: w :: _ => .conflict v w

def selectFrom (g : Gamma) (records : Finset VersionRecord) (versions : List Nat)
    (app : App) : Result Nat :=
  if KeyConsistent records then
    if versions.Nodup then
      if pending g records versions app = [] then single (candidates g records versions app)
      else .unknown .applicabilityUnknown
    else .rejected .versionConflict
  else .rejected .observationBindingMismatch

def selectVersion (g : Gamma) (history : List VersionRecord) (versions : List Nat)
    (app : App) : Result Nat :=
  selectFrom g (visibleSet g history) versions app

theorem single_success_is_exact (xs : List Nat) (v : Nat) (h : single xs = .known v) :
    xs = [v] := by
  cases xs with
  | nil => simp [single] at h
  | cons a rest =>
      cases rest with
      | nil => simpa [single] using h
      | cons b tail => simp [single] at h

theorem selection_success_contract (g : Gamma) (records : Finset VersionRecord)
    (versions : List Nat) (app : App) (v : Nat)
    (accepted : selectFrom g records versions app = .known v) :
    KeyConsistent records ∧ versions.Nodup ∧ pending g records versions app = [] ∧
      candidates g records versions app = [v] := by
  unfold selectFrom at accepted
  split at accepted
  next keyed =>
    split at accepted
    next unique =>
      split at accepted
      next resolved => exact ⟨keyed, unique, resolved, single_success_is_exact _ _ accepted⟩
      next => simp at accepted
    next => simp at accepted
  next => simp at accepted

theorem successful_version_is_applicable (g : Gamma) (history : List VersionRecord)
    (versions : List Nat) (app : App) (v : Nat)
    (accepted : selectVersion g history versions app = .known v) :
    v ∈ versions ∧ app g (visibleSet g history) v = .yes := by
  have exactCandidates := (selection_success_contract _ _ _ _ _ accepted).2.2.2
  have member : v ∈ candidates g (visibleSet g history) versions app := by
    rw [exactCandidates]
    simp
  simpa [candidates] using member

theorem visible_set_is_permutation_invariant (g : Gamma) (h h' : List VersionRecord)
    (perm : h.Perm h') : visibleSet g h = visibleSet g h' := by
  apply List.toFinset.ext
  intro e
  simp only [proposed_event_evidence_versions, List.mem_filter]
  rw [perm.mem_iff]

theorem selection_is_permutation_invariant (g : Gamma) (h h' : List VersionRecord)
    (versions : List Nat) (app : App) (perm : h.Perm h') :
    selectVersion g h versions app = selectVersion g h' versions app := by
  unfold selectVersion
  rw [visible_set_is_permutation_invariant g h h' perm]

theorem selection_stable_after_invisible_append (g : Gamma) (h extra : List VersionRecord)
    (versions : List Nat) (app : App) (later : ∀ e ∈ extra, visible g e = false) :
    selectVersion g (h ++ extra) versions app = selectVersion g h versions app := by
  unfold selectVersion visibleSet
  rw [u08_1_history_stable_under_append_after_cut g h extra later]

-- App may inspect all visible transition/exception records. In this restricted
-- example it uses exactly the declared half-open interval predicate.
def intervalApp : App := fun g records version =>
  if ∃ e ∈ records, e.version = version ∧ applies g e = true then .yes else .no

def selectThenCut (g : Gamma) (history : List VersionRecord) (versions : List Nat)
    (app : App) : Result Nat :=
  match selectFrom g history.toFinset versions app with
  | .known v =>
      if ∃ e ∈ visibleSet g history, e.version = v then .known v else .unknown .missingEvidence
  | .unknown e => .unknown e
  | .rejected e => .rejected e
  | .conflict l r => .conflict l r

theorem visible_records_preserve_key_consistency (g : Gamma) (history : List VersionRecord)
    (keyed : KeyConsistent history.toFinset) : KeyConsistent (visibleSet g history) := by
  intro e he f hf sameId
  have eMember : e ∈ history :=
    (List.mem_filter.mp (List.mem_toFinset.mp he)).1
  have fMember : f ∈ history :=
    (List.mem_filter.mp (List.mem_toFinset.mp hf)).1
  exact keyed e (List.mem_toFinset.mpr eMember) f (List.mem_toFinset.mpr fMember) sameId

-- Locality and visible support are substantive sufficient conditions.
-- Neither is assumed for the late-exception counterexample.
theorem cut_and_selection_commute_under_locality (g : Gamma) (history : List VersionRecord)
    (versions : List Nat) (app : App) (keyed : KeyConsistent history.toFinset)
    (locality : ∀ v, app g history.toFinset v = app g (visibleSet g history) v)
    (visibleSupport : ∀ v, app g (visibleSet g history) v = .yes →
      ∃ e ∈ visibleSet g history, e.version = v) :
    selectThenCut g history versions app = selectVersion g history versions app := by
  have equalSelection : selectFrom g history.toFinset versions app =
      selectVersion g history versions app := by
    simp only [selectFrom, selectVersion, candidates, pending]
    simp_rw [locality]
    simp [keyed, visible_records_preserve_key_consistency g history keyed]
  unfold selectThenCut
  rw [equalSelection]
  cases selected : selectVersion g history versions app with
  | known v =>
      have supported := visibleSupport v (successful_version_is_applicable _ _ _ _ _ selected).2
      simp [supported]
  | unknown e => rfl
  | rejected e => rfl
  | conflict l r => rfl

def InHalfOpenInterval (e : VersionRecord) (t : Int) : Prop :=
  e.factFrom.ordinal ≤ t ∧ ∀ finish, e.factUntil = some finish → t < finish.ordinal

-- Coverage, distinct starts and ordered nonoverlapping half-open boundaries
-- justify the latest-start calculation only inside this restricted model.
-- Actual App must additionally agree with these intervals and all records
-- used here must be visible; transition/retroactivity exceptions are excluded.
theorem latest_start_is_correct_in_ordered_interval_model
    (records : List VersionRecord) (t : Int) (latest : VersionRecord)
    (latestMember : latest ∈ records) (latestStarted : latest.factFrom.ordinal ≤ t)
    (maximal : ∀ e ∈ records, e.factFrom.ordinal ≤ t →
      e.factFrom.ordinal ≤ latest.factFrom.ordinal)
    (coverage : ∃ e ∈ records, InHalfOpenInterval e t)
    (distinct : ∀ e ∈ records, ∀ f ∈ records,
      e.factFrom = f.factFrom → e = f)
    (orderedEnds : ∀ e ∈ records, ∀ f ∈ records,
      e.factFrom.ordinal < f.factFrom.ordinal →
      ∃ finish, e.factUntil = some finish ∧ finish.ordinal ≤ f.factFrom.ordinal) :
    InHalfOpenInterval latest t ∧
      ∀ e ∈ records, InHalfOpenInterval e t → e = latest := by
  have identifies : ∀ e ∈ records, InHalfOpenInterval e t → e = latest := by
    intro e member inside
    have startsLe := maximal e member inside.1
    have sameStart : e.factFrom.ordinal = latest.factFrom.ordinal := by
      by_contra different
      have strict : e.factFrom.ordinal < latest.factFrom.ordinal := lt_of_le_of_ne startsLe different
      obtain ⟨finish, endEq, before⟩ := orderedEnds e member latest latestMember strict
      have beforeEnd := inside.2 finish endEq
      omega
    apply distinct e member latest latestMember
    cases he : e.factFrom with
    | mk a =>
        cases hf : latest.factFrom with
        | mk b =>
            simp only [he, hf] at sameStart
            exact congrArg LawDate.mk sameStart
  obtain ⟨active, activeMember, inside⟩ := coverage
  exact ⟨(identifies active activeMember inside) ▸ inside, identifies⟩

structure PartialVersion where
  id : EventId
  version : Nat
  jurisdiction : String
  question : Nat
  factFrom : LawDate
  factUntil : Option LawDate
  recordedAt : Instant
  knownAt : Option Instant
  deriving DecidableEq, Repr

def completeKnownAt (p : PartialVersion) (t : Instant) : VersionRecord :=
  ⟨p.id, p.version, p.jurisdiction, p.question, p.factFrom, p.factUntil, p.recordedAt, t⟩

-- A nonempty finite range is a declared possible-time model, not proof that
-- the true historical time lies in it. Empty unknown ranges stay unresolved.
def knownAtAlternatives (g : Gamma) (history : List VersionRecord) (versions : List Nat)
    (app : App) (p : PartialVersion) (possibleTimes : List Instant) : List (Result Nat) :=
  match p.knownAt with
  | some t => [selectVersion g (history ++ [completeKnownAt p t]) versions app]
  | none =>
      match possibleTimes with
      | [] => [.unknown .missingEvidence]
      | _ :: _ => possibleTimes.map fun t =>
          selectVersion g (history ++ [completeKnownAt p t]) versions app

theorem unknown_time_retains_each_completion (g : Gamma) (history : List VersionRecord)
    (versions : List Nat) (app : App) (p : PartialVersion) (times : List Instant)
    (unknownTime : p.knownAt = none) (t : Instant) (possible : t ∈ times) :
    selectVersion g (history ++ [completeKnownAt p t]) versions app ∈
      knownAtAlternatives g history versions app p times := by
  cases times with
  | nil => simp at possible
  | cons first rest =>
      simp only [knownAtAlternatives, unknownTime]
      exact List.mem_map.mpr ⟨t, possible, rfl⟩

def Must {W : Type} (worlds : List W) (p : W → Prop) : Prop :=
  worlds ≠ [] ∧ ∀ w ∈ worlds, p w

theorem nonempty_constraint_refinement_preserves_must {W : Type} (old next : List W)
    (p : W → Prop) (nonempty : next ≠ []) (narrows : ∀ w ∈ next, w ∈ old)
    (prior : Must old p) : Must next p :=
  ⟨nonempty, fun w member => prior.2 w (narrows w member)⟩

theorem must_truth_requires_actual_world_membership {W : Type} (worlds : List W)
    (p : W → Prop) (actual : W) (belongs : actual ∈ worlds) (known : Must worlds p) :
    p actual := known.2 actual belongs

def Lossless {E Q A : Type} (events : List E) (questions : List Q)
    (options : E → List Nat) (answer : Nat → E → Q → A) (chosen : Nat) : Prop :=
  ∀ e ∈ events, options e ≠ [] ∧
    ∀ v ∈ options e, ∀ q ∈ questions, answer v e q = answer chosen e q

def checkLossless {E Q A : Type} [DecidableEq A] (events : List E) (questions : List Q)
    (options : E → List Nat) (answer : Nat → E → Q → A) (chosen : Nat) : Bool :=
  events.all fun e => !((options e).isEmpty) && (options e).all fun v =>
    questions.all fun q => decide (answer v e q = answer chosen e q)

theorem finite_lossless_reflection {E Q A : Type} [DecidableEq A]
    (events : List E) (questions : List Q) (options : E → List Nat)
    (answer : Nat → E → Q → A) (chosen : Nat) :
    checkLossless events questions options answer chosen = true ↔
      Lossless events questions options answer chosen := by
  simp [checkLossless, Lossless, List.all_eq_true]

theorem labels_preserved_implies_all_answers {E Q A : Type}
    (events : List E) (questions : List Q) (options : E → List Nat)
    (answer : Nat → E → Q → A) (chosen : Nat)
    (labels : ∀ e ∈ events, options e ≠ [] ∧ ∀ v ∈ options e, v = chosen) :
    Lossless events questions options answer chosen := by
  intro e member
  refine ⟨(labels e member).1, ?_⟩
  intro v selected q _
  rw [(labels e member).2 v selected]

structure TimedCompilation where
  selectedVersion : Nat
  compiled : CompiledView

def selectedGate (selected : Nat) (ruleGate : Gamma → RuleUse → Bool)
    (ctx : Gamma) (rule : RuleUse) : Bool :=
  decide (ctx.normVersion = selected ∧ rule.normVersion = selected) && ruleGate ctx rule

-- No Gamma rewriting: the source snapshot, selected norm version and rule
-- invocation must agree. Unknown App blocks even a leaf-only compilation.
def compileTimed (s : MaterialSnapshot) (history : List VersionRecord) (versions : List Nat)
    (app : App) (branch : Nat) (catalog : List InterpretationRow) (rules : List RuleUse)
    (ruleGate : Gamma → RuleUse → Bool) (nodes : List Node) (root query : Nat) : Result TimedCompilation :=
  match selectVersion s.gamma history versions app with
  | .known selected =>
      if selected = s.gamma.normVersion then
        match compileView s branch catalog rules (selectedGate selected ruleGate) nodes root query with
        | .known out => .known ⟨selected, out⟩
        | .unknown e => .unknown e
        | .rejected e => .rejected e
        | .conflict l r => .conflict l r
      else .rejected .versionConflict
  | .unknown e => .unknown e
  | .rejected e => .rejected e
  | .conflict l r => .conflict l r

theorem timed_compiler_consumes_selected_version (s : MaterialSnapshot)
    (history : List VersionRecord) (versions : List Nat) (app : App) (branch : Nat)
    (catalog : List InterpretationRow) (rules : List RuleUse) (ruleGate : Gamma → RuleUse → Bool)
    (nodes : List Node) (root query : Nat) (out : TimedCompilation)
    (accepted : compileTimed s history versions app branch catalog rules ruleGate nodes root query = .known out) :
    selectVersion s.gamma history versions app = .known out.selectedVersion ∧
      out.selectedVersion = s.gamma.normVersion ∧
      compileView s branch catalog rules (selectedGate out.selectedVersion ruleGate) nodes root query =
        .known out.compiled := by
  cases selected : selectVersion s.gamma history versions app with
  | unknown e => simp [compileTimed, selected] at accepted
  | rejected e => simp [compileTimed, selected] at accepted
  | conflict l r => simp [compileTimed, selected] at accepted
  | known version =>
      by_cases sameVersion : version = s.gamma.normVersion
      · cases compiled : compileView s branch catalog rules (selectedGate version ruleGate) nodes root query with
        | unknown e => simp [compileTimed, selected, sameVersion, compiled] at accepted
        | rejected e => simp [compileTimed, selected, sameVersion, compiled] at accepted
        | conflict l r => simp [compileTimed, selected, sameVersion, compiled] at accepted
        | known result =>
            simp only [compileTimed, selected, if_pos sameVersion, compiled, Result.known.injEq] at accepted
            cases accepted
            exact ⟨rfl, sameVersion, compiled⟩
      · simp [compileTimed, selected, sameVersion] at accepted

theorem timed_compilation_has_actual_app_and_closure (s : MaterialSnapshot)
    (history : List VersionRecord) (versions : List Nat) (app : App) (branch : Nat)
    (catalog : List InterpretationRow) (rules : List RuleUse) (ruleGate : Gamma → RuleUse → Bool)
    (nodes : List Node) (root query : Nat) (out : TimedCompilation)
    (accepted : compileTimed s history versions app branch catalog rules ruleGate nodes root query = .known out) :
    app s.gamma (visibleSet s.gamma history) out.selectedVersion = .yes ∧
      query ∈ out.compiled.closure ∧ BackwardFrom 0 nodes := by
  have flow := timed_compiler_consumes_selected_version _ _ _ _ _ _ _ _ _ _ _ _ accepted
  exact ⟨(successful_version_is_applicable _ _ _ _ _ flow.1).2,
    actual_compilation_enters_finite_closure _ _ _ _ _ _ _ _ _ flow.2.2⟩

theorem temporal_source_rule_semantic_composition (s : MaterialSnapshot)
    (history : List VersionRecord) (versions : List Nat) (app : App) (branch : Nat)
    (catalog : List InterpretationRow) (rules : List RuleUse) (ruleGate : Gamma → RuleUse → Bool)
    (nodes : List Node) (root query : Nat) (out : TimedCompilation)
    (Interpret : MaterialSnapshot → ConsumedView → Prop) (truth : Nat → Prop)
    (catalogFaithful : ∀ row ∈ catalog, row.material = s → row.branch = branch → Interpret s row.decoded)
    (primitiveMeaning : ∀ decoded, Interpret s decoded → ∀ f ∈ decoded.atoms, truth f.value)
    (rulesSound : ∀ version ∈ versions, app s.gamma (visibleSet s.gamma history) version = .yes →
      ∀ r ∈ activeRules s.gamma rules (selectedGate version ruleGate),
        (∀ a ∈ r.premises, truth a) → truth r.conclusion)
    (accepted : compileTimed s history versions app branch catalog rules ruleGate nodes root query = .known out) :
    truth query := by
  have flow := timed_compiler_consumes_selected_version _ _ _ _ _ _ _ _ _ _ _ _ accepted
  have applicable := successful_version_is_applicable _ _ _ _ _ flow.1
  exact interpreted_material_to_query _ _ _ _ _ _ _ _ _ Interpret truth catalogFaithful primitiveMeaning
    (rulesSound out.selectedVersion applicable.1 applicable.2) flow.2.2

end JurisLean.Candidates.TemporalInterpretation20261027
