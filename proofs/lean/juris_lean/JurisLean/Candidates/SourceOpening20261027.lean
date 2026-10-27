import JurisLean.Candidates.SourceStages20261027
import JurisLean.Candidates.BusinessFeedbackLoop20261027

/-!
Source interpretation and actual finite legal validation supply a common
business opening. Every declared branch is retained. This executable contract
requires the same fully represented debt, formation projection and payment
payloads across those branches; it does not claim completeness for every pair
of semantically equivalent but differently represented legal objects.

The source window consists of formation and two payments. The runtime opening
is before those payments. Structural source stages are never reused as commit
receipts. Norm history and its derived environment are published together.
Parsing, source authority and the fidelity of legal interpretations remain
external premises. Neither source formation nor this constructor grants a
transaction permission or changes the supplied learner's context.
-/

namespace JurisLean.Candidates.SourceOpening20261027

open JurisLean.Candidates.Final20261021
open JurisLean.Candidates.SourceCompilation20261027
open JurisLean.Candidates.SourceStages20261027
open JurisLean.Candidates.FiniteLegalValidation20261027
open JurisLean.Candidates.LegalActionDomain20261027
open JurisLean.Candidates.AdaptiveRoundLedger20261027
open JurisLean.Candidates.BusinessFeedbackLoop20261027

structure BranchOpening (W : Type) where
  key : Nat
  legal : ValidationReport W
  frame : SourceFrame

def frameReport {W : Type} (row : Nat × Result (ValidationReport W)) : Result (BranchOpening W) :=
  match row.2 with
  | .known report => match stagesFromView report.bound.source with
      | .known frame => .known ⟨row.1, report, frame⟩
      | .unknown e => .unknown e
      | .rejected e => .rejected e
      | .conflict a b => .conflict a b
  | .unknown e => .unknown e
  | .rejected e => .rejected e
  | .conflict a b => .conflict a b

def collectFrames {W : Type} : List (Nat × Result (ValidationReport W)) → Result (List (BranchOpening W))
  | [] => .known []
  | row :: rest => match frameReport row with
      | .known head => match collectFrames rest with
          | .known tail => .known (head :: tail)
          | .unknown e => .unknown e
          | .rejected e => .rejected e
          | .conflict a b => .conflict a b
      | .unknown e => .unknown e
      | .rejected e => .rejected e
      | .conflict a b => .conflict a b

theorem known_frame_consumes_actual_legal_source {W : Type}
    (row : Nat × Result (ValidationReport W)) (out : BranchOpening W)
    (accepted : frameReport row = .known out) :
    row.2 = .known out.legal ∧ out.key = row.1 ∧
      stagesFromView out.legal.bound.source = .known out.frame := by
  cases actual : row.2 with
  | unknown e => simp [frameReport, actual] at accepted
  | rejected e => simp [frameReport, actual] at accepted
  | conflict a b => simp [frameReport, actual] at accepted
  | known report =>
      cases framed : stagesFromView report.bound.source with
      | unknown e => simp [frameReport, actual, framed] at accepted
      | rejected e => simp [frameReport, actual, framed] at accepted
      | conflict a b => simp [frameReport, actual, framed] at accepted
      | known frame =>
          simp only [frameReport, actual, framed, Result.known.injEq] at accepted
          subst out
          exact ⟨actual, rfl, framed⟩

theorem every_collected_frame_has_an_actual_report {W : Type}
    (rows : List (Nat × Result (ValidationReport W))) (frames : List (BranchOpening W))
    (accepted : collectFrames rows = .known frames) :
    ∀ frame ∈ frames, ∃ row ∈ rows, frameReport row = .known frame := by
  induction rows generalizing frames with
  | nil =>
      simp only [collectFrames, Result.known.injEq] at accepted
      subst frames
      simp
  | cons row rest ih =>
      cases first : frameReport row with
      | unknown e => simp [collectFrames, first] at accepted
      | rejected e => simp [collectFrames, first] at accepted
      | conflict a b => simp [collectFrames, first] at accepted
      | known head =>
          cases tail : collectFrames rest with
          | unknown e => simp [collectFrames, first, tail] at accepted
          | rejected e => simp [collectFrames, first, tail] at accepted
          | conflict a b => simp [collectFrames, first, tail] at accepted
          | known remaining =>
              simp only [collectFrames, first, tail, Result.known.injEq] at accepted
              subst frames
              intro frame member
              rcases List.mem_cons.mp member with same | later
              · subst frame
                exact ⟨row, List.mem_cons_self, first⟩
              · obtain ⟨origin, present, source⟩ := ih remaining tail frame later
                exact ⟨origin, List.mem_cons_of_mem row present, source⟩

theorem collected_branch_keys_are_not_filtered {W : Type}
    (rows : List (Nat × Result (ValidationReport W))) (frames : List (BranchOpening W))
    (accepted : collectFrames rows = .known frames) :
    frames.map BranchOpening.key = rows.map Prod.fst := by
  induction rows generalizing frames with
  | nil =>
      simp only [collectFrames, Result.known.injEq] at accepted
      subst frames
      rfl
  | cons row rest ih =>
      cases first : frameReport row with
      | unknown e => simp [collectFrames, first] at accepted
      | rejected e => simp [collectFrames, first] at accepted
      | conflict a b => simp [collectFrames, first] at accepted
      | known head =>
          cases tail : collectFrames rest with
          | unknown e => simp [collectFrames, first, tail] at accepted
          | rejected e => simp [collectFrames, first, tail] at accepted
          | conflict a b => simp [collectFrames, first, tail] at accepted
          | known remaining =>
              simp only [collectFrames, first, tail, Result.known.injEq] at accepted
              subst frames
              simp only [List.map_cons, (known_frame_consumes_actual_legal_source row head first).2.1,
                ih remaining tail]

def sameOpeningCore (a b : SourceFrame) : Bool :=
  decide (a.first.relation.value = b.first.relation.value ∧
    a.stages.afterFormation.state.formations = b.stages.afterFormation.state.formations ∧
    a.first.payment.value.key = b.first.payment.value.key ∧
    a.first.payment.value.payload = b.first.payment.value.payload ∧
    a.second.payment.value.key = b.second.payment.value.key ∧
    a.second.payment.value.payload = b.second.payment.value.payload) &&
  sameDebt a.first.debt.value b.first.debt.value

def openingHandle (frame : SourceFrame) (history : List Temporal.VersionRecord) : Ledger.Handle :=
  let initial := Trace.initial frame.source.material.gamma frame.first.relation.value
  {initial with state := {initial.state with
    formations := frame.stages.afterFormation.state.formations
    normHistory := history
    env := Temporal.proposed_applicability initial.gamma history}}

theorem opening_reads_formed_source_without_claiming_payments
    (frame : SourceFrame) (history : List Temporal.VersionRecord) :
    (openingHandle frame history).state.debt = frame.first.relation.value ∧
    (openingHandle frame history).state.formations = frame.stages.afterFormation.state.formations ∧
    (openingHandle frame history).state.paid = 0 ∧
    (openingHandle frame history).state.receipts = [] ∧
    (openingHandle frame history).state.env =
      Temporal.proposed_applicability frame.source.material.gamma history := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem source_opening_has_a_proved_initial_invariant
    (view : ExtractedView) (frame : SourceFrame) (history : List Temporal.VersionRecord)
    (accepted : stagesFromView view = .known frame) :
    Trace.Invariant (openingHandle frame history) := by
  have bindings := accepted_view_binds_both_actual_payments view frame accepted
  have checks := (successful_binding_reads_actual_rows view 1 frame.first bindings.2.1).2
  rcases checks with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, amount, nonneg, _⟩
  have debtNonneg : 0 ≤ frame.first.relation.value.amount.value := by
    rw [congrArg Amount.value amount]
    exact nonneg
  have initial := Trace.initial_invariant frame.source.material.gamma frame.first.relation.value debtNonneg
  exact ⟨initial.1, initial.2.1, rfl, initial.2.2.2⟩

structure SharedOpening (W : Type) where
  anchor : BranchOpening W
  branches : List (BranchOpening W)
  handle : Ledger.Handle

def proposeOpening {W : Type} (input : LegalInput W)
    (branches : List (BranchOpening W)) : Result (SharedOpening W) :=
  match branches.find? (fun row => decide (row.frame.source.material = input.anchor)) with
  | none => .unknown .incompatibleFiber
  | some anchor =>
      if branches.all (fun row => sameOpeningCore row.frame anchor.frame) then
        .known ⟨anchor, branches, openingHandle anchor.frame input.history⟩
      else .unknown .incompatibleFiber

theorem known_opening_keeps_every_common_branch {W : Type}
    (input : LegalInput W) (branches : List (BranchOpening W)) (out : SharedOpening W)
    (accepted : proposeOpening input branches = .known out) :
    out.anchor ∈ branches ∧ out.branches = branches ∧
    out.anchor.frame.source.material = input.anchor ∧
    out.handle = openingHandle out.anchor.frame input.history ∧
    ∀ branch ∈ branches, sameOpeningCore branch.frame out.anchor.frame = true := by
  unfold proposeOpening at accepted
  cases selected : branches.find? (fun row => decide (row.frame.source.material = input.anchor)) with
  | none => simp [selected] at accepted
  | some anchor =>
      simp only [selected] at accepted
      split at accepted
      · rename_i common
        cases accepted
        exact ⟨List.mem_of_find?_eq_some selected, rfl, of_decide_eq_true (List.find?_some selected),
          rfl, List.all_eq_true.mp common⟩
      · cases accepted

def initialize {W : Type} {m : Nat} (opening : SharedOpening W) (learning : RoundState m) : Result (State m) :=
  if learning.service.gamma = opening.handle.gamma then
    .known ⟨⟨.success, some opening.handle, [], []⟩, learning,
      .known [], .unknown .missingEvidence, [], []⟩
  else .unknown .scopeMismatch

def framesFor {W : Type} (input : LegalInput W) : Result (List (BranchOpening W)) :=
  match input.inspect with
  | .known reports => collectFrames reports
  | .unknown e => .unknown e
  | .rejected e => .rejected e
  | .conflict a b => .conflict a b

def openingFor {W : Type} (input : LegalInput W) : Result (SharedOpening W) :=
  match framesFor input with
  | .known frames => proposeOpening input frames
  | .unknown e => .unknown e
  | .rejected e => .rejected e
  | .conflict a b => .conflict a b

def start {W : Type} {m : Nat} (input : LegalInput W) (learning : RoundState m) : Result (State m) :=
  match openingFor input with
  | .known opening => initialize opening learning
  | .unknown e => .unknown e
  | .rejected e => .rejected e
  | .conflict a b => .conflict a b

theorem known_opening_consumes_the_actual_inspection {W : Type}
    (input : LegalInput W) (out : SharedOpening W) (accepted : openingFor input = .known out) :
    ∃ reports frames, input.inspect = .known reports ∧ collectFrames reports = .known frames ∧
      proposeOpening input frames = .known out := by
  cases inspected : input.inspect with
  | unknown e => simp [openingFor, framesFor, inspected] at accepted
  | rejected e => simp [openingFor, framesFor, inspected] at accepted
  | conflict a b => simp [openingFor, framesFor, inspected] at accepted
  | known reports =>
      cases framed : collectFrames reports with
      | unknown e => simp [openingFor, framesFor, inspected, framed] at accepted
      | rejected e => simp [openingFor, framesFor, inspected, framed] at accepted
      | conflict a b => simp [openingFor, framesFor, inspected, framed] at accepted
      | known frames =>
          exact ⟨reports, frames, inspected, framed,
            by simpa only [openingFor, framesFor, inspected, framed] using accepted⟩

theorem known_common_opening_has_proved_business_invariant {W : Type}
    (input : LegalInput W) (out : SharedOpening W) (accepted : openingFor input = .known out) :
    Trace.Invariant out.handle := by
  obtain ⟨reports, frames, inspected, collected, proposed⟩ :=
    known_opening_consumes_the_actual_inspection input out accepted
  have common := known_opening_keeps_every_common_branch input frames out proposed
  obtain ⟨row, _, framed⟩ := every_collected_frame_has_an_actual_report reports frames collected out.anchor common.1
  have actual := (known_frame_consumes_actual_legal_source row out.anchor framed).2.2
  rw [common.2.2.2.1]
  exact source_opening_has_a_proved_initial_invariant _ _ _ actual

theorem initialized_state_keeps_supplied_learner_and_actual_opening {W : Type} {m : Nat}
    (opening : SharedOpening W) (learning : RoundState m) (out : State m)
    (accepted : initialize opening learning = .known out) :
    out.learning = learning ∧ out.business.current = some opening.handle ∧
      learning.service.gamma = opening.handle.gamma := by
  unfold initialize at accepted
  split at accepted
  · rename_i same
    cases accepted
    exact ⟨rfl, rfl, same⟩
  · cases accepted

theorem source_initialized_state_has_proved_known_invariant {W : Type} {m : Nat}
    (input : LegalInput W) (learning : RoundState m) (out : State m)
    (accepted : start input learning = .known out) :
    KnownBusinessInvariant out ∧ out.learning = learning := by
  cases opening : openingFor input with
  | unknown e => simp [start, opening] at accepted
  | rejected e => simp [start, opening] at accepted
  | conflict a b => simp [start, opening] at accepted
  | known opened =>
      have initialized : initialize opened learning = .known out := by simpa only [start, opening] using accepted
      have actual := initialized_state_keeps_supplied_learner_and_actual_opening opened learning out initialized
      refine ⟨?_, actual.1⟩
      intro post reported
      have same : opened.handle = post := Option.some.inj (actual.2.1.symm.trans reported)
      exact same ▸ known_common_opening_has_proved_business_invariant input opened opening

theorem arbitrary_finite_commands_start_from_actual_source {W : Type} {m : Nat}
    (input : LegalInput W) (learning : RoundState m) (initial : State m)
    (commands : List (Command W m)) (accepted : start input learning = .known initial)
    (budget : roundSpent learning ≤ learning.limit) :
    KnownBusinessInvariant (commands.foldl step initial) ∧
    (commands.foldl step initial).learning.limit = learning.limit ∧
    roundSpent (commands.foldl step initial).learning ≤ learning.limit := by
  have initialProof := source_initialized_state_has_proved_known_invariant input learning initial accepted
  have result := arbitrary_finite_commands_consume_actual_posts commands initial initialProof.1
    (by simpa only [initialProof.2] using budget)
  simpa only [initialProof.2] using result

end JurisLean.Candidates.SourceOpening20261027
