import JurisLean.Candidates.FiniteLegalValidation20261027
import JurisLean.Candidates.DecisionTrajectoryConsumer20261027

/-!
Original 04 edge 5: actual source/version/evidence/process results determine the
finite legal action domain consumed by the sampled decision and payment path.
Independent meanings bind a complete instruction list, not merely an action ID.
The normative meaning of atoms and completeness of the supplied successor model
remain explicit interpretation premises. No empirical or legal authority is
created by the finite checker. Unknown/failed branches remain in the review.
-/

namespace JurisLean.Candidates.LegalActionDomain20261027

open JurisLean.Candidates.Final20261021
open JurisLean.Candidates.Final20261021.EvidenceProcedure
open JurisLean.Candidates.SourceCompilation20261027
open JurisLean.Candidates.CompilerProvenance20261027
open JurisLean.Candidates.TemporalInterpretation20261027
open JurisLean.Candidates.EvidenceWorlds20261027
open JurisLean.Candidates.FiniteLegalValidation20261027
open JurisLean.Candidates.LearningConsumer20261027
open JurisLean.Candidates.SampleCalibrationConsumer20261027
open JurisLean.Candidates.IntervalDecisionConsumer20261027
open JurisLean.Candidates.DecisionTrajectoryConsumer20261027

structure Proposal where
  quote : BinaryQuote
  steps : List Instruction
  deriving DecidableEq, Repr

-- An independently supplied normative interpretation row. Checker and fitted
-- model versions are distinct. The source reference identifies the external
-- meaning contract; its presence is not a proof of that contract's truth.
structure ActionMeaning where
  gamma : Gamma
  checkerVersion : Nat
  source : SourceRef
  actionId : Nat
  steps : List Instruction
  permissionAtoms : List Nat
  requiresClosed : Bool
  deriving DecidableEq, Repr

structure ActionModel (W S : Type) where
  checkerVersion : Nat
  meanings : List ActionMeaning
  successors : Gamma → W → S → List Instruction → List S
  invariant : Gamma → W → S → Bool

def meaningRows {W S : Type} (model : ActionModel W S) (g : Gamma)
    (proposal : Proposal) : List ActionMeaning :=
  model.meanings.filter fun row => decide (row.gamma = g ∧
    row.checkerVersion = model.checkerVersion ∧ row.actionId = proposal.quote.id ∧
    row.steps = proposal.steps)

theorem meaning_row_binds_full_instructions {W S : Type} (model : ActionModel W S)
    (g : Gamma) (proposal : Proposal) (row : ActionMeaning) :
    row ∈ meaningRows model g proposal ↔ row ∈ model.meanings ∧ row.gamma = g ∧
      row.checkerVersion = model.checkerVersion ∧ row.actionId = proposal.quote.id ∧
      row.steps = proposal.steps := by
  simp [meaningRows]

def rowSafe {W S : Type} (model : ActionModel W S) (truth : W → Nat → Bool)
    (before : S) (row : ActionMeaning) (worlds : List W) : Bool :=
  worlds.all fun w => row.permissionAtoms.all (truth w) &&
    !(model.successors row.gamma w before row.steps).isEmpty &&
    (model.successors row.gamma w before row.steps).all (model.invariant row.gamma w)

theorem finite_row_checks_every_world_and_successor {W S : Type}
    (model : ActionModel W S) (truth : W → Nat → Bool) (before : S)
    (row : ActionMeaning) (worlds : List W) :
    rowSafe model truth before row worlds = true ↔
      ∀ w ∈ worlds, (∀ atom ∈ row.permissionAtoms, truth w atom = true) ∧
        model.successors row.gamma w before row.steps ≠ [] ∧
        ∀ after ∈ model.successors row.gamma w before row.steps,
          model.invariant row.gamma w after = true := by
  simp [rowSafe, List.all_eq_true, Bool.and_eq_true, and_assoc]

def checkMeaning {W S : Type} (model : ActionModel W S) (truth : W → Nat → Bool)
    (before : S) (row : ActionMeaning) (worlds : List W) (procedure : Procedure) : Result Bool :=
  if worlds.isEmpty then .unknown .incompatibleFiber
  else if row.requiresClosed && decide (procedure ≠ .closedLawfully) then .unknown .openMissingOpportunity
  else .known (rowSafe model truth before row worlds)

theorem accepted_meaning_has_nonempty_worlds_and_required_closure {W S : Type}
    (model : ActionModel W S) (truth : W → Nat → Bool) (before : S)
    (row : ActionMeaning) (worlds : List W) (procedure : Procedure)
    (accepted : checkMeaning model truth before row worlds procedure = .known true) :
    worlds ≠ [] ∧ (row.requiresClosed = true → procedure = .closedLawfully) ∧
      rowSafe model truth before row worlds = true := by
  unfold checkMeaning at accepted
  split at accepted
  · cases accepted
  · rename_i nonempty
    split at accepted
    · cases accepted
    · rename_i closure
      have rowChecked : rowSafe model truth before row worlds = true := Result.known.inj accepted
      refine ⟨by simpa using nonempty, ?_, rowChecked⟩
      intro needed
      simpa [needed] using closure

def checkBranch {W S : Type} (model : ActionModel W S) (truth : W → Nat → Bool)
    (before : S) (proposal : Proposal) (report : ValidationReport W) : Result Bool :=
  match report.worldView with
  | .known view =>
      match report.procedure with
      | .known procedure =>
          match meaningRows model report.bound.source.material.gamma proposal with
          | [row] => checkMeaning model truth before row view.possibleWorlds procedure
          | [] => .unknown .authorityUnresolved
          | _ => .rejected .versionConflict
      | .unknown e => .unknown e
      | .rejected e => .rejected e
      | .conflict l r => .conflict l r
  | .unknown e => .unknown e
  | .rejected e => .rejected e
  | .conflict l r => .conflict l r

theorem branch_acceptance_uses_actual_worlds_and_unique_meaning {W S : Type}
    (model : ActionModel W S) (truth : W → Nat → Bool) (before : S)
    (proposal : Proposal) (report : ValidationReport W)
    (accepted : checkBranch model truth before proposal report = .known true) :
    ∃ view procedure row,
      report.worldView = .known view ∧ report.procedure = .known procedure ∧
      meaningRows model report.bound.source.material.gamma proposal = [row] ∧
      checkMeaning model truth before row view.possibleWorlds procedure = .known true := by
  unfold checkBranch at accepted
  cases worldResult : report.worldView with
  | unknown e => simp [worldResult] at accepted
  | rejected e => simp [worldResult] at accepted
  | conflict l r => simp [worldResult] at accepted
  | known view =>
      simp only [worldResult] at accepted
      cases processResult : report.procedure with
      | unknown e => simp [processResult] at accepted
      | rejected e => simp [processResult] at accepted
      | conflict l r => simp [processResult] at accepted
      | known procedure =>
          simp only [processResult] at accepted
          cases rows : meaningRows model report.bound.source.material.gamma proposal with
          | nil => simp [rows] at accepted
          | cons row rest =>
              cases rest with
              | nil => exact ⟨view, procedure, row, rfl, rfl, rfl,
                  by simpa only [rows] using accepted⟩
              | cons other rest => simp [rows] at accepted

def branchCheck {W S : Type} (model : ActionModel W S) (truth : W → Nat → Bool)
    (before : S) (proposal : Proposal) : Result (ValidationReport W) → Result Bool
  | .known report => checkBranch model truth before proposal report
  | .unknown e => .unknown e
  | .rejected e => .rejected e
  | .conflict l r => .conflict l r

def checks {W S : Type} (model : ActionModel W S) (truth : W → Nat → Bool)
    (before : S) (proposal : Proposal) (branches : List (Nat × Result (ValidationReport W))) :
    List (Nat × Result Bool) :=
  branches.map fun branch => (branch.1, branchCheck model truth before proposal branch.2)

def accepts {W S : Type} (model : ActionModel W S) (truth : W → Nat → Bool)
    (before : S) (g : Gamma) (branches : List (Nat × Result (ValidationReport W)))
    (proposal : Proposal) : Bool :=
  decide (proposal.quote.gamma = g ∧ paymentPayloads proposal.steps = proposal.quote.execution) &&
    !branches.isEmpty && (checks model truth before proposal branches).all fun check =>
      decide (check.2 = .known true)

theorem acceptance_binds_proposal_and_every_branch {W S : Type}
    (model : ActionModel W S) (truth : W → Nat → Bool) (before : S) (g : Gamma)
    (branches : List (Nat × Result (ValidationReport W))) (proposal : Proposal) :
    accepts model truth before g branches proposal = true ↔
      (proposal.quote.gamma = g ∧ paymentPayloads proposal.steps = proposal.quote.execution) ∧
      branches ≠ [] ∧ ∀ branch ∈ branches,
        branchCheck model truth before proposal branch.2 = .known true := by
  simp [accepts, checks, List.all_eq_true, Bool.and_eq_true, and_assoc]

theorem accepted_actual_branch_step_preserves_declared_invariant {W S : Type}
    (model : ActionModel W S) (truth : W → Nat → Bool) (before after : S)
    (proposal : Proposal) (report : ValidationReport W) (actual : W)
    (view : EvidenceView W) (procedure : Procedure) (row : ActionMeaning)
    (accepted : checkBranch model truth before proposal report = .known true)
    (worldResult : report.worldView = .known view)
    (processResult : report.procedure = .known procedure)
    (meaning : meaningRows model report.bound.source.material.gamma proposal = [row])
    (actualWorld : actual ∈ view.possibleWorlds)
    (actualStep : after ∈ model.successors row.gamma actual before row.steps) :
    (∀ atom ∈ row.permissionAtoms, truth actual atom = true) ∧
      model.invariant row.gamma actual after = true := by
  have checked : checkMeaning model truth before row view.possibleWorlds procedure = .known true := by
    simpa only [checkBranch, worldResult, processResult, meaning] using accepted
  have safe := (accepted_meaning_has_nonempty_worlds_and_required_closure
    model truth before row view.possibleWorlds procedure checked).2.2
  have atActual := (finite_row_checks_every_world_and_successor model truth before row
    view.possibleWorlds).mp safe actual actualWorld
  exact ⟨atActual.1, atActual.2.2 after actualStep⟩

theorem unresolved_branch_cannot_be_silently_removed {W S : Type}
    (model : ActionModel W S) (truth : W → Nat → Bool) (before : S) (g : Gamma)
    (branches : List (Nat × Result (ValidationReport W))) (proposal : Proposal)
    (key : Nat) (e : Error) (pending : (key, Result.unknown e) ∈ branches) :
    accepts model truth before g branches proposal ≠ true := by
  intro accepted
  have allBranches := (acceptance_binds_proposal_and_every_branch model truth before g
    branches proposal).mp accepted
  have impossible := allBranches.2.2 (key, Result.unknown e) pending
  cases impossible

def allowedProposals {W S : Type} (model : ActionModel W S) (truth : W → Nat → Bool)
    (before : S) (g : Gamma) (branches : List (Nat × Result (ValidationReport W)))
    (proposals : List Proposal) : List Proposal :=
  proposals.filter (accepts model truth before g branches)

theorem legal_domain_is_exact_filter_not_a_generator {W S : Type}
    (model : ActionModel W S) (truth : W → Nat → Bool) (before : S) (g : Gamma)
    (branches : List (Nat × Result (ValidationReport W))) (proposals : List Proposal)
    (proposal : Proposal) :
    proposal ∈ allowedProposals model truth before g branches proposals ↔
      proposal ∈ proposals ∧ accepts model truth before g branches proposal = true := by
  exact List.mem_filter

structure LegalInput (W : Type) where
  anchor : MaterialSnapshot
  branches : List BranchCase
  catalog : List InterpretationRow
  supplements : List Supplement
  policies : List ProcessPolicy
  history : List Temporal.VersionRecord
  versions : List Nat
  app : App
  rules : List RuleUse
  ruleGate : Gamma → RuleUse → Bool
  allowedPairs : List (Nat × W)
  truth : W → Nat → Bool

def LegalInput.inspect {W : Type} (input : LegalInput W) :
    Result (List (Nat × Result (ValidationReport W))) :=
  validateFamily input.anchor input.branches input.catalog input.supplements input.policies
    input.history input.versions input.app input.rules input.ruleGate input.allowedPairs input.truth

structure DomainReview (W : Type) where
  validation : Result (List (Nat × Result (ValidationReport W)))
  results : List (Proposal × List (Nat × Result Bool))
  allowed : List Proposal

def review {W S : Type} (input : LegalInput W) (model : ActionModel W S)
    (before : S) (proposals : List Proposal) : DomainReview W :=
  let validation := input.inspect
  match validation with
  | .known branches => ⟨validation,
      proposals.map (fun p => (p, checks model input.truth before p branches)),
      allowedProposals model input.truth before input.anchor.gamma branches proposals⟩
  | _ => ⟨validation, [], []⟩

theorem domain_consumes_actual_validator {W S : Type} (input : LegalInput W)
    (model : ActionModel W S) (before : S) (proposals : List Proposal) (proposal : Proposal)
    (included : proposal ∈ (review input model before proposals).allowed) :
    ∃ branches, input.inspect = .known branches ∧ proposal ∈ proposals ∧
      accepts model input.truth before input.anchor.gamma branches proposal = true := by
  cases inspected : input.inspect with
  | known branches =>
      have filtered : proposal ∈ allowedProposals model input.truth before input.anchor.gamma
          branches proposals := by simpa only [review, inspected] using included
      exact ⟨branches, rfl, (legal_domain_is_exact_filter_not_a_generator
        model input.truth before input.anchor.gamma branches proposals proposal).mp filtered⟩
  | unknown e => simp [review, inspected] at included
  | rejected e => simp [review, inspected] at included
  | conflict l r => simp [review, inspected] at included

-- The chosen complete plan is recovered by reevaluating the same quote against
-- the actual probability receipt. An ID-only lookup is intentionally absent.
def matchingSelection {m : Nat} (request : DecisionRequest m) (utility : ℚ → ℚ)
    (selected : IntervalDecision m) (proposals : List Proposal) : List Proposal :=
  proposals.filter fun p => decide (evaluateInterval request utility selected.probability p.quote =
    .known selected)

def selectPlan {m : Nat} (request : DecisionRequest m) (utility : ℚ → ℚ)
    (selected : IntervalDecision m) (proposals : List Proposal) : Option Proposal :=
  (matchingSelection request utility selected proposals).head?

theorem selected_plan_was_approved_and_reproduces_the_decision {m : Nat}
    (request : DecisionRequest m) (utility : ℚ → ℚ) (selected : IntervalDecision m)
    (proposals : List Proposal) (proposal : Proposal)
    (chosen : selectPlan request utility selected proposals = some proposal) :
    proposal ∈ proposals ∧
      evaluateInterval request utility selected.probability proposal.quote = .known selected := by
  unfold selectPlan at chosen
  cases listed : matchingSelection request utility selected proposals with
  | nil => simp [listed] at chosen
  | cons first rest =>
      have same : first = proposal := by simpa [listed] using chosen
      subst first
      have member : proposal ∈ matchingSelection request utility selected proposals := by simp [listed]
      simpa [matchingSelection] using member

structure ExecutionChoice where
  proposal : Option Proposal
  payment : Pipeline.PaymentRun

def executeDecision {m : Nat} (request : DecisionRequest m) (utility : ℚ → ℚ)
    (proposals : List Proposal) (decision : Result (IntervalDecision m))
    (grants : List Authorization.Grant) (initial : Ledger.Handle) : ExecutionChoice :=
  match decision with
  | .known selected =>
      match selectPlan request utility selected proposals with
      | some proposal => ⟨some proposal, executeSelected selected grants initial proposal.steps⟩
      | none => ⟨none, ⟨.rejected, some initial, [], [.scopeMismatch]⟩⟩
  | .unknown e => ⟨none, ⟨.undecided, some initial, [], [e]⟩⟩
  | .rejected e => ⟨none, ⟨.rejected, some initial, [], [e]⟩⟩
  | .conflict _ _ => ⟨none, ⟨.undecided, some initial, [], [.versionConflict]⟩⟩

theorem no_selected_plan_preserves_all_business_state {m : Nat}
    (request : DecisionRequest m) (utility : ℚ → ℚ) (proposals : List Proposal)
    (decision : Result (IntervalDecision m)) (grants : List Authorization.Grant)
    (initial : Ledger.Handle)
    (noneSelected : (executeDecision request utility proposals decision grants initial).proposal = none) :
    (executeDecision request utility proposals decision grants initial).payment.current = some initial ∧
    (executeDecision request utility proposals decision grants initial).payment.outcomes = [] := by
  cases decision with
  | known selected =>
      cases plan : selectPlan request utility selected proposals with
      | none => simp [executeDecision, plan]
      | some proposal => simp [executeDecision, plan] at noneSelected
  | unknown e => simp [executeDecision]
  | rejected e => simp [executeDecision]
  | conflict l r => simp [executeDecision]

theorem chosen_execution_uses_the_entire_approved_instruction_list {m : Nat}
    (request : DecisionRequest m) (utility : ℚ → ℚ) (proposals : List Proposal)
    (decision : Result (IntervalDecision m)) (grants : List Authorization.Grant)
    (initial : Ledger.Handle) (proposal : Proposal)
    (chosen : (executeDecision request utility proposals decision grants initial).proposal = some proposal) :
    ∃ selected, decision = .known selected ∧ proposal ∈ proposals ∧
      evaluateInterval request utility selected.probability proposal.quote = .known selected ∧
      (executeDecision request utility proposals decision grants initial).payment =
        executeSelected selected grants initial proposal.steps := by
  cases decision with
  | known selected =>
      cases plan : selectPlan request utility selected proposals with
      | none => simp [executeDecision, plan] at chosen
      | some actual =>
          have same : actual = proposal := by simpa only [executeDecision, plan, Option.some.injEq] using chosen
          subst actual
          have linked := selected_plan_was_approved_and_reproduces_the_decision request utility
            selected proposals proposal plan
          exact ⟨selected, rfl, linked.1, linked.2, by simp [executeDecision, plan]⟩
  | unknown e => simp [executeDecision] at chosen
  | rejected e => simp [executeDecision] at chosen
  | conflict l r => simp [executeDecision] at chosen

theorem execution_choice_preserves_reported_state_invariant {m : Nat}
    (request : DecisionRequest m) (utility : ℚ → ℚ) (proposals : List Proposal)
    (decision : Result (IntervalDecision m)) (grants : List Authorization.Grant)
    (initial final : Ledger.Handle) (valid : Trace.Invariant initial)
    (reported : (executeDecision request utility proposals decision grants initial).payment.current = some final) :
    Trace.Invariant final := by
  cases choice : (executeDecision request utility proposals decision grants initial).proposal with
  | none =>
      have frame := (no_selected_plan_preserves_all_business_state request utility proposals decision
        grants initial choice).1
      have same : initial = final := Option.some.inj (frame.symm.trans reported)
      simpa [← same] using valid
  | some proposal =>
      obtain ⟨selected, _, _, _, executed⟩ := chosen_execution_uses_the_entire_approved_instruction_list
        request utility proposals decision grants initial proposal choice
      exact selected_execution_preserves_full_invariant selected grants initial final proposal.steps valid
        (by simpa only [executed] using reported)

structure LegalDecisionRun (W : Type) (m : Nat) where
  review : DomainReview W
  decision : Result (IntervalDecision m)
  execution : ExecutionChoice

def runLegalDecision {W : Type} {m n k : Nat} (input : LegalInput W)
    (model : ActionModel W Ledger.Handle) (proposals : List Proposal)
    (request : DecisionRequest m) (sampleProtocol : LearningProtocol)
    (loss : ℚ → Bool → ℚ) (models : List (List ℚ))
    (training : Fin n → SampleObservation m Bool) (calibration : Fin k → SampleObservation m Bool)
    (radius : ℚ) (exponent : Nat) (supported : Bool) (utility : ℚ → ℚ)
    (grants : List Authorization.Grant) (initial : Ledger.Handle) : LegalDecisionRun W m :=
  let domain := review input model initial proposals
  let decision := if input.anchor.gamma ≠ request.gamma ∨ initial.gamma ≠ request.gamma then
      Result.rejected .scopeMismatch
    else fitChooseMaximin request sampleProtocol loss models training calibration radius exponent supported utility
      (domain.allowed.map fun p => p.quote.id) (domain.allowed.map Proposal.quote)
  ⟨domain, decision, executeDecision request utility domain.allowed decision grants initial⟩

theorem complete_consumer_choice_has_actual_legal_validation {W : Type} {m n k : Nat}
    (input : LegalInput W) (model : ActionModel W Ledger.Handle) (proposals : List Proposal)
    (request : DecisionRequest m) (sampleProtocol : LearningProtocol) (loss : ℚ → Bool → ℚ)
    (models : List (List ℚ)) (training : Fin n → SampleObservation m Bool)
    (calibration : Fin k → SampleObservation m Bool) (radius : ℚ) (exponent : Nat)
    (supported : Bool) (utility : ℚ → ℚ) (grants : List Authorization.Grant)
    (initial : Ledger.Handle) (proposal : Proposal)
    (chosen : (runLegalDecision input model proposals request sampleProtocol loss models training calibration
      radius exponent supported utility grants initial).execution.proposal = some proposal) :
    ∃ branches, input.inspect = .known branches ∧ proposal ∈ proposals ∧
      accepts model input.truth initial input.anchor.gamma branches proposal = true := by
  have linked := chosen_execution_uses_the_entire_approved_instruction_list request utility
    (review input model initial proposals).allowed _ grants initial proposal chosen
  obtain ⟨selected, _, member, _, _⟩ := linked
  exact domain_consumes_actual_validator input model initial proposals proposal member

-- Original 02.3/02.5: a deterministic observation-only decision cannot be both
-- sound and complete when the same observation hides different permissions.
theorem indistinguishable_permission_prevents_sound_and_complete {S O A : Type}
    (observe : S → O) (admissible : S → A → Prop) (gate : O → A → Bool)
    (s t : S) (a : A) (same : observe s = observe t)
    (allowed : admissible s a) (forbidden : ¬ admissible t a)
    (sound : ∀ state action, gate (observe state) action = true → admissible state action)
    (complete : ∀ state action, admissible state action → gate (observe state) action = true) : False := by
  have accepted := complete s a allowed
  rw [same] at accepted
  exact forbidden (sound t a accepted)

theorem pure_filter_cannot_offer_an_unproposed_action {A : Type} (candidate : A)
    (proposals : List A) (safe : A → Bool) (absent : candidate ∉ proposals) :
    candidate ∉ proposals.filter safe := by
  intro included
  exact absent (List.mem_filter.mp included).1

-- Ratios have distinct denominators. Zero coverage is not zero accepted risk,
-- and an empty truly-allowed population has no defined false-blocking rate.
def rateReport (acceptedMass badAcceptedMass allowedMass blockedAllowedMass : ℚ) : Result ℚ × Result ℚ :=
  (Harness.conditionalRisk badAcceptedMass acceptedMass,
    Harness.conditionalRisk blockedAllowedMass allowedMass)

theorem undefined_denominators_remain_unknown :
    rateReport 0 0 0 0 = (Result.unknown .notIdentified, Result.unknown .notIdentified) := by
  simp [rateReport, Harness.conditionalRisk]

end JurisLean.Candidates.LegalActionDomain20261027
