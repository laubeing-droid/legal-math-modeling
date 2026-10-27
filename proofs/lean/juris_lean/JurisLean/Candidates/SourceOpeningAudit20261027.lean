import JurisLean.Candidates.SourceOpening20261027
import JurisLean.Candidates.SourceStagesAudit20261027
import JurisLean.Candidates.FiniteLegalValidationAudit20261027
import JurisLean.Candidates.AdaptiveRoundLedgerAudit20261027

#check JurisLean.Candidates.SourceOpening20261027.known_frame_consumes_actual_legal_source
#print axioms JurisLean.Candidates.SourceOpening20261027.known_frame_consumes_actual_legal_source
#check JurisLean.Candidates.SourceOpening20261027.every_collected_frame_has_an_actual_report
#print axioms JurisLean.Candidates.SourceOpening20261027.every_collected_frame_has_an_actual_report
#check JurisLean.Candidates.SourceOpening20261027.collected_branch_keys_are_not_filtered
#print axioms JurisLean.Candidates.SourceOpening20261027.collected_branch_keys_are_not_filtered
#check JurisLean.Candidates.SourceOpening20261027.opening_reads_formed_source_without_claiming_payments
#print axioms JurisLean.Candidates.SourceOpening20261027.opening_reads_formed_source_without_claiming_payments
#check JurisLean.Candidates.SourceOpening20261027.source_opening_has_a_proved_initial_invariant
#print axioms JurisLean.Candidates.SourceOpening20261027.source_opening_has_a_proved_initial_invariant
#check JurisLean.Candidates.SourceOpening20261027.known_opening_keeps_every_common_branch
#print axioms JurisLean.Candidates.SourceOpening20261027.known_opening_keeps_every_common_branch
#check JurisLean.Candidates.SourceOpening20261027.known_opening_consumes_the_actual_inspection
#print axioms JurisLean.Candidates.SourceOpening20261027.known_opening_consumes_the_actual_inspection
#check JurisLean.Candidates.SourceOpening20261027.known_common_opening_has_proved_business_invariant
#print axioms JurisLean.Candidates.SourceOpening20261027.known_common_opening_has_proved_business_invariant
#check JurisLean.Candidates.SourceOpening20261027.initialized_state_keeps_supplied_learner_and_actual_opening
#print axioms JurisLean.Candidates.SourceOpening20261027.initialized_state_keeps_supplied_learner_and_actual_opening
#check JurisLean.Candidates.SourceOpening20261027.source_initialized_state_has_proved_known_invariant
#print axioms JurisLean.Candidates.SourceOpening20261027.source_initialized_state_has_proved_known_invariant
#check JurisLean.Candidates.SourceOpening20261027.arbitrary_finite_commands_start_from_actual_source
#print axioms JurisLean.Candidates.SourceOpening20261027.arbitrary_finite_commands_start_from_actual_source

open JurisLean.Candidates.Final20261021
open JurisLean.Candidates.SourceCompilation20261027
open JurisLean.Candidates.SourceStages20261027
open JurisLean.Candidates.FiniteLegalValidation20261027
open JurisLean.Candidates.LegalActionDomain20261027
open JurisLean.Candidates.AdaptiveRoundLedger20261027
open JurisLean.Candidates.BusinessFeedbackLoop20261027
open JurisLean.Candidates.SourceOpening20261027

namespace JurisLean.Candidates.SourceOpening20261027.Audit

def materialA : MaterialSnapshot := FiniteLegalValidation20261027.Audit.material
def materialB : MaterialSnapshot := {materialA with gamma := {materialA.gamma with interpretation := 8}}

def source : ConsumedView :=
  {stageView with
    record := FiniteLegalValidation20261027.Audit.source.record
    atoms := FiniteLegalValidation20261027.Audit.source.atoms}

def history : List Temporal.VersionRecord := [⟨⟨80⟩, 8, "synthetic", 3, ⟨0⟩, none, ⟨0⟩, ⟨0⟩⟩]

def legalInput : LegalInput (List Nat) :=
  { anchor := materialA
    branches := [⟨0, materialA, 0⟩, ⟨1, materialB, 0⟩]
    catalog := [⟨materialA, 0, source⟩, ⟨materialB, 0, source⟩]
    supplements := [FiniteLegalValidation20261027.Audit.supplement,
      {FiniteLegalValidation20261027.Audit.supplement with material := materialB}]
    policies := [FiniteLegalValidation20261027.Audit.policy,
      {FiniteLegalValidation20261027.Audit.policy with gamma := materialB.gamma}]
    history := history
    versions := [8]
    app := FiniteLegalValidation20261027.Audit.app
    rules := FiniteLegalValidation20261027.Audit.rules
    ruleGate := fun _ _ => true
    allowedPairs := FiniteLegalValidation20261027.Audit.worlds.map (fun w => (0, w)) ++
      FiniteLegalValidation20261027.Audit.worlds.map (fun w => (1, w))
    truth := FiniteLegalValidation20261027.Audit.valuation }

def isKnown {A : Type} : Result A → Bool
  | .known _ => true
  | _ => false

/-- info: true -/
#guard_msgs in
#eval match openingFor legalInput with
  | .known out => decide (out.branches.map BranchOpening.key = [0, 1] ∧
      out.anchor.frame.source.material = materialA ∧ out.handle.gamma = materialA.gamma ∧
      out.handle.state.initialDebt = 10 ∧ Ledger.balance out.handle.state = 10 ∧
      out.handle.state.formations = [(⟨9⟩ : RelationId)] ∧ out.handle.state.paid = 0 ∧
      out.handle.state.receipts = [] ∧ out.handle.state.cash = [] ∧
      out.handle.state.normHistory = history ∧ out.handle.state.env = Result.known (8 : Nat) ∧
      out.anchor.frame.stages.afterSecond.state.paid = 14)
  | _ => false

-- A structural opening grants neither a supported judgment nor closed procedure.
/-- info: true -/
#guard_msgs in
#eval match openingFor legalInput with
  | .known out => decide (out.handle.state.judgment = Judgment.insufficient ∧
      out.handle.state.procedure = Procedure.open ∧ out.handle.state.claim = Applicable.unknown ∧
      out.handle.state.executionEligible = false)
  | _ => false

/-- info: true -/
#guard_msgs in
#eval match openingFor {legalInput with branches := []} with
  | .known _ => false
  | _ => true

/-- info: true -/
#guard_msgs in
#eval match openingFor {legalInput with branches := [⟨0, materialB, 0⟩]} with
  | .unknown .incompatibleFiber => true
  | _ => false

/-- info: true -/
#guard_msgs in
#eval
  let missing := {legalInput with catalog := [⟨materialA, 0, source⟩]}
  match missing.inspect, openingFor missing with
  | .known reports, .unknown .missingEvidence => decide (reports.map Prod.fst = [0, 1])
  | _, _ => false

/-- info: true -/
#guard_msgs in
#eval
  let changed := {source with
    relations := source.relations.map (fun r => {r with value :=
      {r.value with amount := ⟨20, stageTag⟩}})
    ledger := source.ledger.map (fun d => {d with value :=
      {d.value with item := {d.value.item with amount := 20}}})}
  match openingFor {legalInput with catalog := [⟨materialA, 0, source⟩, ⟨materialB, 0, changed⟩]} with
  | .unknown .incompatibleFiber => true
  | _ => false

/-- info: true -/
#guard_msgs in
#eval
  let changed := {source with payments := source.payments.map fun p =>
    {p with value := {p.value with payload := {p.value.payload with amount := ⟨8, stageTag⟩}}}}
  match openingFor {legalInput with catalog := [⟨materialA, 0, source⟩, ⟨materialB, 0, changed⟩]} with
  | .unknown .incompatibleFiber => true
  | _ => false

/-- info: true -/
#guard_msgs in
#eval
  let broken := {source with payments := source.payments ++ source.payments}
  !isKnown (openingFor {legalInput with catalog := [⟨materialA, 0, source⟩, ⟨materialB, 0, broken⟩]})

/-- info: true -/
#guard_msgs in
#eval !isKnown (openingFor {legalInput with branches := [⟨0, materialA, 0⟩, ⟨0, materialB, 0⟩]})

-- The environment is derived from the actual supplied history, including its
-- unresolved result. It is not filled in from the validator's separate app table.
/-- info: true -/
#guard_msgs in
#eval match openingFor {legalInput with history := []} with
  | .known out => decide (out.handle.state.env = (Result.unknown Error.missingEvidence : Result Nat) ∧
      out.handle.state.normHistory = [] ∧ out.handle.state.paid = 0)
  | _ => false

/-- info: true -/
#guard_msgs in
#eval ValidatedFeedbackLoadFixture.check (fun service _ =>
  let learning := AdaptiveRoundLedgerFixture.base {service with gamma := materialA.gamma}
  match start legalInput learning with
  | .known out => match out.business.current with
    | some post => decide (out.learning = learning ∧ post.state.debt.amount.value = 10 ∧
        out.business.outcomes = [] ∧ out.policyRows = .known [] ∧ out.feedbackQueue = [])
    | none => false
  | _ => false)

/-- info: true -/
#guard_msgs in
#eval ValidatedFeedbackLoadFixture.check (fun service _ =>
  match start legalInput (AdaptiveRoundLedgerFixture.base service) with
  | .unknown .scopeMismatch => true
  | _ => false)

end JurisLean.Candidates.SourceOpening20261027.Audit
