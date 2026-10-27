import JurisLean.Candidates.FiniteLegalValidation20261027

#check JurisLean.Candidates.FiniteLegalValidation20261027.fired_conclusions_are_enabled_rules
#print axioms JurisLean.Candidates.FiniteLegalValidation20261027.fired_conclusions_are_enabled_rules
#check JurisLean.Candidates.FiniteLegalValidation20261027.advance_is_recorded_round
#print axioms JurisLean.Candidates.FiniteLegalValidation20261027.advance_is_recorded_round
#check JurisLean.Candidates.FiniteLegalValidation20261027.generated_trace_has_actual_rule_premises
#print axioms JurisLean.Candidates.FiniteLegalValidation20261027.generated_trace_has_actual_rule_premises
#check JurisLean.Candidates.FiniteLegalValidation20261027.replay_generated_trace_is_exact_closure
#print axioms JurisLean.Candidates.FiniteLegalValidation20261027.replay_generated_trace_is_exact_closure
#check JurisLean.Candidates.FiniteLegalValidation20261027.trace_has_exact_number_of_rounds
#print axioms JurisLean.Candidates.FiniteLegalValidation20261027.trace_has_exact_number_of_rounds
#check JurisLean.Candidates.FiniteLegalValidation20261027.enabled_count_bounded_by_rule_count
#print axioms JurisLean.Candidates.FiniteLegalValidation20261027.enabled_count_bounded_by_rule_count
#check JurisLean.Candidates.FiniteLegalValidation20261027.closure_list_size_bound
#print axioms JurisLean.Candidates.FiniteLegalValidation20261027.closure_list_size_bound
#check JurisLean.Candidates.FiniteLegalValidation20261027.full_horn_consumes_every_source_fact
#print axioms JurisLean.Candidates.FiniteLegalValidation20261027.full_horn_consumes_every_source_fact
#check JurisLean.Candidates.FiniteLegalValidation20261027.full_horn_trace_is_checked
#print axioms JurisLean.Candidates.FiniteLegalValidation20261027.full_horn_trace_is_checked
#check JurisLean.Candidates.FiniteLegalValidation20261027.bound_data_keeps_exact_source_and_independent_policy
#print axioms JurisLean.Candidates.FiniteLegalValidation20261027.bound_data_keeps_exact_source_and_independent_policy
#check JurisLean.Candidates.FiniteLegalValidation20261027.selected_horn_cannot_rewrite_original_context
#print axioms JurisLean.Candidates.FiniteLegalValidation20261027.selected_horn_cannot_rewrite_original_context
#check JurisLean.Candidates.FiniteLegalValidation20261027.model_check_exact
#print axioms JurisLean.Candidates.FiniteLegalValidation20261027.model_check_exact
#check JurisLean.Candidates.FiniteLegalValidation20261027.horn_world_membership
#print axioms JurisLean.Candidates.FiniteLegalValidation20261027.horn_world_membership
#check JurisLean.Candidates.FiniteLegalValidation20261027.validator_consumes_actual_bound_source
#print axioms JurisLean.Candidates.FiniteLegalValidation20261027.validator_consumes_actual_bound_source
#check JurisLean.Candidates.FiniteLegalValidation20261027.inspected_closed_process_exhausts_independent_requirements
#print axioms JurisLean.Candidates.FiniteLegalValidation20261027.inspected_closed_process_exhausts_independent_requirements
#check JurisLean.Candidates.FiniteLegalValidation20261027.full_horn_worlds_keep_actual_truth_conditionally
#print axioms JurisLean.Candidates.FiniteLegalValidation20261027.full_horn_worlds_keep_actual_truth_conditionally


open JurisLean.Candidates.Final20261021.Compiler
open JurisLean.Candidates.FiniteLegalValidation20261027

/-- info: true -/
#guard_msgs in
#eval decide (replayTrace [1] (traceRounds [⟨[1], 2⟩, ⟨[2], 3⟩] 3 [1]) =
  proposed_rule_input [⟨[1], 2⟩, ⟨[2], 3⟩] 3 [1])

/-- info: true -/
#guard_msgs in
#eval decide (traceRounds [⟨[1], 2⟩, ⟨[2], 3⟩] 2 [1] =
  [[⟨[1], 2⟩], [⟨[1], 2⟩, ⟨[2], 3⟩]])

/-- info: true -/
#guard_msgs in
#eval decide (traceRounds [⟨[2], 1⟩, ⟨[1], 2⟩] 2 [] = [[], []])

/-- info: true -/
#guard_msgs in
#eval decide (replayTrace [1, 4] (traceRounds [⟨[4], 5⟩] 3 [1, 4]) = [1, 4, 5, 5, 5])

/-- info: true -/
#guard_msgs in
#eval decide (traceRounds ([] : List (Rule Nat)) 0 [] = [])

open JurisLean.Candidates.Final20261021
open JurisLean.Candidates.Final20261021.EvidenceProcedure
open JurisLean.Candidates.SourceCompilation20261027
open JurisLean.Candidates.CompilerProvenance20261027

namespace JurisLean.Candidates.FiniteLegalValidation20261027.Audit

def context : Gamma := ⟨⟨1⟩, 1, 1, "synthetic", 3, 7, 8, ⟨10⟩, ⟨20⟩, ⟨20⟩, 1, 1, 1⟩

def material : MaterialSnapshot := ⟨context, 2, 3,
  [⟨⟨1⟩, 0, 0, "synthetic source atoms 1 and 4"⟩,
   ⟨⟨11⟩, 0, 1, "execution record"⟩, ⟨⟨12⟩, 0, 2, "closure record"⟩]⟩

def quoted {A : Type} (a : A) : Quoted A := ⟨⟨⟨1⟩, 0, 2, 3⟩, a⟩

def source : ConsumedView :=
  { record := quoted ⟨⟨0, 1, 2, 1, .normScope⟩, 0, true⟩
    relations := []
    ledger := []
    payments := []
    initialHistory := []
    historyEvents := []
    objects := [quoted (⟨1⟩, .relation ⟨9⟩)]
    observed := quoted (⟨1⟩, ⟨9⟩)
    atoms := [quoted 1, quoted 4] }

def rawClosed : RawProcess := ⟨[1], [1], [⟨1, 0, some ⟨11⟩, none, []⟩], some ⟨12⟩, false⟩

def supplement : Supplement :=
  ⟨material, 0, 2, 6, [], rawClosed, [⟨⟨11⟩, 0, 2, 3⟩, ⟨⟨12⟩, 0, 2, 3⟩]⟩

def policy : ProcessPolicy := ⟨context, 6, [1], [⟨11⟩], [], [⟨12⟩]⟩

def rules : List RuleUse := [⟨50, 8, ⟨[1], 2⟩⟩, ⟨51, 8, ⟨[4], 5⟩⟩, ⟨52, 8, ⟨[9], 10⟩⟩]

def worlds : List (List Nat) := [[1, 2, 4, 5], [1, 2, 4, 5, 7]]

def valuation (w : List Nat) (a : Nat) : Bool := decide (a ∈ w)

def app : TemporalInterpretation20261027.App := fun _ _ v => if v = 8 then .yes else .no

def run (s : Supplement := supplement) (p : ProcessPolicy := policy) :
    Result (ValidationReport (List Nat)) :=
  validate material 0 [⟨material, 0, source⟩] [s] [p] [] [8] app rules (fun _ _ => true) worlds valuation

/-- info: true -/
#guard_msgs in
#eval match run with
  | .known out => match out.horn, out.worldView with
    | .known horn, .known evidence => decide (horn.source.decoded.atoms.map Quoted.value = [1, 4] ∧
        2 ∈ horn.closure ∧ 5 ∈ horn.closure ∧ 10 ∉ horn.closure ∧
        evidence.possibleWorldJudgment = .supported ∧ out.procedure = .known .closedLawfully ∧
        out.bound.source.material.gamma.question = 3 ∧ out.bound.supplement.queryAtom = 2 ∧
        FailureWitness.missingPremise 52 9 ∈ out.failures)
    | _, _ => false
  | _ => false

/-- info: true -/
#guard_msgs in
#eval match run { supplement with queryAtom := 7 } with
  | .known out => match out.worldView with
    | .known evidence => decide (evidence.possibleWorldJudgment = .insufficient ∧
        out.evidenceJudgment = .insufficient ∧ out.procedure = .known .closedLawfully ∧
        FailureWitness.queryNotDerived 7 ∈ out.failures)
    | _ => false
  | _ => false

/-- info: true -/
#guard_msgs in
#eval match run { supplement with evidence := [quoted ⟨⟨1⟩, 2, .yes, true, true⟩],
    process := { rawClosed with records := [] } } with
  | .known out => decide (out.evidenceJudgment = .supported ∧ out.procedure = .known .open ∧
      FailureWitness.unfinishedOpportunity 1 ∈ out.failures)
  | _ => false

/-- info: true -/
#guard_msgs in
#eval match run { supplement with evidence := [quoted ⟨⟨1⟩, 2, .yes, true, true⟩,
    quoted ⟨⟨1⟩, 2, .yes, true, false⟩], process := { rawClosed with records := [] } } with
  | .known out => match out.worldView with
    | .known evidence => decide (out.evidenceJudgment = .incompatible ∧
        evidence.possibleWorldJudgment = .incompatible ∧ evidence.possibleWorlds = [] ∧
        out.procedure = .known .open ∧ FailureWitness.incompatibleWorlds ∈ out.failures)
    | _ => false
  | _ => false

/-- info: true -/
#guard_msgs in
#eval match run { supplement with process := { rawClosed with records := [], blocked := true } } with
  | .known out => decide (out.evidenceJudgment = .insufficient ∧ out.procedure = .known .blocked)
  | _ => false

/-- info: true -/
#guard_msgs in
#eval match run { supplement with process := { rawClosed with declaredRequired := [], domain := [], records := [] } } with
  | .known out => decide (out.procedure = .rejected .scopeMismatch ∧
      FailureWitness.requiredMismatch ∈ out.failures ∧ FailureWitness.omittedOpportunity 1 ∈ out.failures)
  | _ => false

/-- info: true -/
#guard_msgs in
#eval match run supplement { policy with validClosures := [] } with
  | .known out => decide (out.procedure = .known .open ∧ FailureWitness.missingClosureAuthority ∈ out.failures)
  | _ => false

/-- info: true -/
#guard_msgs in
#eval match run { supplement with process := { rawClosed with domain := [] } } with
  | .known out => decide (out.procedure = .known .open ∧ FailureWitness.omittedOpportunity 1 ∈ out.failures)
  | _ => false

/-- info: true -/
#guard_msgs in
#eval match run { supplement with process := { rawClosed with records := [⟨1, 0, some ⟨11⟩, none, [1]⟩] } } with
  | .known out => decide (out.procedure = .known .open ∧ FailureWitness.unfinishedOpportunity 1 ∈ out.failures)
  | _ => false

/-- info: true -/
#guard_msgs in
#eval match run { supplement with evidence := [quoted ⟨⟨1⟩, 7, .unknown, true, true⟩], queryAtom := 7 } with
  | .known out => match out.worldView with
    | .known evidence => decide (evidence.pending = [⟨1⟩] ∧ evidence.possibleWorldJudgment = .insufficient ∧
        FailureWitness.pendingEvidence ⟨1⟩ ∈ out.failures)
    | _ => false
  | _ => false

/-- info: true -/
#guard_msgs in
#eval match run { supplement with receiptCitations := [] } with
  | .rejected .observationBindingMismatch => true
  | _ => false

/-- info: true -/
#guard_msgs in
#eval match run supplement { policy with gamma := { context with caseRevision := 99 } } with
  | .unknown .authorityUnresolved => true
  | _ => false

/-- info: true -/
#guard_msgs in
#eval match validate material 0 [⟨material, 0, source⟩] [supplement] [policy] [] [8]
    (fun _ _ _ => .unknown) rules (fun _ _ => true) worlds valuation with
  | .known out => match out.horn, out.worldView with
    | .unknown .applicabilityUnknown, .unknown .applicabilityUnknown =>
        decide (out.procedure = .known .closedLawfully ∧ out.pendingVersions = [8])
    | _, _ => false
  | _ => false

/-- info: true -/
#guard_msgs in
#eval match validate material 0 [⟨material, 0, source⟩] [supplement] [policy] [] [7]
    (fun _ _ _ => .yes) rules (fun _ _ => true) worlds valuation with
  | .known out => match out.horn with
    | .rejected .versionConflict => true
    | _ => false
  | _ => false

/-- info: true -/
#guard_msgs in
#eval match validate material 0 [⟨material, 0, source⟩] [supplement, supplement] [policy] [] [8]
    app rules (fun _ _ => true) worlds valuation with
  | .conflict 0 2 => true
  | _ => false

/-- info: true -/
#guard_msgs in
#eval match run supplement { policy with validExecutions := [] } with
  | .known out => decide (out.procedure = .known .open ∧ FailureWitness.unfinishedOpportunity 1 ∈ out.failures)
  | _ => false

/-- info: true -/
#guard_msgs in
#eval match run { supplement with evidence := [quoted ⟨⟨99⟩, 2, .yes, true, true⟩] } with
  | .rejected .observationBindingMismatch => true
  | _ => false

/-- info: true -/
#guard_msgs in
#eval match validate material 0 [⟨material, 0, source⟩] [supplement] [policy] [] [8]
    app rules (fun _ _ => true) ([] : List (List Nat)) valuation with
  | .known out => match out.worldView with
    | .known evidence => decide (evidence.possibleWorldJudgment = .incompatible ∧
        FailureWitness.incompatibleWorlds ∈ out.failures)
    | _ => false
  | _ => false

end JurisLean.Candidates.FiniteLegalValidation20261027.Audit
