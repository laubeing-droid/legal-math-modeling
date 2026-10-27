import JurisLean.Candidates.Final20261021.EvidenceProcedure

/-!
Original 08.5/08.6 and the termination distinction in 08.8.
The independent required-opportunity list is not recovered from a policy's
own declared domain. Execution/waiver/closure registries remain externally
justified inputs. Finite inspection termination is not future business
termination or an impossibility theorem about future evidence.
-/

namespace JurisLean.Candidates.ProcedureClosure20261027

open JurisLean.Candidates.Final20261021
open JurisLean.Candidates.Final20261021.EvidenceProcedure

def validPolicy (required : List Nat) (p : ProcessInput) : Bool :=
  decide (p.required = required) && covered p &&
    decide ((p.records.map (·.id)).Nodup) &&
    p.closureAuthority.any (fun r => decide (r ∈ p.validClosureAuthorities))

def checkProcess (required : List Nat) (p : ProcessInput) : Result Procedure :=
  if p.required = required then .known (procedure p) else .rejected .scopeMismatch

theorem lawful_closed_iff_local_checks (p : ProcessInput) :
    procedure p = .closedLawfully ↔
      covered p = true ∧ exhausted p = true ∧
      decide ((p.records.map (·.id)).Nodup) = true ∧
      p.closureAuthority.any (fun r => decide (r ∈ p.validClosureAuthorities)) = true := by
  cases coverage : covered p <;> cases exhaustion : exhausted p <;>
    cases unique : decide ((p.records.map (·.id)).Nodup) <;>
    cases authorized : p.closureAuthority.any (fun r => decide (r ∈ p.validClosureAuthorities)) <;>
    cases blockage : p.blocked <;>
    simp [procedure, coverage, exhaustion, unique, authorized, blockage]

theorem checked_closed_iff_valid_and_exhausted (required : List Nat) (p : ProcessInput) :
    checkProcess required p = .known .closedLawfully ↔
      validPolicy required p = true ∧ exhausted p = true := by
  by_cases binding : p.required = required
  · simp [checkProcess, binding, lawful_closed_iff_local_checks, validPolicy,
      Bool.and_eq_true, and_assoc, and_left_comm, and_comm]
  · simp [checkProcess, binding, validPolicy]

theorem checked_closure_exhausts_independent_requirements (required : List Nat) (p : ProcessInput)
    (closed : checkProcess required p = .known .closedLawfully) :
    ∀ o ∈ required, terminal p o = true := by
  have parts := (checked_closed_iff_valid_and_exhausted required p).mp closed
  have contract := parts.1
  simp only [validPolicy, Bool.and_eq_true, decide_eq_true_eq] at contract
  have actual := necessary_exhausted p contract.1.1.2 parts.2
  simpa only [contract.1.1.1] using actual

theorem exhaustion_transfers_under_coverage (required : List Nat) (p : ProcessInput)
    (coverage : ∀ o ∈ required, o ∈ p.policyDomain) (done : exhausted p = true) :
    ∀ o ∈ required, terminal p o = true := by
  have allDone : ∀ o ∈ p.policyDomain, terminal p o = true := by
    simpa [exhausted, List.all_eq_true] using done
  exact fun o member => allDone o (coverage o member)

theorem reverse_exhaustion_needs_no_extra_domain (required : List Nat) (p : ProcessInput)
    (noExtra : ∀ o ∈ p.policyDomain, o ∈ required)
    (done : ∀ o ∈ required, terminal p o = true) : exhausted p = true := by
  apply List.all_eq_true.mpr
  exact fun o member => done o (noExtra o member)

def missingOpportunities (required : List Nat) (p : ProcessInput) : List Nat :=
  required.filter fun o => decide (o ∉ p.policyDomain)

def unfinishedOpportunities (p : ProcessInput) : List Nat :=
  p.policyDomain.filter fun o => !(terminal p o)

theorem missing_witness_is_an_actual_uncovered_requirement (required : List Nat)
    (p : ProcessInput) (o : Nat) :
    o ∈ missingOpportunities required p ↔ o ∈ required ∧ o ∉ p.policyDomain := by
  simp [missingOpportunities]

theorem unfinished_witness_is_an_actual_open_policy_opportunity (p : ProcessInput) (o : Nat) :
    o ∈ unfinishedOpportunities p ↔ o ∈ p.policyDomain ∧ terminal p o = false := by
  simp [unfinishedOpportunities]

def finalUndetermined (state : Judgment × Procedure) : Bool :=
  decide (state.1 = .insufficient ∧ state.2 = .closedLawfully)

theorem final_undetermined_exact (state : Judgment × Procedure) :
    finalUndetermined state = true ↔
      state.1 = .insufficient ∧ state.2 = .closedLawfully := by
  simp [finalUndetermined]

-- A zero inspection budget is a failed check, not normative authority.
def inspect (budget : Nat) (required : List Nat) (query : Nat)
    (evidence : List EvidenceItem) (p : ProcessInput) : Result (Judgment × Procedure) :=
  match budget with
  | 0 => .unknown .checkIncomplete
  | _ + 1 =>
      match checkProcess required p with
      | .known result => .known (judgment query evidence, result)
      | .unknown e => .unknown e
      | .rejected e => .rejected e
      | .conflict l r => .conflict l r

theorem successful_inspection_reads_actual_process_result (budget : Nat) (required : List Nat)
    (query : Nat) (evidence : List EvidenceItem) (p : ProcessInput) (out : Judgment × Procedure)
    (accepted : inspect budget required query evidence p = .known out) :
    0 < budget ∧ checkProcess required p = .known out.2 ∧ out.1 = judgment query evidence := by
  cases budget with
  | zero => simp [inspect] at accepted
  | succ available =>
      cases checked : checkProcess required p with
      | unknown e => simp [inspect, checked] at accepted
      | rejected e => simp [inspect, checked] at accepted
      | conflict l r => simp [inspect, checked] at accepted
      | known result =>
          simp only [inspect, checked, Result.known.injEq] at accepted
          cases accepted
          exact ⟨Nat.zero_lt_succ _, rfl, rfl⟩

theorem inspected_final_undetermined_retains_coverage (budget : Nat) (required : List Nat)
    (query : Nat) (evidence : List EvidenceItem) (p : ProcessInput) (out : Judgment × Procedure)
    (accepted : inspect budget required query evidence p = .known out)
    (final : finalUndetermined out = true) :
    judgment query evidence = .insufficient ∧ ∀ o ∈ required, terminal p o = true := by
  have flow := successful_inspection_reads_actual_process_result _ _ _ _ _ _ accepted
  have finalState := (final_undetermined_exact out).mp final
  refine ⟨flow.2.2.symm.trans finalState.1, ?_⟩
  apply checked_closure_exhausts_independent_requirements required p
  simpa only [finalState.2] using flow.2.1

-- Independent branch states are retained, including open/blocked branches.
def inspectBranches (budget : Nat) (required : Nat → List Nat) (query : Nat)
    (evidence : Nat → List EvidenceItem) (processes : Nat → ProcessInput)
    (branches : List Nat) : List (Nat × Result (Judgment × Procedure)) :=
  branches.map fun branch => (branch, inspect budget (required branch) query (evidence branch) (processes branch))

theorem branch_inspection_does_not_drop_open_results (budget : Nat) (required : Nat → List Nat)
    (query : Nat) (evidence : Nat → List EvidenceItem) (processes : Nat → ProcessInput)
    (branches : List Nat) (branch : Nat) (member : branch ∈ branches) :
    (branch, inspect budget (required branch) query (evidence branch) (processes branch)) ∈
      inspectBranches budget required query evidence processes branches :=
  List.mem_map.mpr ⟨branch, member, rfl⟩

theorem strict_rank_bounds_finite_transition_count {S : Type} (rank : S → Nat)
    (step : S → S → Prop) (decreases : ∀ s t, step s t → rank t < rank s)
    (path : Nat → S) (n : Nat) (valid : ∀ k < n, step (path k) (path (k + 1))) :
    rank (path n) + n ≤ rank (path 0) := by
  induction n with
  | zero => simp
  | succ n ih =>
      have prefixBound := ih (fun k hk => valid k (by omega))
      have strict := decreases _ _ (valid n (by omega))
      omega

theorem strict_rank_excludes_infinite_execution {S : Type} (rank : S → Nat)
    (step : S → S → Prop) (decreases : ∀ s t, step s t → rank t < rank s) :
    ¬ ∃ path : Nat → S, ∀ k, step (path k) (path (k + 1)) := by
  rintro ⟨path, forever⟩
  have bound := strict_rank_bounds_finite_transition_count rank step decreases path
    (rank (path 0) + 1) (fun k _ => forever k)
  omega

theorem self_loop_has_no_strict_natural_rank {S : Type} (rank : S → Nat)
    (step : S → S → Prop) (state : S) (loop : step state state) :
    ¬ (∀ s t, step s t → rank t < rank s) := by
  intro decreases
  exact Nat.lt_irrefl _ (decreases state state loop)

end JurisLean.Candidates.ProcedureClosure20261027

