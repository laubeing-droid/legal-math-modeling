import Mathlib
import JurisLean.Candidates.U06_1FiniteBellman20261030
import JurisLean.Candidates.Final20261021.Interfaces
import JurisLean.Candidates.Final20261021.Decision

/-!
Frozen original 06.3 L105/L107/L109: connect reachable common policies,
finite branchwise expected utilities, and the explicitly supplied max-min
preference. The frozen total plan L522 supplies finite nonempty Λ; the question
line L107 itself is not described as adding that premise. The concrete example
uses the existing finite-horizon trajectory law. Legal permission and preference
remain external Results; unknown inputs stay unknown. No runtime Pipeline
consumer, minimax interchange, mixed-strategy theorem, or legal probability over
interpretations is claimed.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators
open JurisLean.Candidates.Final20261021
open JurisLean.Candidates.Final20261021.Decision
open JurisLean.Candidates.U06_1FiniteBellman20261030

namespace JurisLean.Candidates.U06_3OriginalCommonRobustStrategy20261102

universe u v w

/-- A policy sees time, visible state/action history, and current visible state;
there is no legal-branch argument through which it could inspect j. -/
abbrev VisiblePolicy (S : Type u) (A : Type v) :=
  ℕ → History S A → S → A

/-! `next j t h s a s'` is the given possible-successor relation for one
branch. Reachability records only paths induced by the same visible policy. -/
inductive Reachable {J S : Type u} {A : Type v}
    (horizon : ℕ) (initial : J → S)
    (next : J → ℕ → History S A → S → A → S → Prop)
    (π : VisiblePolicy S A) : J → ℕ → History S A → S → Prop
  | start (j : J) : Reachable horizon initial next π j 0 [] (initial j)
  | step {j t h s s'}
      (hr : Reachable horizon initial next π j t h s)
      (ht : t < horizon)
      (hn : next j t h s (π t h s) s') :
      Reachable horizon initial next π j (t + 1) ((s, π t h s) :: h) s'

/-- Feasibility is checked at every reachable, nonterminal history in each
listed branch. Infeasible actions at unreachable histories are irrelevant. -/
def Feasible {J S : Type u} {A : Type v} [DecidableEq A]
    (horizon : ℕ) (branches : Finset J) (initial : J → S)
    (next : J → ℕ → History S A → S → A → S → Prop)
    (legal : J → ℕ → History S A → S → Finset A)
    (implementable : ℕ → History S A → S → Finset A)
    (π : VisiblePolicy S A) : Prop :=
  ∀ j ∈ branches, ∀ t h s,
    Reachable horizon initial next π j t h s → t < horizon →
      π t h s ∈ legal j t h s ∧ π t h s ∈ implementable t h s

def commonPolicies {J S : Type u} {A : Type v} {P : Type w}
    [DecidableEq J] [DecidableEq A] [DecidableEq P]
    (candidates : Finset P) (realize : P → VisiblePolicy S A)
    (horizon : ℕ) (branches : Finset J) (initial : J → S)
    (next : J → ℕ → History S A → S → A → S → Prop)
    (legal : J → ℕ → History S A → S → Finset A)
    (implementable : ℕ → History S A → S → Finset A) : Finset P := by
  classical
  exact candidates.filter (fun p =>
    Feasible horizon branches initial next legal implementable (realize p))

theorem common_policy_is_branch_blind {S : Type u} {A : Type v}
    (π : VisiblePolicy S A) (t₁ t₂ : ℕ) (h₁ h₂ : History S A) (s₁ s₂ : S)
    (ht : t₁ = t₂) (hh : h₁ = h₂) (hs : s₁ = s₂) :
    π t₁ h₁ s₁ = π t₂ h₂ s₂ := by
  subst t₂
  subst h₂
  subst s₂
  rfl

theorem empty_joint_actions_block_common_policy
    {J S : Type u} {A : Type v} [DecidableEq A]
    (horizon : ℕ) (branches : Finset J) (initial : J → S)
    (next : J → ℕ → History S A → S → A → S → Prop)
    (legal : J → ℕ → History S A → S → Finset A)
    (implementable : ℕ → History S A → S → Finset A)
    (π : VisiblePolicy S A) (j₁ j₂ : J) (t : ℕ)
    (h : History S A) (s : S)
    (hj₁ : j₁ ∈ branches) (hj₂ : j₂ ∈ branches)
    (hr₁ : Reachable horizon initial next π j₁ t h s)
    (hr₂ : Reachable horizon initial next π j₂ t h s)
    (ht : t < horizon)
    (hempty : legal j₁ t h s ∩ legal j₂ t h s ∩ implementable t h s = ∅) :
    ¬ Feasible horizon branches initial next legal implementable π := by
  intro hfeasible
  have h₁ := (hfeasible j₁ hj₁ t h s hr₁ ht).1
  have h₂ := (hfeasible j₂ hj₂ t h s hr₂ ht).1
  have hf := (hfeasible j₁ hj₁ t h s hr₁ ht).2
  have hmem : π t h s ∈ legal j₁ t h s ∩ legal j₂ t h s ∩ implementable t h s := by
    simp [h₁, h₂, hf]
  rw [hempty] at hmem
  simp at hmem

def worstBranchValue {J P : Type} [DecidableEq J]
    (branches : Finset J) (hbranches : branches.Nonempty)
    (values : P → J → ℝ) (p : P) : ℝ :=
  branches.inf' hbranches (values p)

theorem worst_branch_attained {J P : Type} [DecidableEq J]
    (branches : Finset J) (hbranches : branches.Nonempty)
    (values : P → J → ℝ) (p : P) :
    ∃ j ∈ branches, values p j = worstBranchValue branches hbranches values p := by
  obtain ⟨j, hj, heq⟩ := Finset.exists_mem_eq_inf' hbranches (values p)
  exact ⟨j, hj, heq.symm⟩

theorem finite_max_min_attained {J P : Type} [DecidableEq J] [DecidableEq P]
    (branches : Finset J) (hbranches : branches.Nonempty)
    (policies : Finset P) (hpolicies : policies.Nonempty)
    (values : P → J → ℝ) :
    ∃ p ∈ policies, ∀ q ∈ policies,
      worstBranchValue branches hbranches values q ≤
        worstBranchValue branches hbranches values p := by
  classical
  let score : P → ℝ := worstBranchValue branches hbranches values
  obtain ⟨p, hp, hscore⟩ := Finset.exists_mem_eq_sup' hpolicies score
  refine ⟨p, hp, ?_⟩
  intro q hq
  have hqle : score q ≤ policies.sup' hpolicies score :=
    (Finset.sup'_le_iff hpolicies score).mp le_rfl q hq
  simpa [score, hscore] using hqle

noncomputable def pickMaxMin {J P : Type} [DecidableEq J] [DecidableEq P]
    (branches : Finset J) (hbranches : branches.Nonempty)
    (policies : Finset P) (values : P → J → ℝ) : Option P :=
  if hp : policies.Nonempty then
    some (Classical.choose (finite_max_min_attained branches hbranches policies hp values))
  else none

theorem pickMaxMin_spec {J P : Type} [DecidableEq J] [DecidableEq P]
    (branches : Finset J) (hbranches : branches.Nonempty)
    (policies : Finset P) (values : P → J → ℝ) (p : P)
    (hpick : pickMaxMin branches hbranches policies values = some p) :
    p ∈ policies ∧ ∀ q ∈ policies,
      worstBranchValue branches hbranches values q ≤
        worstBranchValue branches hbranches values p := by
  classical
  unfold pickMaxMin at hpick
  by_cases hpolicies : policies.Nonempty
  · simp only [dif_pos hpolicies, Option.some.injEq] at hpick
    subst p
    exact Classical.choose_spec
      (finite_max_min_attained branches hbranches policies hpolicies values)
  · simp [hpolicies] at hpick

theorem pickMaxMin_none_iff {J P : Type} [DecidableEq J] [DecidableEq P]
    (branches : Finset J) (hbranches : branches.Nonempty)
    (policies : Finset P) (values : P → J → ℝ) :
    pickMaxMin branches hbranches policies values = none ↔ policies = ∅ := by
  classical
  by_cases hpolicies : policies.Nonempty
  · have hne : policies ≠ ∅ := by
      obtain ⟨p, hp⟩ := hpolicies
      intro he
      rw [he] at hp
      exact Finset.not_mem_empty p hp
    simp [pickMaxMin, hpolicies, hne]
  · have hempty : policies = ∅ := by
      by_contra hne
      exact hpolicies (Finset.nonempty_of_ne_empty hne)
    simp [pickMaxMin, hpolicies, hempty]

/-- Actual expected utility under the fixed law for one legal branch. -/
noncomputable def branchExpectedUtility {J P Ω : Type}
    [MeasurableSpace Ω] (law : J → Measure Ω) (utility : J → ℝ → ℝ)
    (outcome : P → Ω → ℝ) (p : P) (j : J) : ℝ :=
  ∫ ω, utility j (outcome p ω) ∂law j

/-- Inputs needed for the preceding integral to represent a probability
expectation rather than Lean's totalized integral on an ill-formed input. -/
def expectedUtilityInputsWellFormed {J P Ω : Type}
    [MeasurableSpace Ω] (branches : Finset J) (policies : Finset P)
    (law : J → Measure Ω) (utility : J → ℝ → ℝ)
    (outcome : P → Ω → ℝ) : Prop :=
  (∀ j ∈ branches, IsProbabilityMeasure (law j)) ∧
  ∀ p ∈ policies, ∀ j ∈ branches,
    Integrable (fun ω => utility j (outcome p ω)) (law j)

/-- The table used for selection is computed from the declared branch laws and
actual utility integrals, rather than supplied independently of them. -/
noncomputable def expectedUtilityMatrix {J P Ω : Type}
    [MeasurableSpace Ω] (law : J → Measure Ω) (utility : J → ℝ → ℝ)
    (outcome : P → Ω → ℝ) : P → J → ℝ :=
  fun p j => branchExpectedUtility law utility outcome p j

def conditionalAdvice {J S A P Ω : Type}
    [MeasurableSpace Ω]
    [DecidableEq J] [DecidableEq A] [DecidableEq P]
    (horizon : ℕ) (branches : Finset J) (hbranches : branches.Nonempty)
    (initial : J → S)
    (next : J → ℕ → History S A → S → A → S → Prop)
    (implementable : ℕ → History S A → S → Finset A)
    (candidates : Finset P) (realize : P → VisiblePolicy S A)
    (law : J → Measure Ω) (utility : J → ℝ → ℝ)
    (outcome : P → Ω → ℝ)
    (_hWellFormed : expectedUtilityInputsWellFormed branches candidates law utility outcome)
    (legalInput : Result (J → ℕ → History S A → S → Finset A))
    (preferenceInput : Result Unit) :
    (P → J → ℝ) × Result (Finset P) × Result (Option P) :=
  let values := expectedUtilityMatrix law utility outcome
  match legalInput with
  | .known legal =>
      let common := commonPolicies candidates realize horizon branches initial next legal implementable
      (values, .known common,
        match preferenceInput with
        | .known () => .known (pickMaxMin branches hbranches common values)
        | .unknown e => .unknown e
        | .rejected e => .rejected e
        | .conflict l r => .conflict l r)
  | .unknown e => (values, .unknown e, .unknown e)
  | .rejected e => (values, .rejected e, .rejected e)
  | .conflict l r => (values, .conflict l r, .conflict l r)

theorem conditional_advice_preserves_legal_unknown {J S A P Ω : Type}
    [DecidableEq J] [DecidableEq A] [DecidableEq P]
    (horizon : ℕ) (branches : Finset J) (hbranches : branches.Nonempty)
    (initial : J → S) (next : J → ℕ → History S A → S → A → S → Prop)
    (implementable : ℕ → History S A → S → Finset A)
    (candidates : Finset P) (realize : P → VisiblePolicy S A)
    [MeasurableSpace Ω]
    (law : J → Measure Ω) (utility : J → ℝ → ℝ) (outcome : P → Ω → ℝ)
    (hWellFormed : expectedUtilityInputsWellFormed branches candidates law utility outcome)
    (reason : Error) (preference : Result Unit) :
    let result := conditionalAdvice horizon branches hbranches initial next implementable
      candidates realize law utility outcome hWellFormed (.unknown reason) preference
    result.2.1 = .unknown reason ∧ result.2.2 = .unknown reason := by
  cases preference <;> constructor <;> rfl

theorem conditional_advice_preserves_preference_unknown {J S A P Ω : Type}
    [DecidableEq J] [DecidableEq A] [DecidableEq P]
    (horizon : ℕ) (branches : Finset J) (hbranches : branches.Nonempty)
    (initial : J → S) (next : J → ℕ → History S A → S → A → S → Prop)
    (implementable : ℕ → History S A → S → Finset A)
    (candidates : Finset P) (realize : P → VisiblePolicy S A)
    [MeasurableSpace Ω]
    (law : J → Measure Ω) (utility : J → ℝ → ℝ) (outcome : P → Ω → ℝ)
    (hWellFormed : expectedUtilityInputsWellFormed branches candidates law utility outcome)
    (legal : J → ℕ → History S A → S → Finset A)
    (reason : Error) :
    let result := conditionalAdvice horizon branches hbranches initial next implementable
      candidates realize law utility outcome hWellFormed (.known legal) (.unknown reason)
    (result.2.1 = .known
        (commonPolicies candidates realize horizon branches initial next legal implementable)) ∧
      result.2.2 = .unknown reason := by
  constructor <;> rfl

theorem conditional_advice_known_empty_returns_none {J S A P Ω : Type}
    [DecidableEq J] [DecidableEq A] [DecidableEq P]
    (horizon : ℕ) (branches : Finset J) (hbranches : branches.Nonempty)
    (initial : J → S) (next : J → ℕ → History S A → S → A → S → Prop)
    (implementable : ℕ → History S A → S → Finset A)
    (candidates : Finset P) (realize : P → VisiblePolicy S A)
    [MeasurableSpace Ω]
    (law : J → Measure Ω) (utility : J → ℝ → ℝ) (outcome : P → Ω → ℝ)
    (hWellFormed : expectedUtilityInputsWellFormed branches candidates law utility outcome)
    (legal : J → ℕ → History S A → S → Finset A)
    (hempty : commonPolicies candidates realize horizon branches initial next legal implementable = ∅) :
    (conditionalAdvice horizon branches hbranches initial next implementable
      candidates realize law utility outcome hWellFormed (.known legal) (.known ())).2.2 = .known none := by
  simp [conditionalAdvice, hempty, pickMaxMin_none_iff branches hbranches]

theorem conditional_advice_known_choice_is_feasible_max_min
    {J S A P Ω : Type}
    [DecidableEq J] [DecidableEq A] [DecidableEq P]
    (horizon : ℕ) (branches : Finset J) (hbranches : branches.Nonempty)
    (initial : J → S) (next : J → ℕ → History S A → S → A → S → Prop)
    (implementable : ℕ → History S A → S → Finset A)
    (candidates : Finset P) (realize : P → VisiblePolicy S A)
    [MeasurableSpace Ω]
    (law : J → Measure Ω) (utility : J → ℝ → ℝ) (outcome : P → Ω → ℝ)
    (hWellFormed : expectedUtilityInputsWellFormed branches candidates law utility outcome)
    (legal : J → ℕ → History S A → S → Finset A)
    (p : P)
    (hchoice : (conditionalAdvice horizon branches hbranches initial next implementable
      candidates realize law utility outcome hWellFormed (.known legal) (.known ())).2.2 = .known (some p)) :
    p ∈ candidates ∧
      Feasible horizon branches initial next legal implementable (realize p) ∧
      ∀ q ∈ candidates,
        Feasible horizon branches initial next legal implementable (realize q) →
          worstBranchValue branches hbranches (expectedUtilityMatrix law utility outcome) q ≤
            worstBranchValue branches hbranches (expectedUtilityMatrix law utility outcome) p := by
  let values := expectedUtilityMatrix law utility outcome
  have hpick : pickMaxMin branches hbranches
      (commonPolicies candidates realize horizon branches initial next legal implementable) values =
        some p := by
    simpa [conditionalAdvice] using hchoice
  have hspec := pickMaxMin_spec branches hbranches
    (commonPolicies candidates realize horizon branches initial next legal implementable)
    values p hpick
  rcases Finset.mem_filter.mp hspec.1 with ⟨hp, hfeasible⟩
  refine ⟨hp, hfeasible, ?_⟩
  intro q hq hqFeasible
  exact hspec.2 q (Finset.mem_filter.mpr ⟨hq, hqFeasible⟩)

theorem conditional_advice_known_none_iff_no_feasible_candidate
    {J S A P Ω : Type}
    [DecidableEq J] [DecidableEq A] [DecidableEq P]
    (horizon : ℕ) (branches : Finset J) (hbranches : branches.Nonempty)
    (initial : J → S) (next : J → ℕ → History S A → S → A → S → Prop)
    (implementable : ℕ → History S A → S → Finset A)
    (candidates : Finset P) (realize : P → VisiblePolicy S A)
    [MeasurableSpace Ω]
    (law : J → Measure Ω) (utility : J → ℝ → ℝ) (outcome : P → Ω → ℝ)
    (hWellFormed : expectedUtilityInputsWellFormed branches candidates law utility outcome)
    (legal : J → ℕ → History S A → S → Finset A) :
    (conditionalAdvice horizon branches hbranches initial next implementable
      candidates realize law utility outcome hWellFormed (.known legal) (.known ())).2.2 = .known none ↔
    ∀ p ∈ candidates,
      ¬ Feasible horizon branches initial next legal implementable (realize p) := by
  let common := commonPolicies candidates realize horizon branches initial next legal implementable
  let values := expectedUtilityMatrix law utility outcome
  constructor
  · intro hnone p hp hfeasible
    have hpick : pickMaxMin branches hbranches common values = none := by
      simpa [conditionalAdvice, common] using hnone
    have hempty : common = ∅ := (pickMaxMin_none_iff branches hbranches common values).mp hpick
    have hmem : p ∈ common := Finset.mem_filter.mpr ⟨hp, hfeasible⟩
    rw [hempty] at hmem
    exact Finset.not_mem_empty p hmem
  · intro hnone
    have hempty : common = ∅ := by
      ext p
      constructor
      · intro hp
        rcases Finset.mem_filter.mp hp with ⟨hc, hf⟩
        exact False.elim (hnone p hc hf)
      · simp
    have hpick : pickMaxMin branches hbranches common values = none :=
      (pickMaxMin_none_iff branches hbranches common values).mpr hempty
    simpa [conditionalAdvice, common] using hpick

/-! The finite witness instantiates the old one-step trajectory model. The
observation is just the visible unit-state/history trace, while j is kept as a
separate conditioning index and never passed to the policy. -/
abbrev DemoBranch := Fin 2
abbrev DemoAction := Fin 3
abbrev DemoTrace := U06_1FiniteBellman20261030.Trace Unit 1
abbrev DemoWorld := DemoBranch × DemoTrace

local instance : MeasurableSpace DemoTrace := ⊤
local instance : MeasurableSpace DemoWorld := ⊤

def demoPayoff (j : DemoBranch) (a : DemoAction) : ℝ :=
  if j.val = 0 then
    if a.val = 0 then 10 else if a.val = 1 then 0 else 4
  else
    if a.val = 0 then 0 else if a.val = 1 then 10 else 4

def demoControl : U06_1FiniteBellman20261030.Control Unit DemoAction where
  legal := fun _ _ => Finset.univ
  kernel := fun _ _ _ _ => 1
  kernel_nonneg := by intros; norm_num
  kernel_one := by intros; simp

def demoPolicy (a : DemoAction) : U06_1FiniteBellman20261030.Policy demoControl :=
  fun _ _ _ _ => ⟨a, Finset.mem_univ a⟩

def demoVisiblePolicy (a : DemoAction) : VisiblePolicy Unit DemoAction :=
  fun _ _ _ => a

theorem demo_policy_matches_visible_policy (a : DemoAction) (n : ℕ)
    (h : History Unit DemoAction) (s : Unit)
    (hn : (demoControl.legal (n + 1) s).Nonempty) :
    (demoPolicy a n h s hn).val = demoVisiblePolicy a n h s := rfl

def demoObserve (_ : DemoWorld) : Unit := ()

theorem demo_visible_actions_equal_across_worlds
    (a : DemoAction) (w₁ w₂ : DemoWorld) (n : ℕ) (h : History Unit DemoAction)
    (hobs : demoObserve w₁ = demoObserve w₂) :
    demoVisiblePolicy a n h (demoObserve w₁) = demoVisiblePolicy a n h (demoObserve w₂) := by
  exact common_policy_is_branch_blind (demoVisiblePolicy a) n n h h
    (demoObserve w₁) (demoObserve w₂) rfl rfl hobs

def demoInitial (_j : DemoBranch) : Unit := ()

def demoNext (_j : DemoBranch) (t : ℕ)
    (_h : U06_1FiniteBellman20261030.History Unit DemoAction)
    (s : Unit) (a : DemoAction) (s' : Unit) : Prop :=
  0 < demoControl.kernel (t + 1) s a s'

def demoLegal (_j : DemoBranch) (_t : ℕ)
    (_h : U06_1FiniteBellman20261030.History Unit DemoAction)
    (_s : Unit) : Finset DemoAction := Finset.univ

def demoImplementable (_t : ℕ)
    (_h : U06_1FiniteBellman20261030.History Unit DemoAction)
    (_s : Unit) : Finset DemoAction := Finset.univ

theorem demo_policies_feasible (a : DemoAction) :
    Feasible 1 Finset.univ demoInitial demoNext demoLegal demoImplementable (demoVisiblePolicy a) := by
  intro j hj t h s hr ht
  constructor <;> exact Finset.mem_univ _

def demoCandidatePolicies : Finset DemoAction := Finset.univ

theorem demo_common_policy_set_eq_univ :
    commonPolicies demoCandidatePolicies demoVisiblePolicy 1 Finset.univ demoInitial
      demoNext demoLegal demoImplementable = Finset.univ := by
  ext a
  simp [commonPolicies, demoCandidatePolicies, demo_policies_feasible, demoVisiblePolicy]

def demoBranchSet : Finset DemoBranch := Finset.univ

theorem demo_branches_nonempty : demoBranchSet.Nonempty := by
  exact ⟨0, Finset.mem_univ _⟩

def demoTrajectoryLaw : PMF DemoTrace :=
  U06_1FiniteBellman20261030.trajectoryLaw demoControl (demoPolicy 0) 1 [] ()

theorem demo_trace_eq_terminal (x : DemoTrace) :
    x = U06_1FiniteBellman20261030.terminalTrace () 1 := by
  cases x with
  | mk s tail => cases s; cases tail; rfl

theorem demo_trajectory_law_is_pure (a : DemoAction) :
    U06_1FiniteBellman20261030.trajectoryLaw demoControl (demoPolicy a) 1 [] () =
      PMF.pure (U06_1FiniteBellman20261030.terminalTrace () 1) := by
  ext x
  rw [demo_trace_eq_terminal x]
  simp [U06_1FiniteBellman20261030.trajectoryLaw,
    U06_1FiniteBellman20261030.trajectoryWeight, demoControl, demoPolicy,
    U06_1FiniteBellman20261030.terminalTrace]

def fixedBranchLaw (j : DemoBranch) : PMF DemoWorld :=
  demoTrajectoryLaw.map (fun tr => (j, tr))

def demoBranchMeasure (j : DemoBranch) : Measure DemoWorld :=
  (fixedBranchLaw j).toMeasure

local instance (j : DemoBranch) : IsProbabilityMeasure (demoBranchMeasure j) := by
  change IsProbabilityMeasure ((fixedBranchLaw j).toMeasure)
  infer_instance

def inducedWorldLaw (p : DemoAction) (j : DemoBranch) : PMF DemoWorld :=
  (U06_1FiniteBellman20261030.trajectoryLaw demoControl (demoPolicy p) 1 [] ()).map
    (fun tr => (j, tr))

theorem every_policy_induces_fixed_branch_law (p : DemoAction) (j : DemoBranch) :
    inducedWorldLaw p j = fixedBranchLaw j ∧
      fixedBranchLaw j = PMF.pure (j, U06_1FiniteBellman20261030.terminalTrace () 1) := by
  have hembed : (fun tr : DemoTrace => (j, tr)) =
      Function.const DemoTrace (j, U06_1FiniteBellman20261030.terminalTrace () 1) := by
    funext tr
    exact congrArg (fun q : DemoTrace => (j, q)) (demo_trace_eq_terminal tr)
  have hi : inducedWorldLaw p j = PMF.pure
      (j, U06_1FiniteBellman20261030.terminalTrace () 1) := by
    unfold inducedWorldLaw
    rw [hembed, PMF.map_const]
  have hf : fixedBranchLaw j = PMF.pure
      (j, U06_1FiniteBellman20261030.terminalTrace () 1) := by
    unfold fixedBranchLaw
    rw [hembed, PMF.map_const]
  exact ⟨hi.trans hf.symm, hf⟩

def demoOutcome (a : DemoAction) (ω : DemoWorld) : ℝ :=
  U06_1FiniteBellman20261030.realizedReturn demoControl
    (fun _ _ action => demoPayoff ω.1 action) (fun _ => 0)
    (demoPolicy a) 1 [] () ω.2

def demoUtilities (a : DemoAction) (j : DemoBranch) : ℝ :=
  expectedUtilityMatrix demoBranchMeasure (fun _ x => x) demoOutcome a j

theorem demo_expected_utility_inputs_well_formed :
    expectedUtilityInputsWellFormed demoBranchSet demoCandidatePolicies
      demoBranchMeasure (fun _ x => x) demoOutcome := by
  constructor
  · intro j hj
    infer_instance
  · intro a ha j hj
    exact Integrable.of_finite

theorem demo_expected_utility_is_actual_trajectory_payoff
    (a : DemoAction) (j : DemoBranch) : demoUtilities a j = demoPayoff j a := by
  unfold demoUtilities expectedUtilityMatrix branchExpectedUtility demoBranchMeasure
  have hLaw := (every_policy_induces_fixed_branch_law a j).2
  rw [hLaw]
  rw [PMF.integral_eq_sum]
  simp [demoOutcome, U06_1FiniteBellman20261030.realizedReturn,
    demoPolicy, demoControl, U06_1FiniteBellman20261030.terminalTrace,
    demoPayoff]

theorem demo_max_min_scores :
    worstBranchValue demoBranchSet demo_branches_nonempty demoUtilities 0 = 0 ∧
    worstBranchValue demoBranchSet demo_branches_nonempty demoUtilities 1 = 0 ∧
    worstBranchValue demoBranchSet demo_branches_nonempty demoUtilities 2 = 4 := by
  have hbranches : demoBranchSet = ({0, 1} : Finset DemoBranch) := by decide
  norm_num [worstBranchValue, hbranches,
    demo_expected_utility_is_actual_trajectory_payoff, demoPayoff]

theorem demo_common_strategy_maximizes_minimum :
    ∀ a ∈ demoCandidatePolicies,
      worstBranchValue demoBranchSet demo_branches_nonempty demoUtilities a ≤
        worstBranchValue demoBranchSet demo_branches_nonempty demoUtilities 2 := by
  intro a ha
  rcases demo_max_min_scores with ⟨h₀, h₁, h₂⟩
  fin_cases a
  · change worstBranchValue demoBranchSet demo_branches_nonempty demoUtilities (0 : DemoAction) ≤
      worstBranchValue demoBranchSet demo_branches_nonempty demoUtilities 2
    rw [h₀, h₂]
    norm_num
  · change worstBranchValue demoBranchSet demo_branches_nonempty demoUtilities (1 : DemoAction) ≤
      worstBranchValue demoBranchSet demo_branches_nonempty demoUtilities 2
    rw [h₁, h₂]
    norm_num
  · change worstBranchValue demoBranchSet demo_branches_nonempty demoUtilities (2 : DemoAction) ≤
      worstBranchValue demoBranchSet demo_branches_nonempty demoUtilities 2
    exact le_rfl

theorem demo_branchwise_optima_differ :
    (∀ a : DemoAction, demoUtilities a 0 ≤ demoUtilities 0 0) ∧
    (∀ a : DemoAction, demoUtilities a 1 ≤ demoUtilities 1 1) ∧
    demoUtilities 0 0 = 10 ∧ demoUtilities 1 1 = 10 ∧ demoUtilities 2 0 = 4 ∧
    demoUtilities 2 1 = 4 ∧ demoUtilities 2 0 < demoUtilities 0 0 ∧
    demoUtilities 2 1 < demoUtilities 1 1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a
    simp only [demo_expected_utility_is_actual_trajectory_payoff]
    fin_cases a <;> norm_num [demoPayoff]
  · intro a
    simp only [demo_expected_utility_is_actual_trajectory_payoff]
    fin_cases a <;> norm_num [demoPayoff]
  all_goals simp only [demo_expected_utility_is_actual_trajectory_payoff] <;>
    norm_num [demoPayoff]

end JurisLean.Candidates.U06_3OriginalCommonRobustStrategy20261102
