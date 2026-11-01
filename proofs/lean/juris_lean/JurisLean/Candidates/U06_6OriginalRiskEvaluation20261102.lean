import JurisLean.Candidates.U06_3OriginalCommonRobustStrategy20261102
import Mathlib.Probability.ProbabilityMassFunction.Integrals

/-!
Original 06.6 L129/L133: filter an already finite class of common legal and
implementable policies by actual branch-law expected loss, retain the original
utility max-min on that filtered class, and report an empty class as no choice.
The finite example uses the accepted 06.3 branch laws and demonstrates exclusion
of an unconstrained optimum. These are conditional model quantities; no actual
or deployed-value claim follows without a separate identifying argument.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace Core := JurisLean.Candidates.U06_3OriginalCommonRobustStrategy20261102

namespace JurisLean.Candidates.U06_6OriginalRiskEvaluation20261102

/-- The branch-specific expected loss under the supplied model law. -/
def lossMean {J P Ω : Type} [MeasurableSpace Ω]
    (law : J → Measure Ω) (loss : P → Ω → ℝ) (p : P) (j : J) : ℝ :=
  Core.branchExpectedUtility law (fun _ x => x) loss p j

/-- Worst branch expected loss; branches must be finite and nonempty. -/
def worstExpectedLoss {J P Ω : Type} [MeasurableSpace Ω]
    (branches : Finset J) (hbranches : branches.Nonempty)
    (law : J → Measure Ω) (loss : P → Ω → ℝ) (p : P) : ℝ :=
  branches.sup' hbranches (lossMean law loss p)

/-- Risk inputs are usable only when every listed branch has a probability law
and the candidate's actual loss is integrable under each such law. -/
def riskModelInputsWellFormed {J P Ω : Type} [MeasurableSpace Ω]
    (branches : Finset J) (law : J → Measure Ω) (loss : P → Ω → ℝ)
    (p : P) : Prop :=
  (∀ j ∈ branches, IsProbabilityMeasure (law j)) ∧
  ∀ j ∈ branches, Integrable (loss p) (law j)

/-- Risk feasibility includes well-formed branch expectations and the actual
supremum of those expectations, avoiding totalized-integral false safety. -/
def RiskFeasible {J P Ω : Type} [MeasurableSpace Ω]
    (branches : Finset J) (hbranches : branches.Nonempty)
    (law : J → Measure Ω) (loss : P → Ω → ℝ) (limit : ℝ) (p : P) : Prop :=
  riskModelInputsWellFormed branches law loss p ∧
    worstExpectedLoss branches hbranches law loss p ≤ limit

/-- Apply the risk constraint to a given finite candidate class. -/
noncomputable def riskPolicies {J P Ω : Type} [MeasurableSpace Ω]
    [DecidableEq P]
    (candidates : Finset P) (branches : Finset J) (hbranches : branches.Nonempty)
    (law : J → Measure Ω) (loss : P → Ω → ℝ) (limit : ℝ) : Finset P := by
  classical
  exact candidates.filter (fun p => RiskFeasible branches hbranches law loss limit p)

theorem riskPolicies_mem_iff {J P Ω : Type} [MeasurableSpace Ω] [DecidableEq P]
    (candidates : Finset P) (branches : Finset J) (hbranches : branches.Nonempty)
    (law : J → Measure Ω) (loss : P → Ω → ℝ) (limit : ℝ) (p : P) :
    p ∈ riskPolicies candidates branches hbranches law loss limit ↔
      p ∈ candidates ∧ RiskFeasible branches hbranches law loss limit p := by
  simp [riskPolicies]

theorem riskPolicies_subset_candidates {J P Ω : Type} [MeasurableSpace Ω]
    [DecidableEq P] (candidates : Finset P) (branches : Finset J)
    (hbranches : branches.Nonempty) (law : J → Measure Ω)
    (loss : P → Ω → ℝ) (limit : ℝ) :
    riskPolicies candidates branches hbranches law loss limit ⊆ candidates :=
  Finset.filter_subset _ _

theorem riskPolicies_commonPolicies_subset {J S A P Ω : Type}
    [MeasurableSpace Ω] [DecidableEq J] [DecidableEq A] [DecidableEq P]
    (candidates : Finset P) (realize : P → Core.VisiblePolicy S A)
    (horizon : ℕ) (branches : Finset J) (initial : J → S)
    (next : J → ℕ → Core.History S A → S → A → S → Prop)
    (legal : J → ℕ → Core.History S A → S → Finset A)
    (implementable : ℕ → Core.History S A → S → Finset A)
    (hbranches : branches.Nonempty) (law : J → Measure Ω)
    (loss : P → Ω → ℝ) (limit : ℝ) :
    riskPolicies
        (Core.commonPolicies candidates realize horizon branches initial next legal implementable)
        branches hbranches law loss limit ⊆
      Core.commonPolicies candidates realize horizon branches initial next legal implementable :=
  Finset.filter_subset _ _

/-- Membership in the risk-filtered common class retains the original
06.3 feasibility proof; this is the consumer connection, not a new legal layer. -/
theorem riskPolicies_common_member_is_feasible {J S A P Ω : Type}
    [MeasurableSpace Ω] [DecidableEq J] [DecidableEq A] [DecidableEq P]
    (candidates : Finset P) (realize : P → Core.VisiblePolicy S A)
    (horizon : ℕ) (branches : Finset J) (initial : J → S)
    (next : J → ℕ → Core.History S A → S → A → S → Prop)
    (legal : J → ℕ → Core.History S A → S → Finset A)
    (implementable : ℕ → Core.History S A → S → Finset A)
    (hbranches : branches.Nonempty) (law : J → Measure Ω)
    (loss : P → Ω → ℝ) (limit : ℝ) (p : P)
    (hp : p ∈ riskPolicies
      (Core.commonPolicies candidates realize horizon branches initial next legal implementable)
      branches hbranches law loss limit) :
    p ∈ Core.commonPolicies candidates realize horizon branches initial next legal implementable ∧
      Core.Feasible horizon branches initial next legal implementable (realize p) := by
  have hmem := (riskPolicies_mem_iff
    (Core.commonPolicies candidates realize horizon branches initial next legal implementable)
    branches hbranches law loss limit p).mp hp
  classical
  exact ⟨hmem.1, (Finset.mem_filter.mp hmem.1).2⟩

theorem riskPolicies_mem_model_inputs_well_formed {J P Ω : Type}
    [MeasurableSpace Ω] [DecidableEq P]
    (candidates : Finset P) (branches : Finset J) (hbranches : branches.Nonempty)
    (law : J → Measure Ω) (loss : P → Ω → ℝ) (limit : ℝ) (p : P)
    (hp : p ∈ riskPolicies candidates branches hbranches law loss limit) :
    riskModelInputsWellFormed branches law loss p :=
  ((riskPolicies_mem_iff candidates branches hbranches law loss limit p).mp hp).2.1

theorem riskPolicies_mem_each_expected_loss_le {J P Ω : Type}
    [MeasurableSpace Ω] [DecidableEq P]
    (candidates : Finset P) (branches : Finset J) (hbranches : branches.Nonempty)
    (law : J → Measure Ω) (loss : P → Ω → ℝ) (limit : ℝ) (p : P)
    (hp : p ∈ riskPolicies candidates branches hbranches law loss limit) :
    ∀ j ∈ branches, (∫ ω, loss p ω ∂law j) ≤ limit := by
  rcases (riskPolicies_mem_iff candidates branches hbranches law loss limit p).mp hp with
    ⟨_, hinputs, hworst⟩
  intro j hj
  have hbound :=
    (Finset.sup'_le_iff hbranches (lossMean law loss p)).mp hworst j hj
  simpa [lossMean, Core.branchExpectedUtility] using hbound

theorem riskPickMaxMin_some_spec {J P Ω : Type} [MeasurableSpace Ω]
    [DecidableEq J] [DecidableEq P]
    (candidates : Finset P) (branches : Finset J) (hbranches : branches.Nonempty)
    (law : J → Measure Ω) (loss : P → Ω → ℝ) (limit : ℝ)
    (values : P → J → ℝ) (p : P)
    (hpick : Core.pickMaxMin branches hbranches
      (riskPolicies candidates branches hbranches law loss limit) values = some p) :
    p ∈ riskPolicies candidates branches hbranches law loss limit ∧
      ∀ q ∈ riskPolicies candidates branches hbranches law loss limit,
        Core.worstBranchValue branches hbranches values q ≤
          Core.worstBranchValue branches hbranches values p :=
  Core.pickMaxMin_spec branches hbranches
    (riskPolicies candidates branches hbranches law loss limit) values p hpick

theorem riskPickMaxMin_none_iff_empty {J P Ω : Type} [MeasurableSpace Ω]
    [DecidableEq J] [DecidableEq P]
    (candidates : Finset P) (branches : Finset J) (hbranches : branches.Nonempty)
    (law : J → Measure Ω) (loss : P → Ω → ℝ) (limit : ℝ)
    (values : P → J → ℝ) :
    Core.pickMaxMin branches hbranches
      (riskPolicies candidates branches hbranches law loss limit) values = none ↔
        riskPolicies candidates branches hbranches law loss limit = ∅ :=
  Core.pickMaxMin_none_iff branches hbranches
    (riskPolicies candidates branches hbranches law loss limit) values

/-- A conditional/model-dependent assessment. It intentionally has no
actual/deployed-value or verified-status field. -/
structure ConditionalModelRiskReport (J P : Type) where
  conditionalModelCandidates : Finset P
  conditionalModelExpectedUtility : P → J → ℝ
  conditionalModelWorstExpectedLoss : P → Option ℝ
  conditionalModelRiskFilteredPolicies : Finset P
  conditionalModelChoice : Option P

/-- Build a report from the supplied branch laws and a pre-existing finite
candidate class. `none` in the loss field means the branch-law/integrability
inputs do not support a well-formed expected-loss value for that policy. -/
noncomputable def conditionalModelRiskEvaluation {J P Ω : Type}
    [MeasurableSpace Ω] [DecidableEq J] [DecidableEq P]
    (branches : Finset J) (hbranches : branches.Nonempty)
    (candidates : Finset P) (law : J → Measure Ω)
    (utility : J → ℝ → ℝ) (outcome : P → Ω → ℝ)
    (hUtility : Core.expectedUtilityInputsWellFormed branches candidates law utility outcome)
    (loss : P → Ω → ℝ) (limit : ℝ) : ConditionalModelRiskReport J P := by
  classical
  exact {
    conditionalModelCandidates := candidates
    conditionalModelExpectedUtility := Core.expectedUtilityMatrix law utility outcome
    conditionalModelWorstExpectedLoss := fun p =>
      if h : riskModelInputsWellFormed branches law loss p then
        some (worstExpectedLoss branches hbranches law loss p)
      else none
    conditionalModelRiskFilteredPolicies :=
      riskPolicies candidates branches hbranches law loss limit
    conditionalModelChoice := Core.pickMaxMin branches hbranches
      (riskPolicies candidates branches hbranches law loss limit)
      (Core.expectedUtilityMatrix law utility outcome)
  }

/-! The finite example is a concrete common-policy class, not a claim about
arbitrary legal branches or deployed distributions. -/

local instance : MeasurableSpace Core.DemoWorld := ⊤

local instance (j : Core.DemoBranch) : IsProbabilityMeasure (Core.demoBranchMeasure j) := by
  change IsProbabilityMeasure ((Core.fixedBranchLaw j).toMeasure)
  infer_instance

abbrev RiskDemoPolicy := Fin 2

def riskDemoCoreAction (p : RiskDemoPolicy) : Core.DemoAction :=
  if p.val = 0 then 0 else 2

def riskDemoRealize (p : RiskDemoPolicy) : Core.VisiblePolicy Unit Core.DemoAction :=
  Core.demoVisiblePolicy (riskDemoCoreAction p)

theorem riskDemo_realization_matches_existing_policy (p : RiskDemoPolicy) (n : ℕ)
    (h : Core.History Unit Core.DemoAction) (s : Unit)
    (hn : (Core.demoControl.legal (n + 1) s).Nonempty) :
    (Core.demoPolicy (riskDemoCoreAction p) n h s hn).val =
      riskDemoRealize p n h s := by
  simpa [riskDemoRealize] using
    Core.demo_policy_matches_visible_policy (riskDemoCoreAction p) n h s hn

theorem riskDemo_induced_law_is_fixed (p : RiskDemoPolicy) (j : Core.DemoBranch) :
    Core.inducedWorldLaw (riskDemoCoreAction p) j = Core.fixedBranchLaw j :=
  (Core.every_policy_induces_fixed_branch_law (riskDemoCoreAction p) j).1

def riskDemoCommonPolicies : Finset RiskDemoPolicy :=
  Core.commonPolicies Finset.univ riskDemoRealize 1 Core.demoBranchSet
    Core.demoInitial Core.demoNext Core.demoLegal Core.demoImplementable

theorem riskDemoCommonPolicies_eq_univ : riskDemoCommonPolicies = Finset.univ := by
  classical
  ext p
  simp [riskDemoCommonPolicies, Core.commonPolicies, riskDemoRealize,
    Core.demo_policies_feasible, Core.demoVisiblePolicy]

def riskDemoLaw (j : Core.DemoBranch) : Measure Core.DemoWorld := Core.demoBranchMeasure j

def riskDemoOutcome (p : RiskDemoPolicy) (_ω : Core.DemoWorld) : ℝ :=
  if p.val = 0 then 10 else 4

def riskDemoLoss (p : RiskDemoPolicy) (ω : Core.DemoWorld) : ℝ :=
  if p.val = 0 then if ω.1.val = 0 then 0 else 3 else 1

private theorem riskDemo_branch_integral_eq (j : Core.DemoBranch)
    (f : Core.DemoWorld → ℝ) :
    (∫ ω, f ω ∂riskDemoLaw j) =
      f (j, JurisLean.Candidates.U06_1FiniteBellman20261030.terminalTrace () 1) := by
  classical
  change (∫ ω, f ω ∂(Core.fixedBranchLaw j).toMeasure) = _
  rw [(Core.every_policy_induces_fixed_branch_law (0 : Core.DemoAction) j).2]
  rw [PMF.integral_eq_sum]
  rw [Finset.sum_eq_single
    (j, JurisLean.Candidates.U06_1FiniteBellman20261030.terminalTrace () 1)]
  · simp [PMF.pure_apply]
  · intro ω hω hne
    simp [PMF.pure_apply, hne]
  · intro hnot
    exact (hnot (Finset.mem_univ _)).elim

theorem riskDemo_expected_utility_values (p : RiskDemoPolicy) (j : Core.DemoBranch) :
    Core.expectedUtilityMatrix riskDemoLaw (fun _ x => x) riskDemoOutcome p j =
      if p.val = 0 then 10 else 4 := by
  have h := riskDemo_branch_integral_eq j (fun ω => riskDemoOutcome p ω)
  simpa [Core.expectedUtilityMatrix, Core.branchExpectedUtility, riskDemoOutcome,
    riskDemoLaw] using h

theorem riskDemo_expected_loss_values :
    lossMean riskDemoLaw riskDemoLoss (0 : RiskDemoPolicy) 0 = 0 ∧
    lossMean riskDemoLaw riskDemoLoss (0 : RiskDemoPolicy) 1 = 3 ∧
    lossMean riskDemoLaw riskDemoLoss (1 : RiskDemoPolicy) 0 = 1 ∧
    lossMean riskDemoLaw riskDemoLoss (1 : RiskDemoPolicy) 1 = 1 := by
  have h00 := riskDemo_branch_integral_eq (0 : Core.DemoBranch)
    (fun ω => riskDemoLoss (0 : RiskDemoPolicy) ω)
  have h01 := riskDemo_branch_integral_eq (1 : Core.DemoBranch)
    (fun ω => riskDemoLoss (0 : RiskDemoPolicy) ω)
  have h10 := riskDemo_branch_integral_eq (0 : Core.DemoBranch)
    (fun ω => riskDemoLoss (1 : RiskDemoPolicy) ω)
  have h11 := riskDemo_branch_integral_eq (1 : Core.DemoBranch)
    (fun ω => riskDemoLoss (1 : RiskDemoPolicy) ω)
  constructor
  · simpa [lossMean, Core.branchExpectedUtility, riskDemoLoss, riskDemoLaw] using h00
  constructor
  · simpa [lossMean, Core.branchExpectedUtility, riskDemoLoss, riskDemoLaw] using h01
  constructor
  · simpa [lossMean, Core.branchExpectedUtility, riskDemoLoss, riskDemoLaw] using h10
  · simpa [lossMean, Core.branchExpectedUtility, riskDemoLoss, riskDemoLaw] using h11

theorem riskDemo_loss_nonnegative (p : RiskDemoPolicy) (ω : Core.DemoWorld) :
    0 ≤ riskDemoLoss p ω := by
  by_cases hp : p.val = 0
  · by_cases hω : ω.1.val = 0 <;> norm_num [riskDemoLoss, hp, hω]
  · norm_num [riskDemoLoss, hp]

private theorem riskDemo_model_inputs (p : RiskDemoPolicy) :
    riskModelInputsWellFormed Core.demoBranchSet riskDemoLaw riskDemoLoss p := by
  constructor
  · intro j hj
    infer_instance
  · intro j hj
    exact Integrable.of_finite

theorem riskDemo_unconstrained_original_optimum :
    (∀ j : Core.DemoBranch,
      Core.expectedUtilityMatrix riskDemoLaw (fun _ x => x) riskDemoOutcome 0 j = 10) ∧
    (∀ j : Core.DemoBranch,
      Core.expectedUtilityMatrix riskDemoLaw (fun _ x => x) riskDemoOutcome 1 j = 4) ∧
    (∀ p : RiskDemoPolicy, p ≠ 0 →
      Core.worstBranchValue Core.demoBranchSet Core.demo_branches_nonempty
        (Core.expectedUtilityMatrix riskDemoLaw (fun _ x => x) riskDemoOutcome) p <
      Core.worstBranchValue Core.demoBranchSet Core.demo_branches_nonempty
        (Core.expectedUtilityMatrix riskDemoLaw (fun _ x => x) riskDemoOutcome) 0) := by
  constructor
  · intro j
    simpa using riskDemo_expected_utility_values 0 j
  constructor
  · intro j
    simpa using riskDemo_expected_utility_values 1 j
  · intro p hp
    fin_cases p
    · exact (hp rfl).elim
    · have hzero : Core.expectedUtilityMatrix riskDemoLaw (fun _ x => x)
          riskDemoOutcome 0 = fun _ => 10 := by
        funext j
        exact riskDemo_expected_utility_values 0 j
      have hone : Core.expectedUtilityMatrix riskDemoLaw (fun _ x => x)
          riskDemoOutcome 1 = fun _ => 4 := by
        funext j
        exact riskDemo_expected_utility_values 1 j
      norm_num [Core.worstBranchValue, Core.demoBranchSet, hzero, hone]

theorem riskDemo_filter_at_two_is_singleton :
    riskPolicies riskDemoCommonPolicies Core.demoBranchSet Core.demo_branches_nonempty
      riskDemoLaw riskDemoLoss 2 = ({1} : Finset RiskDemoPolicy) := by
  classical
  rw [riskDemoCommonPolicies_eq_univ]
  rcases riskDemo_expected_loss_values with ⟨_, hLoss01, hLoss10, hLoss11⟩
  have hPolicy01 : (0 : RiskDemoPolicy) ≠ 1 := by decide
  ext p
  fin_cases p
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton, hPolicy01]
    constructor
    · rintro ⟨_, hWorst⟩
      have hAll := (Finset.sup'_le_iff Core.demo_branches_nonempty
        (lossMean riskDemoLaw riskDemoLoss (0 : RiskDemoPolicy))).mp hWorst
      have hbad := hAll 1 (by simp [Core.demoBranchSet])
      norm_num [hLoss01] at hbad
    · intro h
      exact False.elim h
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · intro _
      rfl
    · intro _
      refine ⟨riskDemo_model_inputs 1, ?_⟩
      apply (Finset.sup'_le_iff Core.demo_branches_nonempty
        (lossMean riskDemoLaw riskDemoLoss (1 : RiskDemoPolicy))).mpr
      intro j hj
      fin_cases j <;> norm_num [hLoss10, hLoss11]

theorem riskDemo_risk_picker_selects_one :
    Core.pickMaxMin Core.demoBranchSet Core.demo_branches_nonempty
      (riskPolicies riskDemoCommonPolicies Core.demoBranchSet Core.demo_branches_nonempty
        riskDemoLaw riskDemoLoss 2)
      (Core.expectedUtilityMatrix riskDemoLaw (fun _ x => x) riskDemoOutcome) = some 1 := by
  classical
  rw [riskDemo_filter_at_two_is_singleton]
  have hne : ({1} : Finset RiskDemoPolicy).Nonempty := ⟨1, by simp⟩
  unfold Core.pickMaxMin
  rw [dif_pos hne]
  have hchoose := Classical.choose_spec
    (Core.finite_max_min_attained Core.demoBranchSet Core.demo_branches_nonempty
      ({1} : Finset RiskDemoPolicy) hne
      (Core.expectedUtilityMatrix riskDemoLaw (fun _ x => x) riskDemoOutcome))
  have hvalue : Classical.choose
      (Core.finite_max_min_attained Core.demoBranchSet Core.demo_branches_nonempty
        ({1} : Finset RiskDemoPolicy) hne
        (Core.expectedUtilityMatrix riskDemoLaw (fun _ x => x) riskDemoOutcome)) = 1 := by
    simpa using Finset.mem_singleton.mp hchoose.1
  exact congrArg some hvalue

theorem riskDemo_filter_at_zero_is_empty :
    riskPolicies riskDemoCommonPolicies Core.demoBranchSet Core.demo_branches_nonempty
      riskDemoLaw riskDemoLoss 0 = ∅ := by
  classical
  rw [riskDemoCommonPolicies_eq_univ]
  rcases riskDemo_expected_loss_values with ⟨_, hLoss01, hLoss10, _⟩
  ext p
  fin_cases p
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.not_mem_empty]
    constructor
    · rintro ⟨_, hWorst⟩
      have hAll := (Finset.sup'_le_iff Core.demo_branches_nonempty
        (lossMean riskDemoLaw riskDemoLoss (0 : RiskDemoPolicy))).mp hWorst
      have hbad := hAll 1 (by simp [Core.demoBranchSet])
      norm_num [hLoss01] at hbad
    · intro hfalse
      exact False.elim hfalse
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.not_mem_empty]
    constructor
    · rintro ⟨_, hWorst⟩
      have hAll := (Finset.sup'_le_iff Core.demo_branches_nonempty
        (lossMean riskDemoLaw riskDemoLoss (1 : RiskDemoPolicy))).mp hWorst
      have hbad := hAll 0 (by simp [Core.demoBranchSet])
      norm_num [hLoss10] at hbad
    · intro hfalse
      exact False.elim hfalse

theorem riskDemo_zero_limit_picker_returns_none :
    Core.pickMaxMin Core.demoBranchSet Core.demo_branches_nonempty
      (riskPolicies riskDemoCommonPolicies Core.demoBranchSet Core.demo_branches_nonempty
        riskDemoLaw riskDemoLoss 0)
      (Core.expectedUtilityMatrix riskDemoLaw (fun _ x => x) riskDemoOutcome) = none := by
  rw [riskDemo_filter_at_zero_is_empty]
  exact (Core.pickMaxMin_none_iff Core.demoBranchSet Core.demo_branches_nonempty
    ∅ (Core.expectedUtilityMatrix riskDemoLaw (fun _ x => x) riskDemoOutcome)).2 rfl

end JurisLean.Candidates.U06_6OriginalRiskEvaluation20261102
