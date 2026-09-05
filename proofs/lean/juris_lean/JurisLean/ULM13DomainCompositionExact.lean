import JurisLean.ULM12Procedure

/-! Domain bundles, policy-bound structural choices, and unit-indexed exact calculation. -/

namespace JurisLean.ULM

structure DomainOutcome where
  request : RequestKey
  outcomeId : String
deriving DecidableEq

structure DomainBundle where
  branch : SemanticBranchKey
  candidates : Finset DomainOutcome
deriving DecidableEq

def DomainBundle.WF (bundle : DomainBundle) : Prop :=
  ∀ candidate ∈ bundle.candidates,
    candidate.request = bundle.branch.scenario.request

structure CompositionPolicy where
  request : RequestKey
  policyId : String
  allows : Finset DomainOutcome → Bool

structure CompositionChoice where
  branch : SemanticBranchKey
  policyId : String
  selected : Finset DomainOutcome
deriving DecidableEq

/-- The actual bundle and actual policy both constrain a valid choice. -/
structure ChoiceWF
    (bundle : DomainBundle) (policy : CompositionPolicy)
    (choice : CompositionChoice) : Prop where
  bundleWellFormed : bundle.WF
  policyRequest : policy.request = bundle.branch.scenario.request
  policyId : choice.policyId = policy.policyId
  branch : choice.branch = bundle.branch
  selectedSubset : choice.selected ⊆ bundle.candidates
  selectedNonempty : choice.selected.Nonempty
  allowed : policy.allows choice.selected = true

/-- Finite reference choice carrier. It enumerates nonempty candidate subsets
accepted by the frozen actual policy. -/
def compositionChoices
    (bundle : DomainBundle) (policy : CompositionPolicy) :
    Finset CompositionChoice :=
  (bundle.candidates.powerset.filter fun selected =>
      selected.Nonempty ∧ policy.allows selected = true).image
    (fun selected =>
      { branch := bundle.branch
        policyId := policy.policyId
        selected := selected })

theorem compositionChoices_sound
    {bundle : DomainBundle} {policy : CompositionPolicy}
    (hBundle : bundle.WF)
    (hPolicy : policy.request = bundle.branch.scenario.request)
    {choice : CompositionChoice}
    (hChoice : choice ∈ compositionChoices bundle policy) :
    ChoiceWF bundle policy choice := by
  rcases Finset.mem_image.mp hChoice with ⟨selected, hSelected, rfl⟩
  rcases Finset.mem_filter.mp hSelected with ⟨hPowerset, hAllowed⟩
  exact
    { bundleWellFormed := hBundle
      policyRequest := hPolicy
      policyId := rfl
      branch := rfl
      selectedSubset := Finset.mem_powerset.mp hPowerset
      selectedNonempty := hAllowed.1
      allowed := hAllowed.2 }

theorem choice_wf_selected_subset
    {bundle : DomainBundle} {policy : CompositionPolicy}
    {choice : CompositionChoice}
    (h : ChoiceWF bundle policy choice) :
    choice.selected ⊆ bundle.candidates := h.selectedSubset

theorem choice_wf_policy_bound
    {bundle : DomainBundle} {policy : CompositionPolicy}
    {choice : CompositionChoice}
    (h : ChoiceWF bundle policy choice) :
    choice.policyId = policy.policyId := h.policyId

structure BranchChoiceKey where
  policyId : String
  selected : Finset DomainOutcome
deriving DecidableEq

structure ChildBranchKey where
  parent : SemanticBranchKey
  choice : BranchChoiceKey
deriving DecidableEq

def choiceKey (choice : CompositionChoice) : BranchChoiceKey :=
  { policyId := choice.policyId, selected := choice.selected }

def childOfChoice (choice : CompositionChoice) : ChildBranchKey :=
  { parent := choice.branch, choice := choiceKey choice }

@[simp] theorem childOfChoice_selected (choice : CompositionChoice) :
    (childOfChoice choice).choice.selected = choice.selected := rfl

@[simp] theorem childOfChoice_policy (choice : CompositionChoice) :
    (childOfChoice choice).choice.policyId = choice.policyId := rfl

inductive DurationUnit where
  | day
  | month
  | year
deriving DecidableEq

/-- Currency, duration unit, and rate basis are part of the type index. Thus an
addition cannot even be formed for RMB and USD or for days and months. -/
inductive Dimension where
  | scalar
  | money (currency : String)
  | duration (unit : DurationUnit)
  | rate (basis : String)
deriving DecidableEq

inductive ExactExpr : Dimension → Type where
  | lit (d : Dimension) (value : ℚ) : ExactExpr d
  | add {d : Dimension} (left right : ExactExpr d) : ExactExpr d
  | sub {d : Dimension} (left right : ExactExpr d) : ExactExpr d
  | scale {d : Dimension} (factor : ℚ) (value : ExactExpr d) : ExactExpr d

namespace ExactExpr

def eval : {d : Dimension} → ExactExpr d → ℚ
  | _, .lit _ q => q
  | _, .add a b => eval a + eval b
  | _, .sub a b => eval a - eval b
  | _, .scale q a => q * eval a

/-- Independent recursive denotation. The theorem below is interpreter
correctness, not validation of a statutory calculation policy. -/
def denote : {d : Dimension} → ExactExpr d → ℚ
  | _, .lit _ q => q
  | _, .add a b => denote a + denote b
  | _, .sub a b => denote a - denote b
  | _, .scale q a => q * denote a

@[simp] theorem eval_eq_denote {d : Dimension} (e : ExactExpr d) :
    eval e = denote e := by
  induction e <;> simp [eval, denote, *]

end ExactExpr

def executeExact {d : Dimension} (e : ExactExpr d) : Outcome ℚ :=
  .complete e.eval

@[simp] theorem exact_execution_matches_denotation
    {d : Dimension} (e : ExactExpr d) :
    executeExact e = .complete e.denote := by
  simp [executeExact, ExactExpr.eval_eq_denote]

end JurisLean.ULM
