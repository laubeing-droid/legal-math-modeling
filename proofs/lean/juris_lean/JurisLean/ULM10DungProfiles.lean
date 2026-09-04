import JurisLean.ULM09AttackDefeat
import JurisLean.FiniteMonotoneIteration
import Mathlib.Order.Preorder.Finite

/-! Finite request-bound Dung defeat semantics and powerset reference specs. -/

namespace JurisLean.ULM

abbrev ArgId := CanonicalArgument

structure DefeatAF where
  request : RequestKey
  args : Finset ArgId
  defeats : Finset (ArgId × ArgId)
deriving DecidableEq

/-- Every argument and defeat endpoint belongs to the same request-bound finite
carrier; every argument also satisfies the independent support-graph contract. -/
structure DefeatAF.WellFormed (af : DefeatAF) : Prop where
  argsRequestBound : ∀ a ∈ af.args, a.request = af.request
  argsWellFormed : ∀ a ∈ af.args, ArgumentWF a
  defeatEndpoints : ∀ p ∈ af.defeats, p.1 ∈ af.args ∧ p.2 ∈ af.args

/-- Structured input to the first real heterogeneous bridge. The full argument
support graph remains inside each `CanonicalArgument`; only the final resolved
defeat relation is abstracted to Dung. -/
structure StructuredArgumentation where
  request : RequestKey
  arguments : Finset CanonicalArgument
  attacks : ValidatedAttackSet
  attackSetRequest : attacks.request = request
  argumentsRequestBound : ∀ a ∈ arguments, a.request = request
  argumentsWellFormed : ∀ a ∈ arguments, ArgumentWF a
  attackEndpoints : ∀ attack ∈ attacks.attacks,
    attack.attacker ∈ arguments ∧ attack.target ∈ arguments

/-- Priority/authority/guard policy is resolved before the Dung evaluator. -/
def resolveToDefeatAF
    (input : StructuredArgumentation) (policy : DefeatPolicy) : DefeatAF :=
  { request := input.request
    args := input.arguments
    defeats := resolveDefeat input.attacks policy }

theorem resolveToDefeatAF_wellFormed
    (input : StructuredArgumentation) (policy : DefeatPolicy) :
    (resolveToDefeatAF input policy).WellFormed := by
  refine
    { argsRequestBound := input.argumentsRequestBound
      argsWellFormed := input.argumentsWellFormed
      defeatEndpoints := ?_ }
  intro p hp
  rcases (mem_resolveDefeat_iff.mp hp) with ⟨a, ha, _, hx, hy⟩
  have hendpoints := input.attackEndpoints a ha
  constructor
  · simpa [← hx] using hendpoints.1
  · simpa [← hy] using hendpoints.2

def attackers (af : DefeatAF) (a : ArgId) : Finset ArgId :=
  af.args.filter (fun b => (b, a) ∈ af.defeats)

/-- Dung characteristic function over the resolved binary defeat graph. -/
def characteristic (af : DefeatAF) (s : Finset ArgId) : Finset ArgId :=
  af.args.filter (fun a =>
    ∀ b ∈ attackers af a,
      ((attackers af b).filter (fun c => c ∈ s)) ≠ ∅)

def defeatSystem (af : DefeatAF) : FiniteMonotoneSystem ArgId where
  univ := af.args
  step := characteristic af
  step_subset_univ := by
    intro s
    exact Finset.filter_subset _ _
  step_monotone := by
    intro s t hst
    rw [characteristic, characteristic]
    intro a ha
    rw [Finset.mem_filter] at ha ⊢
    rcases ha with ⟨haArgs, haDefended⟩
    refine ⟨haArgs, ?_⟩
    intro b hb
    have hnonempty :
        ((attackers af b).filter (fun c => c ∈ s)).Nonempty :=
      Finset.nonempty_iff_ne_empty.mpr (haDefended b hb)
    rcases hnonempty with ⟨c, hc⟩
    rcases Finset.mem_filter.mp hc with ⟨hcAttack, hcS⟩
    have hcT : c ∈ (attackers af b).filter (fun c => c ∈ t) :=
      Finset.mem_filter.mpr ⟨hcAttack, hst hcS⟩
    exact Finset.nonempty_iff_ne_empty.mp ⟨c, hcT⟩

/-- Grounded extension for the request-bound structural carrier. -/
def groundedExtension (af : DefeatAF) : Finset ArgId :=
  FiniteMonotoneSystem.iter (defeatSystem af) af.args.card

theorem groundedExtension_fixed (af : DefeatAF) :
    characteristic af (groundedExtension af) = groundedExtension af := by
  have hfixed := FiniteMonotoneSystem.fixed_at_card (defeatSystem af)
  rw [FiniteMonotoneSystem.iter_succ (defeatSystem af) af.args.card] at hfixed
  simpa [groundedExtension, defeatSystem] using hfixed.symm

theorem groundedExtension_least (af : DefeatAF)
    (s : Finset ArgId) (hs : characteristic af s = s) :
    groundedExtension af ⊆ s := by
  have hind : ∀ n : Nat, FiniteMonotoneSystem.iter (defeatSystem af) n ⊆ s := by
    intro n
    induction n with
    | zero => simp [FiniteMonotoneSystem.iter]
    | succ n ih =>
        rw [FiniteMonotoneSystem.iter_succ]
        have hmono := (defeatSystem af).step_monotone ih
        simpa [defeatSystem, hs] using hmono
  exact hind af.args.card

theorem groundedExtension_subset_args (af : DefeatAF) :
    groundedExtension af ⊆ af.args :=
  FiniteMonotoneSystem.iter_subset_univ (defeatSystem af) af.args.card

def ConflictFree (af : DefeatAF) (s : Finset ArgId) : Prop :=
  s ⊆ af.args ∧
    ∀ a ∈ s, ∀ b ∈ s, (a, b) ∉ af.defeats

def Defends (af : DefeatAF) (s : Finset ArgId) (a : ArgId) : Prop :=
  ∀ b ∈ af.args, (b, a) ∈ af.defeats →
    ∃ c ∈ s, (c, b) ∈ af.defeats

def Admissible (af : DefeatAF) (s : Finset ArgId) : Prop :=
  ConflictFree af s ∧ ∀ a ∈ s, Defends af s a

/-- Complete extensions are admissible fixed points of the characteristic
function. Fixed-point equality alone is insufficient because a non-conflict-free
set can be self-defending. -/
def Complete (af : DefeatAF) (s : Finset ArgId) : Prop :=
  Admissible af s ∧ characteristic af s = s

/-- Grounded is the least characteristic fixed point. Its standard equivalence
with the least complete extension is a separate theorem family. -/
def Grounded (af : DefeatAF) (s : Finset ArgId) : Prop :=
  characteristic af s = s ∧
    ∀ t : Finset ArgId, characteristic af t = t → s ⊆ t

/-- Preferred means inclusion-maximal admissible. -/
def Preferred (af : DefeatAF) (s : Finset ArgId) : Prop :=
  Admissible af s ∧
    ∀ t : Finset ArgId, Admissible af t → s ⊆ t → t ⊆ s

/-- Stable remains a separate profile and may have no extension. -/
def Stable (af : DefeatAF) (s : Finset ArgId) : Prop :=
  ConflictFree af s ∧
    ∀ a ∈ af.args, a ∉ s → ∃ b ∈ s, (b, a) ∈ af.defeats

def SatisfiesProfile
    (af : DefeatAF) (profile : SemanticProfile) (s : Finset ArgId) : Prop :=
  match profile with
  | .grounded => Grounded af s
  | .preferred => Preferred af s
  | .stable => Stable af s
  | .complete => Complete af s

theorem groundedExtension_is_grounded (af : DefeatAF) :
    Grounded af (groundedExtension af) :=
  ⟨groundedExtension_fixed af, groundedExtension_least af⟩

theorem grounded_unique {af : DefeatAF} {s : Finset ArgId}
    (h : Grounded af s) : s = groundedExtension af := by
  apply Finset.Subset.antisymm
  · exact h.2 _ (groundedExtension_fixed af)
  · exact groundedExtension_least af s h.1

noncomputable def admissibleFamily (af : DefeatAF) :
    Finset (Finset ArgId) := by
  classical
  exact af.args.powerset.filter (Admissible af)

noncomputable def completeExtensions (af : DefeatAF) :
    Finset (Finset ArgId) := by
  classical
  exact af.args.powerset.filter (Complete af)

noncomputable def preferredExtensions (af : DefeatAF) :
    Finset (Finset ArgId) := by
  classical
  exact af.args.powerset.filter (Preferred af)

noncomputable def stableExtensions (af : DefeatAF) :
    Finset (Finset ArgId) := by
  classical
  exact af.args.powerset.filter (Stable af)

theorem empty_admissible (af : DefeatAF) : Admissible af ∅ := by
  constructor
  · exact ⟨Finset.empty_subset _, by simp⟩
  · simp

theorem admissibleFamily_nonempty (af : DefeatAF) :
    (admissibleFamily af).Nonempty := by
  classical
  refine ⟨∅, ?_⟩
  exact Finset.mem_filter.mpr
    ⟨Finset.mem_powerset.mpr (Finset.empty_subset _), empty_admissible af⟩

theorem exists_preferred (af : DefeatAF) : ∃ s, Preferred af s := by
  classical
  obtain ⟨s, hs⟩ :=
    (admissibleFamily af).exists_maximal (admissibleFamily_nonempty af)
  refine ⟨s, ?_⟩
  constructor
  · exact (Finset.mem_filter.mp hs.1).2
  · intro t ht hst
    have htMem : t ∈ admissibleFamily af :=
      Finset.mem_filter.mpr
        ⟨Finset.mem_powerset.mpr ht.1.1, ht⟩
    exact hs.2 htMem hst

theorem mem_completeExtensions_iff
    (af : DefeatAF) (s : Finset ArgId) :
    s ∈ completeExtensions af ↔ Complete af s := by
  classical
  constructor
  · intro h
    exact (Finset.mem_filter.mp h).2
  · intro h
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_powerset.mpr h.1.1.1, h⟩

theorem mem_preferredExtensions_iff
    (af : DefeatAF) (s : Finset ArgId) :
    s ∈ preferredExtensions af ↔ Preferred af s := by
  classical
  constructor
  · intro h
    exact (Finset.mem_filter.mp h).2
  · intro h
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_powerset.mpr h.1.1.1, h⟩

theorem mem_stableExtensions_iff
    (af : DefeatAF) (s : Finset ArgId) :
    s ∈ stableExtensions af ↔ Stable af s := by
  classical
  constructor
  · intro h
    exact (Finset.mem_filter.mp h).2
  · intro h
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_powerset.mpr h.1.1, h⟩

theorem preferredExtensions_sound
    {af : DefeatAF} {s : Finset ArgId}
    (h : s ∈ preferredExtensions af) : Preferred af s :=
  (mem_preferredExtensions_iff af s).mp h

theorem preferredExtensions_complete
    {af : DefeatAF} {s : Finset ArgId}
    (h : Preferred af s) : s ∈ preferredExtensions af :=
  (mem_preferredExtensions_iff af s).mpr h

theorem preferredExtensions_nonempty (af : DefeatAF) :
    (preferredExtensions af).Nonempty := by
  classical
  obtain ⟨s, hs⟩ := exists_preferred af
  exact ⟨s, preferredExtensions_complete hs⟩

end JurisLean.ULM
