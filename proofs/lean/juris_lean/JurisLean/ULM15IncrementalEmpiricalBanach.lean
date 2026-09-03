import JurisLean.ULM14CoverageTrust
import JurisLean.HornFixedPoint
import Mathlib.Topology.MetricSpace.Contracting

/-! Add-only Horn specification, read-only empirical artifacts, and genuine
mathlib Banach fixed-point reuse. -/

namespace JurisLean.ULM

section HornAddOnly

variable {α : Type*} [DecidableEq α]

structure HornAddDelta (sys : HornSystem α) where
  facts : Finset α
  rules : Finset (HornRule α)
  facts_subset_univ : facts ⊆ sys.univ
  heads_subset_univ : ∀ r ∈ rules, r.conclusion ∈ sys.univ


def extendHorn (sys : HornSystem α) (delta : HornAddDelta sys) : HornSystem α where
  univ := sys.univ
  initialFacts := sys.initialFacts ∪ delta.facts
  rules := sys.rules ∪ delta.rules
  initialFacts_subset_univ :=
    Finset.union_subset sys.initialFacts_subset_univ delta.facts_subset_univ
  heads_subset_univ := by
    intro r hr
    rcases Finset.mem_union.mp hr with hrOld | hrNew
    · exact sys.heads_subset_univ r hrOld
    · exact delta.heads_subset_univ r hrNew


theorem TH_subset_extend (sys : HornSystem α) (delta : HornAddDelta sys)
    (s : Finset α) :
    HornSystem.TH sys s ⊆ HornSystem.TH (extendHorn sys delta) s := by
  intro a ha
  simp only [HornSystem.TH, Finset.mem_union, Finset.mem_image,
    Finset.mem_filter] at ha ⊢
  rcases ha with hInit | ⟨r, ⟨hr, hprem⟩, rfl⟩
  · exact Or.inl (Or.inl hInit)
  · exact Or.inr ⟨r, ⟨Or.inl hr, hprem⟩, rfl⟩


theorem horn_iter_subset_extend (sys : HornSystem α)
    (delta : HornAddDelta sys) (n : Nat) :
    FiniteMonotoneSystem.iter (HornSystem.toFiniteMonotoneSystem sys) n ⊆
    FiniteMonotoneSystem.iter
      (HornSystem.toFiniteMonotoneSystem (extendHorn sys delta)) n := by
  induction n with
  | zero => simp [FiniteMonotoneSystem.iter]
  | succ n ih =>
      rw [FiniteMonotoneSystem.iter_succ, FiniteMonotoneSystem.iter_succ]
      change HornSystem.TH sys _ ⊆ HornSystem.TH (extendHorn sys delta) _
      exact Finset.Subset.trans (HornSystem.TH_monotone sys ih)
        (TH_subset_extend sys delta _)


theorem horn_closure_subset_extend (sys : HornSystem α)
    (delta : HornAddDelta sys) :
    FiniteMonotoneSystem.iter
        (HornSystem.toFiniteMonotoneSystem sys) sys.univ.card ⊆
    FiniteMonotoneSystem.iter
        (HornSystem.toFiniteMonotoneSystem (extendHorn sys delta)) sys.univ.card :=
  horn_iter_subset_extend sys delta sys.univ.card

/-- Child-subject full recomputation is the independent specification. -/
def childFullRecompute (sys : HornSystem α)
    (delta : HornAddDelta sys) : Finset α :=
  FiniteMonotoneSystem.iter
    (HornSystem.toFiniteMonotoneSystem (extendHorn sys delta)) sys.univ.card

/-- An optimised worklist implementation is correct only if it refines the child
full-recompute specification. -/
def IncrementalImplementationCorrect
    (implementation : HornAddDelta sys → Finset α) : Prop :=
  ∀ delta, implementation delta = childFullRecompute sys delta

theorem incremental_correct_returns_full_recompute
    {implementation : HornAddDelta sys → Finset α}
    (h : IncrementalImplementationCorrect (sys := sys) implementation)
    (delta : HornAddDelta sys) :
    implementation delta = childFullRecompute sys delta := h delta


theorem childFullRecompute_fixed
    (sys : HornSystem α) (delta : HornAddDelta sys) :
    HornSystem.TH (extendHorn sys delta)
      (childFullRecompute sys delta) =
      childFullRecompute sys delta := by
  simpa [childFullRecompute] using
    HornSystem.horn_result_fixed_point (extendHorn sys delta)

end HornAddOnly

structure EmpiricalArtifact (α : Type*) where
  normativeSolutions : Finset α
  score : ℚ
  label : String


def attachEmpirical (solutions : Finset α) (score : ℚ) : EmpiricalArtifact α :=
  { normativeSolutions := solutions, score := score, label := "empirical" }

@[simp] theorem empirical_is_read_only (solutions : Finset α) (score : ℚ) :
    (attachEmpirical solutions score).normativeSolutions = solutions := rfl


def deviationScore {n : Nat} (weight feature : Fin n → ℚ) : ℚ :=
  ∑ i, weight i * feature i

@[simp] theorem deviationScore_decomposes {n : Nat}
    (weight feature : Fin n → ℚ) :
    deviationScore weight feature = ∑ i, weight i * feature i := rfl

section GenuineBanach

variable {β : Type*} [MetricSpace β] [CompleteSpace β] [Nonempty β]
variable {K : ℝ≥0} {f : β → β}

/-- Genuine Banach fixed-point existence, using mathlib's `fixedPoint`. -/
theorem banach_exists_fixedPoint (hf : ContractingWith K f) :
    ∃ y, Function.IsFixedPt f y := by
  exact ⟨ContractingWith.fixedPoint f hf, hf.fixedPoint_isFixedPt⟩

/-- Genuine uniqueness of the fixed point. -/
theorem banach_fixedPoint_unique (hf : ContractingWith K f)
    {x y : β} (hx : Function.IsFixedPt f x)
    (hy : Function.IsFixedPt f y) : x = y := by
  calc
    x = ContractingWith.fixedPoint f hf := hf.fixedPoint_unique hx
    _ = y := (hf.fixedPoint_unique hy).symm

/-- Genuine convergence of all iterates to the mathlib fixed point. -/
theorem banach_iterates_converge (hf : ContractingWith K f) (x : β) :
    Filter.Tendsto (fun n ↦ f^[n] x) Filter.atTop
      (nhds (ContractingWith.fixedPoint f hf)) :=
  hf.tendsto_iterate_fixedPoint x


/-- The standard a-priori Banach error estimate from the pinned mathlib API. -/
theorem banach_apriori_error_bound
    (hf : ContractingWith K f) (x : β) (n : Nat) :
    dist (f^[n] x) (ContractingWith.fixedPoint f hf) ≤
      dist x (f x) * (K : ℝ) ^ n / (1 - K) :=
  hf.apriori_dist_iterate_fixedPoint_le x n

end GenuineBanach

end JurisLean.ULM
