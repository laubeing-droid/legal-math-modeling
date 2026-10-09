import Mathlib.Tactic
import JurisLean.Seams.SourceNorms

/-
Unified Horn provenance bridge and Ionescu-Tulcea kernel wiring
(main doc 8.2 leftovers; master plan 3.3 layer-B extension and 9.3).

Part 1 - HORN PROVENANCE BRIDGE (master plan 3.3: a derived atom keeps
the source leaves of its derivation).  `HProvN` is a height-indexed
provenance-carrying derivation over the existing `HornSystem`: the
fact case cites the declared source set of an initial fact; the rule
case derives a conclusion with provenance EXACTLY the union of the
premises' provenances (`biUnion f`).  The height index (children at
level n, parent at n+1) is what makes the inductions go through -
membership-style hypotheses carry no IH.
Deliverables:
- soundness `hprovN_mem_closure`: every derivable atom is in the
  semantic closure (composes with `horn_closure_semantic_iff`);
- completeness `closure_mem_hprov`: every closure atom has a
  derivation with SOME provenance (choose + biUnion);
- provenance soundness `hprovN_prov_sound`: every source cited by a
  derivation belongs to the declared sources of some INITIAL FACT -
  a derivation cannot invent provenance.

Part 2 - IONESCU-TULCEA WIRING, discrete fragment (master plan 9.3).
The finite-prefix recursion of 9.3 on a finite state space:
`pathMass mu0 K (x :: l) = mu0 x * chainMass K x l`, and the cylinder
compatibility the extension theorem consumes:
- `chain_marginal` (isStochastic rows: summing over an appended state
  recovers the chain mass);
- `pathMass_marginal` (the trajectory-level version: projecting away
  the LAST coordinate of a longer prefix returns the prefix mass);
- `pathMass_init_total` (a normalized initial distribution gives
  total mass 1 on the one-step cylinder).
The existence/uniqueness of the INFINITE trajectory measure is
Mathlib's `ProbabilityTheory.Kernel.trajMeasure` at the pinned commit
(signature verified 2026-10-08, appendix I).  This file proves the
kernel-side hypotheses on the discrete carrier; it does not reprove
the theorem and does not instantiate the standard-Borel machinery -
that heavier instantiation remains an honestly-recorded open item,
same scoping discipline as layer O for CAD.

STATUS: proved theorems pending their CI compile round; this file
contains no sorry, no admit, no custom axiom, no `: True :=`, no
native_decide.
-/

namespace JurisLean.Seams.UnifiedHornIT

open Finset

/-! ## Part 1: Horn provenance bridge -/

variable {α : Type} [DecidableEq α]

/-- Height-indexed provenance-carrying derivation: the fact case holds
at any level; a rule step takes premise derivations at level n and
concludes at level n+1, with provenance exactly the union of the
premise provenances. -/
inductive HProvN (sys : HornSystem α) (ι : Type) [DecidableEq ι]
    (srcOf : α → Finset ι) : ℕ → Finset ι → α → Prop
  | fact (n : ℕ) (a : α) (h : a ∈ sys.initialFacts) :
      HProvN sys ι srcOf n (srcOf a) a
  | rule (n : ℕ) (r : HornRule α) (hr : r ∈ sys.rules)
      (f : α → Finset ι)
      (hch : ∀ p ∈ r.premises, HProvN sys ι srcOf n (f p) p) :
      HProvN sys ι srcOf (n + 1) (r.premises.biUnion f) r.conclusion

/-- Unheighted wrapper. -/
def HProv (sys : HornSystem α) (ι : Type) [DecidableEq ι]
    (srcOf : α → Finset ι) (P : Finset ι) (a : α) : Prop :=
  ∃ n, HProvN sys ι srcOf n P a

/-- Soundness: every derivable atom is in the semantic closure. -/
theorem hprovN_mem_closure (sys : HornSystem α) (ι : Type) [DecidableEq ι]
    (srcOf : α → Finset ι) :
    ∀ (n : ℕ) (P : Finset ι) (a : α),
      HProvN sys ι srcOf n P a → a ∈ JurisLean.Seams.SourceNorms.closureAt sys := by
  intro n
  induction n with
  | zero =>
      intro P a h
      cases h with
      | @fact _ _ hm =>
          exact (JurisLean.Seams.SourceNorms.closure_is_model sys).1 hm
  | succ k ih =>
      intro P a h
      cases h with
      | @fact _ _ hm =>
          exact (JurisLean.Seams.SourceNorms.closure_is_model sys).1 hm
      | @rule _ r hr f hch =>
          have hfp : HornSystem.TH sys
              (JurisLean.Seams.SourceNorms.closureAt sys)
              = JurisLean.Seams.SourceNorms.closureAt sys :=
            HornSystem.horn_result_fixed_point sys
          refine hfp ▸ Finset.mem_union.mpr (Or.inr ?_)
          refine Finset.mem_image.mpr ⟨r, Finset.mem_filter.mpr ⟨hr, ?_⟩, rfl⟩
          intro p hp
          exact ih (f p) p (hch p hp)

/-- Provenance soundness: every source cited by a derivation belongs
to the declared sources of some initial fact. -/
theorem hprovN_prov_sound (sys : HornSystem α) (ι : Type) [DecidableEq ι]
    (srcOf : α → Finset ι) :
    ∀ (n : ℕ) (P : Finset ι) (a : α),
      HProvN sys ι srcOf n P a →
        ∀ s ∈ P, ∃ b : α, b ∈ sys.initialFacts ∧ s ∈ srcOf b := by
  intro n
  induction n with
  | zero =>
      intro P a h s hs
      exact match h, hs with
        | .fact _ b hb, hs => ⟨b, hb, hs⟩
  | succ k ih =>
      intro P a h s hs
      exact match h, hs with
        | .fact _ b hb, hs => ⟨b, hb, hs⟩
        | .rule _ _ _ f hch, hs =>
            match Finset.mem_biUnion.mp hs with
            | ⟨p, hp, hfp⟩ => ih (f p) p (hch p hp) s hfp

/-- Iteration lemma: an atom inside iteration level n has a
level-n derivation. -/
theorem iter_mem_hprovN (sys : HornSystem α) (ι : Type) [DecidableEq ι]
    (srcOf : α → Finset ι) :
    ∀ (n : ℕ) (a : α),
        a ∈ FiniteMonotoneSystem.iter (HornSystem.toFiniteMonotoneSystem sys) n →
        ∃ P : Finset ι, HProvN sys ι srcOf n P a := by
  intro n
  induction n with
  | zero =>
      intro a ha
      simp only [FiniteMonotoneSystem.iter] at ha
      exact absurd ha (by simp)
  | succ k ih =>
      intro a ha
      rw [FiniteMonotoneSystem.iter_succ] at ha
      simp only [HornSystem.toFiniteMonotoneSystem] at ha
      unfold HornSystem.TH at ha
      rcases Finset.mem_union.mp ha with (ha0 | ha1)
      · exact ⟨srcOf a, HProvN.fact (k + 1) a ha0⟩
      · rcases Finset.mem_image.mp ha1 with ⟨r, hr, rfl⟩
        rcases Finset.mem_filter.mp hr with ⟨hr, hprem⟩
        choose! f hf using
          fun (p : α) (hp : p ∈ r.premises) => ih p (hprem hp)
        refine ⟨r.premises.biUnion f, HProvN.rule k r hr f ?_⟩
        intro p hp
        exact hf p hp

/-- Completeness: every closure atom has a provenance derivation. -/
theorem closure_mem_hprov (sys : HornSystem α) (ι : Type) [DecidableEq ι]
    (srcOf : α → Finset ι) {a : α}
    (h : a ∈ JurisLean.Seams.SourceNorms.closureAt sys) :
    ∃ P : Finset ι, HProv sys ι srcOf P a := by
  obtain ⟨P, hP⟩ := iter_mem_hprovN sys ι srcOf
    (Finset.card sys.univ) a h
  exact ⟨P, Finset.card sys.univ, hP⟩

/-- Bridge, both directions: derivable-with-provenance iff in the
semantic closure. -/
theorem hprov_iff_closure (sys : HornSystem α) (ι : Type) [DecidableEq ι]
    (srcOf : α → Finset ι) (a : α) :
    (∃ P : Finset ι, HProv sys ι srcOf P a) ↔
      a ∈ JurisLean.Seams.SourceNorms.closureAt sys := by
  constructor
  · rintro ⟨P, n, hn⟩
    exact hprovN_mem_closure sys ι srcOf n P a hn
  · intro h
    exact closure_mem_hprov sys ι srcOf h

/-! ## Part 2: Ionescu-Tulcea wiring, discrete fragment -/

section IonescuTulcea

open scoped NNReal

variable {σ : Type} [Fintype σ] [DecidableEq σ]

/-- Stochastic kernel: every row sums to one. -/
def isStochastic (K : σ → σ → ℝ≥0) : Prop :=
  ∀ x : σ, ∑ y, K x y = 1

/-- Chain mass: the transfer product along a list from state x. -/
def chainMass (K : σ → σ → ℝ≥0) (x : σ) : List σ → ℝ≥0
  | [] => 1
  | y :: l => K x y * chainMass K y l

/-- Prefix mass (the discrete form of the 9.3 finite-prefix
recursion). -/
def pathMass (μ0 : σ → ℝ≥0) (K : σ → σ → ℝ≥0) : List σ → ℝ≥0
  | [] => 1
  | x :: l => μ0 x * chainMass K x l

/-- Cylinder compatibility, kernel side: summing over an appended
last state recovers the chain mass. -/
theorem chain_marginal (K : σ → σ → ℝ≥0) (hK : isStochastic K)
    (x : σ) (l : List σ) :
    ∑ y, chainMass K x (l ++ [y]) = chainMass K x l := by
  induction l generalizing x with
  | nil =>
      simp only [List.nil_append, chainMass, mul_one]
      exact hK x
  | cons z t ih =>
      simp only [List.cons_append, chainMass]
      rw [← Finset.mul_sum, ih z]

/-- Cylinder compatibility, trajectory side (the 9.3 reading:
projecting away the last coordinate returns the prefix mass). -/
theorem pathMass_marginal (μ0 : σ → ℝ≥0) (K : σ → σ → ℝ≥0)
    (hK : isStochastic K) (x : σ) (l : List σ) :
    ∑ y, pathMass μ0 K ((x :: l) ++ [y]) = pathMass μ0 K (x :: l) := by
  simp only [List.cons_append, pathMass]
  rw [← Finset.mul_sum, chain_marginal K hK x l]

/-- A normalized initial distribution gives total mass one on the
one-step cylinder (the empty-prefix convention endpoint). -/
theorem pathMass_init_total (μ0 : σ → ℝ≥0) (K : σ → σ → ℝ≥0)
    (hμ : ∑ x, μ0 x = 1) : ∑ y, pathMass μ0 K [y] = 1 := by
  simp only [pathMass, chainMass, mul_one]
  exact hμ

/-- Masses are nonnegative (trivial on ℝ≥0; recorded as a
readout). -/
theorem chainMass_nonneg (K : σ → σ → ℝ≥0) (x : σ)
    (l : List σ) : 0 ≤ chainMass K x l := by
  induction l generalizing x with
  | nil => exact zero_le_one
  | cons y t ih =>
      simp only [chainMass]
      exact mul_nonneg (zero_le _) (ih y)

theorem pathMass_nonneg (μ0 : σ → ℝ≥0) (K : σ → σ → ℝ≥0)
    (l : List σ) : 0 ≤ pathMass μ0 K l := by
  cases l with
  | nil => exact zero_le_one
  | cons x t =>
      simp only [pathMass]
      exact mul_nonneg (zero_le _) (chainMass_nonneg K x t)

end IonescuTulcea

end JurisLean.Seams.UnifiedHornIT
