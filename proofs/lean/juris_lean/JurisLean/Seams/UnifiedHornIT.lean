import Mathlib.Tactic
import JurisLean.Seams.SourceNorms

/-
Unified Horn provenance bridge and Ionescu-Tulcea kernel wiring
(main doc 8.2 leftovers; master plan 3.3 layer-B extension and 9.3).

Part 1 - HORN PROVENANCE BRIDGE (master plan 3.3: "closure provenance
feeds into the grammar, a derived p keeps the source-leaf tree").
`HProvN` is a height-indexed provenance-carrying derivation over the
existing `HornSystem`: the fact case cites the declared source set of
an initial fact; the rule case derives a conclusion with provenance
EXACTLY the union of the premises' provenances (`biUnion f`).  The
height index (children at level n, parent at n+1) is what makes the
inductions go through - membership-style hypotheses carry no IH.
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
  the LAST coordinate of a length-(n+1) prefix mass returns the
  length-n prefix mass);
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

/-- 高度索引的溯源推导：叶层任意 n（初始事实在每层可用）；规则步的
子推导住 n 层、父推导住 n+1 层。结论的来源集恰为诸前提来源集的并。 -/
inductive HProvN (sys : HornSystem α) {ι : Type} (srcOf : α → Finset ι) :
    ℕ → Finset ι → α → Prop
  | fact (n : ℕ) (a : α) (h : a ∈ sys.initialFacts) :
      HProvN sys srcOf n (srcOf a) a
  | rule (n : ℕ) (r : HornRule α) (hr : r ∈ sys.rules)
      (f : α → Finset ι)
      (hch : ∀ p ∈ r.premises, HProvN sys srcOf n (f p) p) :
      HProvN sys srcOf (r.premises.biUnion f) r.conclusion

/-- 无高度包装。 -/
def HProv (sys : HornSystem α) {ι : Type} (srcOf : α → Finset ι)
    (P : Finset ι) (a : α) : Prop :=
  ∃ n, HProvN sys srcOf n P a

/-- 健全性：凡可溯源推导的原子都在语义闭包里。 -/
theorem hprovN_mem_closure {sys : HornSystem α} {ι : Type}
    (srcOf : α → Finset ι) :
    ∀ (n : ℕ) (P : Finset ι) (a : α),
      HProvN sys srcOf n P a → a ∈ JurisLean.Seams.SourceNorms.closureAt sys := by
  intro n
  induction n with
  | zero =>
      intro P a h
      cases h with
      | fact _ a h =>
          exact (JurisLean.Seams.SourceNorms.closure_is_model sys).1 h
  | succ k ih =>
      intro P a h
      cases h with
      | fact _ a h =>
          exact (JurisLean.Seams.SourceNorms.closure_is_model sys).1 h
      | rule _ r hr f hch =>
          have hfp : HornSystem.TH sys
              (JurisLean.Seams.SourceNorms.closureAt sys)
              = JurisLean.Seams.SourceNorms.closureAt sys :=
            HornSystem.horn_result_fixed_point sys
          refine hfp ▸ Finset.mem_union.mpr (Or.inr ?_)
          refine Finset.mem_image.mpr ⟨r, Finset.mem_filter.mpr ⟨hr, ?_⟩, rfl⟩
          intro p hp
          exact ih (f p) p (hch p hp)

/-- 溯源健全性：推导引用的每个来源都属于某个初始事实的声明来源集——
推导不能发明来源。 -/
theorem hprovN_prov_sound {sys : HornSystem α} {ι : Type}
    (srcOf : α → Finset ι) :
    ∀ (n : ℕ) (P : Finset ι) (a : α),
      HProvN sys srcOf n P a →
        ∀ s ∈ P, ∃ b : α, b ∈ sys.initialFacts ∧ s ∈ srcOf b := by
  intro n
  induction n with
  | zero =>
      intro P a h s hs
      cases h with
      | fact _ b hb => exact ⟨b, hb, hs⟩
  | succ k ih =>
      intro P a h s hs
      cases h with
      | fact _ b hb => exact ⟨b, hb, hs⟩
      | rule _ r _ f hch =>
          rcases Finset.mem_biUnion.mp hs with ⟨p, hp, hfp⟩
          exact ih (f p) p (hch p hp) s hfp

/-- 迭代层引理：第 n 层迭代里的原子都有第 n 层溯源推导。 -/
theorem iter_mem_hprovN {sys : HornSystem α} {ι : Type}
    (srcOf : α → Finset ι) :
    ∀ (n : ℕ) (a : α),
        a ∈ FiniteMonotoneSystem.iter (HornSystem.toFiniteMonotoneSystem sys) n →
        ∃ P : Finset ι, HProvN sys srcOf n P a := by
  intro n
  induction n with
  | zero =>
      intro a ha
      simp only [FiniteMonotoneSystem.iter] at ha
      exact absurd ha (by simp)
  | succ k ih =>
      intro a ha
      rw [FiniteMonotoneSystem.iter_succ] at ha
      unfold HornSystem.TH at ha
      rcases Finset.mem_union.mp ha with (ha0 | ha1)
      · exact ⟨srcOf a, HProvN.fact (k + 1) a ha0⟩
      · rcases Finset.mem_image.mp ha1 with ⟨r, hr, rfl⟩
          rcases Finset.mem_filter.mp hr with ⟨hr, hprem⟩
        choose f hf using
          fun (p : α) (hp : p ∈ r.premises) => ih p (hprem hp)
        refine ⟨r.premises.biUnion f, HProvN.rule (k + 1) r hr f ?_⟩
        intro p hp
        exact hf p hp

/-- 完备性：闭包里的原子都有溯源推导（无高度包装）。 -/
theorem closure_mem_hprov {sys : HornSystem α} {ι : Type}
    (srcOf : α → Finset ι) {a : α}
    (h : a ∈ JurisLean.Seams.SourceNorms.closureAt sys) :
    ∃ P : Finset ι, HProv sys srcOf P a :=
  let ⟨P, hP⟩ := iter_mem_hprovN srcOf
    (Finset.card sys.univ) a h
  ⟨P, Finset.card sys.univ, hP⟩

/-- 桥接双侧：可溯源推导 ⟺ 语义闭包成员。 -/
theorem hprov_iff_closure {sys : HornSystem α} {ι : Type}
    (srcOf : α → Finset ι) (a : α) :
    (∃ P : Finset ι, HProv sys srcOf P a) ↔
      a ∈ JurisLean.Seams.SourceNorms.closureAt sys := by
  constructor
  · rintro ⟨P, n, hn⟩
      exact hprovN_mem_closure srcOf n P a hn
  · intro h
      exact closure_mem_hprov srcOf h

/-! ## Part 2: Ionescu-Tulcea wiring, discrete fragment -/

section IonescuTulcea

variable {σ : Type} [Fintype σ] [DecidableEq σ]

/-- 随机核（行和为一）。 -/
def isStochastic (K : σ → σ → ℝ≥0) : Prop :=
  ∀ x : σ, ∑ y, K x y = 1

/-- 链质量：从状态 x 出发沿列表转移的乘积。 -/
def chainMass (K : σ → σ → ℝ≥0) (x : σ) : List σ → ℝ≥0
  | [] => 1
  | y :: l => K x y * chainMass K y l

/-- 前缀测度（§9.3 有限前缀递推的离散形）。 -/
def pathMass (μ0 : σ → ℝ≥0) (K : σ → σ → ℝ≥0) : List σ → ℝ≥0
  | [] => 1
  | x :: l => μ0 x * chainMass K x l

/-- 柱集相容（核侧）：对追加的末坐标求和恢复原链质量。 -/
theorem chain_marginal (K : σ → σ → ℝ≥0) (hK : isStochastic K)
    (x : σ) (l : List σ) :
    ∑ y, chainMass K x (l ++ [y]) = chainMass K x l := by
  induction l generalizing x with
  | nil =>
      simp only [List.nil_append, List.cons_append, chainMass, List.nil_append,
        mul_one]
      rw [← Finset.mul_sum]
      exact congrArg (K x) (hK x) ▸ congrArg (fun v => K x * v) (hK x)
  | cons z t ih =>
      simp only [List.cons_append, chainMass]
      rw [Finset.sum_mul]
      exact congrArg (fun v => K x z * v) (ih z)

/-- 柱集相容（轨迹侧，§9.3 原文读数）：投影掉末坐标恢复前缀测度。 -/
theorem pathMass_marginal (μ0 : σ → ℝ≥0) (K : σ → σ → ℝ≥0)
    (hK : isStochastic K) (x : σ) (l : List σ) :
    ∑ y, pathMass μ0 K ((x :: l) ++ [y]) = pathMass μ0 K (x :: l) := by
  simp only [List.cons_append, pathMass]
  rw [Finset.sum_mul]
  exact congrArg (fun v => μ0 x * v) (chain_marginal K hK x l)

/-- 初始分布归一 ⟹ 一步柱集总质量为 1（空路径约定的退化端）。 -/
theorem pathMass_init_total (μ0 : σ → ℝ≥0) (K : σ → σ → ℝ≥0)
    (hμ : ∑ x, μ0 x = 1) : ∑ y, pathMass μ0 K [y] = 1 := by
  simp only [pathMass, chainMass, mul_one]
  exact hμ

/-- 质量非负（ℝ≥0 载体上平凡，登记为读数）。 -/
theorem pathMass_nonneg (μ0 : σ → ℝ≥0) (K : σ → σ → ℝ≥0)
    (l : List σ) : 0 ≤ pathMass μ0 K l := by
  induction l with
  | nil => exact zero_le 1
  | cons x t ih =>
      simp only [pathMass]
      exact mul_nonneg (zero_le _) ih

end IonescuTulcea

end JurisLean.Seams.UnifiedHornIT
