import JurisLean.UnifiedV21.Context
import JurisLean.UnifiedV2.FiniteContract

namespace JurisLean.ULM.UnifiedV21

/-- Mathematical interpretation includes infinite real sets. Only the supported
certificate languages may be accepted by an executable checker. -/
inductive RealRep where
  | empty
  | finite (values : Finset ℝ)
  | interval (lo hi : ℝ)
  | union (left right : RealRep)

def RealRep.denote : RealRep → Set ℝ
  | .empty => ∅
  | .finite s => {x | x ∈ s}
  | .interval lo hi => {x | lo ≤ x ∧ x ≤ hi}
  | .union a b => a.denote ∪ b.denote

structure IntervalProblem where
  lo₁ : ℝ
  lo₂ : ℝ
  hi₁ : ℝ
  hi₂ : ℝ

def intervalSpec (p : IntervalProblem) : Set ℝ :=
  {x | p.lo₁ ≤ x ∧ p.lo₂ ≤ x ∧ x ≤ p.hi₁ ∧ x ≤ p.hi₂}

def intervalSolve (p : IntervalProblem) : RealRep :=
  .interval (max p.lo₁ p.lo₂) (min p.hi₁ p.hi₂)

/-- A concrete symbolic solver describes all real solutions, not just endpoints. -/
theorem interval_solver_exact (p : IntervalProblem) :
    (intervalSolve p).denote = intervalSpec p := by
  ext x
  simp only [intervalSolve, RealRep.denote, intervalSpec, Set.mem_setOf_eq,
    max_le_iff, le_min_iff]
  tauto

theorem interval_empty_when_reversed (lo hi : ℝ) (h : hi < lo) :
    (RealRep.interval lo hi).denote = ∅ := by
  ext x
  simp only [RealRep.denote, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
  intro hx
  linarith [hx.1, hx.2]

/-- Endpoints fail to describe a nondegenerate real interval. -/
theorem endpoints_miss_midpoint (lo hi : ℝ) (h : lo < hi) :
    (lo + hi) / 2 ∈ (RealRep.interval lo hi).denote ∧
    (lo + hi) / 2 ≠ lo ∧ (lo + hi) / 2 ≠ hi := by
  constructor
  · constructor <;> linarith
  · constructor <;> linarith

/-- One Farkas-combination row, later lifted by finite sums. -/
theorem scaled_constraint_sound (a b c d k x : ℝ)
    (hk : 0 ≤ k) (ha : k*a = c) (hb : k*b ≤ d) (hx : a*x ≤ b) :
    c*x ≤ d := by
  have hm := mul_le_mul_of_nonneg_left hx hk
  calc
    c*x = (k*a)*x := by rw [ha]
    _ = k*(a*x) := by ring
    _ ≤ k*b := hm
    _ ≤ d := hb

/-- Soundness in both directions yields exact denotation. This is an interface
lemma; each production certificate language needs its own reflection proof. -/
theorem representations_exact_of_mutual_inclusion {S T : Set α}
    (hst : S ⊆ T) (hts : T ⊆ S) : S = T :=
  Set.Subset.antisymm hst hts

end JurisLean.ULM.UnifiedV21
