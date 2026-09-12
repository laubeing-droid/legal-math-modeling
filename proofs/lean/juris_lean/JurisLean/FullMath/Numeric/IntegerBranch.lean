import JurisLean.FullMath.Core.Foundations

/-!
N05 — Integer branch-and-bound certificates.

Branching `x ≤ k ∨ x ≥ k+1` covers the parent integer domain; minimizing
over a superset of integer points cannot beat minimizing over the subset
(relaxation bound); a verified pruning bound certifies incumbent optimality
over incumbent plus all node points; pruning at equal value can discard
alternative optima — recorded as an explicit adversarial fact.
-/

namespace JurisLean.FullMath.Numeric

/-- N05(a): branching `x ≤ k` / `x ≥ k+1` covers the parent integer box. -/
theorem branch_cover (lo k hi : ℤ) (x : ℤ)
    (hx : lo ≤ x ∧ x ≤ hi) :
    (lo ≤ x ∧ x ≤ k) ∨ (k + 1 ≤ x ∧ x ≤ hi) := by
  rcases le_or_lt x k with h1 | h1
  · exact Or.inl ⟨hx.1, h1⟩
  · exact Or.inr ⟨by omega, hx.2⟩

/-- Minima over supersets are at most minima over subsets. -/
theorem min'_subset (S T : Finset ℤ) (hsub : S ⊆ T) (hS : S.Nonempty) (hT : T.Nonempty) :
    T.min' hT ≤ S.min' hS :=
  Finset.min'_le (S.min' hS) (hsub (S.min'_mem hS))

/-- N05(b): relaxation bound — since the integer points of the sub-box are a
subset of the integer points of the super-box, the super-box minimum is a
lower bound for the sub-box minimum. -/
theorem relaxation_lower_bound (lo hi lo' hi' : ℤ)
    (hsub : ∀ x : ℤ, (lo ≤ x ∧ x ≤ hi) → (lo' ≤ x ∧ x ≤ hi'))
    (x₀ : ℤ) (hx₀ : lo ≤ x₀ ∧ x₀ ≤ hi)
    (y₀ : ℤ) (hy₀ : lo' ≤ y₀ ∧ y₀ ≤ hi') :
    (Finset.Icc lo' hi').min' ⟨y₀, Finset.mem_Icc.mpr hy₀⟩ ≤
    (Finset.Icc lo hi).min' ⟨x₀, Finset.mem_Icc.mpr hx₀⟩ := by
  refine min'_subset _ _ ?_ _ _
  intro x hx
  exact Finset.mem_Icc.mpr (hsub x (Finset.mem_Icc.mp hx))

/-- N05(c): pruning certificate — if every node point is sandwiched between
the incumbent value and the node bound, the incumbent is optimal over
incumbent plus all node points. -/
theorem pruning_certificate (obj : ℤ → ℚ) (incumbent : ℤ)
    (nodes : List (Finset ℤ))
    (nodeBound : Finset ℤ → ℚ)
    (hboundvalid : ∀ N ∈ nodes, ∀ v ∈ N,
      obj incumbent ≤ nodeBound N ∧ nodeBound N ≤ obj v) :
    ∀ v ∈ [incumbent] ++ nodes.join, obj incumbent ≤ obj v := by
  intro v hv
  rw [List.mem_append] at hv
  rcases hv with hv | hv
  · rw [List.mem_singleton] at hv
    subst hv
    exact le_refl _
  · rw [List.mem_join] at hv
    obtain ⟨N, hN, hvN⟩ := hv
    exact (hboundvalid N hN v hvN).1.trans (hboundvalid N hN v hvN).2

/-- N05(d) adversarial fact: pruning at equal value can discard alternative
optima — two distinct integer points attain the same global minimum of
`x · (x − 3)`. -/
theorem pruning_equal_value_alternatives :
    ∃ (obj : ℤ → ℚ) (a b : ℤ), a ≠ b ∧ obj a = obj b ∧ ∀ x : ℤ, obj a ≤ obj x := by
  refine ⟨fun x => (x : ℚ) * ((x : ℚ) - 3), 1, 2, by decide, by norm_num, ?_⟩
  intro x
  have hfact : (((x : ℚ)) - 1) * (((x : ℚ)) - 2) ≥ 0 := by
    rcases le_total 2 x with h2 | h2
    · exact mul_nonneg (by exact_mod_cast le_trans (by omega : (1 : ℤ) ≤ 2) h2)
        (by exact_mod_cast h2)
    · rcases le_total x 1 with h1 | h1
      · exact mul_nonneg_of_nonpos_of_nonpos (by exact_mod_cast h1)
          (by exact_mod_cast le_trans h1 (by omega : (1 : ℤ) ≤ 2))
      · omega
  have hrw : ((x : ℚ)) * (((x : ℚ)) - 3) = (((x : ℚ)) - 1) * (((x : ℚ)) - 2) - 2 := by ring
  have hmin : ((1 : ℚ) * ((1 : ℚ) - 3)) = -2 := by norm_num
  have hgoal : (fun x => (x : ℚ) * ((x : ℚ) - 3)) 1 ≤ (x : ℚ) * ((x : ℚ) - 3) := by
    rw [hrw]
    have hone : (fun x => (x : ℚ) * ((x : ℚ) - 3)) 1 = -2 := by norm_num
    rw [hone]
    linarith
  exact hgoal

end JurisLean.FullMath.Numeric
