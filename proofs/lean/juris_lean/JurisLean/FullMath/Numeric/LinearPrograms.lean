import JurisLean.FullMath.Core.Foundations

/-!
N03 — Linear programming: weak duality and certificate optimality.

LP form `min cᵀx` over `Ax ≥ b` with free `x`; dual `max bᵀλ`, `Aᵀλ = c`,
`λ ≥ 0`. Weak duality holds for every dimension; feasible primal/dual pairs
with equal objective values certify global optimality. Sign restrictions on
`x` would require a matching dual change; the statement here is for free `x`.
-/

namespace JurisLean.FullMath.Numeric

section LP
variable {n : ℕ}

/-- Primal feasibility: `A x ≥ b` row-wise. -/
def PrimalFeasible (A : Fin n → Fin n → ℚ) (b : Fin n → ℚ) (x : Fin n → ℚ) : Prop :=
  ∀ i, b i ≤ ∑ j, A i j * x j

/-- Dual feasibility: `Aᵀλ = c` and `λ ≥ 0`. -/
def DualFeasible (A : Fin n → Fin n → ℚ) (b : Fin n → ℚ) (c : Fin n → ℚ)
    (lam : Fin n → ℚ) : Prop :=
  (∀ j, ∑ i, lam i * A i j = c j) ∧ (∀ i, 0 ≤ lam i)

/-- Objective of the primal. -/
def primalObj (c : Fin n → ℚ) (x : Fin n → ℚ) : ℚ := ∑ j, c j * x j

/-- Objective of the dual. -/
def dualObj (b : Fin n → ℚ) (lam : Fin n → ℚ) : ℚ := ∑ i, lam i * b i

/-- N03(a): weak duality — every feasible primal/dual pair satisfies
`bᵀλ ≤ cᵀx`. -/
theorem weak_duality (A : Fin n → Fin n → ℚ) (b c : Fin n → ℚ)
    (x lam : Fin n → ℚ)
    (hP : PrimalFeasible A b x) (hD : DualFeasible A b c lam) :
    dualObj b lam ≤ primalObj c x := by
  have hstep1 : ∑ i, lam i * b i ≤ ∑ i, lam i * (∑ j, A i j * x j) := by
    refine Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hP i) (hD.2 i))
  have hstep2 : ∑ i, lam i * (∑ j, A i j * x j)
      = ∑ j, c j * x j := by
    have hexpand : ∑ i, lam i * (∑ j, A i j * x j)
        = ∑ i, ∑ j, lam i * (A i j * x j) :=
      Finset.sum_congr rfl (fun i _ => by rw [Finset.mul_sum])
    have hswap : ∑ i, ∑ j, lam i * (A i j * x j)
        = ∑ j, ∑ i, lam i * (A i j * x j) := Finset.sum_comm
    have hcollect : ∑ j, ∑ i, lam i * (A i j * x j) = ∑ j, x j * ∑ i, lam i * A i j := by
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      ring
    rw [hexpand, hswap, hcollect]
    have hfinal : ∑ j, x j * ∑ i, lam i * A i j = ∑ j, c j * x j := by
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [hD.1 j]
      ring
    rw [hfinal]
  exact le_trans hstep1 (le_of_eq hstep2)

/-- N03(b): a feasible pair with equal objectives certifies global optimality
of the primal point. -/
theorem equal_objectives_certify (A : Fin n → Fin n → ℚ) (b c : Fin n → ℚ)
    (xstar lam : Fin n → ℚ)
    (hPstar : PrimalFeasible A b xstar) (hDstar : DualFeasible A b c lam)
    (heq : primalObj c xstar = dualObj b lam) :
    ∀ x, PrimalFeasible A b x → primalObj c xstar ≤ primalObj c x := by
  intro x hx
  have := weak_duality A b c x lam hx hDstar
  rw [← heq] at this
  exact this

end LP

end JurisLean.FullMath.Numeric
