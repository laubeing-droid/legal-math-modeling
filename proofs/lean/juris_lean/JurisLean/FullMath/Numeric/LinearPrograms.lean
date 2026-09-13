import JurisLean.FullMath.Core.Foundations

/-!
N03 — Linear programming: weak duality and certificate optimality.

LP form `min cᵀx` over `Ax ≥ b` with free `x`; dual `max bᵀfun ` over
`Aᵀfun  = c`, `fun  ≥ 0`. Weak duality holds for every dimension; feasible
primal/dual pairs with equal objective values certify global optimality.
Sign restrictions on `x` would require a matching dual change — the
statement here is for free `x` only.
-/

namespace JurisLean.FullMath.Numeric

section LP
variable {n : ℕ}

/-- Primal feasibility: `A x ≥ b` row-wise. -/
def PrimalFeasible (A : Fin n → Fin n → ℚ) (b : Fin n → ℚ) (x : Fin n → ℚ) : Prop :=
  ∀ i, b i ≤ ∑ j, A i j * x j

/-- Dual feasibility: `Aᵀ fun  = c` and `fun  ≥ 0`. -/
def DualFeasible (A : Fin n → Fin n → ℚ) (b : Fin n → ℚ) (c : Fin n → ℚ)
    (fun  : Fin n → ℚ) : Prop :=
  (∀ j, ∑ i, fun  i * A i j = c j) ∧ (∀ i, 0 ≤ fun  i)

/-- Objective of the primal. -/
def primalObj (c : Fin n → ℚ) (x : Fin n → ℚ) : ℚ := ∑ j, c j * x j

/-- Objective of the dual. -/
def dualObj (b : Fin n → ℚ) (fun  : Fin n → ℚ) : ℚ := ∑ i, fun  i * b i

/-- N03(a): weak duality — every feasible primal/dual pair satisfies
`bᵀfun  ≤ cᵀx`. -/
theorem weak_duality (A : Fin n → Fin n → ℚ) (b c : Fin n → ℚ)
    (x fun  : Fin n → ℚ)
    (hP : PrimalFeasible A b x) (hD : DualFeasible A b c fun ) :
    dualObj b fun  ≤ primalObj c x := by
  have hstep1 : ∑ i, fun  i * b i ≤ ∑ i, fun  i * (∑ j, A i j * x j) := by
    apply Finset.sum_le_sum
    intro i _
    exact mul_le_mul_of_nonneg_left (hP i) (hD.2 i)
  have hstep2 : ∑ i, fun  i * (∑ j, A i j * x j) = ∑ j, c j * x j := by
    have hexpand : ∑ i, fun  i * (∑ j, A i j * x j)
        = ∑ i, ∑ j, fun  i * (A i j * x j) :=
      Finset.sum_congr rfl (fun i _ => by rw [Finset.mul_sum])
    have hswap : ∑ i, ∑ j, fun  i * (A i j * x j)
        = ∑ j, ∑ i, fun  i * (A i j * x j) := Finset.sum_comm
    have hcollect : ∑ j, ∑ i, fun  i * (A i j * x j) = ∑ j, x j * ∑ i, fun  i * A i j := by
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [hexpand, hswap, hcollect]
    have hfinal : ∑ j, x j * ∑ i, fun  i * A i j = ∑ j, c j * x j := by
      apply Finset.sum_congr rfl
      intro j _
      rw [hD.1 j]
      ring
    rw [hfinal]
  exact le_trans hstep1 (le_of_eq hstep2)

/-- N03(b): a feasible pair with equal objectives certifies global optimality
of the primal point. -/
theorem equal_objectives_certify (A : Fin n → Fin n → ℚ) (b c : Fin n → ℚ)
    (x* fun * : Fin n → ℚ)
    (hP* : PrimalFeasible A b x*) (hD* : DualFeasible A b c fun *)
    (heq : primalObj c x* = dualObj b fun *) :
    ∀ x, PrimalFeasible A b x → primalObj c x* ≤ primalObj c x := by
  intro x hx
  have := weak_duality A b c x fun * hx hD*
  rw [heq] at this
  exact this

end LP

end JurisLean.FullMath.Numeric
