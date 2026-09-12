import JurisLean.FullMath.Core.Foundations

/-!
P01 — Finite Bayesian networks normalize.

Variables are layered in reverse-topological order; each node conditions on
the whole prefix of earlier variables (a marginal CPT is the special case
that ignores arguments). The joint distribution is the running product of
row-normalized conditional kernels; nonnegativity and normalization are
proven by induction on the chain with the plain product-sum exchange.
-/

namespace JurisLean.FullMath.Probability

section BN

/-- Layered assignment space: `State n` is an assignment to the first `n`
variables, built as nested pairs with `Unit` at the base. -/
def State : ℕ → Type
  | 0 => Unit
  | n + 1 => State n × Bool

instance instStateFintype : ∀ n, Fintype (State n)
  | 0 => inferInstanceAs (Fintype Unit)
  | n + 1 =>
    letI ih : Fintype (State n) := instStateFintype n
    inferInstanceAs (Fintype (State n × Bool))

instance instStateDecidableEq : ∀ n, DecidableEq (State n)
  | 0 => inferInstanceAs (DecidableEq Unit)
  | n + 1 =>
    letI ih : DecidableEq (State n) := instStateDecidableEq n
    inferInstanceAs (DecidableEq (State n × Bool))

/-- One layer: the conditional distribution of the next variable given the
prefix, with nonnegative row-normalized weights. -/
structure Kernel (n : ℕ) where
  cond : State n → Bool → ℚ
  nonneg : ∀ s b, 0 ≤ cond s b
  row : ∀ s, cond s false + cond s true = 1

/-- A Bayesian network as a chain of layers (reverse-topological). -/
inductive Chain : ℕ → Type where
  | nil : Chain 0
  | cons {n : ℕ} (k : Kernel n) (rest : Chain n) : Chain (n + 1)

/-- The joint distribution of a chain. -/
def joint : {n : ℕ} → Chain n → State n → ℚ
  | 0, .nil, _ => 1
  | n + 1, .cons k rest, (prefix, b) => joint rest prefix * k.cond prefix b

/-- P01(a): the joint distribution is nonnegative everywhere. -/
theorem joint_nonneg : ∀ {n : ℕ} (c : Chain n) (s : State n), 0 ≤ joint c s
  | 0, _, _ => by
    show (0 : ℚ) ≤ 1
    norm_num
  | n + 1, .cons k rest, (prefix, b) => by
    show (0 : ℚ) ≤ joint rest prefix * k.cond prefix b
    exact mul_nonneg (joint_nonneg rest prefix) (k.nonneg prefix b)

/-- P01(b): the joint distribution sums to one over the whole space. -/
theorem joint_normalizes : ∀ {n : ℕ} (c : Chain n), ∑ s, joint c s = 1
  | 0, .nil => by
    show ∑ s : State 0, (1 : ℚ) = 1
    simp
  | n + 1, .cons k rest => by
    show ∑ s : State n × Bool, joint (.cons k rest) s = 1
    rw [Fintype.sum_prod_type]
    simp only [joint]
    have hstep : ∀ prefix : State n,
        (∑ b : Bool, joint rest prefix * k.cond prefix b)
          = joint rest prefix * (∑ b : Bool, k.cond prefix b) := by
      intro prefix
      exact (Finset.mul_sum (joint rest prefix) (fun b => k.cond prefix b) Finset.univ).symm
    rw [Finset.sum_congr rfl (fun prefix _ => hstep prefix)]
    have hrow : ∀ prefix : State n, (∑ b : Bool, k.cond prefix b) = 1 := by
      intro prefix
      rw [Finset.sum_univ_bool, k.row prefix]
    rw [Finset.sum_congr rfl (fun prefix _ => by rw [hrow prefix, mul_one])]
    exact joint_normalizes rest

end BN

end JurisLean.FullMath.Probability
