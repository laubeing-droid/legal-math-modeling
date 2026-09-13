import JurisLean.FullMath.Core.Foundations

/-!
P01 — Finite Bayesian networks normalize.

Variables are layered in reverse-topological order; each node conditions on
the whole pre of earlier variables (a marginal CPT is the special case
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
pre, with nonnegative row-normalized weights. -/
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
  | n + 1, .cons k rest, (pre, b) => joint rest pre * k.cond pre b

/-- P01(a): the joint distribution is nonnegative everywhere. -/
theorem joint_nonneg {n : ℕ} (c : Chain n) (s : State n) : 0 ≤ joint c s := by
  cases c with
  | nil => exact zero_le_one
  | cons k rest =>
    obtain ⟨pre, b⟩ := s
    show (0 : ℚ) ≤ joint rest pre * k.cond pre b
    exact mul_nonneg (joint_nonneg rest pre) (k.nonneg pre b)

/-- P01(b): the joint distribution sums to one over the whole space. -/
theorem joint_normalizes {n : ℕ} (c : Chain n) :
    Finset.sum Finset.univ (fun s : State n => joint c s) = 1 := by
  cases c with
  | nil =>
    show Finset.sum Finset.univ (fun _ : State 0 => (1 : ℚ)) = 1
    simp
  | cons k rest =>
    show Finset.sum Finset.univ
        (fun s : State n × Bool => joint (Chain.cons k rest) s) = 1
    rw [Fintype.sum_prod_type]
    have hstep : ∀ pre : State n,
        Finset.sum Finset.univ (fun b : Bool => joint (Chain.cons k rest) (pre, b))
          = joint rest pre * 1 := by
      intro pre
      have hsplit : Finset.sum Finset.univ (fun b : Bool => joint rest pre * k.cond pre b)
          = joint rest pre * Finset.sum Finset.univ (fun b : Bool => k.cond pre b) := by
        rw [Finset.mul_sum]
      rw [Finset.mul_sum, Finset.sum_congr rfl (fun b _ => rfl)] at hsplit
      rw [hsplit]
      show joint rest pre * Finset.sum Finset.univ (fun b : Bool => k.cond pre b) = joint rest pre * 1
      have hrow : Finset.sum Finset.univ (fun b : Bool => k.cond pre b) = 1 := by
        show k.cond pre false + (k.cond pre true + 0) = 1
        rw [k.row pre]
        norm_num
      rw [hrow]
    rw [Finset.sum_congr rfl (fun pre _ => hstep pre)]
    have hih : Finset.sum Finset.univ (fun pre : State n => joint rest pre * 1)
        = Finset.sum Finset.univ (fun pre : State n => joint rest pre) := by
      exact Finset.sum_congr rfl (fun pre _ => mul_one _)
    rw [hih]
    exact joint_normalizes rest

end BN

end JurisLean.FullMath.Probability
