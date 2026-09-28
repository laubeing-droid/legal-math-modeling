/-
Mandate module (R-07, family conclusion): the ReLU instantiation of the Leshno
(1993) universal-approximation line.

What this module is: it defines the rectified linear unit `relu : ℝ → ℝ` and
instantiates the backported Leshno carrier
`JurisLean.External.NeuralNetworkProofs.UniversalApproximation.Leshno`
(davorrunje/neural-network-proofs @ f909425, cross-pin backport from the
upstream's mathlib v4.32.0-rc1 to this repository's v4.30.0; first compile
pending) at that activation. The chain is the owner's directive, instantiate
FROM the carrier rather than rebuild: ReLU is continuous, hence in the Leshno
class `M` by the carrier's `ClassM.of_continuous`; ReLU is not
almost-everywhere polynomial, via the carrier's own bridge
`isPolynomialFun_of_continuous_of_aePolynomial` plus elementary polynomial
facts; `leshno_dense` / `leshno_dense_iff` then give the family conclusion:
finite sums of ReLU ridge units `x ↦ relu (⟪w, x⟫ + b)` approximate every
continuous function on every compact subset of every ℝⁿ in sup norm.

Literature: Leshno, Lin, Pinkus, Schocken, Neural Networks 6 (1993) 861-867.

Status: no build attestation claimed; booked in PENDING_CI_MODULES
(scripts/ci/check_import_reachability.py) pending this file's first CI build.
Lean is never run locally (AGENTS.md), so everything below is provisional until
that build. Every mathlib name used was verified by text search against the
pinned mathlib v4.30.0 checkout (proofs/lean/juris_lean/.lake/packages/mathlib):
`max_le_max` (Mathlib/Order/MinMax.lean), `Continuous.max`
(Mathlib/Topology/Order/OrderClosed.lean), `Polynomial.zero_of_eval_zero` and
`Polynomial.funext` (Mathlib/Algebra/Polynomial/Roots.lean),
`Polynomial.eval_mul` / `eval_sub` / `eval_X` / `eval_zero`
(Mathlib/Algebra/Polynomial/Eval/Defs.lean), `mul_eq_zero`
(Mathlib/Algebra/GroupWithZero/Defs.lean), `sub_eq_zero` (used by Roots.lean
itself), and the `max_eq_left` / `max_eq_right` / `le_max_right` sign-split
lemmas that Mandate/ReLUApprox.lean already elaborated green against this same
pin (CI run 36344882459).
-/
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Order.MinMax
import Mathlib.Order.Monotone.Basic
import Mathlib.Tactic
import Mathlib.Topology.Order.OrderClosed
import JurisLean.External.NeuralNetworkProofs.UniversalApproximation.Leshno

/-! # Mandate R-07: the Leshno line instantiated at ReLU

`relu_dense` is `UniversalApproximation.Leshno.leshno_dense` applied to
`relu_classM` and `relu_not_isAEPolynomial`; `relu_dense_iff` is the carrier's
headline `leshno_dense_iff` at `relu_classM`. Nothing here re-proves
approximation content: the only self-built steps are the elementary facts about
`max x 0` (half-line identities, monotone, non-constant, continuous) and the
refutation of a.e.-polynomiality sketched above `relu_not_isAEPolynomial`.
-/

namespace JurisLean.Mandate.ReLUFamily

open UniversalApproximation.Leshno

/-- The rectified linear unit on `ℝ`, as `max x 0`.

This repository's mathlib pin (v4.30.0) ships no `relu`, and nothing else in
this package exports one at this type: `Mandate/ReLUApprox.lean` carries its own
`relu : ℚ → ℚ` for a two-layer stability witness over the rationals, a
different type and a different claim, so there is nothing to reuse and no name
collision. The form `max x 0` (not `if x ≤ 0 then 0 else x`) is deliberate:
continuity is then `Continuous.max`, monotonicity is `max_le_max`, and the two
half-line identities are `max_eq_left` / `max_eq_right` -- the exact lemmas
ReLUApprox already used green against this pin. Every later proof is those
rewrites plus ordered-field reasoning. -/
def relu (x : ℝ) : ℝ := max x 0

/-- On the non-negative half-line the unit is the identity. -/
theorem relu_of_nonneg {x : ℝ} (hx : 0 ≤ x) : relu x = x :=
  max_eq_left hx

/-- On the non-positive half-line the unit clamps to zero. -/
theorem relu_of_nonpos {x : ℝ} (hx : x ≤ 0) : relu x = 0 :=
  max_eq_right hx

/-- The unit is non-negative. -/
theorem relu_nonneg (x : ℝ) : 0 ≤ relu x :=
  le_max_right x 0

/-- ReLU is monotone. (`ClassM` does not need this -- continuity is what the
carrier's `ClassM.of_continuous` consumes below -- but the mandate item asks
for it, and with the `max x 0` form it is one `max_le_max`.) -/
theorem monotone_relu : Monotone relu := by
  intro a b hab
  show max a 0 ≤ max b 0
  exact max_le_max hab (le_refl 0)

/-- Two point values, computed rather than assumed, so non-constancy is a
checked fact. -/
theorem relu_one : relu 1 = 1 :=
  relu_of_nonneg (by norm_num)

/-- The clamped corner. -/
theorem relu_neg_one : relu (-1) = 0 :=
  relu_of_nonpos (by norm_num)

/-- ReLU is not a constant function: it separates `1` from `-1`. -/
theorem relu_not_constant : relu 1 ≠ relu (-1) := by
  rw [relu_one, relu_neg_one]
  exact one_ne_zero

/-- ReLU is continuous: the pointwise `max` of the identity and the zero
constant. -/
theorem continuous_relu : Continuous relu :=
  (continuous_id (α := ℝ)).max (continuous_const (c := (0 : ℝ)))

/-- ReLU lies in the Leshno activation class `M`: it is continuous, and
`ClassM.of_continuous` is the whole argument -- local boundedness and the null
discontinuity closure are the carrier's proof, not repeated here. -/
theorem relu_classM : ClassM relu :=
  ClassM.of_continuous continuous_relu

/-! ### ReLU is not almost-everywhere polynomial

`IsAEPolynomial σ` says `σ` agrees Lebesgue-a.e. with `p.eval` for some `p`.
The refutation goes through the carrier's own bridge
`isPolynomialFun_of_continuous_of_aePolynomial` (Leshno/ClassM.lean): a
continuous a.e. polynomial is an everywhere polynomial. So an a.e. witness for
`relu` yields `q` with `relu = fun t => q.eval t` EVERYWHERE, hence by the two
half-line identities `q.eval t = t` for all `t ≥ 0` and `q.eval t = 0` for all
`t ≤ 0`.

From there no measure theory and no root-counting is needed: the product
`q * (X - q)` evaluates to `0` at EVERY real `t` (each `t` lies on one of the
half-lines and there the corresponding factor vanishes), so it is the zero
polynomial (`Polynomial.zero_of_eval_zero`); `ℝ[X]` has no zero divisors
(`mul_eq_zero`), so `q = 0` or `q = X`; the first contradicts `q.eval 1 = 1`,
the second `q.eval (-1) = 0` since `(X).eval (-1) = -1`. -/
theorem relu_not_isAEPolynomial : ¬ IsAEPolynomial relu := by
  intro hp
  obtain ⟨p, hp⟩ := hp
  obtain ⟨q, hq⟩ :=
    isPolynomialFun_of_continuous_of_aePolynomial continuous_relu ⟨p, hp⟩
  -- `relu = fun t => q.eval t` everywhere; read it off both half-lines.
  have hpos : ∀ t : ℝ, 0 ≤ t → q.eval t = t := fun t ht =>
    (congrFun hq t).symm.trans (relu_of_nonneg ht)
  have hneg : ∀ t : ℝ, t ≤ 0 → q.eval t = 0 := fun t ht =>
    (congrFun hq t).symm.trans (relu_of_nonpos ht)
  -- The product kills both half-lines at once, so it is the zero polynomial.
  have hzero : q * (Polynomial.X - q) = 0 :=
    Polynomial.zero_of_eval_zero (q * (Polynomial.X - q)) fun t => by
      rw [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X]
      rcases le_total 0 t with ht | ht
      · rw [hpos t ht]; ring
      · rw [hneg t ht]; ring
  rcases mul_eq_zero.mp hzero with h | h
  · -- `q = 0` is refuted at `t = 1`.
    have h1 : q.eval 1 = 1 := hpos 1 (by norm_num)
    rw [h, Polynomial.eval_zero] at h1
    norm_num at h1
  · -- `X - q = 0`, i.e. `q = X`, is refuted at `t = -1`.
    have h2 : q.eval (-1) = 0 := hneg (-1) (by norm_num)
    rw [(sub_eq_zero.mp h).symm, Polynomial.eval_X] at h2
    norm_num at h2

/-! ### The family conclusion -/

/-- **The ReLU family conclusion: Leshno (1993) instantiated at ReLU.** Since
ReLU is in class `M` (`relu_classM`) and not almost-everywhere polynomial
(`relu_not_isAEPolynomial`), the carrier's `leshno_dense` gives: on every
compact `K ⊆ ℝⁿ`, every continuous `f : K → ℝ` is approximable in sup norm by
the single-hidden-layer ReLU family -- finite sums of ridge units
`x ↦ relu (⟪w, x⟫ + b)` spanning `genSpan relu K`. All approximation content
is the carrier's theorem; this module supplies only the instantiation. -/
theorem relu_dense : DenselyApproximates relu :=
  leshno_dense relu_classM relu_not_isAEPolynomial

/-- The carrier's headline equivalence at `relu`: `leshno_dense_iff` applied to
`relu_classM`; `relu_not_isAEPolynomial` supplies the right-hand side. -/
theorem relu_dense_iff : DenselyApproximates relu ↔ ¬ IsAEPolynomial relu :=
  leshno_dense_iff relu_classM

/-- `relu_dense` with the carrier's binders visible: for every compact
`K ⊆ ℝⁿ`, every continuous `f` on `K`, and every `ε > 0`, some `g` in the ReLU
ridge span approximates `f` within `ε` at every point of `K`. This adds no
mathematics; it is `relu_dense` applied. -/
theorem relu_approx {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsCompact K)
    (f : C(↥K, ℝ)) {ε : ℝ} (hε : 0 < ε) :
    ∃ g ∈ genSpan relu K, ∀ x, |f x - g x| < ε :=
  relu_dense K hK f hε

end JurisLean.Mandate.ReLUFamily
