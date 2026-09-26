import Mathlib

/-!
# Mandate module C — a certificate whose error bound is computed, not supplied

The audit's finding on the approximator mandate (P-118) was precise: in
`BanachCertificate.lean` the structure already carries
`errorWithinTolerance : errorBound ≤ tolerance` as a *field*, so the five
"certificate theorems" project an assumption the caller brought, and
`verifyCertificate` returns `true` unconditionally. Nothing computed a bound.

This module does the minimal honest version of the opposite: for a named
approximation family (geometric contraction by a rational ratio — the shape a
one-layer linear solver reduces to), the *n*-step value is proved equal to a
closed form, the bound is **produced by this module** as that closed form, and
the admission decision is proved equivalent to comparing the computed bound with
a tolerance.

It is deliberately not claimed to be a neural network: it is a trained
approximator only in the sense that the fixed point of `x ↦ q·x` is the target.
Extending it to the weighted-sup-norm operator family is the next step and needs
the `WeightedSupNorm` bridge, which is a CI-verified change.

Status: NOT imported by `JurisLean.lean`, NOT in `AxiomAudit.lean`; needs a CI
module build before it may be cited.
-/

namespace JurisLean.Mandate.DerivedCertificate

/-- The approximation step: contract the current value by the rational ratio. -/
def step (q : ℚ) (x : ℚ) : ℚ := q * x

/-- The *n*-step approximation actually run by the approximator. -/
def approx (q : ℚ) : ℚ → Nat → ℚ
  | x, 0 => x
  | x, k + 1 => step q (approx q x k)

/--
Closed form for the iteration. Everything below rests on this: the quantity is
computed, and this theorem says what it equals.
-/
theorem approx_closed (q x : ℚ) : ∀ n : ℕ, approx q x n = q ^ n * x := by
  intro n
  induction n with
  | zero => rw [pow_zero]; simp [approx]
  | succ k ih =>
      show step q (approx q x k) = q ^ (k + 1) * x
      rw [step, pow_succ, ih]
      ring

/-- The computed bound of an *n*-step run. No caller supplies it. -/
def computedBound (q : ℚ) (x : ℚ) (n : ℕ) : ℚ := q ^ n * x

/-- The iteration error against the fixed point 0 *is* the computed bound. -/
theorem approx_error_eq_computedBound (q x : ℚ) (n : ℕ) :
    approx q x n - 0 = computedBound q x n := by
  simp [computedBound, approx_closed]

/-- A rational ratio in [0,1] stays in [0,1] under exponentiation. -/
theorem pow_damped (q : ℚ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    ∀ n : ℕ, 0 ≤ q ^ n ∧ q ^ n ≤ 1 := by
  intro n
  induction n with
  | zero =>
      constructor
      · simp
      · simp
  | succ k ih =>
      rw [pow_succ]
      constructor
      · nlinarith
      · nlinarith

/--
Damped family: the run never leaves the interval between 0 and its start, so the
computed bound really is an upper bound rather than an optimism.
-/
theorem approx_damped (q x : ℚ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hx : 0 ≤ x) :
    ∀ n : ℕ, 0 ≤ approx q x n ∧ approx q x n ≤ x := by
  intro n
  rw [approx_closed]
  obtain ⟨hp0, hp1⟩ := pow_damped q hq0 hq1 n
  constructor
  · nlinarith
  · nlinarith

/--
A certificate as produced by this module: the bound field is
`computedBound`, and the justification is an identity proved above — not a
premise handed in by whoever constructs the record.
-/
structure DerivedCert where
  q : ℚ
  x : ℚ
  n : ℕ
  bound : ℚ
  boundEq : bound = computedBound q x n

/-- Construction of a certificate: the only way in is through the computed value. -/
def certificate (q : ℚ) (x : ℚ) (n : ℕ) : DerivedCert :=
  { q := q, x := x, n := n, bound := computedBound q x n, boundEq := rfl }

theorem certificate_bound_is_computed (q x : ℚ) (n : ℕ) :
    (certificate q x n).bound = approx q x n :=
  (approx_closed q x n).symm

/--
Admission is decidable, and the decider is proved sound *against the iteration
itself*: `admits = true` exactly when the realised error is within tolerance.
This is the equivalence the field-projection certificates never state.
-/
def admits (q x : ℚ) (n : ℕ) (tolerance : ℚ) : Bool :=
  (certificate q x n).bound ≤ tolerance

theorem admits_iff (q x : ℚ) (n : ℕ) (tolerance : ℚ) :
    admits q x n tolerance = true ↔ approx q x n ≤ tolerance := by
  show (certificate q x n).bound ≤ tolerance ↔ _
  rw [certificate_bound_is_computed]

/-- No certificate admits a negative tolerance: the gate cannot be opened by fiat. -/
theorem not_admits_negative (q x : ℚ) (n : ℕ) (hq0 : 0 ≤ q) (hx : 0 ≤ x) (t : ℚ)
    (ht : t < 0) : admits q x n t = false := by
  show ¬ (certificate q x n).bound ≤ t
  rw [certificate_bound_is_computed, approx_closed]
  intro h
  have h1 : 0 ≤ q ^ n * x := by
    have hp : 0 ≤ q ^ n := by
      induction n with
      | zero => simp [pow_zero]
      | succ k ih => rw [pow_succ]; nlinarith
    nlinarith
  linarith

/-- Zero iterations return the input, so a certificate never hides a no-op run. -/
theorem approx_zero (q x : ℚ) : approx q x 0 = x := rfl

end JurisLean.Mandate.DerivedCertificate
