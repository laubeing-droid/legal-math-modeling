import JurisLean.FullMath.Probability.FiniteBN

/-!
P02 — Posterior conditioning and zero evidence mass.

For any finite rational distribution and decidable evidence: if the evidence
mass `Z` is positive, the renormalized posterior is nonnegative and sums to
one; if `Z = 0` the conditioning result is the incompatible branch — never a
division through a totalized zero. The branches are decided by an explicit
returned type.
-/

namespace JurisLean.FullMath.Probability

section Cond
variable {S : Type} [Fintype S] [DecidableEq S]

/-- Conditioning result: posterior or incompatible. -/
inductive CondResult (S : Type) where
  /-- Positive evidence mass: the normalized posterior. -/
  | posterior (q : S → ℚ)
  /-- Zero evidence mass: the model is incompatible with the evidence. -/
  | incompatible

/-- The evidence mass. -/
def evMass (p : S → ℚ) (e : S → Bool) : ℚ := ∑ s, if e s then p s else 0

/-- Conditioning by explicit evidence-mass decision. -/
def condition (p : S → ℚ) (e : S → Bool) : CondResult S :=
  if 0 < evMass p e then
    .posterior (fun s => if e s then p s / evMass p e else 0)
  else .incompatible

/-- The branches are decided by the mass alone. -/
theorem condition_incompatible_iff (p : S → ℚ) (e : S → Bool) :
    condition p e = .incompatible ↔ ¬ (0 < evMass p e) := by
  unfold condition
  by_cases h : 0 < evMass p e
  · rw [if_pos h]
    exact fun hne => CondResult.noConfusion hne
  · rw [if_neg h]
    exact fun _ => h

/-- The posterior function when the mass is positive (definitional view). -/
def posterior (p : S → ℚ) (e : S → Bool) (hZ : 0 < evMass p e) : S → ℚ :=
  fun s => if e s then p s / evMass p e else 0

/-- P02(a): with positive mass, the posterior is nonnegative. -/
theorem posterior_nonneg (p : S → ℚ) (hp : ∀ s, 0 ≤ p s) (e : S → Bool)
    (hZ : 0 < evMass p e) (s : S) : 0 ≤ posterior p e hZ s := by
  show 0 ≤ (if e s then p s / evMass p e else 0)
  by_cases he : e s
  · rw [if_pos he]
    exact div_nonneg (hp s) (le_of_lt hZ)
  · rw [if_neg he]
    norm_num

/-- P02(b): with positive mass, the posterior sums to one. -/
theorem posterior_normalizes (p : S → ℚ) (hp : ∀ s, 0 ≤ p s) (e : S → Bool)
    (hZ : 0 < evMass p e) : ∑ s, posterior p e hZ s = 1 := by
  have hsplit : ∑ s, (if e s then p s / evMass p e else 0)
      = evMass p e / evMass p e := by
    have h1 : ∑ s, (if e s then p s / evMass p e else 0)
        = (∑ s, if e s then p s else 0) / evMass p e := by
      rw [← Finset.sum_div]
      exact Finset.sum_congr rfl (fun s _ => by
        by_cases he : e s
        · rw [if_pos he, if_pos he]
        · rw [if_neg he, if_neg he, zero_div])
    rw [h1]
  show ∑ s, (if e s then p s / evMass p e else 0) = 1
  rw [hsplit]
  exact div_self (ne_of_gt hZ)

end Cond

end JurisLean.FullMath.Probability
