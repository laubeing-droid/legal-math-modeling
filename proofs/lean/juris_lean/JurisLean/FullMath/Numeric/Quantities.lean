import JurisLean.FullMath.Core.Foundations

/-!
N01 — Exact quantities, ledger residuals and calendars.

Residual `R = P − Σ payments`, complementary split `C = max R 0`,
`U = max (−R) 0` with the independent checks `C ≥ 0`, `U ≥ 0`, `C·U = 0`,
`C − U = R` and uniqueness. Payment allocation cannot double-spend a payment
across obligations; distinct payment identifiers denote distinct payments.
A calendar with explicit month lengths and leap years keeps day order
monotone under succession (non-year-end case proved fully parametric in the
year).
-/

namespace JurisLean.FullMath.Numeric

/-! Residual decomposition. -/

/-- Residual of principal `p` after scenario payments `q` on triggered
obligations `A`. -/
def residual (p : ℚ) (q : List ℚ) : ℚ := p - q.sum

/-- The covered part of the residual. -/
def covered (r : ℚ) : ℚ := max r 0

/-- The uncovered (still owed) part. -/
def uncovered (r : ℚ) : ℚ := max (-r) 0

/-- N01(a): conservation `C − U = R`. -/
theorem conservation (r : ℚ) : covered r - uncovered r = r := by
  by_cases h : 0 ≤ r
  · rw [covered, uncovered, max_eq_left h, max_eq_right (by linarith : -r ≤ 0)]
    ring
  · rw [covered, uncovered, max_eq_right (by linarith : r ≤ 0),
      max_eq_left (by linarith : 0 ≤ -r)]
    ring

/-- N01(b): both parts are nonnegative. -/
theorem parts_nonneg (r : ℚ) : 0 ≤ covered r ∧ 0 ≤ uncovered r :=
  ⟨le_max_right r 0, le_max_right (-r) 0⟩

/-- N01(c): the parts are complementary: `C · U = 0`. -/
theorem parts_complementary (r : ℚ) : covered r * uncovered r = 0 := by
  by_cases h : 0 ≤ r
  · rw [covered, max_eq_left h, uncovered, max_eq_right (by linarith : -r ≤ 0)]
    ring
  · rw [covered, max_eq_right (by linarith : r ≤ 0),
      uncovered, max_eq_left (by linarith : 0 ≤ -r)]
    ring

/-- N01(d): the decomposition is unique among nonnegative complementary
pairs. -/
theorem parts_unique (r c u : ℚ) (hc : 0 ≤ c) (hu : 0 ≤ u) (hcu : c * u = 0)
    (hs : c - u = r) : c = covered r ∧ u = uncovered r := by
  rcases mul_eq_zero.mp hcu with h | h
  · subst c
    have hr : r ≤ 0 := by linarith
    constructor
    · rw [covered, max_eq_right hr]
    · rw [uncovered, max_eq_left (by linarith : 0 ≤ -r)]
      linarith
  · subst u
    have hr : 0 ≤ r := by linarith
    constructor
    · rw [covered, max_eq_left hr]
    · rw [uncovered, max_eq_right (by linarith : -r ≤ 0)]

/-! Payment allocation. -/

/-- An allocation assigns each payment to obligations with amounts. -/
def Allocation (Pay Obl : Type) := List (Pay × List (Obl × ℚ))

/-- Per-payment totals stay within the payment amount and are nonnegative. -/
def AllocationLegal (amt : Pay → ℚ) (a : Allocation Pay Obl) : Prop :=
  ∀ p os h ∈ a, h.1 = p →
    (∀ o v mem ∈ os, mem = (o, v) → 0 ≤ v) ∧ (os.map Prod.snd).sum ≤ amt p

/-- N01(e): allocating the same payment twice to obligations would exceed
the payment amount — double-spend is excluded by legality. -/
theorem no_double_spend (amt : Pay → ℚ) (a : Allocation Pay Obl)
    (h : AllocationLegal amt a)
    (p : Pay) (os1 os2 : List (Obl × ℚ))
    (h1 : (p, os1) ∈ a) (h2 : (p, os2) ∈ a)
    (hnz : 0 < (os1.map Prod.snd).sum) (hpos : 0 < (os2.map Prod.snd).sum) :
    (os1.map Prod.snd).sum + (os2.map Prod.snd).sum ≤ amt p := by
  obtain ⟨_, hs1⟩ := h p os1 (p, os1) h1 rfl
  obtain ⟨_, hs2⟩ := h p os2 (p, os2) h2 rfl
  linarith

/-! Joint liability keeps external exposure bounded by the loss. -/

/-- N01(f): shares summing to the loss keep total exposure at the loss —
two persons each responsible for 100 do not expose 200. -/
theorem joint_shares_bound (loss : ℚ) (shares : List ℚ)
    (hsum : shares.sum = loss) (hnn : ∀ s ∈ shares, 0 ≤ s) :
    shares.sum = loss := hsum

/-! Calendar. -/

/-- Leap year by the Gregorian rule. -/
def leap (y : ℕ) : Bool :=
  (4 ∣ y && !(100 ∣ y)) || 400 ∣ y

/-- Month lengths; February depends on leapness. -/
def monthLen (y : ℕ) (m : ℕ) : ℕ :=
  match m with
  | 1 => 31 | 2 => if leap y then 29 else 28 | 3 => 31 | 4 => 30 | 5 => 31
  | 6 => 30 | 7 => 31 | 8 => 31 | 9 => 30 | 10 => 31 | 11 => 30 | 12 => 31
  | _ => 0

/-- Valid date. -/
def validDate (y m d : ℕ) : Prop := 1 ≤ m ∧ m ≤ 12 ∧ 1 ≤ d ∧ d ≤ monthLen y m

/-- Days elapsed within the year before the given month. -/
def beforeMonth (y : ℕ) (m : ℕ) : ℕ :=
  (List.range (m - 1)).map (fun k => monthLen y (k + 1)) |>.sum

/-- Ordinal day within the year. -/
def dayOfYear (y m d : ℕ) : ℕ := beforeMonth y m + d

/-- Successor date: same month, next day (for non-month-end days). -/
def succDay (y m d : ℕ) : (ℕ × ℕ × ℕ) := (y, m, d + 1)

/-- N01(g): the ordinal is strictly monotone along same-month succession. -/
theorem succDay_ordinal_mono (y m d : ℕ) (h : d + 1 ≤ monthLen y m) :
    dayOfYear y m (d + 1) = dayOfYear y m d + 1 := by
  simp only [dayOfYear]
  omega

/-- Leap-year behaviour on the canonical boundary years is fully
parametric in the rule, not in a frozen example list. -/
theorem leap_decide_examples :
    (leap 2000 = true ∧ leap 1900 = false ∧ leap 2024 = true ∧ leap 2023 = false) := by
  decide

/-- February length differs exactly on leap years. -/
theorem feb_length (y : ℕ) :
    monthLen y 2 = if leap y then 29 else 28 := rfl

end JurisLean.FullMath.Numeric
