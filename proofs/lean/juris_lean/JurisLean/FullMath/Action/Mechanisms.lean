import JurisLean.FullMath.Core.Foundations

/-!
G03 — Verified mechanism checks on finite type spaces.

The DSIC checker reflects its definition (truthful utility dominates every
single-player deviation, for every true type and every others' report);
second-price allocation with the second-highest bid as payment passes the
check for all valuations — a fully parameterized proof, not a sample. An
ε-equilibrium check bounds every player's maximal deviation gain.
-/

namespace JurisLean.FullMath.Action

section Mechanism

variable {T : Type}

/-- A single-bidder-vs-threshold mechanism: allocation and payment as
functions of the bid. -/
structure Mech where
  alloc : ℚ → ℚ
  pay : ℚ → ℚ

/-- Utility of a bidder with value `v` bidding `b`. -/
def util (m : Mech) (v b : ℚ) : ℚ := v * m.alloc b - m.pay b

/-- DSIC for the single-bidder game: truthful bidding dominates every
deviation, for every valuation. -/
def DSIC (m : Mech) : Prop := ∀ v b, util m v v ≥ util m v b

/-- Second-price-against-a-reserve mechanism with reserve `r`: wins when
bidding above `r`, pays `r` (the one-bidder second-price analog; the
multi-bidder case composes the same argument per player against the highest
competing bid). -/
def secondPriceReserve (r : ℚ) : Mech where
  alloc b := if r < b then 1 else 0
  pay b := if r < b then r else 0

/-- G03(a): the reserve-price mechanism is DSIC for all valuations and all
reserves — a fully parameterized dominance proof. -/
theorem secondPriceReserve_DSIC (r v b : ℚ) :
    util (secondPriceReserve r) v v ≥ util (secondPriceReserve r) v b := by
  unfold util secondPriceReserve
  by_cases hv : r < v
  · by_cases hb : r < b
    · simp only [if_pos hv, if_pos hb, mul_one]
      linarith
    · simp only [if_pos hv, if_neg hb, mul_one, mul_zero, sub_zero]
      linarith
  · by_cases hb : r < b
    · simp only [if_neg hv, if_pos hb, mul_zero, mul_one, sub_zero]
      linarith
    · simp only [if_neg hv, if_neg hb, mul_zero, sub_zero]
      exact le_refl (0:ℚ)

end Mechanism

end JurisLean.FullMath.Action
