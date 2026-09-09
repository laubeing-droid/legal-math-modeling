import Mathlib
import JurisLean.BusinessRoot.Semantics

/-!
ROOT03 (part 2) — Scenario-domain enumeration coverage and checker reflection.

Three independent pieces:
1. The conservation-plus-complementarity decomposition accepted by the real
   checker is unique: C/U values are forced to be exactly the clipped maximum
   decomposition of the scenario residual (no field-type check can do this).
2. For the frozen single-atom scenario shape, every Ω member is one of the two
   declared branches and both branches are Ω members — the enumeration domain
   is exact in both directions, never reconstructed from a solver result.
3. Checker reflection: any row satisfying the independent JointSem conditions
   carries exactly the clipped residual decomposition.
-/

namespace JurisLean.BusinessRoot

/-- Uniqueness of the nonnegative complementary decomposition of a residual. -/
theorem decomposition_unique (balance excess residual : ℚ)
    (hb : 0 ≤ balance) (he : 0 ≤ excess)
    (hsub : balance - excess = residual) (hmul : balance * excess = 0) :
    balance = max residual 0 ∧ excess = max (-residual) 0 := by
  rcases mul_eq_zero.mp hmul with h | h
  · subst balance
    have hr : residual ≤ 0 := by linarith
    constructor
    · simp [max_eq_right hr]
    · rw [max_eq_left (by linarith : (0 : ℚ) ≤ -residual)]
      linarith
  · subst excess
    have hr : 0 ≤ residual := by linarith
    constructor
    · rw [max_eq_left hr]
      linarith
    · simp [max_eq_right (by linarith : -residual ≤ (0 : ℚ))]

/-- The clipped identities are consequences, not definitions: C = max R 0 and
U = max (−R) 0 follow from the four independent conditions. This is what makes
the real checker's conservation-plus-complementarity acceptance reflect the
unique semantic decomposition, instead of merely re-running the solver. -/
theorem clipped_from_conditions (principal : ℚ) (keys : List String)
    (payments : List Payment) (vals : World) (o : Witness)
    (hb : 0 ≤ o.principalBalance) (hu : 0 ≤ o.overpaymentResidual)
    (hmul : o.principalBalance * o.overpaymentResidual = 0)
    (hsub : o.principalBalance - o.overpaymentResidual =
      residualOf principal keys payments vals) :
    o.principalBalance = clipC (residualOf principal keys payments vals) ∧
      o.overpaymentResidual = clipU (residualOf principal keys payments vals) := by
  exact decomposition_unique o.principalBalance o.overpaymentResidual
    (residualOf principal keys payments vals) hb hu hsub hmul

/-- For the frozen single-atom shape (facts leave the atom open, constraint
`truthy`), an Ω member must be one of the two declared branches. Shape comes
from the length condition of Ω itself — no solver output is consulted. -/
theorem domain_single_key_cases (a : String) (vals : World)
    (h : DomainOf [a] [(a, Option.none : Option Bool)] Guard.truthy vals) :
    vals = [true] ∨ vals = [false] := by
  have hlen := h.1
  cases vals with
  | nil => simp at hlen
  | cons b rest =>
      cases rest with
      | nil =>
          cases b
          · exact Or.inr rfl
          · exact Or.inl rfl
      | cons => simp at hlen

/-- Both declared branches are members of Ω for the frozen shape: the domain is
nonempty in exactly two scenarios. -/
theorem domain_single_key_members (a : String) :
    DomainOf [a] [(a, Option.none : Option Bool)] Guard.truthy [true] ∧
    DomainOf [a] [(a, Option.none : Option Bool)] Guard.truthy [false] := by
  constructor
  · simp [DomainOf, factsExtend, Guard.denote]
  · simp [DomainOf, factsExtend, Guard.denote]

/-- Two-sided exactness of the finite enumeration domain for the frozen shape:
solver enumeration and the independent scenario domain coincide. -/
theorem domain_pair_exact (a : String) (vals : World) :
    DomainOf [a] [(a, Option.none : Option Bool)] Guard.truthy vals ↔
      vals = [true] ∨ vals = [false] := by
  constructor
  · exact domain_single_key_cases a vals
  · intro hor
    obtain ⟨ht, hf⟩ := domain_single_key_members a
    rcases hor with h | h
    · rw [h]; exact ht
    · rw [h]; exact hf

/-- The distinctness of the two branches is structural, so a two-row table over
them cannot silently collapse to one row (no world deletion). -/
theorem branches_distinct : ¬ ([true] : World) = ([false] : World) := by
  intro h
  simp at h

end JurisLean.BusinessRoot
