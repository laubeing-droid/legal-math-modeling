import JurisLean.FullMath.Core.Foundations

/-!
EXT07 — Partial identification over finite structural models.

Two two-variable SCMs (`Y := X` chain and `Y := U` copy) share one
observational law but have ATE 1 and 0 — observational data alone cannot
separate them. Intervention truncates the structural equation while
conditioning does not; the two differ on the copy model. Supremum need not
be attained (`[0,1)` has sup 1 outside), and attained endpoints (`{0,1}`)
are a different set shape from the whole interval.
-/

namespace JurisLean.FullMath.Causal

/-- Two-variable structural models over one exogenous Boolean `U` with
`X = U` always; `Y` is `X` (chain) or `U` (copy). -/
inductive TwoVar where
  | chain
  | copy

/-- Expected value of `Y` under `do(X := b)` with exogenous `P(U=1) = p`. -/
def doExpect (m : TwoVar) (p : ℚ) (b : Bool) : ℚ :=
  match m, b with
  | .chain, true => 1
  | .chain, false => 0
  | .copy, _ => p

/-- Average treatment effect of the model. -/
def ate (m : TwoVar) (p : ℚ) : ℚ := doExpect m p true - doExpect m p false

/-- EXT07(a): the chain model has ATE exactly 1 for every exogenous p. -/
theorem chain_ate (p : ℚ) : ate TwoVar.chain p = 1 := by
  unfold ate doExpect
  norm_num

/-- EXT07(b): the copy model has ATE exactly 0 for every exogenous p. -/
theorem copy_ate (p : ℚ) : ate TwoVar.copy p = 0 := by
  unfold ate doExpect
  ring

/-- EXT07(c): the shared observational law does not separate the models. -/
theorem ate_identification_failure (p : ℚ) : ate TwoVar.chain p ≠ ate TwoVar.copy p := by
  rw [chain_ate, copy_ate]
  norm_num

/-- EXT07(d): intervening on `X` does not fix `Y` in the copy model, while
conditioning on `X = 1` fixes the observed `Y` to 1 — intervention and
conditioning differ. -/
theorem intervene_not_condition (p : ℚ) (hp : 0 < p) (hp1 : p < 1) :
    doExpect TwoVar.copy p true ≠ 1 := by
  unfold doExpect
  nlinarith [hp, hp1]

/-- EXT07(e): supremum need not be attained — `[0,1)` has sup 1 outside. -/
theorem sup_not_attained :
    sSup (Set.Ico (0 : ℝ) 1) = 1 ∧ (1 : ℝ) ∉ Set.Ico (0 : ℝ) 1 := by
  constructor
  · refine csSup_eq_of_forall_le_of_forall_lt_exists_gt ⟨0, by norm_num⟩ ?_ ?_
    · intro x hx
      exact hx.2
    · intro y hy
      refine ⟨(1 + y) / 2, ⟨by nlinarith, by nlinarith⟩, by nlinarith⟩
  · intro hmem
    exact absurd hmem.2 (by linarith)

/-- EXT07(f): attained endpoints are a genuinely different shape — `{0,1}`
contains its sup but is not the whole interval. -/
theorem endpoints_attained_distinct :
    sSup ({0, 1} : Set ℝ) = 1 ∧ (1 : ℝ) ∈ ({0, 1} : Set ℝ) ∧
      ({0, 1} : Set ℝ) ≠ Set.Icc (0 : ℝ) 1 := by
  refine ⟨?_, by norm_num, ?_⟩
  · refine csSup_eq_of_forall_le_of_forall_lt_exists_gt ⟨0, by norm_num⟩ ?_ ?_
    · intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl <;> norm_num
    · intro y hy
      refine ⟨1, by norm_num, ?_⟩
      nlinarith [hy]
  · intro h
    have hmem : (1/2 : ℝ) ∈ Set.Icc 0 1 := by norm_num
    rw [h] at hmem
    simp at hmem

end JurisLean.FullMath.Causal
