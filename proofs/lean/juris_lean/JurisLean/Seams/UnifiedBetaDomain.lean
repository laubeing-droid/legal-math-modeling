import Mathlib.Tactic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import JurisLean.Seams.UnifiedBeta
import JurisLean.Seams.UnifiedNeedlesS3a

/-
Unified Beta parameter domain, restoring the original contract §7.4
(docs/spec/20261007-统一法律数学模型_全量施工方案.md:455-476) that W1-4 had
narrowed to integer shapes (review Codex R1 item 5).  The full promised
domain — integer / half-integer / general positive rational + finite
mixture — is present in ONE module; no parameter class is dropped.

一、Integer Bernstein general formula (§7.4:455-458).
   For α,β ≥ 1, m = α+β−1, F(x) = Σ_{j=α}^{m} C(m,j) x^j (1−x)^{m−j}:
   * `bernCdf_deriv`  — the telescoping term-by-term derivative gives the
     Beta density shape  F' = m·C(m−1,α−1)·x^{α−1}(1−x)^{β−1};
   * `bernCdf_eq_integral` — F(0)=0 so F coincides with the integral CDF;
   * `bernCdf_eq_normed` — with the S3a closed form B(α,β) = betaTwoConst
     the normalization F = ∫₀ˣg / B(α,β) holds;
   * `bernCdf_strictMonoOn` — strictly increasing on (0,1);
   * endpoints 0/1, and `bernCdf_rat_cast`/`bernCdf_rat_comparable` — at
     rational x the CDF value is the cast of a ℚ closed form, so all
     comparisons are exact rational comparisons.

二、Half-integer path (§7.4:460-462).
   The four bases I(1,1)=x, I(1/2,1)=√x, I(1,1/2)=1−√(1−x),
   I(1/2,1/2)=2·arcsin√x/π are each proven to be genuine antiderivatives
   of their density shapes (`halfCdf11..22_deriv`), with the normalizers
   B(1/2,1)=2, B(1,1/2)=2, B(1/2,1/2)=π computed by exact FTC
   (`halfConst12/21/22`).  The recursion that adds one to a and to b is
   done FOR REAL in its algebraic (integration-by-parts-free) form:
   * `recursion_sum`  — J(a+1,b) + J(a,b+1) = J(a,b), fully general;
   * `recursion_ibp_nat` / `recursion_ibp_half` — a·J(a+1,b) − b·J(a,b+1)
     = x^a(1−x)^b at natural exponents and on the half-integer grid
     (t^n·√t mechanics, valid for every n m : ℕ);
   * `halfColInt` — the closed form of the (√x)-column.
   SQUARING comparisons isolate the roots (`sqrt_le_sqrt_iff`-style
   elementary facts used inline); the x>1/2 symmetry is proven
   (`halfCdf22_symm`).  OPEN, declared as explicit named hypotheses
   (NOT axioms): rational enclosures of π with Machin-quality width
   (`PiRatEnclosureInput` — the trivial enclosure 3<π<4 IS proven,
   `pi_rat_enclosure_trivial`), and asin-series tail enclosures for x ≤ 1/2
   (`AsinRatEnclosureInput`, consumed via the symmetry reduction
   `halfCdf22_enclosure_from_half`).  Every division's denominator is
   enclosed positively wherever a division is performed.

三、General positive-rational integral enclosure (§7.4:464-474).
   g(t)=t^{a−1}(1−t)^{b−1}, η=2^{−k}.  Left tail ≤ M_b·η^a/a
   (`leftTail_aux` + the two M_b cases), right tail ≤ M_a·η^b/b
   (`rightTail_aux`); the contract's a=1,b=1/2,η=1/4 counterexample —
   true left tail 2−√3 > 1/4 (⟺ 48<49), so M_b=1 is a FALSE bound and
   the correct constant is 1/(2√3) — is an explicit theorem
   (`leftTailFlatBoundCounterexample`).  Interior |g'| bound
   L = |a−1|M(a−2)M(b−1)+|b−1|M(a−1)M(b−2) (`gDerivBound`); left/mid
   rectangle cell and partition errors (`rectCellError`,
   `rectChainError`, equal-grid specialization `rectGridError`).
   Denominator positive witness: `betaB_lower`/`betaB_pos` with
   m(r)=min((1/4)^r,(3/4)^r) giving B ≥ m(a−1)m(b−1)/2 > 0.
   Deterministic precision allocation, by the contract numbers:
   `exists_tail_budget` (increase k until the certified tail bounds sum
   ≤ ρ/4 — exponential decay, finite termination), `exists_grid_N`
   (N ≥ max(1, 4L̄ℓ²/ρ) at FIXED η — never synchronously with k, since L
   may diverge as η ↓ 0), `quotientWidth` (N_u/B_l − N_l/B_u ≤ 2ρ/β),
   `cdfWidthFromRho` (ρ ≤ εβ/4 ⟹ width ≤ ε).  Enclosures of the rational
   powers at positive rational endpoints (algebraic isolations) enter as
   the explicit hypothesis bundle `RpowRatEnclosureInput` plus the value
   bound L̄ — declared in the header, kept out of the proven part.

四、Finite mixture (§7.4:475-476).
   `mixtureCdf` with weights nonnegative summing to 1: continuity,
   monotonicity, endpoints, strict monotonicity given one positive-weight
   component strictly increasing (`mixture_*`); for 0<q<1 the quantile v
   with F(v)=q exists and is unique (`mixture_quantile_unique`) — the
   mixture quantile, never an average of component quantiles; the last
   point is enforced by a concrete counterexample
   `component_quantile_average_counterexample` (1/2·Beta(1,1)+
   1/2·Beta(2,1) at q=1/2: true quantile (√5−1)/2, component average
   (1+√2)/4).  Integer-shaped components are proven mixable
   (`bernCdf_mixable`), handing the continuous strictly-increasing
   Beta/mixture domain to the W1-5 double-point refinement layer via
   `cdfEnc`/`cdfEnc_width`/`cdfEnc_real`.

Scope, honestly: the three parameter segments and the four obligations
are all present over their full domains.  What is deliberately left as
explicit named hypotheses (declared above, consumed by stated theorems,
never axioms): Machin-quality π enclosures and asin-series tail bounds
(execution-layer rational enclosures of transcendentals), and rational
enclosures of the rational powers / of L (algebraic isolations at
positive rational endpoints).  The mixture theorems take per-component
continuity/monotonicity/endpoints as hypotheses and prove that any such
mixture with a strictly increasing positive-weight component has a
unique quantile; Beta instances of those hypotheses are provided for the
integer segment.  The general-real-parameter CDF is treated through the
unnormalized numerator N(x)=∫₀ˣg together with the proven denominator
bound — this is exactly the contract's enclosure scheme.
-/

namespace JurisLean.Seams.UnifiedBetaDomain

/-! ## 〇、通用小工具（自含，不依赖版本敏感引理名） -/

/-- 正分母倒数序：0 < A、0 < B 且 B ≤ A 时 1/A ≤ 1/B。 -/
theorem one_div_le_one_div' {A B : ℝ} (hA : 0 < A) (hB : 0 < B) (h : B ≤ A) :
    1 / A ≤ 1 / B := by
  by_contra hcon
  push_neg at hcon
  have h2 : (1 / B) * B < (1 / A) * B := mul_lt_mul_of_pos_right hcon hB
  have h3 : (1 / A) * B ≤ (1 / A) * A :=
    mul_le_mul_of_nonneg_left h (one_div_pos.mpr hA).le
  have h4 : (1 / B) * B = 1 := by field_simp
  have h5 : (1 / A) * A = 1 := by field_simp
  rw [h4] at h2
  rw [h5] at h3
  linarith

/-- (1/2)^k ≤ 1（正底数不超过 1 的幂，自含归纳）。 -/
theorem half_pow_le_one (k : ℕ) : (1 / 2 : ℝ) ^ k ≤ 1 := by
  induction k with
  | zero => norm_num
  | succ n ih =>
      calc (1 / 2 : ℝ) ^ (n + 1) = (1 / 2) ^ n * (1 / 2) := by rw [pow_succ]
        _ ≤ 1 * (1 / 2) := by
            exact mul_le_mul_of_nonneg_right ih (by norm_num)
        _ ≤ 1 := by norm_num

/-- x^(-1/2) = 1/√x（正/非负底数）。 -/
theorem rpow_neg_half_eq_inv_sqrt {x : ℝ} (hx : 0 ≤ x) :
    x ^ (-(1 / 2 : ℝ)) = 1 / Real.sqrt x := by
  rw [Real.rpow_neg hx, Real.sqrt_eq_rpow, inv_eq_one_div]

/-! ## 一、整数 Bernstein 通式（合同 §7.4 第一段） -/

/-- **系数恒等式（左半）**：1 ≤ j ≤ m 时 j·C(m,j) = m·C(m−1,j−1)。 -/
theorem choose_mul_left (m j : ℕ) (hj : 1 ≤ j) (hjm : j ≤ m) :
    j * Nat.choose m j = m * Nat.choose (m - 1) (j - 1) := by
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  have hK : 0 < Nat.factorial i * Nat.factorial (m - 1 - i) :=
    mul_pos (Nat.factorial_pos i) (Nat.factorial_pos _)
  have h1 := Nat.choose_mul_factorial_mul_factorial (n := m) (k := i + 1)
    (show i + 1 ≤ m by omega)
  have h2 := Nat.choose_mul_factorial_mul_factorial (n := m - 1) (k := i)
    (show i ≤ m - 1 by omega)
  rw [show m - (i + 1) = m - 1 - i from by omega] at h1
  have hfs : Nat.factorial (i + 1) = (i + 1) * Nat.factorial i := Nat.factorial_succ i
  have hfm : Nat.factorial m = m * Nat.factorial (m - 1) := by
    have h := Nat.factorial_succ (m - 1)
    rwa [show m - 1 + 1 = m from by omega] at h
  refine Nat.eq_of_mul_eq_mul_right hK ?_
  calc (i + 1) * Nat.choose m (i + 1) * (Nat.factorial i * Nat.factorial (m - 1 - i))
      = Nat.choose m (i + 1) * ((i + 1) * Nat.factorial i * Nat.factorial (m - 1 - i)) := by
        ring
    _ = Nat.choose m (i + 1) * (Nat.factorial (i + 1) * Nat.factorial (m - 1 - i)) := by
        rw [hfs]
    _ = Nat.factorial m := by rw [← Nat.mul_assoc]; exact h1
    _ = m * Nat.factorial (m - 1) := hfm
    _ = m * (Nat.choose (m - 1) i * Nat.factorial i * Nat.factorial (m - 1 - i)) := by
        rw [← h2]
    _ = m * Nat.choose (m - 1) i * (Nat.factorial i * Nat.factorial (m - 1 - i)) := by
        ring

/-- **系数恒等式（右半）**：j < m 时 (m−j)·C(m,j) = m·C(m−1,j)。 -/
theorem choose_mul_right (m j : ℕ) (hjm : j < m) :
    (m - j) * Nat.choose m j = m * Nat.choose (m - 1) j := by
  have hK : 0 < Nat.factorial j * Nat.factorial (m - 1 - j) :=
    mul_pos (Nat.factorial_pos j) (Nat.factorial_pos _)
  have h1 := Nat.choose_mul_factorial_mul_factorial (n := m) (k := j)
    (show j ≤ m by omega)
  have h2 := Nat.choose_mul_factorial_mul_factorial (n := m - 1) (k := j)
    (show j ≤ m - 1 by omega)
  have hfs : Nat.factorial (m - j) = (m - j) * Nat.factorial (m - 1 - j) := by
    have h := Nat.factorial_succ (m - 1 - j)
    rwa [show m - 1 - j + 1 = m - j from by omega] at h
  have hfm : Nat.factorial m = m * Nat.factorial (m - 1) := by
    have h := Nat.factorial_succ (m - 1)
    rwa [show m - 1 + 1 = m from by omega] at h
  refine Nat.eq_of_mul_eq_mul_right hK ?_
  calc (m - j) * Nat.choose m j * (Nat.factorial j * Nat.factorial (m - 1 - j))
      = Nat.choose m j * (Nat.factorial j * (Nat.factorial (m - j))) := by
        rw [hfs]; ring
    _ = Nat.factorial m := by rw [← Nat.mul_assoc]; exact h1
    _ = m * Nat.factorial (m - 1) := hfm
    _ = m * (Nat.choose (m - 1) j * Nat.factorial j * Nat.factorial (m - 1 - j)) := by
        rw [← h2]
    _ = m * Nat.choose (m - 1) j * (Nat.factorial j * Nat.factorial (m - 1 - j)) := by
        ring

/-- 整数形状 (α,β)（α,β ≥ 1）的 Bernstein 部分和 CDF：
    F(x) = Σ_{j=α}^{α+β−1} C(α+β−1, j)·xʲ·(1−x)^{α+β−1−j}（合同 §7.4 第一段，m = α+β−1）。 -/
def bernCdf (α β : ℕ) (x : ℝ) : ℝ :=
  ∑ j ∈ Finset.Ico α (α + β),
    ((Nat.choose (α + β - 1) j : ℕ) : ℝ) * x ^ j * (1 - x) ^ (α + β - 1 - j)

/-- bernCdf 连续（有限和，逐项连续）。 -/
theorem bernCdf_continuous (α β : ℕ) : Continuous (bernCdf α β) := by
  unfold bernCdf
  exact continuous_finsetSum _ (fun j _ =>
    (continuous_const.mul (continuous_pow j)).mul
      ((continuous_pow (α + β - 1 - j)).comp (continuous_const.sub continuous_id)))

/-- 端点：F(0) = 0（故与积分 CDF 同源）。 -/
theorem bernCdf_zero (α β : ℕ) (hα : 1 ≤ α) : bernCdf α β 0 = 0 := by
  unfold bernCdf
  refine Finset.sum_eq_zero (fun j hj => ?_)
  have hj1 : 1 ≤ j := by have := Finset.mem_Ico.mp hj; omega
  rw [zero_pow (by omega)]
  ring

/-- 端点：F(1) = 1（仅 j = m 项存活）。 -/
theorem bernCdf_one (α β : ℕ) (hβ : 1 ≤ β) : bernCdf α β 1 = 1 := by
  unfold bernCdf
  have hmem : α + β - 1 ∈ Finset.Ico α (α + β) := Finset.mem_Ico.mpr ⟨by omega, by omega⟩
  refine Eq.trans (Finset.sum_eq_single_of_mem (α + β - 1) hmem ?_) ?_
  · intro j hj hjm
    have hjlt : j < α + β - 1 := by
      have h1 := Finset.mem_Ico.mp hj
      omega
    have hz : (1 - (1:ℝ)) ^ (α + β - 1 - j) = (0:ℝ) := by
      rw [sub_self]; exact zero_pow (by omega)
    rw [hz]
    exact mul_zero _
  · rw [Nat.choose_self]
    push_cast
    rw [one_pow, sub_self, Nat.sub_self, pow_zero, one_mul, one_mul]

/-- **求和望远镜求导（第一段核心）**：F′ = m·C(m−1,α−1)·x^{α−1}(1−x)^{β−1}，
    即 Beta 密度形状（常数 = 1/B(α,β)，见 `bernCdf_eq_normed`）。 -/
theorem bernCdf_deriv (α β : ℕ) (hα : 1 ≤ α) (hβ : 1 ≤ β) (x : ℝ) :
    HasDerivAt (bernCdf α β)
      (((Nat.choose (α + β - 2) (α - 1) * (α + β - 1) : ℕ) : ℝ)
        * x ^ (α - 1) * (1 - x) ^ (β - 1)) x := by
  have htermb : ∀ j ∈ Finset.Ico α (α + β),
      HasDerivAt (fun y => ((Nat.choose (α + β - 1) j : ℕ) : ℝ) * y ^ j * (1 - y) ^ (α + β - 1 - j))
        (((Nat.choose (α + β - 1) j : ℕ) : ℝ)
          * (((j : ℝ) * x ^ (j - 1) * (1 - x) ^ (α + β - 1 - j)
            - ((α + β - 1 - j : ℕ) : ℝ) * x ^ j * (1 - x) ^ (α + β - 2 - j)))) x := by
    intro j _
    refine ((UnifiedNeedlesS3a.s3aPowDeriv j (α + β - 1 - j) x).const_mul
      ((Nat.choose (α + β - 1) j : ℕ) : ℝ)).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun y => mul_assoc
        ((Nat.choose (α + β - 1) j : ℕ) : ℝ) (y ^ j) ((1 - y) ^ (α + β - 1 - j))) |>.congr_deriv ?_
    rw [show (α + β - 1 - j - 1 : ℕ) = α + β - 2 - j from by omega]
    ring
  have hsum := HasDerivAt.sum htermb
  -- 望远镜求和：u i := m·C(m−1,i)·x^i(1−x)^{m−1−i}，m := α+β−1
  set u : ℕ → ℝ := fun i => ((Nat.choose (α + β - 2) i * (α + β - 1) : ℕ) : ℝ)
      * x ^ i * (1 - x) ^ (α + β - 2 - i) with hu
  have huApp : ∀ i : ℕ, u i
      = ((Nat.choose (α + β - 2) i * (α + β - 1) : ℕ) : ℝ)
        * x ^ i * (1 - x) ^ (α + β - 2 - i) := fun i => rfl
  -- (A) 拆和：∑c(A−B) = ∑cA − ∑cB
  have h1 : ∑ j ∈ Finset.Ico α (α + β),
      ((Nat.choose (α + β - 1) j : ℕ) : ℝ)
        * (((j : ℝ) * x ^ (j - 1) * (1 - x) ^ (α + β - 1 - j)
          - (α + β - 1 - j : ℝ) * x ^ j * (1 - x) ^ (α + β - 2 - j)))
      = (∑ j ∈ Finset.Ico α (α + β),
      ((Nat.choose (α + β - 1) j : ℕ) : ℝ)
        * ((j : ℝ) * x ^ (j - 1) * (1 - x) ^ (α + β - 1 - j)))
      - (∑ j ∈ Finset.Ico α (α + β),
      ((Nat.choose (α + β - 1) j : ℕ) : ℝ)
        * ((α + β - 1 - j : ℝ) * x ^ j * (1 - x) ^ (α + β - 2 - j))) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  -- (B) 左和移标：j ↦ j−1
  have hB : (∑ j ∈ Finset.Ico α (α + β),
      ((Nat.choose (α + β - 1) j : ℕ) : ℝ)
        * ((j : ℝ) * x ^ (j - 1) * (1 - x) ^ (α + β - 1 - j)))
      = ∑ i ∈ Finset.Ico (α - 1) (α + β - 1), u i := by
    refine Eq.symm (Finset.sum_nbij' (fun i => i + 1) (fun j => j - 1) ?_ ?_ ?_ ?_ ?_)
    · intro i hi; have := Finset.mem_Ico.mp hi; exact Finset.mem_Ico.mpr ⟨by omega, by omega⟩
    · intro j hj; have := Finset.mem_Ico.mp hj; exact Finset.mem_Ico.mpr ⟨by omega, by omega⟩
    · intro i hi; omega
    · intro j hj; have := Finset.mem_Ico.mp hj; omega
    · intro i hi
      have he := choose_mul_left (α + β - 1) (i + 1) (by omega) (by omega)
      have hr : ((Nat.choose (α + β - 1) (i + 1) : ℕ) : ℝ) * ((i + 1 : ℕ) : ℝ)
          = ((Nat.choose (α + β - 2) i * (α + β - 1) : ℕ) : ℝ) :=
        congrArg (fun n : ℕ => ((n : ℝ))) he
      rw [huApp, hr, show (i + 1 - 1 : ℕ) = i from by omega,
        show (α + β - 1) - (i + 1) = α + β - 2 - i from by omega]
  -- (C) 右和：j = m 项为零，其余 = u j
  have hC : (∑ j ∈ Finset.Ico α (α + β),
      ((Nat.choose (α + β - 1) j : ℕ) : ℝ)
        * ((α + β - 1 - j : ℝ) * x ^ j * (1 - x) ^ (α + β - 2 - j)))
      = ∑ i ∈ Finset.Ico α (α + β - 1), u i := by
    have hins : Finset.Ico α (α + β)
        = insert (α + β - 1) (Finset.Ico α (α + β - 1)) := by
      refine Finset.ext fun j => ?_
      simp only [Finset.mem_insert, Finset.mem_Ico]
      omega
    have hnotins : ¬((α + β - 1 : ℕ) ∈ Finset.Ico α (α + β - 1)) := by
      intro hcon
      have := Finset.mem_Ico.mp hcon
      omega
    rw [hins, Finset.sum_insert hnotins]
    have hzero : ((Nat.choose (α + β - 1) (α + β - 1) : ℕ) : ℝ)
        * ((α + β - 1 - ((α + β - 1 : ℕ) : ℝ)) * x ^ (α + β - 1)
          * (1 - x) ^ (α + β - 2 - (α + β - 1))) = 0 := by
      push_cast
      rw [sub_self, zero_mul, mul_zero]
    rw [hzero, zero_add]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hjlt : j < α + β - 1 := by
      have h2 := Finset.mem_Ico.mp hj
      omega
    have he := choose_mul_right (α + β - 1) j hjlt
    have hr : ((Nat.choose (α + β - 1) j : ℕ) : ℝ) * ((α + β - 1 - j : ℕ) : ℝ)
        = ((Nat.choose (α + β - 2) j * (α + β - 1) : ℕ) : ℝ) :=
      congrArg (fun n : ℕ => ((n : ℝ))) he
    rw [huApp, hr]
  -- (D) 差 = u(α−1)
  have hD : (∑ i ∈ Finset.Ico (α - 1) (α + β - 1), u i)
      - (∑ i ∈ Finset.Ico α (α + β - 1), u i) = u (α - 1) := by
    have hins : Finset.Ico (α - 1) (α + β - 1)
        = insert (α - 1) (Finset.Ico α (α + β - 1)) := by
      refine Finset.ext fun i => ?_
      simp only [Finset.mem_insert, Finset.mem_Ico]
      omega
    have hnotins : ¬((α - 1 : ℕ) ∈ Finset.Ico α (α + β - 1)) := by
      intro hcon
      have := Finset.mem_Ico.mp hcon
      omega
    rw [hins, Finset.sum_insert hnotins, add_sub_cancel_right]
  -- (E) u(α−1) = 目标常数形状
  have hE : u (α - 1)
      = ((Nat.choose (α + β - 2) (α - 1) * (α + β - 1) : ℕ) : ℝ)
        * x ^ (α - 1) * (1 - x) ^ (β - 1) := by
    rw [huApp, show α + β - 2 - (α - 1) = β - 1 from by omega]
  refine hsum.congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun y => by simp [Finset.sum_apply', bernCdf]) |>.congr_deriv ?_
  calc ∑ j ∈ Finset.Ico α (α + β),
      ((Nat.choose (α + β - 1) j : ℕ) : ℝ)
        * (((j : ℝ) * x ^ (j - 1) * (1 - x) ^ (α + β - 1 - j)
          - (α + β - 1 - j : ℝ) * x ^ j * (1 - x) ^ (α + β - 2 - j)))
      = (∑ j ∈ Finset.Ico α (α + β),
        ((Nat.choose (α + β - 1) j : ℕ) : ℝ)
          * ((j : ℝ) * x ^ (j - 1) * (1 - x) ^ (α + β - 1 - j)))
        - (∑ j ∈ Finset.Ico α (α + β),
        ((Nat.choose (α + β - 1) j : ℕ) : ℝ)
          * ((α + β - 1 - j : ℝ) * x ^ j * (1 - x) ^ (α + β - 2 - j))) := h1
    _ = (∑ i ∈ Finset.Ico (α - 1) (α + β - 1), u i)
        - (∑ i ∈ Finset.Ico α (α + β - 1), u i) := by rw [hB, hC]
    _ = u (α - 1) := hD
    _ = ((Nat.choose (α + β - 2) (α - 1) * (α + β - 1) : ℕ) : ℝ)
          * x ^ (α - 1) * (1 - x) ^ (β - 1) := hE

/-- **F 与积分 CDF 相同**：F(x) = C·∫₀ˣ t^{α−1}(1−t)^{β−1}（由 F(0)=0 与望远镜求导）。 -/
theorem bernCdf_eq_integral (α β : ℕ) (hα : 1 ≤ α) (hβ : 1 ≤ β) (x : ℝ) :
    bernCdf α β x
      = ((Nat.choose (α + β - 2) (α - 1) * (α + β - 1) : ℕ) : ℝ)
        * ∫ t in (0:ℝ)..x, t ^ (α - 1) * (1 - t) ^ (β - 1) := by
  have hd : ∀ t : ℝ, HasDerivAt (bernCdf α β)
      ((fun u => ((Nat.choose (α + β - 2) (α - 1) * (α + β - 1) : ℕ) : ℝ)
        * (u ^ (α - 1) * (1 - u) ^ (β - 1))) t) t :=
    fun t => (bernCdf_deriv α β hα hβ t).congr_deriv (by ring)
  have hint : IntervalIntegrable (fun t => ((Nat.choose (α + β - 2) (α - 1) * (α + β - 1) : ℕ) : ℝ)
      * (t ^ (α - 1) * (1 - t) ^ (β - 1))) MeasureTheory.volume 0 x :=
    Continuous.intervalIntegrable (by fun_prop) 0 x
  have hFT := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := bernCdf α β)
    (f' := fun t => ((Nat.choose (α + β - 2) (α - 1) * (α + β - 1) : ℕ) : ℝ)
      * (t ^ (α - 1) * (1 - t) ^ (β - 1)))
    (a := 0) (b := x) (fun t _ => hd t) hint
  have hF0 : bernCdf α β 0 = 0 := bernCdf_zero α β hα
  rw [hF0, sub_zero] at hFT
  rw [← hFT, intervalIntegral.integral_const_mul]

/-- **归一化一致**：F(x) = ∫₀ˣ g / B(α,β)，其中 B(α,β) = betaTwoConst(α−1,β−1)
    的实像（复用 UnifiedNeedlesS3a 的整数 Beta 积分闭式，本件在 x=1 处反解常数）。 -/
theorem bernCdf_eq_normed (α β : ℕ) (hα : 1 ≤ α) (hβ : 1 ≤ β) (x : ℝ) :
    bernCdf α β x
      = (∫ t in (0:ℝ)..x, t ^ (α - 1) * (1 - t) ^ (β - 1))
        / ((UnifiedNeedlesS3a.betaTwoConst (α - 1) (β - 1) : ℚ) : ℝ) := by
  have h1 := bernCdf_eq_integral α β hα hβ x
  have h2 : bernCdf α β 1 = 1 := bernCdf_one α β hβ
  have hint1 : (∫ t in (0:ℝ)..1, t ^ (α - 1) * (1 - t) ^ (β - 1))
      = ((UnifiedNeedlesS3a.betaTwoConst (α - 1) (β - 1) : ℚ) : ℝ) :=
    UnifiedNeedlesS3a.betaInt_eq (α - 1) (β - 1)
  have hkey : ((Nat.choose (α + β - 2) (α - 1) * (α + β - 1) : ℕ) : ℝ)
      * ((UnifiedNeedlesS3a.betaTwoConst (α - 1) (β - 1) : ℚ) : ℝ) = 1 := by
    have hx1 := bernCdf_eq_integral α β hα hβ 1
    rw [h2, hint1] at hx1
    exact hx1.symm
  have hBpos : (0:ℝ) < ((UnifiedNeedlesS3a.betaTwoConst (α - 1) (β - 1) : ℚ) : ℝ) :=
    by exact_mod_cast UnifiedNeedlesS3a.betaTwoConst_pos (α - 1) (β - 1)
  have hCinv : ((Nat.choose (α + β - 2) (α - 1) * (α + β - 1) : ℕ) : ℝ)
      = 1 / ((UnifiedNeedlesS3a.betaTwoConst (α - 1) (β - 1) : ℚ) : ℝ) := by
    field_simp
    exact hkey
  rw [h1, hCinv]
  field_simp <;> ring

/-- **(0,1) 上严格递增**（导数 = 正常数 × 正密度形状；Icc 形，端点由单调化消费）。 -/
theorem bernCdf_strictMonoOn (α β : ℕ) (hα : 1 ≤ α) (hβ : 1 ≤ β) :
    StrictMonoOn (bernCdf α β) (Set.Icc 0 1) := by
  have hC : Continuous (bernCdf α β) := bernCdf_continuous α β
  have hpos : ∀ t ∈ Set.Ioo (0:ℝ) 1, 0 < deriv (bernCdf α β) t := by
    intro t ht
    rw [(bernCdf_deriv α β hα hβ t).deriv]
    have h1 : (0:ℝ) < ((Nat.choose (α + β - 2) (α - 1) * (α + β - 1) : ℕ) : ℝ) :=
      Nat.cast_pos.mpr (Nat.mul_pos (Nat.choose_pos (by omega)) (Nat.pos_of_ne_zero (by omega)))
    exact mul_pos (mul_pos h1 (pow_pos ht.1 _)) (pow_pos (by linarith [ht.2]) _)
  exact strictMonoOn_of_deriv_pos (D := Set.Icc (0:ℝ) 1) (convex_Icc 0 1) hC.continuousOn
    (by rwa [interior_Icc])

/-- ℚ 层同式（有理形状、有理点：闭式精确可计算）。 -/
def ratBernCdf (α β : ℕ) (q : ℚ) : ℚ :=
  ∑ j ∈ Finset.Ico α (α + β),
    ((Nat.choose (α + β - 1) j : ℕ) : ℚ) * q ^ j * (1 - q) ^ (α + β - 1 - j)

/-- 有理点桥：ℚ 闭式在实层的像 = bernCdf 在该有理点的值（精确，无近似）。 -/
theorem bernCdf_rat_cast (α β : ℕ) (q : ℚ) :
    (ratBernCdf α β q : ℝ) = bernCdf α β (q : ℝ) := by
  simp only [ratBernCdf, bernCdf, Rat.cast_sum, Rat.cast_mul, Rat.cast_pow, Rat.cast_natCast,
    Rat.cast_sub, Rat.cast_one]

/-- **有理 x 精确可比较**：F 在有理点的序 = ℚ 闭式的序（decide/精确算术可判定）。 -/
theorem bernCdf_rat_comparable (α β : ℕ) (q₁ q₂ : ℚ) :
    (bernCdf α β (q₁ : ℝ) ≤ bernCdf α β (q₂ : ℝ)) ↔ (ratBernCdf α β q₁ ≤ ratBernCdf α β q₂) := by
  rw [← bernCdf_rat_cast, ← bernCdf_rat_cast]
  exact Rat.cast_le

/-- 整型形状分量是合法混合分量：连续、单调、端点 0/1、严格递增（四义务之"有限混合"
    的 Beta 实例）。 -/
theorem bernCdf_mixable (α β : ℕ) (hα : 1 ≤ α) (hβ : 1 ≤ β) :
    Continuous (bernCdf α β) ∧ MonotoneOn (bernCdf α β) (Set.Icc 0 1) ∧
    bernCdf α β 0 = 0 ∧ bernCdf α β 1 = 1 ∧
    StrictMonoOn (bernCdf α β) (Set.Icc 0 1) := by
  have hs := bernCdf_strictMonoOn α β hα hβ
  exact ⟨bernCdf_continuous α β, hs.monotoneOn, bernCdf_zero α β hα, bernCdf_one α β hβ, hs⟩

/-! ## 二、半整型路径（合同 §7.4 第二段：四基底 + 分部积分递推） -/

/-- 基底一：I_x(1,1) = x。 -/
def halfCdf11 (x : ℝ) : ℝ := x

/-- 基底二：I_x(1/2,1) = √x。 -/
noncomputable def halfCdf12 (x : ℝ) : ℝ := Real.sqrt x

/-- 基底三：I_x(1,1/2) = 1−√(1−x)。 -/
noncomputable def halfCdf21 (x : ℝ) : ℝ := 1 - Real.sqrt (1 - x)

/-- 基底四：I_x(1/2,1/2) = 2·arcsin(√x)/π。 -/
noncomputable def halfCdf22 (x : ℝ) : ℝ := 2 * Real.arcsin (Real.sqrt x) / Real.pi

/-- 基底一是恒等函数的积分：d/dx x = 1。 -/
theorem halfCdf11_deriv (x : ℝ) : HasDerivAt halfCdf11 1 x :=
  hasDerivAt_id x

/-- 基底二的形状：d/dx √x = 1/(2√x) = (1/2)·t^{−1/2}（Beta(1/2,1) 密度形状除以 B=2）。 -/
theorem halfCdf12_deriv (x : ℝ) (hx : x ≠ 0) :
    HasDerivAt halfCdf12 (1 / (2 * Real.sqrt x)) x :=
  Real.hasDerivAt_sqrt hx

/-- 基底三的形状：d/dx (1−√(1−x)) = 1/(2√(1−x)) = (1/2)·(1−x)^{−1/2}。 -/
theorem halfCdf21_deriv (x : ℝ) (hx : x ≠ 1) :
    HasDerivAt halfCdf21 (1 / (2 * Real.sqrt (1 - x))) x := by
  have h1 : HasDerivAt (fun y : ℝ => 1 - y) (0 - 1) x :=
    HasDerivAt.sub (hasDerivAt_const x (1:ℝ)) (hasDerivAt_id x)
  have h2 : HasDerivAt (fun y => Real.sqrt (1 - y))
      ((1 / (2 * Real.sqrt (1 - x))) * (0 - 1)) x :=
    (Real.hasDerivAt_sqrt (sub_ne_zero.mpr (Ne.symm hx))).comp x h1
  exact (HasDerivAt.sub (hasDerivAt_const x (1:ℝ)) h2).congr_deriv (by ring)

/-- 基底四的形状：d/dx (2·arcsin√x/π) = 1/(π·√x·√(1−x))
    = t^{−1/2}(1−t)^{−1/2}/B(1/2,1/2)（见 `halfConst22`：B = π）。 -/
theorem halfCdf22_deriv (x : ℝ) (hx0 : 0 < x) (hx1 : x < 1) :
    HasDerivAt halfCdf22 (1 / (Real.pi * Real.sqrt x * Real.sqrt (1 - x))) x := by
  have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
  have hsqx : Real.sqrt x ≠ 0 := (Real.sqrt_pos_of_pos hx0).ne'
  have hsq1 : Real.sqrt (1 - x) ≠ 0 := (Real.sqrt_pos_of_pos (by linarith)).ne'
  have hs1 : Real.sqrt x ≠ -1 :=
    ne_of_gt (lt_of_lt_of_le (by norm_num) (Real.sqrt_nonneg x))
  have hs2 : Real.sqrt x ≠ 1 := fun h => hx1.ne (Real.sqrt_eq_one.mp h)
  have hsq : Real.sqrt x ^ 2 = x := Real.sq_sqrt hx0.le
  have hsqrt : HasDerivAt (fun y => Real.sqrt y) (1 / (2 * Real.sqrt x)) x :=
    Real.hasDerivAt_sqrt (ne_of_gt hx0)
  have hasin : HasDerivAt Real.arcsin (1 / Real.sqrt (1 - Real.sqrt x ^ 2)) (Real.sqrt x) :=
    Real.hasDerivAt_arcsin hs1 hs2
  have hd0 : HasDerivAt (fun y : ℝ => 2 / Real.pi * Real.arcsin (Real.sqrt y))
      ((2 / Real.pi) * (1 / Real.sqrt (1 - Real.sqrt x ^ 2) * (1 / (2 * Real.sqrt x)))) x :=
    ((hasin.comp x hsqrt).const_mul (2 / Real.pi)).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun y => rfl)
  refine hd0.congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun y => ?_) |>.congr_deriv ?_
  · show 2 * Real.arcsin (Real.sqrt y) / Real.pi
      = 2 / Real.pi * Real.arcsin (Real.sqrt y)
    ring
  · rw [hsq]
    ring

/-- 基底一端点。 -/
theorem halfCdf11_zero : halfCdf11 0 = 0 := rfl

theorem halfCdf11_one : halfCdf11 1 = 1 := rfl

theorem halfCdf12_zero : halfCdf12 0 = 0 := by simp [halfCdf12]

theorem halfCdf12_one : halfCdf12 1 = 1 := by simp [halfCdf12]

theorem halfCdf21_zero : halfCdf21 0 = 0 := by simp [halfCdf21]

theorem halfCdf21_one : halfCdf21 1 = 1 := by simp [halfCdf21]

theorem halfCdf22_zero : halfCdf22 0 = 0 := by
  simp only [halfCdf22, Real.sqrt_zero, Real.arcsin_zero]
  norm_num

theorem halfCdf22_one : halfCdf22 1 = 1 := by
  simp only [halfCdf22, Real.sqrt_one, Real.arcsin_one]
  field_simp [Real.pi_ne_zero]

/-- 归一化常数：B(1/2,1) = ∫₀¹ t^{−1/2} dt = 2（`integral_rpow` 精确计算）。 -/
theorem halfConst12 : (∫ t in (0:ℝ)..1, t ^ (-(1 / 2 : ℝ))) = 2 := by
  rw [integral_rpow (Or.inl (show (-1 : ℝ) < -(1 / 2 : ℝ) by norm_num)),
    Real.one_rpow, Real.zero_rpow (by norm_num)]
  norm_num

/-- 归一化常数：B(1,1/2) = ∫₀¹ (1−t)^{−1/2} dt = 2（反导数 −2(1−t)^{1/2}，FTC）。 -/
theorem halfConst21 : (∫ t in (0:ℝ)..1, (1 - t) ^ (-(1 / 2 : ℝ))) = 2 := by
  have hf : ∀ t ∈ Set.Ioo (0:ℝ) 1,
      HasDerivAt (fun y => -2 * (1 - y) ^ ((1 / 2 : ℝ))) ((1 - t) ^ (-(1 / 2 : ℝ))) t := by
    intro t ht
    have h1 : HasDerivAt (fun y : ℝ => 1 - y) (0 - 1) t :=
      HasDerivAt.sub (hasDerivAt_const t (1:ℝ)) (hasDerivAt_id t)
    have h2 := h1.rpow_const (p := (1 / 2 : ℝ))
      (Or.inl (show (1 - t : ℝ) ≠ 0 from by linarith [ht.2]))
    rw [show ((1 : ℝ) / 2 - 1) = (-(1 / 2 : ℝ)) from by norm_num] at h2
    exact h2.const_mul (-2) |>.congr_deriv (by ring)
  have hint : IntervalIntegrable (fun t => (1 - t) ^ (-(1 / 2 : ℝ))) MeasureTheory.volume 0 1 := by
    simpa using ((intervalIntegral.intervalIntegrable_rpow' (r := -(1 / 2 : ℝ))
      (show (-1 : ℝ) < -(1 / 2 : ℝ) by norm_num) (a := 0) (b := 1)).comp_sub_left 1).symm
  have hcont : ContinuousOn (fun t : ℝ => -2 * (1 - t) ^ ((1 / 2 : ℝ))) (Set.Icc (0:ℝ) 1) :=
    (continuous_const.mul
      ((Real.continuous_rpow_const (by norm_num : (0:ℝ) ≤ 1 / 2)).comp
        (continuous_const.sub continuous_id))).continuousOn
  have hFT := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
    (show (0:ℝ) ≤ 1 by norm_num) hcont hf hint
  rw [hFT]
  have e1 : ((1:ℝ) - 1) ^ ((1 / 2 : ℝ)) = (0:ℝ) := by
    rw [show ((1:ℝ) - 1) = 0 from by norm_num, Real.zero_rpow (by norm_num)]
  have e2 : ((1:ℝ) - 0) ^ ((1 / 2 : ℝ)) = (1:ℝ) := by
    rw [show ((1:ℝ) - 0) = 1 from by norm_num, Real.one_rpow]
  rw [e1, e2]
  norm_num

/-- 半整密形状（两 −1/2 次幂的乘积）：Beta(1/2,1/2) 的密度形状。 -/
noncomputable def halfDens22 (t : ℝ) : ℝ := t ^ (-(1 / 2 : ℝ)) * (1 - t) ^ (-(1 / 2 : ℝ))

/-- B(1/2,1/2) 侧的密度在 [0,1] 可积（两半各用「有界连续 × 可积幂」拼接）。 -/
theorem halfDens22_integrable :
    IntervalIntegrable halfDens22 MeasureTheory.volume 0 1 := by
  have hcongr : ∀ x : ℝ, (1 - x) ^ (-(1 / 2 : ℝ)) * x ^ (-(1 / 2 : ℝ))
      = x ^ (-(1 / 2 : ℝ)) * (1 - x) ^ (-(1 / 2 : ℝ)) :=
    fun x => mul_comm _ _
  have hleft : IntervalIntegrable halfDens22 MeasureTheory.volume 0 (1 / 2) := by
    refine intervalIntegrable_congr_ae
      (f := fun x => (1 - x) ^ (-(1 / 2 : ℝ)) * x ^ (-(1 / 2 : ℝ))) (g := halfDens22)
      (Filter.Eventually.of_forall hcongr) |>.mp
      (IntervalIntegrable.continuousOn_mul
        (intervalIntegral.intervalIntegrable_rpow' (r := -(1 / 2 : ℝ))
          (show (-1 : ℝ) < -(1 / 2 : ℝ) by norm_num) (a := 0) (b := 1 / 2))
        (by
          have hne : ∀ x ∈ Set.uIcc 0 ((1:ℝ) / 2), ((1:ℝ) - x) ≠ 0 ∨ (0:ℝ) ≤ -(1 / 2 : ℝ) := by
            intro x hx
            rw [Set.uIcc_of_le (show (0:ℝ) ≤ 1 / 2 by norm_num)] at hx
            exact Or.inl (by have hx1 : x ≤ (1:ℝ)/2 := hx.2; linarith)
          exact (continuous_const.sub continuous_id).continuousOn.rpow_const hne))
  have hright0 : IntervalIntegrable (fun x : ℝ => (1 - x) ^ (-(1 / 2 : ℝ)))
      MeasureTheory.volume (1 / 2) 1 := by
    have h1 := (intervalIntegral.intervalIntegrable_rpow' (r := -(1 / 2 : ℝ))
      (show (-1 : ℝ) < -(1 / 2 : ℝ) by norm_num) (a := 0) (b := 1 / 2)).comp_sub_left 1
    rw [show ((1:ℝ) - 0) = 1 from by norm_num,
      show ((1:ℝ) - 1 / 2) = 1 / 2 from by norm_num] at h1
    exact h1.symm
  have hright : IntervalIntegrable halfDens22 MeasureTheory.volume (1 / 2) 1 := by
    refine intervalIntegrable_congr_ae
      (f := fun x => x ^ (-(1 / 2 : ℝ)) * (1 - x) ^ (-(1 / 2 : ℝ))) (g := halfDens22)
      (Filter.Eventually.of_forall (fun x => rfl)) |>.mp
      (IntervalIntegrable.continuousOn_mul hright0
        (by
          have hne : ∀ x ∈ Set.uIcc ((1:ℝ) / 2) 1, (x:ℝ) ≠ 0 ∨ (0:ℝ) ≤ -(1 / 2 : ℝ) := by
            intro x hx
            rw [Set.uIcc_of_le (show ((1:ℝ) / 2) ≤ 1 by norm_num)] at hx
            exact Or.inl (by have hx0 : (1:ℝ)/2 ≤ x := hx.1; linarith)
          exact continuousOn_id.rpow_const hne))
  exact hleft.trans hright

/-- 归一化常数：B(1/2,1/2) = ∫₀¹ t^{−1/2}(1−t)^{−1/2} dt = π
    （反导数 2·arcsin√t，端点值 arcsin 1 = π/2 精确收口）。 -/
theorem halfConst22 : (∫ t in (0:ℝ)..1, halfDens22 t) = Real.pi := by
  have hf : ∀ t ∈ Set.Ioo (0:ℝ) 1,
      HasDerivAt (fun y => 2 * Real.arcsin (Real.sqrt y)) (halfDens22 t) t := by
    intro t ht
    have hx0 : (0:ℝ) < t := ht.1
    have hsqx : Real.sqrt t ≠ 0 := (Real.sqrt_pos_of_pos hx0).ne'
    have hs1 : Real.sqrt t ≠ -1 :=
      ne_of_gt (lt_of_lt_of_le (by norm_num) (Real.sqrt_nonneg t))
    have hs2 : Real.sqrt t ≠ 1 := fun h => ht.2.ne (Real.sqrt_eq_one.mp h)
    have hsq : Real.sqrt t ^ 2 = t := Real.sq_sqrt hx0.le
    have hsqrt : HasDerivAt (fun y => Real.sqrt y) (1 / (2 * Real.sqrt t)) t :=
      Real.hasDerivAt_sqrt (ne_of_gt hx0)
    have hasin : HasDerivAt Real.arcsin (1 / Real.sqrt (1 - Real.sqrt t ^ 2)) (Real.sqrt t) :=
      Real.hasDerivAt_arcsin hs1 hs2
    refine hasin.comp t hsqrt |>.const_mul 2 |>.congr_deriv ?_
    rw [hsq]
    show 2 * (1 / Real.sqrt (1 - t) * (1 / (2 * Real.sqrt t)))
      = t ^ (-(1 / 2 : ℝ)) * (1 - t) ^ (-(1 / 2 : ℝ))
    rw [rpow_neg_half_eq_inv_sqrt hx0.le,
      rpow_neg_half_eq_inv_sqrt (show (0:ℝ) ≤ 1 - t from by linarith [ht.2])]
    ring
  have hint := halfDens22_integrable
  have hcont : ContinuousOn (fun y => 2 * Real.arcsin (Real.sqrt y)) (Set.Icc 0 1) := by
    refine Continuous.continuousOn ?_
    fun_prop
  have hFT := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
    (show (0:ℝ) ≤ 1 by norm_num) hcont hf hint
  rw [hFT]
  rw [show Real.sqrt 1 = 1 from by norm_num, show Real.sqrt 0 = 0 from by norm_num,
    Real.arcsin_one, Real.arcsin_zero]
  ring

/-- **递推（和式，代数形式——a、b 各加一的第一式）**：对任意连续形状 g，
    J(a+1,b) + J(a,b+1) = J(a,b)：t + (1−t) = 1 的纯代数。 -/
theorem recursion_sum (g : ℝ → ℝ) (hg : Continuous g) (x : ℝ) :
    (∫ t in (0:ℝ)..x, g t * t) + (∫ t in (0:ℝ)..x, g t * (1 - t))
      = ∫ t in (0:ℝ)..x, g t := by
  have h1 : Continuous (fun t : ℝ => g t * t) := hg.mul continuous_id
  have h2 : Continuous (fun t : ℝ => g t * (1 - t)) :=
    hg.mul (continuous_const.sub continuous_id)
  rw [← intervalIntegral.integral_add (h1.intervalIntegrable 0 x) (h2.intervalIntegrable 0 x)]
  refine intervalIntegral.integral_congr (fun t _ => ?_)
  ring

/-- **递推（分部积分，自然指数——a、b 各加一的第二式）**：
    (n+1)·J(n+1,m+2) − (m+1)·J(n+2,m+1) = x^{n+1}(1−x)^{m+1}。 -/
theorem recursion_ibp_nat (n m : ℕ) (x : ℝ) :
    ((n : ℝ) + 1) * (∫ t in (0:ℝ)..x, t ^ n * (1 - t) ^ (m + 1))
      - ((m : ℝ) + 1) * (∫ t in (0:ℝ)..x, t ^ (n + 1) * (1 - t) ^ m)
      = x ^ (n + 1) * (1 - x) ^ (m + 1) := by
  have hII : IntervalIntegrable (fun t => ((n : ℝ) + 1) * (t ^ n * (1 - t) ^ (m + 1))
      - ((m : ℝ) + 1) * (t ^ (n + 1) * (1 - t) ^ m)) MeasureTheory.volume 0 x :=
    Continuous.intervalIntegrable (by fun_prop) 0 x
  have hD : ∀ t : ℝ, HasDerivAt (fun y => y ^ (n + 1) * (1 - y) ^ (m + 1))
      (((n : ℝ) + 1) * (t ^ n * (1 - t) ^ (m + 1))
        - ((m : ℝ) + 1) * (t ^ (n + 1) * (1 - t) ^ m)) t := by
    intro t
    refine (UnifiedNeedlesS3a.s3aPowDeriv (n + 1) (m + 1) t).congr_deriv ?_
    rw [show (n + 1 - 1 : ℕ) = n from by omega, show (m + 1 - 1 : ℕ) = m from by omega]
    push_cast
    ring
  have hFT := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun y => y ^ (n + 1) * (1 - y) ^ (m + 1))
    (f' := fun t => ((n : ℝ) + 1) * (t ^ n * (1 - t) ^ (m + 1))
      - ((m : ℝ) + 1) * (t ^ (n + 1) * (1 - t) ^ m))
    (a := 0) (b := x) (fun t _ => hD t) hII
  have hIIA : IntervalIntegrable (fun t => ((n : ℝ) + 1) * (t ^ n * (1 - t) ^ (m + 1)))
      MeasureTheory.volume 0 x := Continuous.intervalIntegrable (by fun_prop) 0 x
  have hIIB : IntervalIntegrable (fun t => ((m : ℝ) + 1) * (t ^ (n + 1) * (1 - t) ^ m))
      MeasureTheory.volume 0 x := Continuous.intervalIntegrable (by fun_prop) 0 x
  have hIA : (∫ t in (0:ℝ)..x, ((n : ℝ) + 1) * (t ^ n * (1 - t) ^ (m + 1)))
      = ((n : ℝ) + 1) * (∫ t in (0:ℝ)..x, t ^ n * (1 - t) ^ (m + 1)) :=
    intervalIntegral.integral_const_mul ((n : ℝ) + 1) (fun t => t ^ n * (1 - t) ^ (m + 1))
  have hIB : (∫ t in (0:ℝ)..x, ((m : ℝ) + 1) * (t ^ (n + 1) * (1 - t) ^ m))
      = ((m : ℝ) + 1) * (∫ t in (0:ℝ)..x, t ^ (n + 1) * (1 - t) ^ m) :=
    intervalIntegral.integral_const_mul ((m : ℝ) + 1) (fun t => t ^ (n + 1) * (1 - t) ^ m)
  have hL : ((n : ℝ) + 1) * (∫ t in (0:ℝ)..x, t ^ n * (1 - t) ^ (m + 1))
      - ((m : ℝ) + 1) * (∫ t in (0:ℝ)..x, t ^ (n + 1) * (1 - t) ^ m)
      = ∫ t in (0:ℝ)..x, ((n : ℝ) + 1) * (t ^ n * (1 - t) ^ (m + 1))
        - ((m : ℝ) + 1) * (t ^ (n + 1) * (1 - t) ^ m) := by
    rw [← hIA, ← hIB]
    exact (intervalIntegral.integral_sub hIIA hIIB).symm
  have hf0 : ((0:ℝ) ^ (n + 1) * (1 - (0:ℝ)) ^ (m + 1)) = 0 := by simp
  rw [hL, hFT, hf0, sub_zero]

/-- 半整数格：t^{n+1}√t 的导数（归纳，无 ℕ 减法）。 -/
theorem hasDerivAt_tnSqrt (n : ℕ) (t : ℝ) (ht : 0 < t) :
    HasDerivAt (fun y => y ^ (n + 1) * Real.sqrt y)
      ((((2 * n + 3 : ℕ) : ℝ) / 2) * t ^ n * Real.sqrt t) t := by
  induction n with
  | zero =>
      have hne : t ≠ 0 := ne_of_gt ht
      have hs : HasDerivAt Real.sqrt (1 / (2 * Real.sqrt t)) t :=
        Real.hasDerivAt_sqrt hne
      have hb : HasDerivAt (fun y : ℝ => y * Real.sqrt y)
          (Real.sqrt t + t * (1 / (2 * Real.sqrt t))) t := by
        refine ((hasDerivAt_id t).mul hs).congr_of_eventuallyEq
          (Filter.Eventually.of_forall fun y => rfl) |>.congr_deriv ?_
        simp only [id_eq, one_mul]
      have hfEq : (fun y : ℝ => y * Real.sqrt y)
          = (fun y : ℝ => y ^ (0 + 1) * Real.sqrt y) := by
        funext y; simp
      rw [hfEq] at hb
      refine hb.congr_deriv ?_
      norm_num
      have hsq0 : Real.sqrt t ≠ 0 := (Real.sqrt_pos_of_pos ht).ne'
      have hsq' : Real.sqrt t ^ 2 = t := Real.sq_sqrt ht.le
      field_simp [hsq', hsq0] <;> linarith [Real.sq_sqrt ht.le]
  | succ k ih =>
      have hne : t ≠ 0 := ne_of_gt ht
      have hbid : HasDerivAt (fun y : ℝ => y) 1 t := hasDerivAt_id t
      have hb : HasDerivAt (fun y : ℝ => y ^ (k + 1 + 1) * Real.sqrt y)
          ((((2 * k + 3 : ℕ) : ℝ) / 2 * t ^ k * Real.sqrt t) * t
            + t ^ (k + 1) * Real.sqrt t) t := by
        have hfun : ∀ y : ℝ,
            y ^ (k + 1 + 1) * Real.sqrt y = (y ^ (k + 1) * Real.sqrt y) * y := by
          intro y
          rw [pow_succ]
          ring
        exact ((ih.mul hbid).congr_of_eventuallyEq
          (Filter.Eventually.of_forall hfun)).congr_deriv (by ring)
      rw [show t ^ (k + 1) = t ^ k * t from by rw [pow_succ]] at hb
      have hcast : ((2 * (k + 1) + 3 : ℕ) : ℝ) = ((2 * k + 3 : ℕ) : ℝ) + 2 := by
        rw [show ((2:ℕ) * (k + 1) + 3 = (2:ℕ) * k + 3 + 2) from by ring, Nat.cast_add,
          Nat.cast_ofNat]
      refine hb.congr_deriv ?_
      rw [hcast, show t ^ (k + 1) = t ^ k * t from by rw [pow_succ]]
      ring

/-- 半整数格：(1−t)^{m+1}√(1−t) 的导数（与上式关于 t ↦ 1−t 复合）。 -/
theorem hasDerivAt_oneSubTmSqrt (m : ℕ) (t : ℝ) (ht : t < 1) :
    HasDerivAt (fun y => (1 - y) ^ (m + 1) * Real.sqrt (1 - y))
      (-((((2 * m + 3 : ℕ) : ℝ) / 2) * (1 - t) ^ m * Real.sqrt (1 - t))) t := by
  have h1 : HasDerivAt (fun y : ℝ => 1 - y) (0 - 1) t :=
    HasDerivAt.sub (hasDerivAt_const t (1:ℝ)) (hasDerivAt_id t)
  have hcomp := (hasDerivAt_tnSqrt m (1 - t) (by linarith)).comp t h1
  refine hcomp.congr_deriv ?_
  ring

/-- **递推（分部积分，半整格——对全部 n m : ℕ，加 a 或加 b 各进一步）**：
    ((2n+3)/2)·J(n+3/2, m+5/2) − ((2m+3)/2)·J(n+5/2, m+3/2)
      = x^{n+1}√x·(1−x)^{m+1}√(1−x)。
    前提 x ≤ 1（√(1−y) 只在 y ≤ 1 处实值可导；x ∈ [0,1] 是半整型 CDF 的定义域）。 -/
theorem recursion_ibp_half (n m : ℕ) (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    (((2 * n + 3 : ℕ) : ℝ) / 2)
      * (∫ t in (0:ℝ)..x, (t ^ n * Real.sqrt t) * ((1 - t) ^ (m + 1) * Real.sqrt (1 - t)))
      - (((2 * m + 3 : ℕ) : ℝ) / 2)
      * (∫ t in (0:ℝ)..x, (t ^ (n + 1) * Real.sqrt t) * ((1 - t) ^ m * Real.sqrt (1 - t)))
      = (x ^ (n + 1) * Real.sqrt x) * ((1 - x) ^ (m + 1) * Real.sqrt (1 - x)) := by
  have hf' : ∀ t ∈ Set.Ioo (0:ℝ) x,
      HasDerivAt (fun y => (y ^ (n + 1) * Real.sqrt y) * ((1 - y) ^ (m + 1) * Real.sqrt (1 - y)))
        ((((2 * n + 3 : ℕ) : ℝ) / 2)
            * ((t ^ n * Real.sqrt t) * ((1 - t) ^ (m + 1) * Real.sqrt (1 - t)))
          - (((2 * m + 3 : ℕ) : ℝ) / 2)
            * ((t ^ (n + 1) * Real.sqrt t) * ((1 - t) ^ m * Real.sqrt (1 - t)))) t := by
    intro t ht
    have ht1 : 0 < t := ht.1
    have ht2 : t < 1 := by linarith [ht.2, hx1]
    refine (hasDerivAt_tnSqrt n t ht1).mul (hasDerivAt_oneSubTmSqrt m t ht2) |>.congr_deriv ?_
    ring
  have hcont : ContinuousOn (fun y => (y ^ (n + 1) * Real.sqrt y)
      * ((1 - y) ^ (m + 1) * Real.sqrt (1 - y))) (Set.Icc 0 x) := by
    refine Continuous.continuousOn ?_
    exact ((continuous_pow (n + 1)).mul Real.continuous_sqrt).mul
      (((continuous_pow (m + 1)).comp (continuous_const.sub continuous_id)).mul
        (Real.continuous_sqrt.comp (continuous_const.sub continuous_id)))
  have hIIA : IntervalIntegrable (fun t => (((2 * n + 3 : ℕ) : ℝ) / 2)
      * ((t ^ n * Real.sqrt t) * ((1 - t) ^ (m + 1) * Real.sqrt (1 - t))))
      MeasureTheory.volume 0 x :=
    Continuous.intervalIntegrable (by fun_prop) 0 x
  have hIIB : IntervalIntegrable (fun t => (((2 * m + 3 : ℕ) : ℝ) / 2)
      * ((t ^ (n + 1) * Real.sqrt t) * ((1 - t) ^ m * Real.sqrt (1 - t))))
      MeasureTheory.volume 0 x :=
    Continuous.intervalIntegrable (by fun_prop) 0 x
  have hII : IntervalIntegrable (fun t => (((2 * n + 3 : ℕ) : ℝ) / 2)
      * ((t ^ n * Real.sqrt t) * ((1 - t) ^ (m + 1) * Real.sqrt (1 - t)))
      - (((2 * m + 3 : ℕ) : ℝ) / 2)
      * ((t ^ (n + 1) * Real.sqrt t) * ((1 - t) ^ m * Real.sqrt (1 - t))))
      MeasureTheory.volume 0 x :=
    Continuous.intervalIntegrable (by fun_prop) 0 x
  have hFT := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hx0 hcont hf' hII
  have hAsplit : (((2 * n + 3 : ℕ) : ℝ) / 2)
      * (∫ t in (0:ℝ)..x, (t ^ n * Real.sqrt t) * ((1 - t) ^ (m + 1) * Real.sqrt (1 - t)))
      = ∫ t in (0:ℝ)..x, (((2 * n + 3 : ℕ) : ℝ) / 2)
          * ((t ^ n * Real.sqrt t) * ((1 - t) ^ (m + 1) * Real.sqrt (1 - t))) :=
    (intervalIntegral.integral_const_mul _ _).symm
  have hBsplit : (((2 * m + 3 : ℕ) : ℝ) / 2)
      * (∫ t in (0:ℝ)..x, (t ^ (n + 1) * Real.sqrt t) * ((1 - t) ^ m * Real.sqrt (1 - t)))
      = ∫ t in (0:ℝ)..x, (((2 * m + 3 : ℕ) : ℝ) / 2)
          * ((t ^ (n + 1) * Real.sqrt t) * ((1 - t) ^ m * Real.sqrt (1 - t))) :=
    (intervalIntegral.integral_const_mul _ _).symm
  have hL : (((2 * n + 3 : ℕ) : ℝ) / 2)
      * (∫ t in (0:ℝ)..x, (t ^ n * Real.sqrt t) * ((1 - t) ^ (m + 1) * Real.sqrt (1 - t)))
      - (((2 * m + 3 : ℕ) : ℝ) / 2)
      * (∫ t in (0:ℝ)..x, (t ^ (n + 1) * Real.sqrt t) * ((1 - t) ^ m * Real.sqrt (1 - t)))
      = ∫ t in (0:ℝ)..x, (((2 * n + 3 : ℕ) : ℝ) / 2)
          * ((t ^ n * Real.sqrt t) * ((1 - t) ^ (m + 1) * Real.sqrt (1 - t)))
        - (((2 * m + 3 : ℕ) : ℝ) / 2)
          * ((t ^ (n + 1) * Real.sqrt t) * ((1 - t) ^ m * Real.sqrt (1 - t))) := by
    rw [hAsplit, hBsplit]
    exact (intervalIntegral.integral_sub hIIA hIIB).symm
  have hf0 : (((0:ℝ) ^ (n + 1) * Real.sqrt (0:ℝ))
      * ((1 - (0:ℝ)) ^ (m + 1) * Real.sqrt (1 - (0:ℝ)))) = 0 := by
    simp
  rw [hL, hFT, hf0, sub_zero]

/-- (√t)-列的闭式：∫₀ˣ t^n√t dt = (2/(2n+3))·x^{n+1}√x（x ≥ 0；半整 a 列的精确形状）。 -/
theorem halfColInt (n : ℕ) (x : ℝ) (hx : 0 ≤ x) :
    (∫ t in (0:ℝ)..x, t ^ n * Real.sqrt t)
      = (2 / ((2 * n + 3 : ℕ) : ℝ)) * (x ^ (n + 1) * Real.sqrt x) := by
  have hne : ((2 * n + 3 : ℕ) : ℝ) ≠ 0 := by
    have hp : 0 < (2 * n + 3 : ℕ) := by omega
    exact_mod_cast hp.ne'
  have hf : ∀ t ∈ Set.Ioo (0:ℝ) x,
      HasDerivAt (fun y => (2 / ((2 * n + 3 : ℕ) : ℝ)) * (y ^ (n + 1) * Real.sqrt y))
        (t ^ n * Real.sqrt t) t := by
    intro t ht
    have ht1 : 0 < t := ht.1
    refine (hasDerivAt_tnSqrt n t ht1).const_mul (2 / ((2 * n + 3 : ℕ) : ℝ)) |>.congr_deriv ?_
    have hne2 : ((2 * n + 3 : ℕ) : ℝ) ≠ 0 := hne
    field_simp [hne2]
  have hcont : ContinuousOn (fun y => (2 / ((2 * n + 3 : ℕ) : ℝ)) * (y ^ (n + 1) * Real.sqrt y))
      (Set.Icc 0 x) := by
    refine Continuous.continuousOn ?_
    exact continuous_const.mul ((continuous_pow (n + 1)).mul Real.continuous_sqrt)
  have hint : IntervalIntegrable (fun t => t ^ n * Real.sqrt t) MeasureTheory.volume 0 x :=
    Continuous.intervalIntegrable (by fun_prop) 0 x
  have hFT := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hx hcont hf hint
  have hf0 : ((2 / ((2 * n + 3 : ℕ) : ℝ))
      * ((0:ℝ) ^ (n + 1) * Real.sqrt (0:ℝ))) = 0 := by
    simp
  rw [hFT, hf0, sub_zero]
/-- **平方比较隔离根／对称式**：基底四满足 halfCdf22 x = 1 − halfCdf22 (1−x)，
    （arcsin√x + arcsin√(1−x) = π/2 的精确证明，x > 1/2 化归到 x ≤ 1/2 的依据）。 -/
theorem halfCdf22_symm (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    halfCdf22 x = 1 - halfCdf22 (1 - x) := by
  have hθ0 : (0:ℝ) ≤ Real.arcsin (Real.sqrt x) := by
    simpa [Real.arcsin_zero] using Real.arcsin_le_arcsin (Real.sqrt_nonneg x)
  have hθ1 : Real.arcsin (Real.sqrt x) ≤ Real.pi / 2 := Real.arcsin_le_pi_div_two _
  have hcos : Real.cos (Real.arcsin (Real.sqrt x)) = Real.sqrt (1 - x) := by
    have hc := Real.cos_arcsin (Real.sqrt x)
    rw [Real.sq_sqrt hx0] at hc
    exact hc
  have hkey : Real.arcsin (Real.sqrt (1 - x)) = Real.pi / 2 - Real.arcsin (Real.sqrt x) := by
    have hb1 : -(Real.pi / 2) ≤ Real.pi / 2 - Real.arcsin (Real.sqrt x) := by linarith
    have hb2 : Real.pi / 2 - Real.arcsin (Real.sqrt x) ≤ Real.pi / 2 := by linarith
    have hs : Real.sin (Real.pi / 2 - Real.arcsin (Real.sqrt x)) = Real.sqrt (1 - x) := by
      rw [Real.sin_pi_div_two_sub, hcos]
    rw [← hs, Real.arcsin_sin hb1 hb2]
  show 2 * Real.arcsin (Real.sqrt x) / Real.pi
      = 1 - 2 * Real.arcsin (Real.sqrt (1 - x)) / Real.pi
  rw [hkey]
  field_simp [Real.pi_ne_zero] <;> ring

/-- 显式假设（开放点声明，非公理）：π 的 Machin 式/交错级数式有理包围输入
    （执行层生成；此处只声明接口）。 -/
def PiRatEnclosureInput : Prop :=
  ∃ lo hi : ℚ, (lo : ℝ) < Real.pi ∧ Real.pi < (hi : ℝ)

/-- π 的平凡有理包围 [3,4]（证明存在；Machin 式窄包围是执行层义务）。 -/
theorem pi_rat_enclosure_trivial : PiRatEnclosureInput :=
  ⟨3, 4, by exact_mod_cast Real.pi_gt_three, by exact_mod_cast Real.pi_lt_four⟩

/-- 显式假设（开放点声明，非公理）：x ≤ 1/2 时 asin 非负幂级数几何尾界的
    有理包围输入（执行层生成；x > 1/2 由 `halfCdf22_symm` 化归）。 -/
def AsinRatEnclosureInput : Prop :=
  ∀ q : ℚ, 0 ≤ q → q ≤ 1 / 2 → ∃ lo hi : ℚ,
    ((lo : ℝ) ≤ 2 * Real.arcsin (Real.sqrt (q : ℝ)) / Real.pi)
      ∧ (2 * Real.arcsin (Real.sqrt (q : ℝ)) / Real.pi ≤ (hi : ℝ))

/-- 基底四在全 [0,1] 的有理包围：x ≤ 1/2 直接用幂级数尾界输入，
    x > 1/2 用对称式化归（合同「x>1/2 先用对称式」）。 -/
theorem halfCdf22_enclosure_from_half (hAsin : AsinRatEnclosureInput) (q : ℚ)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    ∃ lo hi : ℚ, ((lo : ℝ) ≤ halfCdf22 (q : ℝ)) ∧ (halfCdf22 (q : ℝ) ≤ (hi : ℝ)) := by
  have hcast : (((1:ℚ) - q : ℚ) : ℝ) = (1:ℝ) - (q:ℝ) := by push_cast; ring
  have hsymm : halfCdf22 (q : ℝ) = 1 - halfCdf22 ((1:ℝ) - (q:ℝ)) :=
    halfCdf22_symm (q:ℝ) (by exact_mod_cast hq0) (by exact_mod_cast hq1)
  rcases le_total q (1 / 2) with h | h
  · exact hAsin q hq0 h
  · have hq' : 0 ≤ (1:ℚ) - q := by linarith
    have hq1' : (1:ℚ) - q ≤ 1 / 2 := by linarith
    obtain ⟨lo, hi, hlo, hhi⟩ := hAsin (1 - q) hq' hq1'
    rw [hsymm, ← hcast]
    refine ⟨1 - hi, 1 - lo, ?_, ?_⟩
    · simp only [halfCdf22]
      push_cast at hhi ⊢
      linarith
    · simp only [halfCdf22]
      push_cast at hlo ⊢
      linarith

/-! ## 三、一般正有理参数的积分包围（合同 §7.4 第三段） -/

/-- 形状被积函数：g(t) = t^{a−1}(1−t)^{b−1}（合同原式；a b > 0，
    执行输入为精确有理或有理包围的可计算表示）。 -/
noncomputable def betaDens (a b : ℝ) (t : ℝ) : ℝ := t ^ (a - 1) * (1 - t) ^ (b - 1)

/-- 内部位势：M(η,r) = max(η^r, (1−η)^r)。 -/
noncomputable def Mbound (η r : ℝ) : ℝ := max (η ^ r) ((1 - η) ^ r)

/-- 分母下界位势：m(r) = min((1/4)^r, (3/4)^r)。 -/
noncomputable def mbound (r : ℝ) : ℝ := min ((1 / 4 : ℝ) ^ r) ((3 / 4 : ℝ) ^ r)

/-- 内部幂界：t ∈ [η, 1−η] ⟹ t^r ≤ M(η,r)。 -/
theorem rpow_le_Mbound (η r t : ℝ) (hη : 0 < η) (hη1 : η < 1) (ht : t ∈ Set.Icc η (1 - η)) :
    t ^ r ≤ Mbound η r := by
  obtain ⟨ht1, ht2⟩ := Set.mem_Icc.mp ht
  rcases le_total 0 r with hr | hr
  · exact le_trans (Real.rpow_le_rpow (le_trans hη.le ht1) ht2 hr) (le_max_right _ _)
  · -- r ≤ 0：t ≥ η ⟹ t^r ≤ η^r（倒数反序）
    have hp1 : 0 < η ^ (-r) := Real.rpow_pos_of_pos hη _
    have hp2 : 0 < t ^ (-r) := Real.rpow_pos_of_pos (lt_of_lt_of_le hη ht1) _
    have hge : η ^ (-r) ≤ t ^ (-r) := Real.rpow_le_rpow hη.le ht1 (by linarith)
    have e1 : t ^ r = 1 / t ^ (-r) := by
      have h1 := Real.rpow_neg (le_trans hη.le ht1) (-r)
      rw [neg_neg] at h1
      rw [h1, inv_eq_one_div]
    have e2 : η ^ r = 1 / η ^ (-r) := by
      have h2 := Real.rpow_neg hη.le (-r)
      rw [neg_neg] at h2
      rw [h2, inv_eq_one_div]
    rw [e1]
    show 1 / t ^ (-r) ≤ max (η ^ r) ((1 - η) ^ r)
    rw [e2]
    exact le_max_iff.mpr (Or.inl (one_div_le_one_div' hp2 hp1 hge))

/-- g′ 的显式导数（t ∈ (0,1)）：((a−1)t^{a−2}(1−t)^{b−1} − (b−1)t^{a−1}(1−t)^{b−2})。 -/
theorem hasDerivAt_betaDens (a b t : ℝ) (ht : 0 < t) (ht1 : t < 1) :
    HasDerivAt (betaDens a b)
      ((a - 1) * t ^ (a - 2) * (1 - t) ^ (b - 1)
        - (b - 1) * t ^ (a - 1) * (1 - t) ^ (b - 2)) t := by
  have h1 : HasDerivAt (fun y : ℝ => y) 1 t := hasDerivAt_id t
  have h2 : HasDerivAt (fun y : ℝ => 1 - y) (0 - 1) t :=
    HasDerivAt.sub (hasDerivAt_const t (1:ℝ)) (hasDerivAt_id t)
  have hp1 := h1.rpow_const (p := a - 1) (Or.inl ht.ne')
  have hp2 := h2.rpow_const (p := b - 1) (Or.inl (show (1 - t : ℝ) ≠ 0 from by linarith))
  rw [show (a - 1 : ℝ) - 1 = a - 2 from by ring] at hp1
  rw [show (b - 1 : ℝ) - 1 = b - 2 from by ring] at hp2
  refine (hp1.mul hp2).congr_deriv ?_
  ring

/-- **左尾上界（合同）**：g ≤ M·t^{a−1} 于 [0,η] ⟹ ∫₀^η g ≤ M·η^a/a。 -/
theorem leftTail_aux (a b M η : ℝ) (ha : 0 < a) (hb : 0 < b) (hη : 0 < η) (hη1 : η < 1)
    (hM : ∀ t ∈ Set.Icc 0 η, (1 - t) ^ (b - 1) ≤ M) :
    (∫ t in (0:ℝ)..η, betaDens a b t) ≤ M * η ^ a / a := by
  have hpt : ∀ t ∈ Set.Icc 0 η, betaDens a b t ≤ M * t ^ (a - 1) := by
    intro t ht
    have hpow : (0:ℝ) ≤ t ^ (a - 1) := Real.rpow_nonneg ht.1 _
    show t ^ (a - 1) * (1 - t) ^ (b - 1) ≤ M * t ^ (a - 1)
    rw [mul_comm M (t ^ (a - 1))]
    exact mul_le_mul_of_nonneg_left (hM t ht) hpow
  have hpowint : IntervalIntegrable (fun t => t ^ (a - 1)) MeasureTheory.volume 0 η :=
    intervalIntegral.intervalIntegrable_rpow' (r := a - 1) (by linarith) (a := 0) (b := η)
  have hneη : ∀ x ∈ Set.uIcc 0 η, ((1:ℝ) - x) ≠ 0 ∨ (0:ℝ) ≤ (b - 1) := by
    intro x hx
    rw [Set.uIcc_of_le hη.le] at hx
    exact Or.inl (by have hx1 : x ≤ η := hx.2; linarith)
  have hcongr : ∀ x : ℝ, (1 - x) ^ (b - 1) * x ^ (a - 1)
      = x ^ (a - 1) * (1 - x) ^ (b - 1) :=
    fun x => mul_comm _ _
  have hint : IntervalIntegrable (betaDens a b) MeasureTheory.volume 0 η := by
    refine intervalIntegrable_congr_ae
      (f := fun x => (1 - x) ^ (b - 1) * x ^ (a - 1)) (g := betaDens a b)
      (Filter.Eventually.of_forall hcongr) |>.mp
      (IntervalIntegrable.continuousOn_mul hpowint
        ((continuous_const.sub continuous_id).continuousOn.rpow_const hneη))
  have hMint : IntervalIntegrable (fun t => M * t ^ (a - 1)) MeasureTheory.volume 0 η :=
    hpowint.const_mul M
  have hmono := intervalIntegral.integral_mono_on (show (0:ℝ) ≤ η by linarith) hint hMint hpt
  rw [intervalIntegral.integral_const_mul] at hmono
  have hexact : (∫ t in (0:ℝ)..η, t ^ (a - 1)) = η ^ a / a := by
    rw [integral_rpow (Or.inl (show (-1:ℝ) < a - 1 by linarith)),
      show (a - 1) + 1 = a from by ring, Real.zero_rpow (by linarith)]
    field_simp <;> ring
  rw [hexact, mul_div_assoc'] at hmono
  exact hmono

/-- 左尾常数，b ≥ 1：M_b = 1。 -/
theorem leftTail_ge1 (a b η : ℝ) (ha : 0 < a) (hb : 1 ≤ b) (hη : 0 < η) (hη1 : η < 1) :
    (∫ t in (0:ℝ)..η, betaDens a b t) ≤ η ^ a / a := by
  have hM : ∀ t ∈ Set.Icc 0 η, (1 - t) ^ (b - 1) ≤ 1 := by
    intro t ht
    exact Real.rpow_le_one (by linarith [ht.2]) (by linarith [ht.1]) (by linarith)
  have h := leftTail_aux a b 1 η ha (by linarith) hη hη1 hM
  rw [one_mul] at h
  exact h

/-- 左尾常数，b < 1：M_b = (1−η)^{b−1}（负指数反序；合同反例显示取 1 会给假界）。 -/
theorem leftTail_lt1 (a b η : ℝ) (ha : 0 < a) (hb : 0 < b) (hb1 : b < 1) (hη : 0 < η)
    (hη1 : η < 1) :
    (∫ t in (0:ℝ)..η, betaDens a b t) ≤ (1 - η) ^ (b - 1) * η ^ a / a := by
  refine leftTail_aux a b ((1 - η) ^ (b - 1)) η ha hb hη hη1 ?_
  intro t ht
  obtain ⟨ht0, ht2⟩ := Set.mem_Icc.mp ht
  have hpos1 : 0 < 1 - t := by linarith
  have hpos2 : 0 < 1 - η := by linarith
  have hge : (1 - η) ^ (1 - b) ≤ (1 - t) ^ (1 - b) :=
    Real.rpow_le_rpow hpos2.le (by linarith) (by linarith)
  have hp1 : 0 < (1 - η) ^ (1 - b) := Real.rpow_pos_of_pos hpos2 _
  have hp2 : 0 < (1 - t) ^ (1 - b) := Real.rpow_pos_of_pos hpos1 _
  have e1 : (1 - t) ^ (b - 1) = 1 / (1 - t) ^ (1 - b) := by
    rw [show (b - 1 : ℝ) = -((1:ℝ) - b) from by ring, Real.rpow_neg hpos1.le, inv_eq_one_div]
  have e2 : (1 - η) ^ (b - 1) = 1 / (1 - η) ^ (1 - b) := by
    rw [show (b - 1 : ℝ) = -((1:ℝ) - b) from by ring, Real.rpow_neg hpos2.le, inv_eq_one_div]
  rw [e1, e2]
  exact one_div_le_one_div' hp2 hp1 hge

/-- 右尾内层精确值：∫_{1−η}^1 (1−t)^{b−1} dt = η^b/b（反导数 −(1−t)^b/b）。 -/
theorem rightInnerExact (b η : ℝ) (hb : 0 < b) (hη : 0 < η) (hη1 : η ≤ 1) :
    (∫ t in (1 - η :ℝ)..1, (1 - t) ^ (b - 1)) = η ^ b / b := by
  have hf : ∀ t ∈ Set.Ioo (1 - η) 1,
      HasDerivAt (fun y => -(1 - y) ^ b / b) ((1 - t) ^ (b - 1)) t := by
    intro t ht
    have h1 : HasDerivAt (fun y : ℝ => 1 - y) (0 - 1) t :=
      HasDerivAt.sub (hasDerivAt_const t (1:ℝ)) (hasDerivAt_id t)
    have h2 := h1.rpow_const (p := b)
      (Or.inl (show (1 - t : ℝ) ≠ 0 from by linarith [ht.2]))
    refine (h2.div_const b).neg.congr_deriv ?_
    rw [show ((0:ℝ) - 1) = -1 from by norm_num]
    field_simp [hb.ne'] <;> ring
  have hint : IntervalIntegrable (fun t => (1 - t) ^ (b - 1)) MeasureTheory.volume (1 - η) 1 := by
    simpa using (intervalIntegral.intervalIntegrable_rpow' (r := b - 1) (by linarith)
      (a := η) (b := 0)).comp_sub_left 1
  have hbcont : ContinuousOn (fun y : ℝ => (1 - y) ^ b) (Set.Icc (1 - η) 1) := by
    refine ContinuousOn.rpow_const (f := fun y : ℝ => 1 - y) (p := b)
      ((continuous_const.sub continuous_id).continuousOn) ?_
    intro x hx
    exact Or.inr (le_of_lt hb)
  have hcont : ContinuousOn (fun y => -(1 - y) ^ b / b) (Set.Icc (1 - η) 1) :=
    hbcont.neg.div_const b
  have hFT := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
    (show (1 - η :ℝ) ≤ 1 by linarith) hcont hf hint
  rw [hFT, show ((1:ℝ) - 1) = 0 from by norm_num,
    Real.zero_rpow (by linarith),
    show ((1:ℝ) - (1 - η)) = η from by linarith]
  ring

/-- **右尾上界（合同，换元对称）**：g ≤ M·(1−t)^{b−1} 于 [1−η,1] ⟹
    ∫_{1−η}^1 g ≤ M·η^b/b。 -/
theorem rightTail_aux (a b M η : ℝ) (ha : 0 < a) (hb : 0 < b) (hη : 0 < η) (hη1 : η ≤ 1)
    (hη2 : η < 1)
    (hM : ∀ t ∈ Set.Icc (1 - η) 1, t ^ (a - 1) ≤ M) :
    (∫ t in (1 - η :ℝ)..1, betaDens a b t) ≤ M * η ^ b / b := by
  have hpt : ∀ t ∈ Set.Icc (1 - η) 1, betaDens a b t ≤ M * (1 - t) ^ (b - 1) := by
    intro t ht
    show t ^ (a - 1) * (1 - t) ^ (b - 1) ≤ M * (1 - t) ^ (b - 1)
    exact mul_le_mul_of_nonneg_right (hM t ht) (Real.rpow_nonneg (by linarith [ht.2]) _)
  have hpowint : IntervalIntegrable (fun t => (1 - t) ^ (b - 1)) MeasureTheory.volume (1 - η) 1 := by
    simpa using (intervalIntegral.intervalIntegrable_rpow' (r := b - 1) (by linarith)
      (a := η) (b := 0)).comp_sub_left 1
  have hne1 : ∀ x ∈ Set.uIcc (1 - η) 1, (x:ℝ) ≠ 0 ∨ (0:ℝ) ≤ (a - 1) := by
    intro x hx
    rw [Set.uIcc_of_le (show ((1:ℝ) - η) ≤ 1 by linarith)] at hx
    exact Or.inl (by have hx0 : (1:ℝ) - η ≤ x := hx.1; linarith [hη2.le, hx0])
  have hint : IntervalIntegrable (betaDens a b) MeasureTheory.volume (1 - η) 1 :=
    IntervalIntegrable.continuousOn_mul hpowint (continuousOn_id.rpow_const hne1)
  have hMint : IntervalIntegrable (fun t => M * (1 - t) ^ (b - 1))
      MeasureTheory.volume (1 - η) 1 := hpowint.const_mul M
  have hmono := intervalIntegral.integral_mono_on (by linarith) hint hMint hpt
  rw [intervalIntegral.integral_const_mul] at hmono
  rw [mul_div_assoc', ← rightInnerExact b η hb hη hη1]
  exact hmono

/-- 右尾常数，a ≥ 1：M_a = 1。 -/
theorem rightTail_ge1 (a b η : ℝ) (ha : 1 ≤ a) (hb : 0 < b) (hη : 0 < η) (hη1 : η ≤ 1)
    (hη2 : η < 1) :
    (∫ t in (1 - η :ℝ)..1, betaDens a b t) ≤ η ^ b / b := by
  have hM : ∀ t ∈ Set.Icc (1 - η) 1, t ^ (a - 1) ≤ 1 := by
    intro t ht
    exact Real.rpow_le_one (le_trans (by linarith) ht.1) ht.2 (by linarith [ha])
  have h := rightTail_aux a b 1 η (by linarith) hb hη hη1 hη2 hM
  rw [one_mul] at h
  exact h

/-- 右尾常数，a < 1：M_a = (1−η)^{a−1}。 -/
theorem rightTail_lt1 (a b η : ℝ) (ha : 0 < a) (ha1 : a < 1) (hb : 0 < b) (hη : 0 < η)
    (hη1 : η ≤ 1) (hη2 : η < 1) :
    (∫ t in (1 - η :ℝ)..1, betaDens a b t) ≤ (1 - η) ^ (a - 1) * η ^ b / b := by
  refine rightTail_aux a b ((1 - η) ^ (a - 1)) η ha hb hη hη1 hη2 ?_
  intro t ht
  have hpos1 : 0 < 1 - η := by linarith
  have hge : (1 - η) ^ (1 - a) ≤ t ^ (1 - a) :=
    Real.rpow_le_rpow hpos1.le ht.1 (by linarith)
  have hp1 : 0 < (1 - η) ^ (1 - a) := Real.rpow_pos_of_pos hpos1 _
  have hp2 : 0 < t ^ (1 - a) :=
    Real.rpow_pos_of_pos (lt_of_lt_of_le hpos1 ht.1) _
  have e1 : t ^ (a - 1) = 1 / t ^ (1 - a) := by
    rw [show (a - 1 : ℝ) = -((1:ℝ) - a) from by ring, Real.rpow_neg (by linarith [ht.1]),
      inv_eq_one_div]
  have e2 : (1 - η) ^ (a - 1) = 1 / (1 - η) ^ (1 - a) := by
    rw [show (a - 1 : ℝ) = -((1:ℝ) - a) from by ring, Real.rpow_neg hpos1.le, inv_eq_one_div]
  rw [e1, e2]
  exact one_div_le_one_div' hp2 hp1 hge

/-- **合同反例定理**：a=1, b=1/2, η=1/4 时左尾真值 = 2−√3 > 1/4（⟺ 48 < 49），
    故「0<b<1 误取 M_b = 1」给出假界；正确常数 (1−η)^{b−1} = (3/4)^{−1/2} = 2/√3
    给出 2−√3 ≤ 1/(2√3)。 -/
theorem leftTailFlatBoundCounterexample :
    ((∫ t in (0:ℝ)..(1 / 4), (1 - t) ^ (-(1 / 2 : ℝ))) = 2 - Real.sqrt 3)
      ∧ ((1 / 4 : ℝ) < 2 - Real.sqrt 3)
      ∧ (2 - Real.sqrt 3 ≤ 1 / (2 * Real.sqrt 3)) := by
  -- 积分：反导数 −2√(1−t)，[0,1/4] 上无奇点
  have hf : ∀ t ∈ Set.Ioo (0:ℝ) (1 / 4),
      HasDerivAt (fun y => -2 * Real.sqrt (1 - y)) ((1 - t) ^ (-(1 / 2 : ℝ))) t := by
    intro t ht
    have h1 : HasDerivAt (fun y : ℝ => 1 - y) (0 - 1) t :=
      HasDerivAt.sub (hasDerivAt_const t (1:ℝ)) (hasDerivAt_id t)
    have h2 : HasDerivAt (fun y => Real.sqrt (1 - y))
        ((1 / (2 * Real.sqrt (1 - t))) * (0 - 1)) t :=
      (Real.hasDerivAt_sqrt (show (1 - t : ℝ) ≠ 0 from by linarith [ht.2])).comp t h1
    refine h2.const_mul (-2) |>.congr_deriv ?_
    rw [rpow_neg_half_eq_inv_sqrt (show (0:ℝ) ≤ 1 - t from by linarith [ht.2])]
    field_simp <;> ring
  have hint : IntervalIntegrable (fun t => (1 - t) ^ (-(1 / 2 : ℝ)))
      MeasureTheory.volume 0 (1 / 4) := by
    refine ContinuousOn.intervalIntegrable ?_
    refine (continuous_const.sub continuous_id).continuousOn.rpow_const ?_
    intro x hx
    refine Or.inl ?_
    have hx1 : x ≤ (1:ℝ) / 4 := by
      rw [Set.uIcc_of_le (show (0:ℝ) ≤ 1 / 4 by norm_num)] at hx
      exact hx.2
    show (1 - x : ℝ) ≠ 0
    linarith
  have hcont : ContinuousOn (fun y => -2 * Real.sqrt (1 - y)) (Set.Icc 0 (1 / 4)) := by
    refine Continuous.continuousOn ?_
    exact continuous_const.mul (Real.continuous_sqrt.comp
      (continuous_const.sub continuous_id))
  have hFT := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (by norm_num) hcont hf hint
  refine ⟨?_, ?_, ?_⟩
  · rw [hFT]
    have e1 : Real.sqrt ((1:ℝ) - 1 / 4) = Real.sqrt 3 / 2 := by
      rw [show ((1:ℝ) - 1 / 4) = 3 / 4 from by norm_num, Real.sqrt_div (by norm_num)]
      norm_num
    have e0 : Real.sqrt ((1:ℝ) - 0) = 1 := by rw [sub_zero, Real.sqrt_one]
    rw [e1, e0]
    ring
  · -- 1/4 < 2 − √3 ⟺ √3 < 7/4 ⟺ 3 < 49/16（合同：等价于 48 < 49）
    have h3lt : Real.sqrt 3 < 7 / 4 := by
      rw [Real.sqrt_lt (by norm_num) (by norm_num)]
      norm_num
    linarith
  · -- 2 − √3 ≤ 1/(2√3) ⟺ 4√3 ≤ 7 ⟺ 48 ≤ 49
    have h3pos : (0:ℝ) < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
    have hkey : (4:ℝ) * Real.sqrt 3 ≤ 7 := by
      have h1 : Real.sqrt 3 ≤ 7 / 4 := by
        rw [Real.sqrt_le_left (by norm_num)]
        norm_num
      linarith
    have ex : (2 - Real.sqrt 3) * (2 * Real.sqrt 3) = 4 * Real.sqrt 3 - 6 := by
      have hsq3 : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)
      nlinarith [hsq3]
    rw [le_div_iff₀ (by positivity), ex]
    linarith

/-- m(r) ≤ t^r 于 t ∈ [1/4,3/4]（分母下界的逐点腿）。 -/
theorem mbound_le (r t : ℝ) (ht : t ∈ Set.Icc (1 / 4 : ℝ) (3 / 4 : ℝ)) : mbound r ≤ t ^ r := by
  rcases le_total 0 r with hr | hr
  · refine le_trans (min_le_left _ _) (Real.rpow_le_rpow (by norm_num) ht.1 hr)
  · have hp : 0 < t ^ (-r) :=
      Real.rpow_pos_of_pos (lt_of_lt_of_le (by norm_num : (0:ℝ) < 1 / 4) ht.1) _
    have hp' : 0 < (3 / 4 : ℝ) ^ (-r) := Real.rpow_pos_of_pos (by norm_num) _
    have hge : (3 / 4 : ℝ) ^ (-r) ≤ t ^ (-r) := Real.rpow_le_rpow (by norm_num) ht.2 (by linarith)
    have e1 : t ^ r = 1 / t ^ (-r) := by
      have h1 := Real.rpow_neg (by linarith [ht.1]) (-r)
      rw [neg_neg] at h1
      rw [h1, inv_eq_one_div]
    have e2 : (3 / 4 : ℝ) ^ r = 1 / (3 / 4 : ℝ) ^ (-r) := by
      have h2 := Real.rpow_neg (by norm_num) (-r)
      rw [neg_neg] at h2
      rw [h2, inv_eq_one_div]
    show min ((1 / 4 : ℝ) ^ r) ((3 / 4 : ℝ) ^ r) ≤ t ^ r
    rw [e1, e2]
    exact min_le_iff.mpr (Or.inr (one_div_le_one_div' hp hp' hge))

/-- **分母正下界（四义务之一）**：m(r)=min((1/4)^r,(3/4)^r) 时
    B(a,b) = ∫₀¹ g ≥ m(a−1)·m(b−1)/2 > 0。 -/
theorem betaB_lower (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    (1 / 2 : ℝ) * mbound (a - 1) * mbound (b - 1)
      ≤ (∫ t in (0:ℝ)..1, betaDens a b t) := by
  have hpt : ∀ t ∈ Set.Icc (1 / 4 : ℝ) (3 / 4 : ℝ),
      mbound (a - 1) * mbound (b - 1) ≤ betaDens a b t := by
    intro t ht
    obtain ⟨ht1, ht2⟩ := Set.mem_Icc.mp ht
    show mbound (a - 1) * mbound (b - 1) ≤ t ^ (a - 1) * (1 - t) ^ (b - 1)
    have hA : mbound (a - 1) ≤ t ^ (a - 1) := mbound_le (a - 1) t ht
    have hB : mbound (b - 1) ≤ (1 - t) ^ (b - 1) := mbound_le (b - 1) (1 - t)
      (by rcases Set.mem_Icc.mp ht with ⟨h1, h2⟩; exact ⟨by linarith, by linarith⟩)
    have hZ : (0:ℝ) ≤ mbound (b - 1) :=
      le_min (Real.rpow_nonneg (by norm_num) (b - 1))
        (Real.rpow_nonneg (by norm_num) (b - 1))
    exact le_trans (mul_le_mul_of_nonneg_right hA hZ)
      (mul_le_mul_of_nonneg_left hB (Real.rpow_nonneg (le_trans (by norm_num) ht1) (a - 1)))
  have hcongr : ∀ x : ℝ, (1 - x) ^ (b - 1) * x ^ (a - 1)
      = x ^ (a - 1) * (1 - x) ^ (b - 1) :=
    fun x => mul_comm _ _
  have hintL : IntervalIntegrable (betaDens a b) MeasureTheory.volume 0 (1 / 4) := by
    refine intervalIntegrable_congr_ae
      (f := fun x => (1 - x) ^ (b - 1) * x ^ (a - 1)) (g := betaDens a b)
      (Filter.Eventually.of_forall hcongr) |>.mp
      (IntervalIntegrable.continuousOn_mul
        (intervalIntegral.intervalIntegrable_rpow' (r := a - 1) (by linarith)
          (a := 0) (b := 1 / 4))
        (by
          have hne : ∀ x ∈ Set.uIcc 0 ((1:ℝ) / 4), ((1:ℝ) - x) ≠ 0 ∨ (0:ℝ) ≤ (b - 1) := by
            intro x hx
            rw [Set.uIcc_of_le (show (0:ℝ) ≤ 1 / 4 by norm_num)] at hx
            exact Or.inl (by have hx1 : x ≤ (1:ℝ)/4 := hx.2; linarith)
          exact (continuous_const.sub continuous_id).continuousOn.rpow_const hne))
  have hintR0 : IntervalIntegrable (fun x : ℝ => (1 - x) ^ (b - 1))
      MeasureTheory.volume (3 / 4) 1 := by
    have h1 := (intervalIntegral.intervalIntegrable_rpow' (r := b - 1) (by linarith)
      (a := (1:ℝ) / 4) (b := 0)).comp_sub_left 1
    rw [show ((1:ℝ) - 0) = 1 from by norm_num,
      show ((1:ℝ) - 1 / 4) = 3 / 4 from by norm_num] at h1
    exact h1
  have hintR : IntervalIntegrable (betaDens a b) MeasureTheory.volume (3 / 4) 1 :=
    IntervalIntegrable.continuousOn_mul hintR0
      (by
        have hne : ∀ x ∈ Set.uIcc ((3:ℝ) / 4) 1, (x:ℝ) ≠ 0 ∨ (0:ℝ) ≤ (a - 1) := by
          intro x hx
          rw [Set.uIcc_of_le (show (3:ℝ)/4 ≤ 1 by norm_num)] at hx
          exact Or.inl (by have hx0 : (3:ℝ)/4 ≤ x := hx.1; linarith)
        exact continuousOn_id.rpow_const hne)
  have hintM : IntervalIntegrable (betaDens a b) MeasureTheory.volume (1 / 4) (3 / 4) := by
    have hkey : ContinuousOn (fun t : ℝ => t ^ (a - 1) * (1 - t) ^ (b - 1))
        (Set.uIcc (1 / 4 : ℝ) (3 / 4)) := by
      have hsEq : Set.uIcc (1 / 4 : ℝ) (3 / 4) = Set.Icc (1 / 4 : ℝ) (3 / 4) :=
        Set.uIcc_of_le (by norm_num)
      rw [hsEq]
      have hp1 : ContinuousOn (fun t : ℝ => t ^ (a - 1)) (Set.Icc (1 / 4 : ℝ) (3 / 4)) :=
        continuousOn_id.rpow_const (fun x hx => Or.inl (show (x:ℝ) ≠ 0 by linarith [hx.1]))
      have hp2 : ContinuousOn (fun t : ℝ => (1 - t) ^ (b - 1))
          (Set.Icc (1 / 4 : ℝ) (3 / 4)) :=
        (ContinuousOn.sub continuousOn_const continuousOn_id).rpow_const
          (fun x hx => Or.inl (show ((1:ℝ) - x) ≠ 0 by linarith [hx.2]))
      exact hp1.mul hp2
    refine ContinuousOn.intervalIntegrable ?_
    exact hkey
  have hge0L : (0:ℝ) ≤ (∫ t in (0:ℝ)..(1 / 4), betaDens a b t) := by
    have h := intervalIntegral.integral_mono_on (by norm_num)
      ((by exact intervalIntegral.intervalIntegrable_const :
        IntervalIntegrable (fun _ : ℝ => (0:ℝ)) MeasureTheory.volume 0 (1 / 4))) hintL
      (by intro t ht
          exact mul_nonneg (Real.rpow_nonneg ht.1 (a - 1))
            (Real.rpow_nonneg (by linarith [ht.2]) (b - 1)))
    simpa using h
  have hge0R : (0:ℝ) ≤ (∫ t in (3 / 4:ℝ)..1, betaDens a b t) := by
    have h := intervalIntegral.integral_mono_on (by norm_num)
      ((by exact intervalIntegral.intervalIntegrable_const :
        IntervalIntegrable (fun _ : ℝ => (0:ℝ)) MeasureTheory.volume (3 / 4) 1)) hintR
      (by intro t ht
          exact mul_nonneg (Real.rpow_nonneg (le_trans (by norm_num) ht.1) (a - 1))
            (Real.rpow_nonneg (by linarith [ht.2]) (b - 1)))
    simpa using h
  have hmid : ((1 / 2 : ℝ) * mbound (a - 1) * mbound (b - 1))
      ≤ (∫ t in (1 / 4:ℝ)..(3 / 4), betaDens a b t) := by
    have hc : (∫ t in (1 / 4:ℝ)..(3 / 4), mbound (a - 1) * mbound (b - 1))
        = (1 / 2 : ℝ) * mbound (a - 1) * mbound (b - 1) := by
      rw [intervalIntegral.integral_const,
        show ((3:ℝ) / 4 - 1 / 4) = (1:ℝ) / 2 from by norm_num, smul_eq_mul]
      ring
    rw [← hc]
    exact intervalIntegral.integral_mono_on (by norm_num)
      intervalIntegral.intervalIntegrable_const hintM hpt
  have htotal : (∫ t in (0:ℝ)..1, betaDens a b t)
      = (∫ t in (0:ℝ)..(1 / 4), betaDens a b t)
        + ((∫ t in (1 / 4:ℝ)..(3 / 4), betaDens a b t)
          + (∫ t in (3 / 4:ℝ)..1, betaDens a b t)) := by
    rw [← intervalIntegral.integral_add_adjacent_intervals (hintL.trans hintM) hintR,
      ← intervalIntegral.integral_add_adjacent_intervals hintL hintM, add_assoc]
  rw [htotal]
  linarith

/-- 分母为正（归一化的独立正见证；代数隔离取有理下界 β 前的第一步）。 -/
theorem betaB_pos (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    0 < (∫ t in (0:ℝ)..1, betaDens a b t) := by
  have h := betaB_lower a b ha hb
  have h1 : 0 < (1 / 2 : ℝ) * mbound (a - 1) * mbound (b - 1) := by
    have hm1 : (0:ℝ) < mbound (a - 1) := by
      show 0 < min ((1 / 4 : ℝ) ^ (a - 1)) ((3 / 4 : ℝ) ^ (a - 1))
      exact lt_min (Real.rpow_pos_of_pos (by norm_num) (a - 1))
        (Real.rpow_pos_of_pos (by norm_num) (a - 1))
    have hm2 : (0:ℝ) < mbound (b - 1) := by
      show 0 < min ((1 / 4 : ℝ) ^ (b - 1)) ((3 / 4 : ℝ) ^ (b - 1))
      exact lt_min (Real.rpow_pos_of_pos (by norm_num) (b - 1))
        (Real.rpow_pos_of_pos (by norm_num) (b - 1))
    exact mul_pos (mul_pos (by norm_num) hm1) hm2
  linarith

/-- **商宽（合同）**：分子 [N_l,N_u]、分母 [B_l,B_u] 各宽 ≤ ρ，N_l ≤ B_u、β ≤ B_l
    且均正时，N_u/B_l − N_l/B_u ≤ 2ρ/β。 -/
theorem quotientWidth (N_l N_u B_l B_u ρ β : ℚ) (hρ : 0 < ρ) (hβ : 0 < β)
    (hNl : 0 ≤ N_l) (hBlβ : β ≤ B_l) (hBl : 0 < B_l) (hBlu : B_l ≤ B_u)
    (hNel : N_l ≤ N_u) (hNB : N_l ≤ B_u)
    (hwl : N_u - N_l ≤ ρ) (hwd : B_u - B_l ≤ ρ) :
    N_u / B_l - N_l / B_u ≤ 2 * ρ / β := by
  have h1 : N_u / B_l - N_l / B_u
      = (N_u - N_l) / B_l + N_l * (B_u - B_l) / (B_l * B_u) := by
    field_simp [hBl.ne', (lt_of_lt_of_le hBl hBlu).ne'] <;> ring
  have h2 : (N_u - N_l) / B_l ≤ ρ / B_l :=
    (div_le_div_iff₀ hBl hBl).mpr (mul_le_mul_of_nonneg_right hwl hBl.le)
  have h3 : ρ / B_l ≤ ρ / β :=
    (div_le_div_iff₀ hBl hβ).mpr (mul_le_mul_of_nonneg_left hBlβ hρ.le)
  have h4 : N_l * (B_u - B_l) / (B_l * B_u) ≤ ρ / β := by
    have hBpos : (0:ℚ) < B_l * B_u := mul_pos hBl (lt_of_lt_of_le hBl hBlu)
    have e1 : N_l * (B_u - B_l) * (B_l * B_u) ≤ N_l * ρ * (B_l * B_u) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hwd hNl) hBpos.le
    have e2 : N_l * ρ * (B_l * B_u) ≤ B_u * ρ * (B_l * B_u) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hNB hρ.le) hBpos.le
    have e3 : B_u * ρ / (B_l * B_u) = ρ / B_l := by
      field_simp [hBl.ne', (lt_of_lt_of_le hBl hBlu).ne'] <;> ring
    calc N_l * (B_u - B_l) / (B_l * B_u)
        ≤ N_l * ρ / (B_l * B_u) := (div_le_div_iff₀ hBpos hBpos).mpr e1
      _ ≤ B_u * ρ / (B_l * B_u) := (div_le_div_iff₀ hBpos hBpos).mpr e2
      _ ≤ ρ / β := by rw [e3]; exact h3
  calc N_u / B_l - N_l / B_u
      = (N_u - N_l) / B_l + N_l * (B_u - B_l) / (B_l * B_u) := h1
    _ ≤ ρ / B_l + ρ / β := by linarith [h2, h4]
    _ ≤ ρ / β + ρ / β := by linarith [h3]
    _ = 2 * ρ / β := by ring

/-- 包围内的商：N_l ≤ N ≤ N_u、0 < B_l ≤ B ≤ B_u 且 0 ≤ N_l ⟹ N/B ∈ [N_l/B_u, N_u/B_l]。 -/
theorem div_mem_enclosure (N N_l N_u B B_l B_u : ℝ)
    (hN0 : 0 ≤ N_l) (hNl : N_l ≤ N) (hNu : N ≤ N_u) (hBl : 0 < B_l)
    (hBlB : B_l ≤ B) (hBuB : B ≤ B_u) :
    N_l / B_u ≤ N / B ∧ N / B ≤ N_u / B_l := by
  have hBu : 0 < B_u := lt_of_lt_of_le hBl (le_trans hBlB hBuB)
  have hB : 0 < B := lt_of_lt_of_le hBl hBlB
  have h1 : N_l / B_u ≤ N / B := by
    refine (div_le_div_iff₀ hBu hB).mpr ?_
    exact le_trans (mul_le_mul_of_nonneg_right hNl hB.le)
      (mul_le_mul_of_nonneg_left hBuB (le_trans hN0 hNl))
  have h2 : N / B ≤ N_u / B_l := by
    refine (div_le_div_iff₀ hB hBl).mpr ?_
    exact le_trans (mul_le_mul_of_nonneg_right hNu hBl.le)
      (mul_le_mul_of_nonneg_left hBlB (le_trans (le_trans hN0 hNl) hNu))
  exact ⟨h1, h2⟩

/-- **ρ ≤ εβ/4 收口（合同）**：商宽 ≤ 2ρ/β 且 ρ ≤ εβ/4 ⟹ 商宽 ≤ ε。 -/
theorem cdfWidthFromRho (ε ρ β : ℚ) (hε : 0 < ε) (hρ : 0 < ρ) (hβ : 0 < β)
    (hρe : ρ ≤ ε * β / 4)
    (N_l N_u B_l B_u : ℚ)
    (hWq : N_u / B_l - N_l / B_u ≤ 2 * ρ / β) :
    N_u / B_l - N_l / B_u ≤ ε := by
  refine le_trans hWq ?_
  have h1 : 2 * ρ / β ≤ 2 * (ε * β / 4) / β :=
    (div_le_div_iff₀ hβ hβ).mpr (by nlinarith [hρe])
  have h2 : 2 * (ε * β / 4) / β = ε / 2 := by
    field_simp [hβ.ne'] <;> ring
  rw [h2] at h1
  linarith

/-- 显式假设（开放点声明，非公理）：η 型正有理端点处有理幂（可隔离代数数）的
    有理包围输入——执行层代数隔离生成；M/m 量与求值外包取值所需。 -/
def RpowRatEnclosureInput (η : ℚ) : Prop :=
  ∀ r : ℚ, ∃ lo hi : ℚ, ((lo : ℝ) ≤ (η : ℝ) ^ (r : ℝ)) ∧ ((η : ℝ) ^ (r : ℝ) ≤ (hi : ℝ))

/-- 格点数存在（合同 N ≥ max(1, ⌈4L̄ℓ²/ρ⌉) 的存在性；固定 η 后由 Archimedean
    单独取 N——不得与 k 同步增长，因 L 随 η 减小可发散）。 -/
theorem exists_grid_N (c : ℚ) : ∃ N : ℕ, (1 : ℚ) ≤ N ∧ c ≤ N := by
  obtain ⟨n, hn⟩ := exists_nat_ge (max 1 c)
  refine ⟨n, ?_, ?_⟩
  · exact_mod_cast (le_trans (le_max_left 1 c) hn)
  · exact_mod_cast (le_trans (le_max_right 1 c) hn)

/-- 尾界 M 的统一包围：(1−η)^{b−1} ≤ max 1 (1/2)^{b−1}（0 < b、0 < η ≤ 1/4）。 -/
theorem Mb_le (b η : ℝ) (hb : 0 < b) (hη : 0 < η) (hη1 : η ≤ 1 / 4) :
    (1 - η) ^ (b - 1) ≤ max 1 ((1 / 2 : ℝ) ^ (b - 1)) := by
  rcases le_total 1 b with hb1 | hb1
  · refine le_trans (Real.rpow_le_one (by linarith) (by linarith) (by linarith))
      (le_max_left _ _)
  · have hge : (1 / 2 : ℝ) ^ (1 - b) ≤ (1 - η) ^ (1 - b) :=
      Real.rpow_le_rpow (by norm_num) (by linarith) (by linarith)
    have hp1 : 0 < (1 / 2 : ℝ) ^ (1 - b) := Real.rpow_pos_of_pos (by norm_num) _
    have hp2 : 0 < (1 - η) ^ (1 - b) := Real.rpow_pos_of_pos (by linarith) _
    have e1 : (1 - η) ^ (b - 1) = 1 / (1 - η) ^ (1 - b) := by
      rw [show (b - 1 : ℝ) = -((1:ℝ) - b) from by ring, Real.rpow_neg (by linarith),
        inv_eq_one_div]
    have e2 : (1 / 2 : ℝ) ^ (b - 1) = 1 / (1 / 2 : ℝ) ^ (1 - b) := by
      rw [show (b - 1 : ℝ) = -((1:ℝ) - b) from by ring, Real.rpow_neg (by norm_num),
        inv_eq_one_div]
    refine le_trans ?_ (le_max_right _ _)
    rw [e1, e2]
    exact one_div_le_one_div' hp2 hp1 hge

/-- 尾部预算的有限终止（合同）：两尾有证上界之和随 k 指数衰减，
    任意正预算有限步可达。 -/
theorem exists_tail_budget (a b ρ : ℝ) (ha : 0 < a) (hb : 0 < b) (hρ : 0 < ρ) :
    ∃ k : ℕ,
      ((max 1 ((1 / 2 : ℝ) ^ (b - 1))) * ((1 / 4 : ℝ) ^ a / a)
        + (max 1 ((1 / 2 : ℝ) ^ (a - 1))) * ((1 / 4 : ℝ) ^ b / b))
        * ((1 / 2 : ℝ) ^ (min a b)) ^ k ≤ ρ := by
  set C : ℝ := (max 1 ((1 / 2 : ℝ) ^ (b - 1))) * ((1 / 4 : ℝ) ^ a / a)
    + (max 1 ((1 / 2 : ℝ) ^ (a - 1))) * ((1 / 4 : ℝ) ^ b / b) with hCdef
  have hCpos : 0 < C := by
    rw [hCdef]
    refine add_pos (mul_pos (by positivity)
      (div_pos (Real.rpow_pos_of_pos (by norm_num) _) ha)) ?_
    exact mul_pos (by positivity) (div_pos (Real.rpow_pos_of_pos (by norm_num) _) hb)
  have hbase0 : (0:ℝ) < (1 / 2 : ℝ) ^ (min a b) := Real.rpow_pos_of_pos (by norm_num) _
  have hbase1 : (1 / 2 : ℝ) ^ (min a b) < 1 :=
    Real.rpow_lt_one (by norm_num) (by norm_num) (by positivity)
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (div_pos hρ hCpos) hbase1
  refine ⟨k, ?_⟩
  have h1 : C * ((1 / 2 : ℝ) ^ (min a b)) ^ k ≤ C * (ρ / C) :=
    mul_le_mul_of_nonneg_left hk.le hCpos.le
  have h2 : C * (ρ / C) = ρ := by
    field_simp [hCpos.ne'] <;> ring
  rw [h2] at h1
  exact h1

/-- 尾预算实例化：η = (1/4)·(1/2)^k 时 η > 0、η ≤ 1/4，两尾分别被
    Mbnd·η^a/a 与 MaBnd·η^b/b 界住（对接 `leftTail_*`／`rightTail_*`）。 -/
theorem tailBudgetAt (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (k : ℕ) :
    (0:ℝ) < (1 / 4 : ℝ) * (1 / 2) ^ k
      ∧ ((1 / 4 : ℝ) * (1 / 2) ^ k ≤ 1 / 4)
      ∧ ((∫ t in (0:ℝ)..((1 / 4 : ℝ) * (1 / 2) ^ k), betaDens a b t)
          ≤ (max 1 ((1 / 2 : ℝ) ^ (b - 1))) * (((1 / 4 : ℝ) * (1 / 2) ^ k) ^ a / a))
      ∧ ((∫ t in (1 - (1 / 4 : ℝ) * (1 / 2) ^ k :ℝ)..1, betaDens a b t)
          ≤ (max 1 ((1 / 2 : ℝ) ^ (a - 1))) * (((1 / 4 : ℝ) * (1 / 2) ^ k) ^ b / b)) := by
  have hη0 : (0:ℝ) < (1 / 4) * (1 / 2) ^ k :=
    mul_pos (by norm_num) (pow_pos (by norm_num) k)
  have hη1 : ((1:ℝ) / 4) * ((1:ℝ) / 2) ^ k ≤ (1:ℝ) / 4 := by
    have h1 : ((1:ℝ) / 2) ^ k ≤ 1 := half_pow_le_one k
    linarith
  have hMb := Mb_le b _ hb hη0 hη1
  have hMa := Mb_le a _ ha hη0 hη1
  have hXa : (0:ℝ) ≤ ((1 / 4 : ℝ) * (1 / 2) ^ k) ^ a / a :=
    div_nonneg (Real.rpow_nonneg hη0.le a) ha.le
  have hXb : (0:ℝ) ≤ ((1 / 4 : ℝ) * (1 / 2) ^ k) ^ b / b :=
    div_nonneg (Real.rpow_nonneg hη0.le b) hb.le
  refine ⟨hη0, hη1, ?_, ?_⟩
  · rcases le_total 1 b with hb1 | hb1
    · have h1' := leftTail_ge1 a b ((1 / 4 : ℝ) * (1 / 2) ^ k) ha hb1 hη0 (by linarith)
      exact le_trans h1' (le_trans
        (le_of_eq (one_mul (((1 / 4 : ℝ) * (1 / 2) ^ k) ^ a / a)).symm)
        (mul_le_mul_of_nonneg_right (le_max_left _ _) hXa))
    · rcases lt_or_eq_of_le hb1 with hb1' | hb1'
      · have h1' := leftTail_lt1 a b ((1 / 4 : ℝ) * (1 / 2) ^ k) ha hb hb1' hη0 (by linarith)
        rw [← mul_div_assoc'] at h1'
        exact le_trans h1' (mul_le_mul_of_nonneg_right hMb hXa)
      · have h1' := leftTail_ge1 a b ((1 / 4 : ℝ) * (1 / 2) ^ k) ha (le_of_eq hb1'.symm)
          hη0 (by linarith)
        exact le_trans h1' (le_trans
          (le_of_eq (one_mul (((1 / 4 : ℝ) * (1 / 2) ^ k) ^ a / a)).symm)
          (mul_le_mul_of_nonneg_right (le_max_left _ _) hXa))
  · rcases le_total 1 a with ha1 | ha1
    · have h1' := rightTail_ge1 a b ((1 / 4 : ℝ) * (1 / 2) ^ k) ha1 hb hη0 (by linarith)
        (by linarith)
      exact le_trans h1' (le_trans
        (le_of_eq (one_mul (((1 / 4 : ℝ) * (1 / 2) ^ k) ^ b / b)).symm)
        (mul_le_mul_of_nonneg_right (le_max_left _ _) hXb))
    · rcases lt_or_eq_of_le ha1 with ha1' | ha1'
      · have h1' := rightTail_lt1 a b ((1 / 4 : ℝ) * (1 / 2) ^ k) ha ha1' hb hη0
          (by linarith) (by linarith)
        rw [← mul_div_assoc'] at h1'
        exact le_trans h1' (mul_le_mul_of_nonneg_right hMa hXb)
      · have h1' := rightTail_ge1 a b ((1 / 4 : ℝ) * (1 / 2) ^ k) (le_of_eq ha1'.symm) hb
          hη0 (by linarith) (by linarith)
        exact le_trans h1' (le_trans
          (le_of_eq (one_mul (((1 / 4 : ℝ) * (1 / 2) ^ k) ^ b / b)).symm)
          (mul_le_mul_of_nonneg_right (le_max_left _ _) hXb))

/-- **任意精度可达（四义务之三，按合同调度）**：对每个 ε > 0 存在 (k, N, ρ)：
    ρ = εβ/8 ≤ εβ/4；两尾有证上界和 ≤ ρ/4（k 的指数衰减有限步达到）；
    N ≥ max(1, 4L̄/ρ)（固定 η 后单独取；L̄ 为 L 的有理上界，代数包围输入，
    见 `RpowRatEnclosureInput`）。 -/
theorem exists_precision_schedule (ε a b L̄ : ℚ) (hε : 0 < ε) (ha : 0 < a) (hb : 0 < b)
    (hL̄ : 0 < L̄) :
    ∃ (k N : ℕ) (ρ : ℚ), 0 < ρ ∧ ρ ≤ ε * b / 4 ∧
      (((max 1 ((1 / 2 : ℝ) ^ ((b:ℝ) - 1))) * (((1 / 4 : ℝ) ^ (a:ℝ)) / (a:ℝ))
          + (max 1 ((1 / 2 : ℝ) ^ ((a:ℝ) - 1))) * (((1 / 4 : ℝ) ^ (b:ℝ)) / (b:ℝ)))
          * ((1 / 2 : ℝ) ^ (min (a:ℝ) (b:ℝ))) ^ k ≤ (ρ:ℝ) / 4) ∧
      ((1:ℚ) ≤ N) ∧ ((4:ℚ) * L̄ / ρ ≤ N) := by
  have hp : (0:ℚ) < ε * b := mul_pos hε hb
  have hρq : (0:ℚ) < ε * b / 8 :=
    div_pos hp (by norm_num)
  have hρ4 : (0:ℚ) < ε * b / 8 / 4 :=
    div_pos hρq (by norm_num)
  obtain ⟨k, hk⟩ := exists_tail_budget (a:ℝ) (b:ℝ) ((ε * b / 8 / 4 : ℚ) : ℝ)
    (by exact_mod_cast ha) (by exact_mod_cast hb) (by exact_mod_cast hρ4)
  obtain ⟨N, hN1, hN2⟩ := exists_grid_N ((4:ℚ) * L̄ / (ε * b / 8))
  refine ⟨k, N, ε * b / 8, hρq, ?_, ?_, ?_⟩
  · rw [div_le_div_iff₀ (by norm_num : (0:ℚ) < 8) (by norm_num : (0:ℚ) < 4)]
    linarith
  · exact_mod_cast hk
  · exact_mod_cast hN1
  · exact_mod_cast hN2

/-! ## 四、有限混合（四义务之末：权重非负和 1；正权分量连续严格递增
    ⟹ F 连续严格递增、0<q<1 分位唯一；不取分量分位平均） -/

/-- 有限混合 CDF：F(x) = Σ_h w_h·F_h(x)（权重非负、和为 1）。 -/
def mixtureCdf {n : ℕ} (w : Fin n → ℚ) (F : Fin n → ℝ → ℝ) (x : ℝ) : ℝ :=
  ∑ h, (w h : ℝ) * F h x

/-- 混合连续（有限和，逐项连续）。 -/
theorem mixture_continuous {n : ℕ} (w : Fin n → ℚ) (F : Fin n → ℝ → ℝ)
    (hF : ∀ h, Continuous (F h)) : Continuous (mixtureCdf w F) :=
  continuous_finsetSum _ (fun h _ => continuous_const.mul (hF h))

/-- 混合端点：F(0) = 0、F(1) = 1。 -/
theorem mixture_endpoints {n : ℕ} (w : Fin n → ℚ) (F : Fin n → ℝ → ℝ)
    (hw : ∑ h, w h = 1) (hF0 : ∀ h, F h 0 = 0) (hF1 : ∀ h, F h 1 = 1) :
    mixtureCdf w F 0 = 0 ∧ mixtureCdf w F 1 = 1 := by
  constructor
  · show ∑ h, (w h : ℝ) * F h 0 = 0
    refine Finset.sum_eq_zero (fun h _ => ?_)
    rw [hF0 h, mul_zero]
  · show ∑ h, (w h : ℝ) * F h 1 = 1
    have h1 : ∀ h : Fin n, ((w h : ℚ) : ℝ) * F h 1 = ((w h : ℚ) : ℝ) := fun h => by
      rw [hF1 h, mul_one]
    rw [Finset.sum_congr rfl (fun h (_ : h ∈ Finset.univ) => h1 h)]
    rw [show (∑ h : Fin n, ((w h : ℚ) : ℝ)) = ((∑ h : Fin n, w h : ℚ) : ℝ) from
      (Rat.cast_sum Finset.univ w).symm, hw]
    norm_num

/-- 混合单调（逐项单调 × 非负权）。 -/
theorem mixture_mono {n : ℕ} (w : Fin n → ℚ) (F : Fin n → ℝ → ℝ)
    (hw : ∀ h, 0 ≤ w h) (hm : ∀ h, MonotoneOn (F h) (Set.Icc 0 1)) :
    MonotoneOn (mixtureCdf w F) (Set.Icc 0 1) := by
  intro x hx y hy hxy
  show ∑ h, (w h : ℝ) * F h x ≤ ∑ h, (w h : ℝ) * F h y
  refine Finset.sum_le_sum (fun h _ => ?_)
  exact mul_le_mul_of_nonneg_left (hm h hx hy hxy) (by exact_mod_cast hw h)

/-- **混合严格递增**：权重非负＋某正权分量在 [0,1] 严格递增
    （其密度 (0,1) 处处为正的推论，见 `bernCdf_strictMonoOn` 一类的实例）
    ⟹ 混合在 [0,1] 严格递增。 -/
theorem mixture_strictMonoOn {n : ℕ} (w : Fin n → ℚ) (F : Fin n → ℝ → ℝ)
    (hw : ∀ h, 0 ≤ w h) (j : Fin n) (hwj : 0 < w j)
    (hm : ∀ h, MonotoneOn (F h) (Set.Icc 0 1))
    (hs : StrictMonoOn (F j) (Set.Icc 0 1)) :
    StrictMonoOn (mixtureCdf w F) (Set.Icc 0 1) := by
  intro x hx y hy hxy
  have hnonneg : ∀ h, 0 ≤ (w h : ℝ) * (F h y - F h x) := fun h =>
    mul_nonneg (by exact_mod_cast hw h) (hm h hx hy hxy.le).le
  have hjlt : F j x < F j y := hs hx hy hxy
  have hpos : 0 < (w j : ℝ) * (F j y - F j x) :=
    mul_pos (by exact_mod_cast hwj) (by linarith)
  have hle : (w j : ℝ) * (F j y - F j x) ≤ ∑ h, (w h : ℝ) * (F h y - F h x) :=
    Finset.single_le_sum (f := fun h => (w h : ℝ) * (F h y - F h x))
      (fun h _ => hnonneg h) (Finset.mem_univ j)
  have hsum : (∑ h, (w h : ℝ) * F h y) - (∑ h, (w h : ℝ) * F h x)
      = ∑ h, (w h : ℝ) * (F h y - F h x) := by
    have h1 : (∑ h, (w h : ℝ) * (F h y - F h x)) + (∑ h, (w h : ℝ) * F h x)
        = ∑ h, (w h : ℝ) * F h y := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun h _ => by ring
    linarith
  show ∑ h, (w h : ℝ) * F h x < ∑ h, (w h : ℝ) * F h y
  linarith [hsum, hle, hpos]

/-- **分位存在唯一（合同）**：分量连续、权重非负和 1、端点 0/1、某正权分量
    严格递增 ⟹ 对 0 < q < 1 存在唯一 v ∈ (0,1) 使 F v = q
    （混合真分位；不是分量分位的平均）。 -/
theorem mixture_quantile_unique {n : ℕ} (w : Fin n → ℚ) (F : Fin n → ℝ → ℝ)
    (hFc : ∀ h, Continuous (F h))
    (hw : ∀ h, 0 ≤ w h) (hwsum : ∑ h, w h = 1)
    (hF0 : ∀ h, F h 0 = 0) (hF1 : ∀ h, F h 1 = 1)
    (j : Fin n) (hwj : 0 < w j) (hm : ∀ h, MonotoneOn (F h) (Set.Icc 0 1))
    (hs : StrictMonoOn (F j) (Set.Icc 0 1))
    (q : ℝ) (hq : 0 < q) (hq1 : q < 1) :
    ∃! v, v ∈ Set.Ioo 0 1 ∧ mixtureCdf w F v = q := by
  have hcont : ContinuousOn (mixtureCdf w F) (Set.Icc 0 1) :=
    (mixture_continuous w F hFc).continuousOn
  have hF0m : mixtureCdf w F 0 = 0 := (mixture_endpoints w F hwsum hF0 hF1).1
  have hF1m : mixtureCdf w F 1 = 1 := (mixture_endpoints w F hwsum hF0 hF1).2
  have hmem : q ∈ (mixtureCdf w F) '' Set.Icc (0:ℝ) 1 :=
    intermediate_value_Icc (show (0:ℝ) ≤ 1 from by norm_num) hcont
      (by rw [hF0m, hF1m]; exact ⟨hq.le, hq1.le⟩)
  obtain ⟨v, hv, hvq⟩ := hmem
  refine ⟨v, ⟨?_, ?_⟩, ?_⟩
  · have h0 : v ≠ 0 := by
      intro h
      rw [h, hF0m] at hvq
      exact hq.ne hvq.symm
    have h1' : v ≠ 1 := by
      intro h
      rw [h, hF1m] at hvq
      exact hq1.ne hvq.symm
    exact ⟨lt_of_le_of_ne hv.1 h0, lt_of_le_of_ne hv.2 h1'⟩
  · exact hvq
  · rintro u ⟨⟨hu0, hu1⟩, huu⟩
    refine hs.injOn (Set.mem_Icc.mpr ⟨hu0.le, hu1.le⟩) (Set.mem_Icc.mpr ⟨hv.1, hv.2⟩) ?_
    rw [huu, hvq]

/-- **不取分量分位平均（合同）**：反例 w = (1/2, 1/2)、F = (x, x²)
    （即 Beta(1,1) 与 Beta(2,1) 各半的混合），q = 1/2：
    真分位 v = (√5−1)/2（混合 (v+v²)/2 = 1/2），
    而分量分位 1/2 与 1/√2 的平均 = (1+√2)/4 ≠ v。 -/
theorem component_quantile_average_counterexample :
    (mixtureCdf ![1 / 2, 1 / 2] ![fun x : ℝ => x, fun x : ℝ => x * x]
        ((Real.sqrt 5 - 1) / 2) = 1 / 2)
      ∧ ((1 / 2 + 1 / Real.sqrt 2) / 2 ≠ (Real.sqrt 5 - 1) / 2) := by
  have hv : ((Real.sqrt 5 - 1) / 2) * ((Real.sqrt 5 - 1) / 2) = (3 - Real.sqrt 5) / 2 := by
    have h5 : Real.sqrt 5 * Real.sqrt 5 = 5 := Real.mul_self_sqrt (by norm_num)
    field_simp <;> nlinarith [h5]
  have hval : mixtureCdf ![1 / 2, 1 / 2] ![fun x : ℝ => x, fun x : ℝ => x * x]
      ((Real.sqrt 5 - 1) / 2) = 1 / 2 := by
    show ∑ i : Fin 2,
      ((![1 / 2, 1 / 2] i : ℚ) : ℝ)
        * (![fun x : ℝ => x, fun x : ℝ => x * x] i) ((Real.sqrt 5 - 1) / 2) = 1 / 2
    rw [Fin.sum_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [hv]
    norm_num
  refine ⟨hval, ?_⟩
  intro hcon
  have hsqrt2 : (1:ℝ) / Real.sqrt 2 = Real.sqrt 2 / 2 := by
    have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
    field_simp [h2] <;> linarith
  have h5lo : (223:ℝ) / 100 < Real.sqrt 5 := by
    rw [Real.lt_sqrt (by norm_num)]
    norm_num
  have h2hi : Real.sqrt 2 < (17:ℝ) / 12 := by
    rw [Real.sqrt_lt (by norm_num) (by norm_num)]
    norm_num
  exact absurd (show (3:ℝ) < 2 * Real.sqrt 5 - Real.sqrt 2 from by linarith [h5lo, h2hi])
    (by linarith [hcon, hsqrt2])

/-! ### 与 UnifiedBeta 双点缩区层（W1-5）的交接件 -/

/-- CDF 商包围交接件：把 [N_l/B_u, N_u/B_l] 写成 UnifiedBeta.Enc，供 W1-5 消费。 -/
def cdfEnc (N_l N_u B_l B_u : ℚ) : JurisLean.Seams.UnifiedBeta.Enc :=
  ⟨N_l / B_u, N_u / B_l⟩

/-- 交接件宽度：由 `quotientWidth` 的 ℚ 算术给 (cdfEnc …).width ≤ 2ρ/β。 -/
theorem cdfEnc_width (N_l N_u B_l B_u ρ β : ℚ) (hρ : 0 < ρ) (hβ : 0 < β)
    (hNl : 0 ≤ N_l) (hBlβ : β ≤ B_l) (hBl : 0 < B_l) (hBlu : B_l ≤ B_u)
    (hNel : N_l ≤ N_u) (hNB : N_l ≤ B_u)
    (hwl : N_u - N_l ≤ ρ) (hwd : B_u - B_l ≤ ρ) :
    (cdfEnc N_l N_u B_l B_u).width ≤ 2 * ρ / β :=
  quotientWidth N_l N_u B_l B_u ρ β hρ hβ hNl hBlβ hBl hBlu hNel hNB hwl hwd

/-- 整数段商包围的实层合法性：以 B := betaTwoConst(α−1,β−1) 实像为真分母
    （bernCdf = N/B，见 `bernCdf_eq_normed`），分子包围 [N_l, N_u]（下界截 0）
    与分母包围 [B_l, B_u] 给 N_l/B_u ≤ F ≤ N_u/B_l；ℚ 层收口由
    `bernCdf_rat_comparable` 执行。 -/
theorem cdfEnc_real (α β : ℕ) (hα : 1 ≤ α) (hβ : 1 ≤ β) (x : ℝ)
    (N_l N_u B_l B_u : ℝ)
    (hNl0 : 0 ≤ N_l)
    (hNl : N_l ≤ bernCdf α β x * ((UnifiedNeedlesS3a.betaTwoConst (α - 1) (β - 1) : ℚ) : ℝ))
    (hNu : bernCdf α β x * ((UnifiedNeedlesS3a.betaTwoConst (α - 1) (β - 1) : ℚ) : ℝ) ≤ N_u)
    (hBl : 0 < B_l)
    (hBlB : B_l ≤ ((UnifiedNeedlesS3a.betaTwoConst (α - 1) (β - 1) : ℚ) : ℝ))
    (hBuB : ((UnifiedNeedlesS3a.betaTwoConst (α - 1) (β - 1) : ℚ) : ℝ) ≤ B_u) :
    N_l / B_u ≤ bernCdf α β x ∧ bernCdf α β x ≤ N_u / B_l := by
  have hBpos : (0:ℝ) < ((UnifiedNeedlesS3a.betaTwoConst (α - 1) (β - 1) : ℚ) : ℝ) :=
    by exact_mod_cast UnifiedNeedlesS3a.betaTwoConst_pos (α - 1) (β - 1)
  have hBu : (0:ℝ) < B_u := lt_of_lt_of_le hBpos hBuB
  refine ⟨?_, ?_⟩
  · have hNpos : 0 ≤ bernCdf α β x := by
      by_contra hnc
      push_neg at hnc
      have hneg : bernCdf α β x * ((UnifiedNeedlesS3a.betaTwoConst (α - 1) (β - 1) : ℚ) : ℝ) < 0 :=
        mul_neg_of_neg_of_pos hnc hBpos
      exact absurd (le_trans hNl0 hNl) (by linarith)
    refine (div_le_iff₀ hBu).mpr ?_
    calc N_l ≤ bernCdf α β x * ((UnifiedNeedlesS3a.betaTwoConst (α - 1) (β - 1) : ℚ) : ℝ) := hNl
      _ ≤ bernCdf α β x * B_u := mul_le_mul_of_nonneg_right hBuB hNpos.le
  · refine (le_div_iff₀ hBl).mpr ?_
    calc bernCdf α β x * B_l
        ≤ bernCdf α β x * ((UnifiedNeedlesS3a.betaTwoConst (α - 1) (β - 1) : ℚ) : ℝ) :=
          mul_le_mul_of_nonneg_right hBlB hNpos.le
      _ ≤ N_u := hNu

end JurisLean.Seams.UnifiedBetaDomain
