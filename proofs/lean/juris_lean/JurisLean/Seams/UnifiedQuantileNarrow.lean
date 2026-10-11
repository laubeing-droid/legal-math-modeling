import Mathlib.Tactic
import Mathlib.Topology.Order.IntermediateValue
import JurisLean.Seams.UnifiedBeta
import JurisLean.Seams.UnifiedBetaDomain

/-
Unified quantile two-point narrowing (W1-5, R1 second wave), on the domain
fixed by review Codex R1 item 6: NOT "any monotone bounded CDF" but the
CONTINUOUS STRICTLY INCREASING Beta / finite-mixture domain equipped with a
VALID CDF ENCLOSER (plan W1-5 row; §7.4:459-476 of
docs/spec/20261007-统一法律数学模型_全量施工方案.md).

The four contracted obligations, on that domain:

1. EVERY STEP'S STRICT COMPARISON IS EVENTUALLY FOUND — `round_discovery`:
   with m1 = L+(U−L)/3, m2 = U−(U−L)/3, while L < U the Δ-argument
   (`round_gap_analysis`: Δ = F(m2)−F(m1) > 0, (q−F(m1))+(F(m2)−q) = Δ,
   hence at least one gap ≥ Δ/2) guarantees one strict comparison is TRUE,
   and the real-level enclosure eventuality (`hi_below_eventually` /
   `lo_above_eventually`) makes the refined enclosure DECIDE it at a finite
   refinement depth.  The decision language is UnifiedBeta's own:
   `cmpEnc`/`Cmp` read ONLY the four rational enclosure endpoints.
2. QUANTILE INVARIANT — `dirUpdate_invariant`: L/U move ONLY on certified
   strict comparisons (`certFound` ⟹ `certCertifies`, i.e. 有证才更新);
   every certified update keeps F(L) ≤ q ≤ F(U), keeps the true quantile
   v inside [L, U], and nests the interval.  Undecided refinement rounds
   KEEP the interval — this is exactly what a coarse "plateau reading" may
   NOT license (§7.4:475); the misuse is a counterexample:
   `coarse_update_deletes_quantile`.
3. TOTAL TERMINATION — `dirUpdate_width` + `exists_run_from` + `full_chain`:
   each certified round multiplies the width by ≤ 2/3; certificates never
   run out while L < U; so for any ε > 0 there is a finite run of rounds,
   each with its strict certificate actually FOUND at a finite refinement
   depth Rs j, ending with width ≤ ε.
4. BETA/MIXTURE INSTANTIATION — `bern_in_domain` / `mixture_in_domain`
   place the UnifiedBetaDomain instances inside the domain record
   `NarrowDomain`; `bern_cdfEnc_valid` lands the W1-4 handoff `cdfEnc` as a
   valid real-level encloser; `bern_full_chain` / `mixture_full_chain` are
   the end-to-end in-domain chains.

5. OUT-OF-DOMAIN DECLARATION — the review's [1/3, 2/3] plateau counterexample
   is preserved as an explicit theorem bundle (`plateau_out_of_domain`,
   `plateau_no_strict_certificate`, `plateau_quantile_not_unique`): a
   continuous CDF with endpoints 0/1 that is CONSTANT on [1/3, 2/3] has
   Δ = 0 at the initial double point (which lands exactly on the plateau
   endpoints), both strict comparisons fail FOREVER, and the q = 1/2
   quantile is not unique — the termination argument does NOT extend to
   flat / discrete / jumpy CDFs; a general quantile contract for those is a
   separate obligation and is not claimed here.

Scope, honestly: the EXECUTION-side rational arithmetic that PRODUCES the
enclosures (Bernstein grids, numerator/denominator enclosures, π/asin/rpow
isolations) is the W1-4 module's delivered content; here it enters only
through the interface `encValid` + `RealRefines` (value kept + width × 2/3),
which is §7.4's "细化至宽 ≤ 2^(−r)" contract shape.  `RealRefines` is a
real-level RESTATEMENT, not a consequence, of UnifiedBeta's
`RefinesContract`: `Enc.holds` is ℚ-valued while a CDF value may be
irrational, so ℚ-level soundness does not transfer to ℝ.  What IS consumed
from UnifiedBeta is the decision layer itself: `Enc`, `Enc.width`, `refN`,
`cmpEnc`, `Cmp` — `certFound` is literally a `cmpEnc … = Cmp.lt` decision on
refined enclosures against the point enclosure `Enc.mk q q`.  Instantiating
the general positive-rational-parameter leg of `henc` requires the W1-4
named hypothesis bundle `RpowRatEnclosureInput`; that open point lives in
UnifiedBetaDomain and is not re-opened here.  No new axioms, no `sorry`.
-/

namespace JurisLean.Seams.UnifiedQuantileNarrow

open JurisLean.Seams.UnifiedBeta
open JurisLean.Seams.UnifiedBetaDomain

/-! ## 一、缩区域与状态不变量 -/

/-- 缩区域（W1-5 的域）：F 在 [0,1] 连续、严格递增、端点 0/1——
    连续严格递增 Beta／有限混合域的抽象记录（实例见 §六）。 -/
structure NarrowDomain where
  /-- CDF 本体。 -/
  F : ℝ → ℝ
  /-- 连续性（分位存在性经 IVT 消费；缩区各步只用严格单调）。 -/
  cont : Continuous F
  /-- [0,1] 上严格递增（Δ > 0 与不变量回传的引擎）。 -/
  smono : StrictMonoOn F (Set.Icc (0:ℝ) 1)
  /-- 左端点。 -/
  zero : F 0 = 0
  /-- 右端点。 -/
  one : F 1 = 1

/-- 缩区状态不变量（合同 2 的 F-形）：0 ≤ L ≤ U ≤ 1 且 F L ≤ q ≤ F U。 -/
def StateOk (F : ℝ → ℝ) (q : ℚ) (L U : ℝ) : Prop :=
  (0:ℝ) ≤ L ∧ U ≤ 1 ∧ L ≤ U ∧ F L ≤ (q:ℝ) ∧ (q:ℝ) ≤ F U

/-- 严格递增域上的序回传：x, y ∈ [0,1] 且 F x < F y 时 x ≤ y
    （反证：y < x 给 F y < F x）。 -/
theorem strictMonoOn_lt_of_lt {F : ℝ → ℝ} (hsm : StrictMonoOn F (Set.Icc (0:ℝ) 1))
    {a b : ℝ} (ha : a ∈ Set.Icc (0:ℝ) 1) (hb : b ∈ Set.Icc (0:ℝ) 1) (h : F a < F b) :
    a ≤ b := by
  by_contra hcon
  push_neg at hcon
  exact absurd (hsm hb ha hcon) (by linarith)

/-- StateOk 的分位回传：区间态＋F v = q 给 v ∈ [L, U]（严格单调下与 F-形等价）。 -/
theorem stateOk_quantile_mem (F : ℝ → ℝ) (hsm : StrictMonoOn F (Set.Icc (0:ℝ) 1)) (q : ℚ)
    (v : ℝ) (hv0 : v ∈ Set.Icc (0:ℝ) 1) (hvq : F v = (q:ℝ))
    (L U : ℝ) (hok : StateOk F q L U) : v ∈ Set.Icc L U := by
  obtain ⟨hL0, hU1, hLU, hFL, hFU⟩ := hok
  have hFLv : F L ≤ F v := by rw [hvq]; exact hFL
  have hFvU : F v ≤ F U := by rw [hvq]; exact hFU
  have hLv : L ≤ v := by
    by_contra hcon
    push_neg at hcon
    exact absurd (hsm (Set.mem_Icc.mpr ⟨hL0, hLU⟩) hv0 hcon) (by linarith)
  have hvU : v ≤ U := by
    by_contra hcon
    push_neg at hcon
    exact absurd (hsm (Set.mem_Icc.mpr ⟨by linarith, hU1⟩) hv0 hcon) (by linarith)
  exact Set.mem_Icc.mpr ⟨hLv, hvU⟩

/-- 缩区域内必含分位（IVT）：dom 连续、端点 0/1、q ∈ [0,1] 时存在 v ∈ [0,1]
    使 F v = q（唯一性不在本件主张；混合唯一性已由 UnifiedBetaDomain
    `mixture_quantile_unique` 交付）。 -/
theorem narrow_quantile_mem (dom : NarrowDomain) (q : ℚ) (hq0 : (0:ℝ) ≤ q) (hq1 : q ≤ 1) :
    ∃ v : ℝ, v ∈ Set.Icc (0:ℝ) 1 ∧ dom.F v = (q:ℝ) := by
  obtain ⟨v, hv, hvq⟩ :=
    intermediate_value_Icc (show (0:ℝ) ≤ 1 from by norm_num) dom.cont.continuousOn
      (show (q:ℝ) ∈ Set.Icc (dom.F 0) (dom.F 1) from by
        rw [dom.zero, dom.one]; exact ⟨hq0, hq1⟩)
  exact ⟨v, hv, hvq⟩

/-! ## 二、双点几何与证书语言 -/

/-- 下三分点：m₁ = L + (U−L)/3（合同 §7.4:471 原式）。 -/
def mid1 (L U : ℝ) : ℝ := L + (U - L) / 3

/-- 上三分点：m₂ = U − (U−L)/3（合同 §7.4:471 原式）。 -/
def mid2 (L U : ℝ) : ℝ := U - (U - L) / 3

/-- 缩区方向：left＝有证 F m₁ < q 才取 L ← m₁；right＝有证 q < F m₂ 才取
    U ← m₂；both＝两比较同时成立时任选一项或同时收缩都安全（§7.4:471）。 -/
inductive Dir : Type where
  | left
  | right
  | both

/-- 单轮有证缩区的区间更新。 -/
def dirUpdate : Dir → ℝ → ℝ → ℝ × ℝ
  | Dir.left, L, U => (mid1 L U, U)
  | Dir.right, L, U => (L, mid2 L U)
  | Dir.both, L, U => (mid1 L U, mid2 L U)

theorem dirUpdate_left_fst (L U : ℝ) : (dirUpdate Dir.left L U).1 = mid1 L U := rfl

theorem dirUpdate_left_snd (L U : ℝ) : (dirUpdate Dir.left L U).2 = U := rfl

theorem dirUpdate_right_fst (L U : ℝ) : (dirUpdate Dir.right L U).1 = L := rfl

theorem dirUpdate_right_snd (L U : ℝ) : (dirUpdate Dir.right L U).2 = mid2 L U := rfl

theorem dirUpdate_both_fst (L U : ℝ) : (dirUpdate Dir.both L U).1 = mid1 L U := rfl

theorem dirUpdate_both_snd (L U : ℝ) : (dirUpdate Dir.both L U).2 = mid2 L U := rfl

/-- 真证书（实层语义）：left 表示 F m₁ < q 有证；right 表示 q < F m₂ 有证；
    both 表示两者同时有证。更新只在真证书在场时被允许（合同 2 的"有证才更新"）。 -/
def certCertifies (F : ℝ → ℝ) (q : ℚ) : Dir → ℝ → ℝ → Prop
  | Dir.left, L, U => F (mid1 L U) < (q:ℝ)
  | Dir.right, L, U => (q:ℝ) < F (mid2 L U)
  | Dir.both, L, U => F (mid1 L U) < (q:ℝ) ∧ (q:ℝ) < F (mid2 L U)

/-- UnifiedBeta 判定语言的最小读出引理：cmpEnc 给出 lt ⟺ 首包围上端低于
    次包围下端（只读两个端点——粗"平台读数"不是这个形状）。 -/
theorem cmpEnc_lt_iff (a b : Enc) : cmpEnc a b = Cmp.lt ↔ a.hi < b.lo := by
  constructor
  · intro h
    unfold cmpEnc at h
    split at h
    · exact h
    · split at h
      · exact absurd h (by simp)
      · exact absurd h (by simp)
  · intro h
    unfold cmpEnc
    rw [if_pos h]

/-- 找到的证书（可执行层）：把 m₁ 处的包围细化 r 轮后，对点包围 `Enc.mk q q`
    做 UnifiedBeta 的 `cmpEnc` 判定为 lt——即细化后的 b₁ < q。
    粗读数（未分离的包围）在此语言下不是证书，自动被排除。 -/
def certFound (F : ℝ → ℝ) (enc : ℝ → Enc) (ref : Enc → Enc) (q : ℚ) :
    Dir → ℝ → ℝ → ℕ → Prop
  | Dir.left, L, U, r => cmpEnc (refN ref r (enc (mid1 L U))) (Enc.mk q q) = Cmp.lt
  | Dir.right, L, U, r => cmpEnc (Enc.mk q q) (refN ref r (enc (mid2 L U))) = Cmp.lt
  | Dir.both, L, U, r =>
      cmpEnc (refN ref r (enc (mid1 L U))) (Enc.mk q q) = Cmp.lt
        ∧ cmpEnc (Enc.mk q q) (refN ref r (enc (mid2 L U))) = Cmp.lt

theorem certFound_left_iff (F : ℝ → ℝ) (enc : ℝ → Enc) (ref : Enc → Enc) (q : ℚ)
    (L U : ℝ) (r : ℕ) :
    certFound F enc ref q Dir.left L U r ↔ (refN ref r (enc (mid1 L U))).hi < q := by
  show cmpEnc (refN ref r (enc (mid1 L U))) (Enc.mk q q) = Cmp.lt
      ↔ (refN ref r (enc (mid1 L U))).hi < q
  rw [cmpEnc_lt_iff]
  rfl

theorem certFound_right_iff (F : ℝ → ℝ) (enc : ℝ → Enc) (ref : Enc → Enc) (q : ℚ)
    (L U : ℝ) (r : ℕ) :
    certFound F enc ref q Dir.right L U r ↔ q < (refN ref r (enc (mid2 L U))).lo := by
  show cmpEnc (Enc.mk q q) (refN ref r (enc (mid2 L U))) = Cmp.lt
      ↔ q < (refN ref r (enc (mid2 L U))).lo
  rw [cmpEnc_lt_iff]
  rfl

theorem certFound_both_iff (F : ℝ → ℝ) (enc : ℝ → Enc) (ref : Enc → Enc) (q : ℚ)
    (L U : ℝ) (r : ℕ) :
    certFound F enc ref q Dir.both L U r ↔
        (refN ref r (enc (mid1 L U))).hi < q ∧ q < (refN ref r (enc (mid2 L U))).lo := by
  show (cmpEnc (refN ref r (enc (mid1 L U))) (Enc.mk q q) = Cmp.lt
      ∧ cmpEnc (Enc.mk q q) (refN ref r (enc (mid2 L U))) = Cmp.lt) ↔ _
  rw [cmpEnc_lt_iff, cmpEnc_lt_iff]
  exact ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.1, h.2⟩⟩

/-! ## 三、每步严格比较可发现（合同 1） -/

/-- 实层包围有效：ℚ 端点的实像夹住实 CDF 值。注意 `UnifiedBeta.Enc.holds`
    是 ℚ 值层而 CDF 值可以是无理数，故另立实层谓词。 -/
def encValid (F : ℝ → ℝ) (e : Enc) (x : ℝ) : Prop := (e.lo : ℝ) ≤ F x ∧ F x ≤ (e.hi : ℝ)

/-- 实层细化合同（§7.4 "同时将两点 CDF 外包细化至宽 ≤ 2^(−r)" 的接口形）：
    细化不丢被围实值＋每轮宽度至多 ×2/3。 -/
structure RealRefines (ref : Enc → Enc) (F : ℝ → ℝ) : Prop where
  /-- 细化不丢被围实值。 -/
  keeps : ∀ e x, encValid F e x → encValid F (ref e) x
  /-- 宽度几何收缩。 -/
  shrinks : ∀ e, (ref e).width ≤ (2 / 3) * e.width

/-- n 轮细化的 ℚ 宽度界：≤ (2/3)ⁿ·初宽。 -/
theorem refN_widthQ (ref : Enc → Enc) (F : ℝ → ℝ) (hrc : RealRefines ref F)
    (n : ℕ) (e : Enc) : (refN ref n e).width ≤ (2 / 3 : ℚ) ^ n * e.width := by
  induction n with
  | zero => norm_num [refN, Enc.width]
  | succ m ih =>
      have h1 := hrc.shrinks (refN ref m e)
      rw [show (2 / 3 : ℚ) ^ (m + 1) = (2 / 3 : ℚ) ^ m * (2 / 3) from by rw [pow_succ]]
      calc (refN ref (m + 1) e).width = (ref (refN ref m e)).width := rfl
        _ ≤ (2 / 3) * (refN ref m e).width := h1
        _ ≤ (2 / 3) * ((2 / 3) ^ m * e.width) := mul_le_mul_of_nonneg_left ih (by norm_num)
        _ = (2 / 3) ^ m * (2 / 3) * e.width := by ring

/-- n 轮细化的实层宽度界（消费 `refN_widthQ` 的升型）。 -/
theorem refN_width_real (ref : Enc → Enc) (F : ℝ → ℝ) (hrc : RealRefines ref F)
    (n : ℕ) (e : Enc) :
    ((refN ref n e).width : ℝ) ≤ ((2:ℝ) / 3) ^ n * ((e.width : ℚ) : ℝ) := by
  have h4r : (((refN ref n e).width : ℚ) : ℝ)
      ≤ ((2:ℝ) / 3) ^ n * ((e.width : ℚ) : ℝ) := by
    have h := Rat.cast_le.mpr (refN_widthQ hrc n e)
    push_cast at h
    exact h
  have h6 : ((e.width : ℚ) : ℝ) = (e.hi : ℝ) - (e.lo : ℝ) := by push_cast [Enc.width]; ring
  have h7 : ((2:ℝ) / 3) ^ n * ((e.width : ℚ) : ℝ)
      ≤ ((2:ℝ) / 3) ^ n * ((e.hi : ℝ) - (e.lo : ℝ)) :=
    mul_le_mul_of_nonneg_left h6 (pow_nonneg (by norm_num) n)
  linarith

/-- 细化保持实层有效（沿 `RealRefines.keeps` 逐轮传递）。 -/
theorem refN_keeps (ref : Enc → Enc) (F : ℝ → ℝ) (hrc : RealRefines ref F)
    (n : ℕ) (e : Enc) (x : ℝ) (hx : encValid F e x) : encValid F (refN ref n e) x := by
  induction n with
  | zero => exact hx
  | succ m ih => exact hrc.keeps _ _ ih

/-- **左证终被发现**：F x < q 为真时，把 x 处的包围细化有限轮后必有
    `(refN ref n e).hi < q`（Δ/2 纪律的实层单向版：宽度几何收缩压过真间隙）。 -/
theorem hi_below_eventually (ref : Enc → Enc) (F : ℝ → ℝ) (hrc : RealRefines ref F)
    (e : Enc) (x : ℝ) (hx : encValid F e x) (q : ℚ) (hlt : F x < (q:ℝ)) :
    ∃ n : ℕ, (refN ref n e).hi < q := by
  have hwd : ((e.width : ℚ) : ℝ) = (e.hi : ℝ) - (e.lo : ℝ) := by push_cast [Enc.width]; ring
  have hw1 : (0:ℝ) < ((e.width : ℚ) : ℝ) + 1 := by rw [hwd]; linarith [hx.1, hx.2]
  have hgap : (0:ℝ) < (q:ℝ) - F x := sub_pos.mpr hlt
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (div_pos hgap hw1)
    (show ((2:ℝ) / 3) < 1 from by norm_num)
  have hmul : ((2:ℝ) / 3) ^ n * (((e.width : ℚ) : ℝ) + 1) < (q:ℝ) - F x :=
    (lt_div_iff₀ hw1).mp hn
  have hstep : ((2:ℝ) / 3) ^ n * ((e.width : ℚ) : ℝ)
      ≤ ((2:ℝ) / 3) ^ n * (((e.width : ℚ) : ℝ) + 1) :=
    mul_le_mul_of_nonneg_right (by linarith) (pow_nonneg (by norm_num) n)
  have hkey : ((2:ℝ) / 3) ^ n * ((e.width : ℚ) : ℝ) < (q:ℝ) - F x :=
    lt_of_le_of_lt hstep hmul
  have hkeep := refN_keeps ref F hrc n e x hx
  have hwid := refN_width_real ref F hrc n e
  have hwrel : ((refN ref n e).hi : ℝ)
      = ((refN ref n e).lo : ℝ) + ((refN ref n e).width : ℝ) := by
    push_cast [Enc.width]; ring
  refine ⟨n, Rat.cast_lt.mp ?_⟩
  linarith

/-- **右证终被发现**：q < F x 为真时，细化有限轮后必有 `q < (refN ref n e).lo`。 -/
theorem lo_above_eventually (ref : Enc → Enc) (F : ℝ → ℝ) (hrc : RealRefines ref F)
    (e : Enc) (x : ℝ) (hx : encValid F e x) (q : ℚ) (hgt : (q:ℝ) < F x) :
    ∃ n : ℕ, q < (refN ref n e).lo := by
  have hwd : ((e.width : ℚ) : ℝ) = (e.hi : ℝ) - (e.lo : ℝ) := by push_cast [Enc.width]; ring
  have hw1 : (0:ℝ) < ((e.width : ℚ) : ℝ) + 1 := by rw [hwd]; linarith [hx.1, hx.2]
  have hgap : (0:ℝ) < F x - (q:ℝ) := sub_pos.mpr hgt
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (div_pos hgap hw1)
    (show ((2:ℝ) / 3) < 1 from by norm_num)
  have hmul : ((2:ℝ) / 3) ^ n * (((e.width : ℚ) : ℝ) + 1) < F x - (q:ℝ) :=
    (lt_div_iff₀ hw1).mp hn
  have hstep : ((2:ℝ) / 3) ^ n * ((e.width : ℚ) : ℝ)
      ≤ ((2:ℝ) / 3) ^ n * (((e.width : ℚ) : ℝ) + 1) :=
    mul_le_mul_of_nonneg_right (by linarith) (pow_nonneg (by norm_num) n)
  have hkey : ((2:ℝ) / 3) ^ n * ((e.width : ℚ) : ℝ) < F x - (q:ℝ) :=
    lt_of_le_of_lt hstep hmul
  have hkeep := refN_keeps ref F hrc n e x hx
  have hwid := refN_width_real ref F hrc n e
  have hwrel : ((refN ref n e).lo : ℝ)
      = ((refN ref n e).hi : ℝ) - ((refN ref n e).width : ℝ) := by
    push_cast [Enc.width]; ring
  refine ⟨n, Rat.cast_lt.mp ?_⟩
  linarith

/-- **找到的证书即真证书**（有证才更新的合法性桥）：包围健全＋细化合同成立时，
    `certFound`（细化后端点分离）给出 `certCertifies`（真严格比较）。 -/
theorem certifies_of_certFound (F : ℝ → ℝ) (enc : ℝ → Enc) (ref : Enc → Enc) (q : ℚ)
    (henc : ∀ x, encValid F (enc x) x) (hrc : RealRefines ref F)
    (d : Dir) (L U : ℝ) (r : ℕ) (hf : certFound F enc ref q d L U r) :
    certCertifies F q d L U := by
  cases d with
  | left =>
      have h1 := (certFound_left_iff F enc ref q L U r).mp hf
      have hv := refN_keeps ref F hrc r (enc (mid1 L U)) (mid1 L U) (henc (mid1 L U))
      have hhi : ((refN ref r (enc (mid1 L U))).hi : ℝ) < (q:ℝ) := by exact_mod_cast h1
      exact lt_of_le_of_lt hv.2 hhi
  | right =>
      have h1 := (certFound_right_iff F enc ref q L U r).mp hf
      have hv := refN_keeps ref F hrc r (enc (mid2 L U)) (mid2 L U) (henc (mid2 L U))
      have hlo : (q:ℝ) < ((refN ref r (enc (mid2 L U))).lo : ℝ) := by exact_mod_cast h1
      exact lt_of_lt_of_le hlo hv.1
  | both =>
      have h1 := (certFound_both_iff F enc ref q L U r).mp hf
      have hv1 := refN_keeps ref F hrc r (enc (mid1 L U)) (mid1 L U) (henc (mid1 L U))
      have hv2 := refN_keeps ref F hrc r (enc (mid2 L U)) (mid2 L U) (henc (mid2 L U))
      have hhi : ((refN ref r (enc (mid1 L U))).hi : ℝ) < (q:ℝ) := by exact_mod_cast h1.1
      have hlo : (q:ℝ) < ((refN ref r (enc (mid2 L U))).lo : ℝ) := by exact_mod_cast h1.2
      exact ⟨lt_of_le_of_lt hv1.2 hhi, lt_of_lt_of_le hlo hv2.1⟩

/-- **Δ-论证（合同 §7.4:473 全文）**：L < U 时 Δ = F(m₂)−F(m₁) > 0、
    (q−F(m₁))+(F(m₂)−q) = Δ、至少一个间隔 ≥ Δ/2、从而至少一个严格比较为真。
    前三条是纯代数＋严格单调；末条由三歧分类收口。 -/
theorem round_gap_analysis (F : ℝ → ℝ) (hsm : StrictMonoOn F (Set.Icc (0:ℝ) 1)) (q : ℚ)
    (L U : ℝ) (hL0 : (0:ℝ) ≤ L) (hU1 : U ≤ 1) (hLU : L < U) :
    (0:ℝ) < F (mid2 L U) - F (mid1 L U)
      ∧ ((q:ℝ) - F (mid1 L U)) + (F (mid2 L U) - (q:ℝ)) = F (mid2 L U) - F (mid1 L U)
      ∧ ((F (mid2 L U) - F (mid1 L U)) / 2 ≤ (q:ℝ) - F (mid1 L U)
          ∨ (F (mid2 L U) - F (mid1 L U)) / 2 ≤ F (mid2 L U) - (q:ℝ))
      ∧ (F (mid1 L U) < (q:ℝ) ∨ (q:ℝ) < F (mid2 L U)) := by
  have hm12 : mid1 L U < mid2 L U := by
    simp only [mid1, mid2]; linarith
  have hmem1 : mid1 L U ∈ Set.Icc (0:ℝ) 1 :=
    ⟨by simp only [mid1]; linarith, by simp only [mid1]; linarith⟩
  have hmem2 : mid2 L U ∈ Set.Icc (0:ℝ) 1 :=
    ⟨by simp only [mid2]; linarith, by simp only [mid2]; linarith⟩
  have hF : F (mid1 L U) < F (mid2 L U) := hsm hmem1 hmem2 hm12
  have hsum : ((q:ℝ) - F (mid1 L U)) + (F (mid2 L U) - (q:ℝ))
      = F (mid2 L U) - F (mid1 L U) := by ring
  refine ⟨by linarith, hsum, ?_, ?_⟩
  · by_contra hcon
    push_neg at hcon
    obtain ⟨h1, h2⟩ := hcon
    linarith
  · rcases lt_or_ge (F (mid1 L U)) (q:ℝ) with h | h
    · exact Or.inl h
    · exact Or.inr (lt_of_le_of_lt h hF)

/-- **每步严格比较可发现（合同 1 总形）**：L < U 且包围器健全、细化合同成立时，
    存在方向 d 与有限细化轮数 r 使 `certFound F enc ref q d L U r`——
    双点缩区永不因"比较不可判"而卡死。 -/
theorem round_discovery (F : ℝ → ℝ) (hsm : StrictMonoOn F (Set.Icc (0:ℝ) 1)) (q : ℚ)
    (enc : ℝ → Enc) (henc : ∀ x, encValid F (enc x) x)
    (ref : Enc → Enc) (hrc : RealRefines ref F)
    (L U : ℝ) (hL0 : (0:ℝ) ≤ L) (hU1 : U ≤ 1) (hLU : L < U) :
    ∃ (d : Dir) (r : ℕ), certFound F enc ref q d L U r := by
  rcases (round_gap_analysis F hsm q L U hL0 hU1 hLU).2.2.2 with hleft | hright
  · obtain ⟨r, hr⟩ := hi_below_eventually ref F hrc (enc (mid1 L U)) (mid1 L U)
      (henc (mid1 L U)) q hleft
    exact ⟨Dir.left, r, (certFound_left_iff F enc ref q L U r).mpr hr⟩
  · obtain ⟨r, hr⟩ := lo_above_eventually ref F hrc (enc (mid2 L U)) (mid2 L U)
      (henc (mid2 L U)) q hright
    exact ⟨Dir.right, r, (certFound_right_iff F enc ref q L U r).mpr hr⟩

/-! ## 四、有证更新与分位不变量（合同 2） -/

/-- **有证缩区保不变量（合同 2 总形）**：真证书在场的更新保持
    StateOk、保持真分位 v 在区间内、并嵌套原区间。未分离轮不更新
    （`dirUpdate` 只在证书语言下动作；粗读数见 §七反例）。 -/
theorem dirUpdate_invariant (F : ℝ → ℝ) (hsm : StrictMonoOn F (Set.Icc (0:ℝ) 1)) (q : ℚ)
    (v : ℝ) (hv0 : v ∈ Set.Icc (0:ℝ) 1) (hvq : F v = (q:ℝ))
    (L U : ℝ) (hok : StateOk F q L U) (d : Dir) (hcert : certCertifies F q d L U) :
    StateOk F q (dirUpdate d L U).1 (dirUpdate d L U).2
      ∧ v ∈ Set.Icc (dirUpdate d L U).1 (dirUpdate d L U).2
      ∧ L ≤ (dirUpdate d L U).1 ∧ (dirUpdate d L U).2 ≤ U := by
  obtain ⟨hL0, hU1, hLU, hFL, hFU⟩ := hok
  have hvmem := stateOk_quantile_mem F hsm q v hv0 hvq L U hok
  cases d with
  | left =>
      rw [dirUpdate_left_fst, dirUpdate_left_snd]
      have hclt : F (mid1 L U) < (q:ℝ) := hcert
      have hm0 : (0:ℝ) ≤ mid1 L U := by simp only [mid1]; linarith
      have hmem : mid1 L U ∈ Set.Icc (0:ℝ) 1 := ⟨hm0, by simp only [mid1]; linarith⟩
      have hmv : mid1 L U ≤ v := strictMonoOn_lt_of_lt hsm hmem hv0 (by rw [hvq]; exact hclt)
      refine ⟨⟨hm0, hU1, by simp only [mid1]; linarith, hclt.le, hFU⟩, ⟨hmv, hvmem.2⟩,
        ⟨by simp only [mid1]; linarith, le_refl U⟩, le_refl U⟩
  | right =>
      rw [dirUpdate_right_fst, dirUpdate_right_snd]
      have hcgt : (q:ℝ) < F (mid2 L U) := hcert
      have hmu1 : mid2 L U ≤ 1 := by simp only [mid2]; linarith
      have hmem : mid2 L U ∈ Set.Icc (0:ℝ) 1 := ⟨by simp only [mid2]; linarith, hmu1⟩
      have hvm : v ≤ mid2 L U := strictMonoOn_lt_of_lt hsm hv0 hmem (by rw [hvq]; exact hcgt)
      refine ⟨⟨hL0, hmu1, by simp only [mid2]; linarith, hFL, hcgt.le⟩, ⟨hvmem.1, hvm⟩,
        ⟨le_refl L, by simp only [mid2]; linarith⟩, by simp only [mid2]; linarith⟩
  | both =>
      rw [dirUpdate_both_fst, dirUpdate_both_snd]
      have hclt : F (mid1 L U) < (q:ℝ) := hcert.1
      have hcgt : (q:ℝ) < F (mid2 L U) := hcert.2
      have hm0 : (0:ℝ) ≤ mid1 L U := by simp only [mid1]; linarith
      have hmu1 : mid2 L U ≤ 1 := by simp only [mid2]; linarith
      have hmem1 : mid1 L U ∈ Set.Icc (0:ℝ) 1 := ⟨hm0, by simp only [mid1]; linarith⟩
      have hmem2 : mid2 L U ∈ Set.Icc (0:ℝ) 1 := ⟨by simp only [mid2]; linarith, hmu1⟩
      have hmv : mid1 L U ≤ v := strictMonoOn_lt_of_lt hsm hmem1 hv0 (by rw [hvq]; exact hclt)
      have hvm : v ≤ mid2 L U := strictMonoOn_lt_of_lt hsm hv0 hmem2 (by rw [hvq]; exact hcgt)
      refine ⟨⟨hm0, hmu1, by simp only [mid1, mid2]; linarith, hclt.le, hcgt⟩,
        ⟨hmv, hvm⟩, ⟨by simp only [mid1]; linarith, by simp only [mid2]; linarith⟩,
        by simp only [mid2]; linarith⟩

/-- 有证缩区的宽度收缩：每轮至多 ×2/3（left/right 恰为 2/3，both 为 1/3）。 -/
theorem dirUpdate_width (d : Dir) (L U : ℝ) (hLU : L ≤ U) :
    (dirUpdate d L U).2 - (dirUpdate d L U).1 ≤ (2 / 3) * (U - L) := by
  cases d with
  | left =>
      have hw : (dirUpdate Dir.left L U).2 - (dirUpdate Dir.left L U).1
          = (2 / 3) * (U - L) := by
        show U - mid1 L U = (2 / 3) * (U - L)
        simp only [mid1]
        ring
      exact hw.le
  | right =>
      have hw : (dirUpdate Dir.right L U).2 - (dirUpdate Dir.right L U).1
          = (2 / 3) * (U - L) := by
        show mid2 L U - L = (2 / 3) * (U - L)
        simp only [mid2]
        ring
      exact hw.le
  | both =>
      have hw : (dirUpdate Dir.both L U).2 - (dirUpdate Dir.both L U).1
          = (1 / 3) * (U - L) := by
        show mid2 L U - mid1 L U = (1 / 3) * (U - L)
        simp only [mid1, mid2]
        ring
      refine hw.le.trans ?_
      linarith

/-! ## 五、总终止（合同 3） -/

/-- 缩区主循环的区间序列：从 (L, U) 出发按方向序列 Ds 折叠 `dirUpdate`。 -/
def runState (L U : ℝ) (Ds : ℕ → Dir) : ℕ → ℝ × ℝ
  | 0 => (L, U)
  | n + 1 => dirUpdate (Ds n) (runState L U Ds n).1 (runState L U Ds n).2

theorem runState_zero (L U : ℝ) (Ds : ℕ → Dir) : runState L U Ds 0 = (L, U) := rfl

/-- 方向序列的首端添加。 -/
def dirCons (d : Dir) (Ds : ℕ → Dir) : ℕ → Dir
  | 0 => d
  | j + 1 => Ds j

@[simp] theorem dirCons_zero (d : Dir) (Ds : ℕ → Dir) : dirCons d Ds 0 = d := rfl

@[simp] theorem dirCons_succ (d : Dir) (Ds : ℕ → Dir) (j : ℕ) :
    dirCons d Ds (j + 1) = Ds j := rfl

/-- 细化轮数序列的首端添加（与 `dirCons` 同构）。 -/
def dirConsN (r : ℕ) (Rs : ℕ → ℕ) : ℕ → ℕ
  | 0 => r
  | j + 1 => Rs j

@[simp] theorem dirConsN_zero (r : ℕ) (Rs : ℕ → ℕ) : dirConsN r Rs 0 = r := rfl

@[simp] theorem dirConsN_succ (r : ℕ) (Rs : ℕ → ℕ) (j : ℕ) :
    dirConsN r Rs (j + 1) = Rs j := rfl

/-- 序列平移引理：从更新后状态出发的运行＝原运行掐头。 -/
theorem runState_cons (L U : ℝ) (d : Dir) (Ds : ℕ → Dir) (n : ℕ) :
    runState (dirUpdate d L U).1 (dirUpdate d L U).2 Ds n
      = runState L U (dirCons d Ds) (n + 1) := by
  induction n with
  | zero => rfl
  | succ m ih => simp only [runState, dirCons, ih]

/-- **总终止（核心归纳）**：只要宽度目标 ((2/3)ᵏ·(U−L) ≤ ε) 成立，就存在有限
    缩区运行：每轮的严格证书都在有限细化深度被实际找到（非宣称），不变量与
    分位包含全程保持，终点宽度 ≤ ε。零轮情形与证书耗尽不可能（L < U 时
    `round_discovery` 永给新证书）都在构造内。 -/
theorem exists_run_from (F : ℝ → ℝ) (hsm : StrictMonoOn F (Set.Icc (0:ℝ) 1)) (q : ℚ)
    (enc : ℝ → Enc) (henc : ∀ x, encValid F (enc x) x)
    (ref : Enc → Enc) (hrc : RealRefines ref F)
    (ε : ℝ) (hε : 0 < ε) (v : ℝ) (hv0 : v ∈ Set.Icc (0:ℝ) 1) (hvq : F v = (q:ℝ)) :
    ∀ (k : ℕ) (L U : ℝ), StateOk F q L U →
      ((2:ℝ) / 3) ^ k * (U - L) ≤ ε →
      ∃ (n : ℕ) (Ds : ℕ → Dir) (Rs : ℕ → ℕ),
        (∀ j, j < n → certFound F enc ref q (Ds j) (runState L U Ds j).1
            (runState L U Ds j).2 (Rs j)) ∧
        (∀ j, j ≤ n → StateOk F q (runState L U Ds j).1 (runState L U Ds j).2
            ∧ v ∈ Set.Icc (runState L U Ds j).1 (runState L U Ds j).2) ∧
        ((runState L U Ds n).2 - (runState L U Ds n).1) ≤ ε := by
  intro k
  induction k with
  | zero =>
      intro L U hok hk
      refine ⟨0, fun _ => Dir.left, fun _ => 0, ?_, ?_, ?_⟩
      · intro j hj
        exact absurd hj (Nat.not_lt_zero j)
      · intro j hj
        rw [Nat.le_zero.mp hj, runState_zero]
        exact ⟨hok, stateOk_quantile_mem F hsm q v hv0 hvq L U hok⟩
      · rw [runState_zero]
        simpa using hk
  | succ k ih =>
      intro L U hok hk
      rcases le_or_gt (U - L) ε with hwle | hwlt
      · refine ⟨0, fun _ => Dir.left, fun _ => 0, ?_, ?_, ?_⟩
        · intro j hj
          exact absurd hj (Nat.not_lt_zero j)
        · intro j hj
          rw [Nat.le_zero.mp hj, runState_zero]
          exact ⟨hok, stateOk_quantile_mem F hsm q v hv0 hvq L U hok⟩
        · rw [runState_zero]
          exact hwle
      · have hpos : (0:ℝ) < U - L := by linarith
        have hLUlt : L < U := sub_pos.mp hpos
        obtain ⟨d, r, hcf⟩ :=
          round_discovery F hsm q enc henc ref hrc L U hok.1 hok.2.1 hLUlt
        have hcert := certifies_of_certFound F enc ref q henc hrc d L U r hcf
        obtain ⟨hok', -, -, -⟩ := dirUpdate_invariant F hsm q v hv0 hvq L U hok d hcert
        have htarget : ((2:ℝ) / 3) ^ k * ((dirUpdate d L U).2 - (dirUpdate d L U).1) ≤ ε := by
          calc ((2:ℝ) / 3) ^ k * ((dirUpdate d L U).2 - (dirUpdate d L U).1)
              ≤ ((2:ℝ) / 3) ^ k * ((2:ℝ) / 3 * (U - L)) :=
                mul_le_mul_of_nonneg_left (dirUpdate_width d L U hok.2.2.1)
                  (pow_nonneg (by norm_num) k)
            _ = ((2:ℝ) / 3) ^ (k + 1) * (U - L) := by rw [pow_succ]; ring
            _ ≤ ε := hk
        obtain ⟨n', Ds', Rs', hc', hok2, hw'⟩ :=
          ih (dirUpdate d L U).1 (dirUpdate d L U).2 hok' htarget
        refine ⟨n' + 1, dirCons d Ds', dirConsN r Rs', ?_, ?_, ?_⟩
        · intro j hj
          rcases Nat.eq_zero_or_pos j with hj0 | hj1
          · subst hj0
            show certFound F enc ref q d L U r
            exact hcf
          · obtain ⟨j', rfl⟩ : ∃ j' : ℕ, j = j' + 1 := ⟨j - 1, by omega⟩
            rw [← runState_cons, dirCons_succ, dirConsN_succ]
            exact hc' j' (by omega)
        · intro j hj
          rcases Nat.eq_zero_or_pos j with hj0 | hj1
          · subst hj0
            show StateOk F q L U ∧ v ∈ Set.Icc L U
            exact ⟨hok, stateOk_quantile_mem F hsm q v hv0 hvq L U hok⟩
          · obtain ⟨j', rfl⟩ : ∃ j' : ℕ, j = j' + 1 := ⟨j - 1, by omega⟩
            rw [← runState_cons, dirCons_succ, dirConsN_succ]
            exact hok2 j' (by omega)
        · rw [← runState_cons]
          exact hw'

/-- **端到端全链（合同 3＋4 合口）**：任一 `NarrowDomain` 域实例＋任意健全
    包围器＋任意满足细化合同的细化器下，对 0 ≤ q ≤ 1 与任意 ε > 0 存在有限
    缩区运行：分位 v 由 IVT 供给，每轮证书在有限细化深度实际找到，不变量与
    分位包含全程保持，终点宽度 ≤ ε。 -/
theorem full_chain (dom : NarrowDomain) (q : ℚ) (hq0 : (0:ℝ) ≤ q) (hq1 : q ≤ 1)
    (ε : ℚ) (hε : 0 < ε)
    (enc : ℝ → Enc) (henc : ∀ x, encValid dom.F (enc x) x)
    (ref : Enc → Enc) (hrc : RealRefines ref dom.F) :
    ∃ (n : ℕ) (Ds : ℕ → Dir) (Rs : ℕ → ℕ) (v : ℝ),
      v ∈ Set.Icc (0:ℝ) 1 ∧ dom.F v = (q:ℝ) ∧
      (∀ j, j < n → certFound dom.F enc ref q (Ds j) (runState 0 1 Ds j).1
          (runState 0 1 Ds j).2 (Rs j)) ∧
      (∀ j, j ≤ n → StateOk dom.F q (runState 0 1 Ds j).1 (runState 0 1 Ds j).2
          ∧ v ∈ Set.Icc (runState 0 1 Ds j).1 (runState 0 1 Ds j).2) ∧
      ((runState 0 1 Ds n).2 - (runState 0 1 Ds n).1) ≤ (ε:ℝ) := by
  obtain ⟨v, hv0, hvq⟩ := narrow_quantile_mem dom q hq0 hq1
  have hεr : (0:ℝ) < (ε:ℝ) := by exact_mod_cast hε
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one hεr
    (show ((2:ℝ) / 3) < 1 from by norm_num)
  have hinit : StateOk dom.F q 0 1 :=
    ⟨by norm_num, by norm_num, by norm_num,
      by rw [dom.zero]; exact hq0, by rw [dom.one]; exact hq1⟩
  have hentry : ((2:ℝ) / 3) ^ k * (1 - 0) ≤ (ε:ℝ) := by
    have h1 : ((2:ℝ) / 3) ^ k * (1 - 0) = ((2:ℝ) / 3) ^ k := by ring
    rw [h1]
    exact hk.le
  obtain ⟨n, Ds, Rs, hcerts, hoks, hwidth⟩ :=
    exists_run_from dom.F dom.smono q enc henc ref hrc (ε:ℝ) hεr v hv0 hvq k 0 1 hinit hentry
  exact ⟨n, Ds, Rs, v, hv0, hvq, hcerts, hoks, hwidth⟩

/-! ## 六、Beta／有限混合实例化（合同 4：域内实例全链） -/

/-- 整数 Bernstein CDF 是域内实例（四件套齐全，消费 UnifiedBetaDomain 交付）。 -/
theorem bern_in_domain (α β : ℕ) (hα : 1 ≤ α) (hβ : 1 ≤ β) : NarrowDomain :=
  ⟨bernCdf α β, bernCdf_continuous α β, bernCdf_strictMonoOn α β hα hβ,
    bernCdf_zero α β hα, bernCdf_one α β hβ⟩

/-- **W1-4 交接件落地**：`cdfEnc`（整数段商包围）是 bernCdf 的有效实层包围器——
    消费 `cdfEnc_real`，把 ℚ 端点的实像合法性逐 x 给出。 -/
theorem bern_cdfEnc_valid (α β : ℕ) (hα : 1 ≤ α) (hβ : 1 ≤ β) (x : ℝ)
    (n_l n_u b_l b_u : ℚ)
    (hNl0 : (0:ℝ) ≤ (n_l:ℝ))
    (hNl : (n_l:ℝ)
      ≤ bernCdf α β x * ((UnifiedNeedlesS3a.betaTwoConst (α - 1) (β - 1) : ℚ) : ℝ))
    (hNu : bernCdf α β x * ((UnifiedNeedlesS3a.betaTwoConst (α - 1) (β - 1) : ℚ) : ℝ)
      ≤ (n_u:ℝ))
    (hBl : (0:ℝ) < (b_l:ℝ))
    (hBlB : (b_l:ℝ) ≤ ((UnifiedNeedlesS3a.betaTwoConst (α - 1) (β - 1) : ℚ) : ℝ))
    (hBuB : ((UnifiedNeedlesS3a.betaTwoConst (α - 1) (β - 1) : ℚ) : ℝ) ≤ (b_u:ℝ)) :
    encValid (bernCdf α β) (cdfEnc n_l n_u b_l b_u) x := by
  have h := cdfEnc_real α β hα hβ x (n_l:ℝ) (n_u:ℝ) (b_l:ℝ) (b_u:ℝ)
    hNl0 hNl hNu hBl hBlB hBuB
  show ((n_l / b_u : ℚ) : ℝ) ≤ bernCdf α β x ∧ bernCdf α β x ≤ ((n_u / b_l : ℚ) : ℝ)
  push_cast
  exact h

/-- **Beta 端到端全链**：整数形状 bernCdf 上，健全包围器＋细化合同给
    `full_chain` 的全部结论（域实例由 `bern_in_domain` 供给）。 -/
theorem bern_full_chain (α β : ℕ) (hα : 1 ≤ α) (hβ : 1 ≤ β)
    (q : ℚ) (hq0 : (0:ℝ) ≤ q) (hq1 : q ≤ 1) (ε : ℚ) (hε : 0 < ε)
    (enc : ℝ → Enc) (henc : ∀ x, encValid (bernCdf α β) (enc x) x)
    (ref : Enc → Enc) (hrc : RealRefines ref (bernCdf α β)) :
    ∃ (n : ℕ) (Ds : ℕ → Dir) (Rs : ℕ → ℕ) (v : ℝ),
      v ∈ Set.Icc (0:ℝ) 1 ∧ bernCdf α β v = (q:ℝ) ∧
      (∀ j, j < n → certFound (bernCdf α β) enc ref q (Ds j) (runState 0 1 Ds j).1
          (runState 0 1 Ds j).2 (Rs j)) ∧
      (∀ j, j ≤ n → StateOk (bernCdf α β) q (runState 0 1 Ds j).1
          (runState 0 1 Ds j).2 ∧ v ∈ Set.Icc (runState 0 1 Ds j).1
          (runState 0 1 Ds j).2) ∧
      ((runState 0 1 Ds n).2 - (runState 0 1 Ds n).1) ≤ (ε:ℝ) :=
  full_chain (bern_in_domain α β hα hβ) q hq0 hq1 ε hε enc henc ref hrc

/-- 有限混合 CDF 是域内实例（权重非负和 1＋某正权分量严格递增；
    消费 UnifiedBetaDomain 的 mixture_* 四件）。 -/
theorem mixture_in_domain {n : ℕ} (w : Fin n → ℚ) (Fs : Fin n → ℝ → ℝ)
    (hFc : ∀ h, Continuous (Fs h)) (hw : ∀ h, 0 ≤ w h) (hwsum : ∑ h, w h = 1)
    (hF0 : ∀ h, Fs h 0 = 0) (hF1 : ∀ h, Fs h 1 = 1)
    (j : Fin n) (hwj : 0 < w j) (hm : ∀ h, MonotoneOn (Fs h) (Set.Icc (0:ℝ) 1))
    (hs : StrictMonoOn (Fs j) (Set.Icc (0:ℝ) 1)) : NarrowDomain :=
  ⟨mixtureCdf w Fs, mixture_continuous w Fs hFc,
    mixture_strictMonoOn w Fs hw j hwj hm hs,
    (mixture_endpoints w Fs hwsum hF0 hF1).1, (mixture_endpoints w Fs hwsum hF0 hF1).2⟩

/-- **混合端到端全链**：混合 CDF 上，健全包围器＋细化合同给 `full_chain` 的
    全部结论。 -/
theorem mixture_full_chain {n : ℕ} (w : Fin n → ℚ) (Fs : Fin n → ℝ → ℝ)
    (hFc : ∀ h, Continuous (Fs h)) (hw : ∀ h, 0 ≤ w h) (hwsum : ∑ h, w h = 1)
    (hF0 : ∀ h, Fs h 0 = 0) (hF1 : ∀ h, Fs h 1 = 1)
    (j : Fin n) (hwj : 0 < w j) (hm : ∀ h, MonotoneOn (Fs h) (Set.Icc (0:ℝ) 1))
    (hs : StrictMonoOn (Fs j) (Set.Icc (0:ℝ) 1))
    (q : ℚ) (hq0 : (0:ℝ) ≤ q) (hq1 : q ≤ 1) (ε : ℚ) (hε : 0 < ε)
    (enc : ℝ → Enc) (henc : ∀ x, encValid (mixtureCdf w Fs) (enc x) x)
    (ref : Enc → Enc) (hrc : RealRefines ref (mixtureCdf w Fs)) :
    ∃ (k : ℕ) (Ds : ℕ → Dir) (Rs : ℕ → ℕ) (v : ℝ),
      v ∈ Set.Icc (0:ℝ) 1 ∧ mixtureCdf w Fs v = (q:ℝ) ∧
      (∀ j, j < k → certFound (mixtureCdf w Fs) enc ref q (Ds j) (runState 0 1 Ds j).1
          (runState 0 1 Ds j).2 (Rs j)) ∧
      (∀ j, j ≤ k → StateOk (mixtureCdf w Fs) q (runState 0 1 Ds j).1
          (runState 0 1 Ds j).2 ∧ v ∈ Set.Icc (runState 0 1 Ds j).1
          (runState 0 1 Ds j).2) ∧
      ((runState 0 1 Ds k).2 - (runState 0 1 Ds k).1) ≤ (ε:ℝ) :=
  full_chain (mixture_in_domain w Fs hFc hw hwsum hF0 hF1 j hwj hm hs) q hq0 hq1 ε hε
    enc henc ref hrc

/-! ## 七、域外声明（评审第 6 条：[1/3, 2/3] 平台反例，必须保留） -/

/-- 平台 CDF（闭式，无分段）：F x = min(max((3/2)x − 1/2, 1/2), (3/2)x)。
    连续、端点 0/1，但在 [1/3, 2/3] 恒为 1/2（真实平坦段）——域外。 -/
noncomputable def plateauCdf (x : ℝ) : ℝ :=
  min (max ((3 / 2 : ℝ) * x - 1 / 2) (1 / 2)) ((3 / 2 : ℝ) * x)

theorem plateauCdf_continuous : Continuous plateauCdf := by
  show Continuous fun x => min (max ((3 / 2 : ℝ) * x - 1 / 2) (1 / 2)) ((3 / 2 : ℝ) * x)
  exact Continuous.min (Continuous.max (by fun_prop) continuous_const) (by fun_prop)

theorem plateauCdf_zero : plateauCdf 0 = 0 := by
  show min (max ((3 / 2 : ℝ) * 0 - 1 / 2) (1 / 2)) ((3 / 2 : ℝ) * 0) = 0
  have hz : ((3:ℝ) / 2 * 0) = 0 := by norm_num
  rw [hz]
  have hm : max ((0:ℝ) - 1 / 2) (1 / 2) = 1 / 2 :=
    le_antisymm (max_le (by norm_num) (le_refl _)) (le_max_right _ _)
  rw [hm]
  refine le_antisymm (min_le_right _ _) (le_min (by norm_num) (le_refl _))

theorem plateauCdf_one : plateauCdf 1 = 1 := by
  show min (max ((3 / 2 : ℝ) * 1 - 1 / 2) (1 / 2)) ((3 / 2 : ℝ) * 1) = 1
  have h1 : ((3:ℝ) / 2 * 1) = 3 / 2 := by norm_num
  have h2 : ((3:ℝ) / 2 * 1 - 1 / 2) = 1 := by rw [h1]; norm_num
  rw [h2, h1]
  have hm : max (1:ℝ) (1 / 2) = 1 :=
    le_antisymm (max_le (le_refl _) (by norm_num)) (le_max_left _ _)
  rw [hm]
  refine le_antisymm (min_le_left _ _) (le_min (le_refl _) (by norm_num))

theorem plateauCdf_flat (x : ℝ) (hx : x ∈ Set.Icc (1 / 3 : ℝ) (2 / 3 : ℝ)) :
    plateauCdf x = 1 / 2 := by
  obtain ⟨h1, h2⟩ := hx
  show min (max ((3 / 2 : ℝ) * x - 1 / 2) (1 / 2)) ((3 / 2 : ℝ) * x) = 1 / 2
  refine le_antisymm ?_ ?_
  · exact le_trans (min_le_left _ _) (max_le (by linarith) (le_refl _))
  · exact le_min (le_max_right _ _) (by linarith)

theorem plateauCdf_not_strictMonoOn : ¬ StrictMonoOn plateauCdf (Set.Icc (0:ℝ) 1) := by
  intro h
  have h13 : plateauCdf ((1:ℝ) / 3) = 1 / 2 := plateauCdf_flat _ ⟨by norm_num, by norm_num⟩
  have h12 : plateauCdf ((1:ℝ) / 2) = 1 / 2 := plateauCdf_flat _ ⟨by norm_num, by norm_num⟩
  have hlt : plateauCdf ((1:ℝ) / 3) < plateauCdf ((1:ℝ) / 2) :=
    h (Set.mem_Icc.mpr ⟨by norm_num, by norm_num⟩)
      (Set.mem_Icc.mpr ⟨by norm_num, by norm_num⟩) (by norm_num)
  rw [h13, h12] at hlt
  exact lt_irrefl (1 / 2 : ℝ) hlt

/-- 平台端点上 Δ = 0：初始双点 m₁ = 1/3、m₂ = 2/3 恰为平台端点，
    F(m₂) − F(m₁) = 0——终止论证的第一前提失效。 -/
theorem plateau_delta_zero : plateauCdf ((2:ℝ) / 3) - plateauCdf ((1:ℝ) / 3) = 0 := by
  have h1 : plateauCdf ((2:ℝ) / 3) = 1 / 2 := plateauCdf_flat _ ⟨by norm_num, by norm_num⟩
  have h2 : plateauCdf ((1:ℝ) / 3) = 1 / 2 := plateauCdf_flat _ ⟨by norm_num, by norm_num⟩
  rw [h1, h2]
  norm_num

/-- 平台上两处严格比较永不成立：F(1/3) = 1/2 = F(2/3)，故 b₁ < q 与
    a₂ > q 都不可证——细化包围到任意宽度都无济于事（评审第 6 条反例核心）。 -/
theorem plateau_no_strict_certificate :
    ¬ (plateauCdf ((1:ℝ) / 3) < (1 / 2 : ℝ) ∨ (1 / 2 : ℝ) < plateauCdf ((2:ℝ) / 3)) := by
  have h1 : plateauCdf ((1:ℝ) / 3) = 1 / 2 := plateauCdf_flat _ ⟨by norm_num, by norm_num⟩
  have h2 : plateauCdf ((2:ℝ) / 3) = 1 / 2 := plateauCdf_flat _ ⟨by norm_num, by norm_num⟩
  rintro (h | h)
  · rw [h1] at h
    exact lt_irrefl (1 / 2 : ℝ) h
  · rw [h2] at h
    exact lt_irrefl (1 / 2 : ℝ) h

/-- 平台段上 q = 1/2 的分位不唯一：[1/3, 2/3] 全段都是分位——
    "唯一分位 v" 语义在该 CDF 上失效，广义分位须另立合同。 -/
theorem plateau_quantile_not_unique :
    ∃ u v : ℝ, u ∈ Set.Icc (1 / 3 : ℝ) (2 / 3 : ℝ) ∧ v ∈ Set.Icc (1 / 3 : ℝ) (2 / 3 : ℝ)
      ∧ u ≠ v ∧ plateauCdf u = 1 / 2 ∧ plateauCdf v = 1 / 2 := by
  refine ⟨1 / 3, 2 / 3, ⟨by norm_num, by norm_num⟩, ⟨by norm_num, by norm_num⟩,
    (by norm_num : (1:ℝ) / 3 ≠ 2 / 3), ?_, ?_⟩
  · exact plateauCdf_flat _ ⟨by norm_num, by norm_num⟩
  · exact plateauCdf_flat _ ⟨by norm_num, by norm_num⟩

/-- **域外声明总形（评审第 6 条）**：plateauCdf 具备 CDF 的一切"良"性质
    （连续、端点 0/1），但严格递增失效，Δ = 0，两处严格比较永不成立，
    分位不唯一——双点缩区的终止论证不外推到平坦段／离散／跳跃 CDF；
    一般广义分位须另立合同，不得沿用本件终止证明。 -/
theorem plateau_out_of_domain :
    Continuous plateauCdf ∧ plateauCdf 0 = 0 ∧ plateauCdf 1 = 1
      ∧ (∀ x ∈ Set.Icc (1 / 3 : ℝ) (2 / 3 : ℝ), plateauCdf x = 1 / 2)
      ∧ ¬ StrictMonoOn plateauCdf (Set.Icc (0:ℝ) 1)
      ∧ plateauCdf ((2:ℝ) / 3) - plateauCdf ((1:ℝ) / 3) = 0
      ∧ ¬ (plateauCdf ((1:ℝ) / 3) < (1 / 2 : ℝ) ∨ (1 / 2 : ℝ) < plateauCdf ((2:ℝ) / 3)) :=
  ⟨plateauCdf_continuous, plateauCdf_zero, plateauCdf_one, plateauCdf_flat,
    plateauCdf_not_strictMonoOn, plateau_delta_zero, plateau_no_strict_certificate⟩

/-- **粗"平台读数"不作更新依据（域内反例，§7.4:475）**：F = id（域内！）、
    q = 1/2、真分位 1/2。初始双点 m₁ = 1/3、m₂ = 2/3 处的粗读数（宽 1 的
    包围 [0,1]）既不能证 F m₁ < q 也不能证 q < F m₂；若无证地把 U 取为 m₁，
    新区间 [0, 1/3] 排除真分位 1/2 且不变量 q ≤ F U 失败——所以本件只认
    `certFound`（细化后端点分离）这一种证据，其安全性由 `dirUpdate_invariant`
    与 `certifies_of_certFound` 给出。 -/
theorem coarse_update_deletes_quantile :
    StrictMonoOn id (Set.Icc (0:ℝ) 1)
      ∧ ((1:ℝ) / 2 ∈ Set.Icc (0:ℝ) 1 ∧ id ((1:ℝ) / 2) = (1:ℝ) / 2)
      ∧ ¬((1:ℝ) / 2 ≤ id ((1:ℝ) / 3))
      ∧ ¬((1:ℝ) / 2 ∈ Set.Icc (0:ℝ) ((1:ℝ) / 3)) := by
  refine ⟨fun _ _ _ _ h => h, ⟨by norm_num, rfl⟩, ?_, ?_⟩
  · intro hcon
    have hb : id ((1:ℝ) / 3) = (1:ℝ) / 3 := rfl
    rw [hb] at hcon
    norm_num at hcon
  · intro hcon
    have hb : id ((1:ℝ) / 3) = (1:ℝ) / 3 := rfl
    rw [hb] at hcon
    obtain ⟨_, h2⟩ := Set.mem_Icc.mp hcon
    norm_num at h2

end JurisLean.Seams.UnifiedQuantileNarrow
