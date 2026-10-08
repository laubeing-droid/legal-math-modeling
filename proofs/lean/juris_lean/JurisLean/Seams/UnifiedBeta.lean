import Mathlib.Tactic

/-
Unified beta enclosures, layer G (plan §7.4; I.4.10 L10 numeric fragment
for U17's `strict_comparison_eventually_found`).

Mirrors the Python contract `tools/unified_math_v2/unified/beta.py`
(double-point refinement): values are compared ONLY through rational
enclosures, and an undecided pair keeps refining until the enclosures
separate.

What this fragment proves, over an ABSTRACT refiner satisfying a
two-clause contract (soundness + width shrink by 2/3):

* `refN_sound`: iterated refinement never loses the enclosed value.
* `refN_width`: after n rounds the width is at most w0 * (2/3)^n.
* `pow_two_thirds_le` / `exists_pow_two_thirds_lt`: (2/3)^n can be made
  smaller than any positive rational (self-contained: (2/3)^(k+2) ≤
  1/(k+2), then Archimedeanness of ℚ).
* `cmpEnc_decided_is_true`: a decided comparison only reads the two
  enclosures' endpoints and is true of every enclosed pair.
* `strict_comparison_eventually_found`: x < y strictly apart, with sound
  enclosures refined under the contract, some round N decides `lt`
  (Δ/2 discipline: each side's width pushed below half the gap).

Scope, honestly: the CONCRETE Beta CDF enclosures (`cdf_enclosure_contains`,
quantile invariants, tail-width schedules) are the Python side's exact
arithmetic; a Lean mirror is future work.  This fragment proves the
decision/termination layer any such encloser must satisfy — the same
split as plan §7.4 (numeric content vs. comparison discipline).
-/

namespace JurisLean.Seams.UnifiedBeta

/-! ## 一、包围载体与抽象细化合同 -/

/-- 有理包围 [lo, hi]。 -/
structure Enc where
  /-- 下端。 -/
  lo : ℚ
  /-- 上端。 -/
  hi : ℚ
  deriving Repr

/-- 包围宽度。 -/
def Enc.width (e : Enc) : ℚ := e.hi - e.lo

/-- v 落在 e 内（健全包围）。 -/
def Enc.sound (e : Enc) (v : ℚ) : Prop := e.lo ≤ v ∧ v ≤ e.hi

/-- 细化合同：健全性保持＋每轮宽度收缩到 2/3 以下
    （主文 §7.4 的"宽度乘 2/3 证明总终止"）。 -/
structure RefinesContract (ref : Enc → Enc) : Prop where
  /-- 细化不丢被围值。 -/
  keeps : ∀ e v, e.sound v → (ref e).sound v
  /-- 宽度几何收缩。 -/
  shrinks : ∀ e, (ref e).width ≤ (2 / 3) * e.width

/-- n 轮细化（先递归后细化，使 refN (n+1) = ref (refN n) 逐字成立）。 -/
def refN (ref : Enc → Enc) : ℕ → Enc → Enc
  | 0, e => e
  | n + 1, e => ref (refN ref n e)

theorem refN_sound (hc : RefinesContract ref) :
    ∀ (n : ℕ) (e : Enc) (v : ℚ), e.sound v → (refN ref n e).sound v := by
  intro n
  induction n with
  | zero => intro e v h; exact h
  | succ m ih =>
      intro e v h
      exact ih (ref e) v (hc.keeps e v h)

theorem refN_width (hc : RefinesContract ref) :
    ∀ (n : ℕ) (e : Enc), (refN ref n e).width ≤ (2 / 3) ^ n * e.width := by
  intro n
  induction n with
  | zero => intro e; norm_num [refN, Enc.width]
  | succ m ih =>
      intro e
      have h1 := hc.shrinks (refN ref m e)
      have h2 := ih e
      rw [show (2 / 3 : ℚ) ^ (m + 1) = (2 / 3) ^ m * (2 / 3) by rw [pow_succ]]
      calc (refN ref (m + 1) e).width = (ref (refN ref m e)).width := rfl
        _ ≤ (2 / 3) * (refN ref m e).width := h1
        _ ≤ (2 / 3) * ((2 / 3) ^ m * e.width) :=
            mul_le_mul_of_nonneg_left h2 (by norm_num)
        _ = (2 / 3) ^ m * (2 / 3) * e.width := by ring

/-! ## 二、除法序小引理与 (2/3)^n 的自含收敛 -/

/-- 除法序引理：0 < A、0 < ε 且 1 < ε * A 时 1/A < ε（field_simp 收口，不依赖版本敏感引理名）。 -/
theorem one_div_lt_of_lt_mul {A ε : ℚ} (hA : 0 < A) (hε : 0 < ε)
    (h : 1 < ε * A) : 1 / A < ε := by
  by_contra hcon
  push_neg at hcon
  have h2 : ε * A ≤ (1 / A) * A := mul_le_mul_of_nonneg_right hcon hA.le
  have h3 : (1 / A) * A = 1 := by field_simp
  rw [h3] at h2
  linarith

/-- 几何收缩的自含上界：(2/3)^(k+2) ≤ 1/(k+2)（单起点归纳，步进无附加条件）。 -/
theorem pow_two_thirds_le :
    ∀ k : ℕ, (2 / 3 : ℚ) ^ (k + 2) ≤ 1 / ((k : ℚ) + 2) := by
  intro k
  induction k with
  | zero => norm_num
  | succ m ih =>
      have hm : (0 : ℚ) ≤ m := by exact_mod_cast Nat.zero_le m
      rw [show ((m + 1 : ℚ)) + 2 = (m : ℚ) + 3 from by push_cast; ring]
      rw [show (2 / 3 : ℚ) ^ (m + 3) = (2 / 3 : ℚ) ^ (m + 2) * (2 / 3) by rw [pow_succ]]
      calc (2 / 3 : ℚ) ^ (m + 2) * (2 / 3)
          ≤ (1 / ((m : ℚ) + 2)) * (2 / 3) :=
            mul_le_mul_of_nonneg_right ih (by norm_num)
        _ ≤ 1 / ((m : ℚ) + 3) := by
            have h2 : (0 : ℚ) < (m : ℚ) + 2 := by linarith
            have h3 : (0 : ℚ) < (m : ℚ) + 3 := by linarith
            field_simp
            linarith

/-- 对任意正有理 ε，存在 n 使 (2/3)^n < ε（自含上界＋Archimedeanness）。 -/
theorem exists_pow_two_thirds_lt (ε : ℚ) (hε : 0 < ε) :
    ∃ n : ℕ, (2 / 3 : ℚ) ^ n < ε := by
  obtain ⟨N, hN⟩ := exists_nat_gt (2 / ε)
  have hNq : (2 / ε) < (N : ℚ) := by exact_mod_cast hN
  have hkey : (2 : ℚ) < (N : ℚ) * ε := by
    by_contra hcon
    push_neg at hcon
    have h3 : (2 / ε) * ε < (N : ℚ) * ε :=
      mul_lt_mul_of_pos_right hNq hε
    have h4 : (2 / ε) * ε = 2 := by field_simp
    rw [h4] at h3
    linarith
  refine ⟨N + 2, ?_⟩
  have hb := pow_two_thirds_le N
  have hNpos : (0 : ℚ) < (N : ℚ) + 2 := by
    have := Nat.cast_nonneg (α := ℚ) N
    linarith
  have h1 : (1 : ℚ) < ε * ((N : ℚ) + 2) := by
    have h2e : (0 : ℚ) < 2 * ε := by linarith
    nlinarith
  exact lt_of_le_of_lt hb (one_div_lt_of_lt_mul hNpos hε h1)

/-! ## 三、双点判定（只读包围端点） -/

/-- 三值比较：包围分离出 lt/gt，否则 unknown（继续细化）。 -/
inductive Cmp : Type
  | lt | gt | unknown
  deriving DecidableEq, Repr

/-- 双点判定：只读两个包围的四个端点（主文 §7.4"双点判定只读 CDF/q 包围端点"）。 -/
def cmpEnc (a b : Enc) : Cmp :=
  if a.hi < b.lo then Cmp.lt
  else if b.hi < a.lo then Cmp.gt
  else Cmp.unknown

/-- **判定为真**：cmpEnc 给出 lt 时，任何被两包围分别容纳的 x < y。 -/
theorem cmpEnc_decided_is_true (a b : Enc) (x y : ℚ)
    (ha : a.sound x) (hb : b.sound y) (h : cmpEnc a b = Cmp.lt) : x < y := by
  unfold cmpEnc at h
  split at h
  · rename_i hlt
    obtain ⟨hal, hah⟩ := ha
    obtain ⟨hbl, hbh⟩ := hb
    linarith
  · split at h
    · exact absurd h (by simp)
    · exact absurd h (by simp)

/-! ## 四、严格比较最终被分离（Δ/2 纪律） -/

/-- 健全包围的宽度非负。 -/
theorem width_nonneg {e : Enc} {v : ℚ} (h : e.sound v) : 0 ≤ e.width := by
  obtain ⟨hlo, hhi⟩ := h
  unfold Enc.width
  linarith

/-- **严格比较最终找到**：x < y（真间隙），两包围健全且细化合同成立时，
    存在轮数 N 使双点判定为 lt——每侧宽度被压到间隙之半以下（Δ/2），
    上界经 (2/3)^N 几何收缩与 Archimedeanness 取得。 -/
theorem strict_comparison_eventually_found (ref : Enc → Enc)
    (hc : RefinesContract ref) (x y : ℚ) (hxy : x < y)
    (ea eb : Enc) (ha : ea.sound x) (hb : eb.sound y) :
    ∃ n : ℕ, cmpEnc (refN ref n ea) (refN ref n eb) = Cmp.lt := by
  have hδ : (0 : ℚ) < y - x := sub_pos.mpr hxy
  set A := ea.width + eb.width + 1 with hAdef
  have hwa0 : ea.width ≤ A := by linarith [width_nonneg hb]
  have hwb0 : eb.width ≤ A := by linarith [width_nonneg ha, width_nonneg hb]
  have hApos : (0 : ℚ) < A := by linarith [width_nonneg ha, width_nonneg hb]
  have h2A : (0 : ℚ) < 2 * A := by linarith
  have htarget : (0 : ℚ) < (y - x) / (2 * A) := div_pos hδ h2A
  obtain ⟨N, hN⟩ := exists_pow_two_thirds_lt _ htarget
  have hNkey : (2 / 3 : ℚ) ^ N * A < (y - x) / 2 := by
    have h1 := mul_lt_mul_of_pos_right hN hApos
    have h2 : (y - x) / (2 * A) * A = (y - x) / 2 := by field_simp
    rw [h2] at h1
    exact h1
  have hNN : (0 : ℚ) ≤ (2 / 3) ^ N := pow_nonneg (by norm_num) N
  have hwapos : (2 / 3 : ℚ) ^ N * ea.width < (y - x) / 2 :=
    lt_of_le_of_lt (mul_le_mul_of_nonneg_left hwa0 hNN) hNkey
  have hwbpos : (2 / 3 : ℚ) ^ N * eb.width < (y - x) / 2 :=
    lt_of_le_of_lt (mul_le_mul_of_nonneg_left hwb0 hNN) hNkey
  refine ⟨N, ?_⟩
  have hwa := refN_width hc N ea
  have hwb := refN_width hc N eb
  have hsa := refN_sound hc N ea x ha
  have hsb := refN_sound hc N eb y hb
  obtain ⟨hl_a, hh_a⟩ := hsa
  obtain ⟨hl_b, hh_b⟩ := hsb
  have e1 : (refN ref N ea).hi ≤ x + ((2 / 3 : ℚ) ^ N * ea.width) := by
    unfold Enc.width at hwa
    linarith
  have e2 : y - ((2 / 3 : ℚ) ^ N * eb.width) ≤ (refN ref N eb).lo := by
    unfold Enc.width at hwb
    linarith
  have hhi_a : (refN ref N ea).hi < (refN ref N eb).lo := by linarith
  unfold cmpEnc
  rw [if_pos hhi_a]

end JurisLean.Seams.UnifiedBeta
