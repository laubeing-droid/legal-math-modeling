import Mathlib.Tactic
import JurisLean.FullMath.Numeric.Quantities

/-
Unified quantities, layer F (plan §6.1 priority waterfall / T25 correction;
I.4.8 L08, fragment for U14–U16).

Mirrors the Python contract `tools/unified_math_v2/unified/quantities.py`
(waterfall): obligations with a total order are paid in sequence, each step
allocates min(remaining, debt).

* U14 conservation: Σ allocations + remaining = payment (same family as
  `JurisLean.FullMath.Numeric` residual/covered/uncovered N01 and the
  `AllocLegal` per-payment bound — this file proves that list-level
  premise; the aggregated `allocation_total_bound` stays where it is).
* T25: a strictly positive allocation at any later position forces every
  earlier position to be fully paid (`waterfall_t25_prefix`) — the
  corrected reading (junior allocation > 0 ⇒ all seniors cleared).
* U15 joint exclusion: allocations individually within each debt but
  jointly exceeding the payment are NOT waterfall outputs — witnessed by
  `joint_overallocation_excluded` ([10,10] pays 15 → [10,5], never [10,10]).
* U16 dependence: outputs move with the upstream payment and debt schedule
  (fixed-output gates cannot pass the total correspondence) — witnessed by
  `waterfall_depends_on_payment` / `waterfall_depends_on_debt`.
* Homogeneity: scaling every debt and the payment by c ≥ 0 scales the
  schedule (units read one upstream basis; no silent re-linearization).

Scope, honestly: the linear waterfall only.  Nonlinear objectives go to
the dedicated CAD track (C0–C5) and are not linearized here; joint-shares
exposure (`joint_shares_bound`) stays in `FullMath.Numeric.Quantities`.
-/

namespace JurisLean.Seams.UnifiedQuantities

/-! ## 一、瀑布与剩余（与 Python 同合同） -/

/-- 优先瀑布：按顺位依次扣减；每步分配＝min(剩余付款, 本顺位债额)。 -/
def waterfall : List ℚ → ℚ → List ℚ
  | [], _ => []
  | d :: ds, p => min p d :: waterfall ds (p - min p d)

/-- 瀑布后的剩余付款。 -/
def remainingAfter : List ℚ → ℚ → ℚ
  | [], p => p
  | d :: ds, p => remainingAfter ds (p - min p d)

theorem waterfall_cons (d : ℚ) (ds : List ℚ) (p : ℚ) :
    waterfall (d :: ds) p = min p d :: waterfall ds (p - min p d) := rfl

theorem remainingAfter_cons (d : ℚ) (ds : List ℚ) (p : ℚ) :
    remainingAfter (d :: ds) p = remainingAfter ds (p - min p d) := rfl

/-- 债表非负时，付款为零 ⇒ 分配全零。 -/
theorem waterfall_zero :
    ∀ (L : List ℚ), (∀ d ∈ L, 0 ≤ d) →
      waterfall L 0 = L.map (fun _ => (0 : ℚ)) := by
  intro L
  induction L with
  | nil => intro _; rfl
  | cons d ds ih =>
      intro hnn
      rw [waterfall_cons, min_eq_left (hnn d (by simp)),
          ih (fun x hx => hnn x (by simp [hx]))]
      rfl

/-- 瀑布输出非负（债表与付款非负时）。 -/
theorem waterfall_mem_nonneg :
    ∀ (L : List ℚ), (∀ d ∈ L, 0 ≤ d) →
      ∀ p : ℚ, 0 ≤ p → ∀ a ∈ waterfall L p, 0 ≤ a := by
  intro L
  induction L with
  | nil => intro _ p _ a ha; simp [waterfall] at ha
  | cons d ds ih =>
      intro hnn p hp a ha
      simp only [waterfall_cons, List.mem_cons] at ha
      rcases ha with rfl | ha
      · exact le_min hp (hnn d (by simp))
      · exact ih (fun x hx => hnn x (by simp [hx])) (p - min p d)
          (by have := min_le_left p d; linarith) a ha

/-! ## 二、守恒与界（U14） -/

/-- **守恒**：分配和＋剩余＝付款。 -/
theorem waterfall_conservation :
    ∀ (L : List ℚ) (p : ℚ), (waterfall L p).sum + remainingAfter L p = p := by
  intro L
  induction L with
  | nil => intro p; simp [waterfall, remainingAfter]
  | cons d ds ih =>
      intro p
      rw [waterfall_cons, remainingAfter_cons, List.sum_cons, ih (p - min p d)]
      by_cases h : p ≤ d
      · rw [min_eq_left h]; ring
      · rw [min_eq_right (by linarith : d ≤ p)]; ring

/-- 剩余非负（付款非负时）。 -/
theorem remainingAfter_nonneg :
    ∀ (L : List ℚ) (p : ℚ), 0 ≤ p → 0 ≤ remainingAfter L p := by
  intro L
  induction L with
  | nil => intro p hp; exact hp
  | cons d ds ih =>
      intro p hp
      exact ih (p - min p d) (by have := min_le_left p d; linarith)

/-- **总额界**：分配和不超过付款（`AllocLegal` 逐付款前提的列表形）。 -/
theorem waterfall_sum_le (L : List ℚ) (p : ℚ) (h0 : 0 ≤ p) :
    (waterfall L p).sum ≤ p := by
  have hc := waterfall_conservation L p
  have hr := remainingAfter_nonneg L p h0
  linarith

/-! ## 三、T25：后顺位获正额 ⇒ 前顺位全清偿 -/

/-- 非负表的尾段和不超过全表和（前缀元素非负）。 -/
theorem drop_sum_le_sum :
    ∀ (l : List ℚ), (∀ a ∈ l, 0 ≤ a) →
      ∀ k : ℕ, (List.drop k l).sum ≤ l.sum := by
  intro l
  induction l with
  | nil => intro _ k; simp
  | cons a as ih =>
      intro hnn k
      cases k with
      | zero => simp
      | succ k =>
          rw [List.drop_succ, List.sum_cons]
          exact le_trans (ih (fun x hx => hnn x (by simp [hx])) k)
            (by linarith [hnn a (by simp)])

/-- 头步全清偿的判别：后续分配和为正 ⇒ 本步 min p d = d。 -/
theorem waterfall_head_full_of_tail_positive (d : ℚ) (ds : List ℚ) (p : ℚ)
    (hnn : ∀ x ∈ ds, 0 ≤ x)
    (hpos : 0 < (waterfall ds (p - min p d)).sum) : min p d = d := by
  by_cases h : p ≤ d
  · by_cases heq : p = d
    · rw [heq]; exact min_self d
    · exfalso
      have hmin : min p d = p := min_eq_left h
      rw [hmin, sub_self] at hpos
      rw [waterfall_zero ds hnn] at hpos
      simp at hpos
  · exact min_eq_right (by linarith : d ≤ p)

/-- **T25 前缀形**：第 k 位之后仍有正分配 ⇒ 前 k 位逐项全清偿
    （waterfall 的前 k 项＝债表前 k 项）。 -/
theorem waterfall_t25_prefix :
    ∀ (L : List ℚ), (∀ d ∈ L, 0 ≤ d) → ∀ (p : ℚ) (k : ℕ),
      0 < (List.drop k (waterfall L p)).sum →
        List.take k (waterfall L p) = List.take k L := by
  intro L
  induction L with
  | nil => intro _ p k hk; simp [waterfall] at hk
  | cons d ds ih =>
      intro hnn p k hk
      have hnnds : ∀ x ∈ ds, 0 ≤ x := fun x hx => hnn x (by simp [hx])
      have hhp : 0 ≤ p - min p d := by have := min_le_left p d; linarith
      have hout : ∀ a ∈ waterfall ds (p - min p d), 0 ≤ a :=
        waterfall_mem_nonneg ds hnnds (p - min p d) hhp
      have hsub : (List.drop k (waterfall ds (p - min p d))).sum
          ≤ (waterfall ds (p - min p d)).sum :=
        drop_sum_le_sum _ hout k
      have hpos : 0 < (waterfall ds (p - min p d)).sum := by linarith
      cases k with
      | zero => rfl
      | succ k =>
          simp only [waterfall_cons, List.drop_succ, List.take_succ_cons] at hk ⊢
          rw [ih hnnds (p - min p d) k hk,
              waterfall_head_full_of_tail_positive d ds p hnnds hpos]

/-! ## 四、联合排除与依赖性（U15/U16 反例见证） -/

/-- **联合超额排除**：单项各自在债额内但联合超过付款的解不是瀑布输出
    （[10,10] 付 15 给 [10,5]，绝不给 [10,10]）。 -/
theorem joint_overallocation_excluded :
    waterfall [10, 10] 15 = [10, 5] := by
  have h1 : min (15 : ℚ) 10 = 10 := min_eq_right (by norm_num)
  have h2 : min ((15 : ℚ) - 10) 10 = 15 - 10 := min_eq_left (by norm_num)
  rw [waterfall_cons, h1, waterfall_cons, h2]
  simp only [waterfall]
  norm_num

/-- **依赖付款**：上游付款变化必须改变允许域（固定输出不得通过总对应）。 -/
theorem waterfall_depends_on_payment :
    waterfall [10, 10] 15 ≠ waterfall [10, 10] 20 := by
  have h20 : waterfall [10, 10] 20 = [10, 10] := by
    have h1 : min (20 : ℚ) 10 = 10 := min_eq_right (by norm_num)
    have h2 : min ((20 : ℚ) - 10) 10 = 20 - 10 := min_eq_left (by norm_num)
    rw [waterfall_cons, h1, waterfall_cons, h2]
    simp only [waterfall]
    norm_num
  rw [joint_overallocation_excluded, h20]
  decide

/-- **依赖债表**：债额变化必须改变允许域。 -/
theorem waterfall_depends_on_debt :
    waterfall [10, 10] 15 ≠ waterfall [10, 8] 15 := by
  have h8 : waterfall [10, 8] 15 = [8, 7] := by
    have h1 : min (15 : ℚ) 8 = 8 := min_eq_right (by norm_num)
    have h2 : min ((15 : ℚ) - 8) 8 = 15 - 8 := min_eq_left (by norm_num)
    rw [waterfall_cons, h1, waterfall_cons, h2]
    simp only [waterfall]
    norm_num
  rw [joint_overallocation_excluded, h8]
  decide

/-! ## 五、齐次性（同一上游依据／单位不重算） -/

/-- **齐次**：债表与付款同乘 c ≥ 0 ⇒ 分配表同乘 c（单位换算不改变瀑布结构）。 -/
theorem waterfall_homogeneous (c : ℚ) (hc : 0 ≤ c) :
    ∀ (L : List ℚ) (p : ℚ), waterfall (L.map (fun d => d * c)) (p * c)
      = (waterfall L p).map (fun a => a * c) := by
  intro L
  induction L with
  | nil => intro p; rfl
  | cons d ds ih =>
      intro p
      have hmin : min (p * c) (d * c) = min p d * c := by
        by_cases h : p ≤ d
        · rw [min_eq_left h, min_eq_left (mul_le_mul_of_nonneg_right h hc)]
        · rw [min_eq_right (by linarith : d ≤ p),
            min_eq_right (mul_le_mul_of_nonneg_right (by linarith : d ≤ p) hc)]
      simp only [List.map_cons, waterfall_cons, hmin, sub_mul]
      rw [ih (p - min p d)]
      try rfl

end JurisLean.Seams.UnifiedQuantities
