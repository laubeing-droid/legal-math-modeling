import Mathlib.Tactic
import JurisLean.Seams.Uncertainty

/-!
# XU 族七针（附录 I.13 逐名承接，UnifiedNeedlesXU）

中文说明：承接 `docs/spec/20261007-统一法律数学模型_附录I_Lean施工明细.md` §I.13 XU 族
七针（#53-#59）。每针以**原验收名**命名，"拟"合同写成显式前提的定理；可复用锚
（`Seams/Uncertainty.lean:134` `finite_positive_support_truth_bridge`、`:170`
`finite_positive_support_truth_mass_iff`、`:303`
`probability_one_on_truth_event_still_allows_not_established`、`:567`
`contamination_and_conditioning_do_not_commute`、`:604`
`nn_interval_certificate_sound_of_two_inputs_two_hidden_one_output`、`:763`
`uncertainty_allowed_non_singleton_with_singleton_kernel`，行号为近似）以全限定名
引用或直接实例化，避免与同名本针遮蔽。降载体处均在语句与本文件内如实声明。

## 逐针人话语义（人话）

- 53 `finite_positive_support_truth_bridge`：有限正支撑上"真值事件概率 1"与
  "每个状态本体为真"互推（载体桥接），且即便概率 1，仍不等于 Judgment 层的认定
  ——给出同载体上的相容性见证（概率 1 且某状态判断为 notEstablished）。
- 54 `ae_truth_not_universal_truth`：概率 1 不等于全称真。连续 Uniform[0,1] 上
  q(x) = x 在 0 处假但概率 1；仓内无连续测度载体，降级为 N 等分有理网格
  {0, 1/N, ..., 1}，0 点零质量原子对应 P({0}) = 0，q(x) = (x != 0) 仍概率 1 而在
  0 处假。连续版开放，不冒称。
- 55 `conjunction_probability_bounds`：合取概率界——P(A 与 B) <= min(P A, P B)，
  max(0, P A + P B - 1) <= P(A 与 B)；事件包含时取到小事件质量；乘积/min/下界
  三个等号都不无条件成立（Bool 均匀载体上的具名反例）。
- 56 `contamination_conditioning_identity`：混合测度条件化恒等式——
  (1 - eps) clean + eps tainted 的混合，其条件份额等于分量条件质量的同一凸组合之比；
  h = 0（条件事件质量为零）单独处理为退化定理，不冒充条件概率。
- 57 `conditioned_contamination_bound`：条件污染比 eps_C = eps*h/((1 - eps)*p + eps*h)
  的显式公式（在 Bool 源载体上经第 56 针恒等式导出），以及 p >= rho 时的上界；
  附 99.02% 筛选反例的精确有理重构（eps = 1/2、p = 1、h = 1/101 时
  eps_C = 1/102，干净存活率 101/102 = 99.0196...% 四舍五入 99.02%）。
- 58 `nn_interval_certificate_sound`：有限一般网络的区间证书健全性——任意
  f : Q x Q -> Q 只要带指定域上的 eta 证书（扰动球内 |f x - f anchor| 型双边稳定界，
  以拆分式给出）与包住可达带的区间，证书就传播到球内一切点；ReLU 片段网络
  经 out_stable 供给 eta 证书，从而锚定理的特例被一般式重新导出。
- 59 `observational_ambiguity_preserved`：两个观测等价而目标不同的模型，任何
  可靠区间生产者都不能无证收成单点（下界 < 上界被强制）；附非空洞性见证与
  (0, 1) 区间实例，说明该约束真实起作用。

## 载体差异（诚实降级声明）

- 第 54 针：仓库无任何连续测度载体（无 Lebesgue/MeasureTheory），本针用显式
  有理网格 {i/N} 有限细分载体如实降级；连续 Uniform[0,1] 版本开放，本件不声称。
  机制是零质量原子（对应锚 `bridge_fails_without_positivity` 的塌桥点），不是锚
  `bridge_fails_without_support_finiteness` 的"窗口外"机制，二者刻意不混同。
- 第 57 针：历史 99.02% 反例的原始参数在仓内文本不可恢复（master-plan 表中仅以
  短语出现），本件给出的是精确有理重构实例，参数取 eps = 1/2、p = 1、h = 1/101，
  数值 101/102 四舍五入后即 99.02%，已在定理语句中以精确有理数声明。
- 第 58 针：一般式把网络特异性（Lipschitz 常数的存在）作为**显式前提** hstab
  引入，不声称任意网络自动具备 eta 证书；可检查接受判据与外部证书格式的对接
  仍未覆盖（沿锚文件未覆盖片段第 4 条口径）。
- 第 59 针：`XUObsModel` 为本件新建最小两模型载体，与锚的 Judgment 三值域示例
  刻意不同名；一般式对任意观测空间/目标陈述，锚 `:763` 只是其在旧判断域上的
  一个层内示例，本件不声称与它等价。
- 第 53/55/56 针在既有载体（`evMass`、Bool、有限 Fintype）上陈述，未新建测度。

## §档位

全部定理在本件内给出完整证明，零 `sorry`、零 `admit`、零新增 `axiom`；`decide`
只经 `decide_eq_true`/`rfl`/`norm_num` 用于可判定点，未使用 `native_decide`，
未使用 `Float`。按仓库边界约定，Lean 权威认定在 CI；本地未编译，状态 CI_NOT_RUN。
-/

namespace JurisLean.Seams.UnifiedNeedlesXU

open JurisLean.Seams.Uncertainty
open JurisLean.FullMath.Probability (evMass)
open JurisLean.KernelV3 (TruthJudgment Judgment)

/-! ## 第 53 针：finite_positive_support_truth_bridge -/

section Needle53TruthBridge

/-- **第 53 针（XU，I.13）**：finite_positive_support_truth_bridge——有限正支撑真值桥
    的逐名承接与载体连接。人话：三件事同时成立——(1) PMF 视角与测度视角在同一载体上
    是同一个量（`evMass p (truthEvent w)` 就是逐点权重的指示和，定义级 rfl）；
    (2) 锚 `Uncertainty.lean:134` 的双向桥原样成立（有限载体 + 每点正质量 + 归一时，
    "真值事件概率 1"与"每个状态本体为真"互推）；(3) 即便概率 1 也**不等于 Judgment**：
    同一载体上存在另一个真值记录，其真值事件概率仍为 1，而某状态的规范判断是
    `notEstablished`（锚 `:303` 的相容性见证）。诚实边界：桥只落在 `truth` 分量上，
    求值器一侧的对接未覆盖（沿锚未覆盖片段第 1 条口径）。 -/
theorem finite_positive_support_truth_bridge
    {α : Type} [Fintype α] [DecidableEq α]
    (p : α → ℚ) (w : α → TruthJudgment)
    (hpos : ∀ a, 0 < p a) (htotal : ∑ a : α, p a = 1) (a₀ : α) :
    (evMass p (truthEvent w) = ∑ a : α, (if truthEvent w a then p a else 0)) ∧
      (evMass p (truthEvent w) = 1 ↔ ∀ a, (w a).truth = true) ∧
      (∃ w' : α → TruthJudgment,
        evMass p (truthEvent w') = 1 ∧ (w' a₀).judgment = Judgment.notEstablished) :=
  ⟨rfl,
    JurisLean.Seams.Uncertainty.finite_positive_support_truth_bridge p w hpos htotal,
    JurisLean.Seams.Uncertainty.probability_one_on_truth_event_still_allows_not_established
      p a₀ htotal⟩

end Needle53TruthBridge

/-! ## 第 54 针：ae_truth_not_universal_truth -/

section Needle54AeNotUniversal

/-- 第 54 针载体（本件新建）：[0,1] 的 N 等分有理网格点 x_i = i/N（i = 0..N）。
    仓内无连续测度载体，连续 Uniform[0,1] 降级为该显式有限细分，声明于文件头。 -/
def xuGridX (N : ℕ) : ℕ → ℚ := fun i => (i : ℚ) / (N : ℚ)

/-- 第 54 针载体（本件新建）：网格质量——0 点为零质量原子（对应连续情形
    P({0}) = 0），其余格点各 1/N，总质量恰为 1。 -/
def xuGridMass (N : ℕ) : ℕ → ℚ := fun i => if i = 0 then (0 : ℚ) else 1 / (N : ℚ)

/-- 第 54 针载体（本件新建）：事件 q(x) = (x != 0)，即拟合同里的 q(x) = x 且
    x != 0。 -/
def xuGridNonzero (N : ℕ) : ℕ → Bool := fun i => decide (xuGridX N i ≠ 0)

/-- 辅助：带零号槽的常数段求和——前 n+1 个自然数里 0 号槽计 0、其余各计 c，
    总和为 n*c。供第 54 针网格质量归一使用。 -/
theorem xuConstRangeSum (n : ℕ) (c : ℚ) :
    ∑ i ∈ Finset.range (n + 1), (if i = 0 then (0 : ℚ) else c) = (n : ℚ) * c := by
  induction n with
  | zero =>
      have h0 : ∑ i ∈ Finset.range (0 + 1), (if i = 0 then (0 : ℚ) else c) = 0 := by
        rw [Finset.sum_range_succ]
        show (∑ i ∈ Finset.range 0, (if i = 0 then (0 : ℚ) else c))
            + (if (0 : ℕ) = 0 then (0 : ℚ) else c) = 0
        rw [if_pos (rfl : (0 : ℕ) = 0)]
        simp
      rw [h0]
      ring
  | succ n ih =>
      rw [Finset.sum_range_succ]
      rw [if_neg (show ¬ ((n : ℕ) + 1 = 0) from by omega), ih]
      push_cast
      ring

/-- 第 54 针分量：网格质量归一（含零质量原子的 0 号槽，总和恰为 1）。 -/
theorem xuGridMassSum (N : ℕ) (hN : 0 < N) :
    ∑ i ∈ Finset.range (N + 1), xuGridMass N i = 1 := by
  show (∑ i ∈ Finset.range (N + 1), (if i = 0 then (0 : ℚ) else 1 / (N : ℚ))) = 1
  rw [xuConstRangeSum]
  have hNq : ((N : ℕ) : ℚ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr hN)
  rw [mul_comm, div_mul_cancel₀ (1 : ℚ) hNq]

/-- 第 54 针分量：q 事件的概率恰为 1——0 号槽被 q 判假但质量为零，其余槽 q 判真。 -/
theorem xuGridEventMass (N : ℕ) (hN : 0 < N) :
    ∑ i ∈ Finset.range (N + 1), (if xuGridNonzero N i then xuGridMass N i else 0) = 1 := by
  have hNq : 0 < ((N : ℕ) : ℚ) := Nat.cast_pos.mpr hN
  have hcond : ∀ i : ℕ,
      (if xuGridNonzero N i then xuGridMass N i else 0) = xuGridMass N i := by
    intro i
    by_cases h0 : i = 0
    · subst h0
      have hq : xuGridNonzero N 0 = false := by
        show decide (xuGridX N 0 ≠ 0) = false
        simp [xuGridX]
      rw [hq]
      simp [xuGridMass]
    · have hip : 0 < (i : ℚ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero h0)
      have hd : 0 < xuGridX N i := div_pos hip hNq
      have hq : xuGridNonzero N i = true := by
        show decide (xuGridX N i ≠ 0) = true
        exact decide_eq_true (ne_of_gt hd)
      rw [hq, if_pos rfl]
  have hsum2 : (∑ i ∈ Finset.range (N + 1), (if xuGridNonzero N i then xuGridMass N i else 0))
      = ∑ i ∈ Finset.range (N + 1), xuGridMass N i :=
    Finset.sum_congr rfl (fun i _ => hcond i)
  rw [hsum2]
  exact xuGridMassSum N hN

/-- **第 54 针（XU，I.13）**：ae_truth_not_universal_truth——概率 1 不等于全称真。
    人话：在 [0,1] 的 N 等分有理网格上，质量函数非负、归一（0 号槽零质量原子，
    其余各 1/N）；事件 q(x) = (x != 0) 的概率**恰为 1**，但 0 这个点就在载体里、
    q 在它上面是假的。这正是连续 Uniform[0,1] 上 q(x) = x 于 0 处假的离散同构：
    零质量原子承担了 P({0}) = 0 的角色。诚实边界：仓内无连续测度载体，连续版
    **开放**；本针机制（载体内部零质量原子）刻意区别于锚
    `bridge_fails_without_support_finiteness`（`:249`，窗口外点），不是其替身；
    最后一个合取项以 rfl 固定 q 与网格坐标的拟合同一（q_i = decide(i/N != 0)）。 -/
theorem ae_truth_not_universal_truth (N : ℕ) (hN : 0 < N) :
    (∀ i ∈ Finset.range (N + 1), 0 ≤ xuGridMass N i) ∧
      (∑ i ∈ Finset.range (N + 1), xuGridMass N i = 1) ∧
      (∑ i ∈ Finset.range (N + 1), (if xuGridNonzero N i then xuGridMass N i else 0) = 1) ∧
      (0 ∈ Finset.range (N + 1) ∧ xuGridNonzero N 0 = false) ∧
      (∀ i ∈ Finset.range (N + 1), xuGridNonzero N i = decide (((i : ℚ) / (N : ℚ)) ≠ 0)) := by
  have hNq : 0 < ((N : ℕ) : ℚ) := Nat.cast_pos.mpr hN
  refine ⟨?_, xuGridMassSum N hN, xuGridEventMass N hN, ?_, fun i _ => rfl⟩
  · intro i _
    show 0 ≤ (if i = 0 then (0 : ℚ) else 1 / (N : ℚ))
    by_cases h0 : i = 0
    · rw [if_pos h0]
    · rw [if_neg h0]
      exact le_of_lt (div_pos (show (0 : ℚ) < 1 from by norm_num) hNq)
  · exact ⟨Finset.mem_range.mpr (by omega), by
      show decide (xuGridX N 0 ≠ 0) = false
      simp [xuGridX]⟩

end Needle54AeNotUniversal

/-! ## 第 55 针：conjunction_probability_bounds -/

section Needle55ConjunctionBounds

/-- 第 55 针数值见证载体：Bool 上的均匀半质量（供等号反例计算使用）。 -/
def xuHalf : Bool → ℚ := fun _ => 1 / 2

/-- 第 55 针逐点引理：合取事件的指示质量不超过第一事件的指示质量（0 <= p 逐点）。 -/
theorem xuIteAnd_le_left {α : Type} (p : α → ℚ) (hnn : ∀ a, 0 ≤ p a) (A B : α → Bool) :
    ∀ a : α, (if A a && B a then p a else 0) ≤ (if A a then p a else 0) := by
  intro a
  by_cases hA : A a = true
  · rw [if_pos hA]
    by_cases hB : B a = true
    · have hab : (A a && B a) = true := by rw [hA, hB, Bool.true_and]
      rw [if_pos hab]
    · have hne : ¬ ((A a && B a) = true) := by
        rw [Bool.and_eq_true]
        exact fun h => hB h.2
      rw [if_neg hne]
      exact hnn a
  · rw [if_neg hA]
    have hne : ¬ ((A a && B a) = true) := by
      rw [Bool.and_eq_true]
      exact fun h => hA h.1
    rw [if_neg hne]

/-- 第 55 针逐点引理：合取事件的指示质量不超过第二事件的指示质量（0 <= p 逐点）。 -/
theorem xuIteAnd_le_right {α : Type} (p : α → ℚ) (hnn : ∀ a, 0 ≤ p a) (A B : α → Bool) :
    ∀ a : α, (if A a && B a then p a else 0) ≤ (if B a then p a else 0) := by
  intro a
  by_cases hB : B a = true
  · rw [if_pos hB]
    by_cases hA : A a = true
    · have hab : (A a && B a) = true := by rw [hA, hB, Bool.true_and]
      rw [if_pos hab]
    · have hne : ¬ ((A a && B a) = true) := by
        rw [Bool.and_eq_true]
        exact fun h => hA h.1
      rw [if_neg hne]
      exact hnn a
  · rw [if_neg hB]
    have hne : ¬ ((A a && B a) = true) := by
      rw [Bool.and_eq_true]
      exact fun h => hB h.2
    rw [if_neg hne]

/-- 第 55 针逐点引理：补集 union 法下界的逐点形态——
    iA + iB - p <= iAB（四种 Bool 组合逐一核对，唯一非平凡分支用 0 <= p）。 -/
theorem xuIteLower {α : Type} (p : α → ℚ) (hnn : ∀ a, 0 ≤ p a) (A B : α → Bool) (a : α) :
    (if A a then p a else 0) + (if B a then p a else 0) - p a
      ≤ (if A a && B a then p a else 0) := by
  by_cases hA : A a = true
  · rw [if_pos hA]
    by_cases hB : B a = true
    · have hab : (A a && B a) = true := by rw [hA, hB, Bool.true_and]
      rw [if_pos hB, if_pos hab]
      linarith
    · have hne : ¬ ((A a && B a) = true) := by
        rw [Bool.and_eq_true]
        exact fun h => hB h.2
      rw [if_neg hB, if_neg hne]
      linarith
  · rw [if_neg hA]
    by_cases hB : B a = true
    · have hne : ¬ ((A a && B a) = true) := by
        rw [Bool.and_eq_true]
        exact fun h => hA h.1
      rw [if_pos hB, if_neg hne]
      linarith
    · have hne : ¬ ((A a && B a) = true) := by
        rw [Bool.and_eq_true]
        exact fun h => hB h.2
      rw [if_neg hB, if_neg hne]
      linarith [hnn a]

/-- 第 55 针附带（合同"事件包含给 min 上界"的另一半）：A 包含于 B 时，
    合取事件就是小事件本身（P(A 与 B) = P A = min 侧的取等机制）。 -/
theorem conjunction_equals_smaller_event_under_inclusion
    {α : Type} [Fintype α] [DecidableEq α] (p : α → ℚ) (A B : α → Bool)
    (hinc : ∀ a, A a = true → B a = true) :
    evMass p (fun a => A a && B a) = evMass p A := by
  show (∑ a : α, (if A a && B a then p a else 0)) = (∑ a : α, (if A a then p a else 0))
  refine Finset.sum_congr rfl (fun a _ => ?_)
  by_cases hA : A a = true
  · have hab : (A a && B a) = true := by rw [hA, hinc a hA, Bool.true_and]
    rw [if_pos hab, if_pos hA]
  · have hne : ¬ ((A a && B a) = true) := by
      rw [Bool.and_eq_true]
      exact fun h => hA h.1
    rw [if_neg hne, if_neg hA]

/-- **第 55 针（XU，I.13）**：conjunction_probability_bounds——合取概率界。
    人话：对任意非负归一质量与两个事件，(1) 上界 P(A 与 B) <= min(P A, P B)；
    (2) 下界 max(0, P A + P B - 1) <= P(A 与 B)（补集 union 法的逐点形态求和）；
    (3)-(5) 乘积、min、下界三个等号都**不无条件**成立：Bool 均匀载体上，
    不相交事件（b 与 !b）把 min 等号打死（0 < 1/2）；相同事件（b 与 b）把
    下界等号打死（1/2 + 1/2 - 1 < 1/2）且把乘积等号打死（1/2 != 1/4）。
    诚实边界：只给双侧夹界与等号反例，独立性/乘积法则未假设也未声称；
    事件包含时的取等见 `conjunction_equals_smaller_event_under_inclusion`。 -/
theorem conjunction_probability_bounds
    {α : Type} [Fintype α] [DecidableEq α]
    (p : α → ℚ) (A B : α → Bool)
    (hnn : ∀ a, 0 ≤ p a) (htotal : ∑ a : α, p a = 1) :
    (evMass p (fun a => A a && B a) ≤ min (evMass p A) (evMass p B)) ∧
      (max 0 (evMass p A + evMass p B - 1) ≤ evMass p (fun a => A a && B a)) ∧
      (∃ (A' B' : Bool → Bool),
        evMass xuHalf (fun b => A' b && B' b) < evMass xuHalf A'
          ∧ evMass xuHalf (fun b => A' b && B' b) < evMass xuHalf B') ∧
      (∃ (A' B' : Bool → Bool),
        evMass xuHalf A' + evMass xuHalf B' - 1 < evMass xuHalf (fun b => A' b && B' b)) ∧
      (∃ (A' B' : Bool → Bool),
        evMass xuHalf (fun b => A' b && B' b) ≠ evMass xuHalf A' * evMass xuHalf B') := by
  have h1 : evMass p (fun a => A a && B a) ≤ evMass p A := by
    show (∑ a : α, (if A a && B a then p a else 0)) ≤ (∑ a : α, (if A a then p a else 0))
    exact Finset.sum_le_sum (fun a _ => xuIteAnd_le_left p hnn A B a)
  have h2 : evMass p (fun a => A a && B a) ≤ evMass p B := by
    show (∑ a : α, (if A a && B a then p a else 0)) ≤ (∑ a : α, (if B a then p a else 0))
    exact Finset.sum_le_sum (fun a _ => xuIteAnd_le_right p hnn A B a)
  have hsum : (∑ a : α, ((if A a then p a else 0) + (if B a then p a else 0) - p a))
      ≤ (∑ a : α, (if A a && B a then p a else 0)) :=
    Finset.sum_le_sum (fun a _ => xuIteLower p hnn A B a)
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib] at hsum
  rw [htotal] at hsum
  have hge0 : 0 ≤ evMass p (fun a => A a && B a) := by
    show 0 ≤ (∑ a : α, (if A a && B a then p a else 0))
    exact Finset.sum_nonneg (fun a _ => by
      by_cases hab : (A a && B a) = true
      · rw [if_pos hab]
        exact hnn a
      · rw [if_neg hab])
  have hDis : evMass xuHalf (fun b => b && !b) = 0 := by
    unfold evMass
    rw [sum_bool_eq]
    simp [xuHalf]
  have hId : evMass xuHalf (fun b => b) = 1 / 2 := by
    unfold evMass
    rw [sum_bool_eq]
    simp [xuHalf]
  have hNot : evMass xuHalf (fun b => !b) = 1 / 2 := by
    unfold evMass
    rw [sum_bool_eq]
    simp [xuHalf]
  have hAndSelf : evMass xuHalf (fun b => b && b) = 1 / 2 := by
    unfold evMass
    rw [sum_bool_eq]
    simp [xuHalf]
  refine ⟨le_min h1 h2, max_le hge0 hsum, ?_, ?_, ?_⟩
  · refine ⟨fun b => b, fun b => !b, ?_, ?_⟩
    · show evMass xuHalf (fun b => b && !b) < evMass xuHalf (fun b => b)
      rw [hDis, hId]
      norm_num
    · show evMass xuHalf (fun b => b && !b) < evMass xuHalf (fun b => !b)
      rw [hDis, hNot]
      norm_num
  · refine ⟨fun b => b, fun b => b, ?_⟩
    show evMass xuHalf (fun b => b) + evMass xuHalf (fun b => b) - 1
      < evMass xuHalf (fun b => b && b)
    rw [hId, hAndSelf]
    norm_num
  · refine ⟨fun b => b, fun b => b, ?_⟩
    show evMass xuHalf (fun b => b && b) ≠ evMass xuHalf (fun b => b)
      * evMass xuHalf (fun b => b)
    rw [hAndSelf, hId]
    intro hcon
    norm_num at hcon

end Needle55ConjunctionBounds

/-! ## 第 56 针：contamination_conditioning_identity -/

section Needle56ContaminationConditioning

/-- 第 56 针载体：混合质量——clean 分量 (1 - eps)*c 与 tainted 分量 eps*t 的
    逐点凸组合。 -/
def xuMixMass {α : Type} (ε : ℚ) (c t : α → ℚ) : α → ℚ :=
  fun a => (1 - ε) * c a + ε * t a

/-- 第 56 针载体：事件条件化份额——分子是 E 与 H 同时成立的质量，分母是 H 的质量。
    当 H 质量为 0（h = 0）时分母为零，份额退化为域的除法约定值，**不是**条件概率
    （见 `contamination_conditioning_degenerate` 的单独处理）。 -/
def xuCondShare {α : Type} [Fintype α] [DecidableEq α] (m : α → ℚ) (E H : α → Bool) : ℚ :=
  evMass m (fun a => E a && H a) / evMass m H

/-- 第 56 针线性引理：混合质量的事件质量等于分量事件质量的同一凸组合。
    逐点拆 ite 后用和的加法/数乘线性性；这是条件化恒等式的引擎。 -/
theorem xuMixMassSum {α : Type} [Fintype α] [DecidableEq α] (ε : ℚ) (c t : α → ℚ)
    (e : α → Bool) :
    evMass (xuMixMass ε c t) e = (1 - ε) * evMass c e + ε * evMass t e := by
  have hsplit : ∀ a : α,
      (if e a then (1 - ε) * c a + ε * t a else 0)
        = (1 - ε) * (if e a then c a else 0) + ε * (if e a then t a else 0) := by
    intro a
    by_cases he : e a = true
    · simp only [if_pos he]
    · simp only [if_neg he]
      ring
  show (∑ a : α, (if e a then (1 - ε) * c a + ε * t a else 0))
      = (1 - ε) * (∑ a : α, (if e a then c a else 0))
        + ε * (∑ a : α, (if e a then t a else 0))
  rw [show (∑ a : α, (if e a then (1 - ε) * c a + ε * t a else 0))
      = ∑ a : α, ((1 - ε) * (if e a then c a else 0) + ε * (if e a then t a else 0)) from
    Finset.sum_congr rfl (fun a _ => hsplit a),
    Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]

/-- **第 56 针（XU，I.13）**：contamination_conditioning_identity——混合测度条件化
    恒等式。人话：把 clean 测度 c 与 tainted 测度 t 按 (1 - eps) : eps 混合后，
    对任意事件对 E、H 做"先混合后条件化"，结果恰好等于"分子分母分别混合"：
    份额 = ((1-eps)*c 侧 E 与 H 的质量 + eps*t 侧 E 与 H 的质量) /
    ((1-eps)*c 侧 H 的质量 + eps*t 侧 H 的质量)。这与锚
    `contamination_and_conditioning_do_not_commute`（`:567`，只参数化族特例）互补：
    锚说两个顺序不可交换，本针给出正确顺序下的**封闭公式**。诚实边界：恒等式
    在任意参数（含 eps 出 [0,1]）下成立；h = 0 的退化分支**单独**处理于
    `contamination_conditioning_degenerate`，本针不把 0/0 约定值冒充条件概率。 -/
theorem contamination_conditioning_identity
    {α : Type} [Fintype α] [DecidableEq α] (ε : ℚ) (c t : α → ℚ) (E H : α → Bool) :
    xuCondShare (xuMixMass ε c t) E H
      = ((1 - ε) * evMass c (fun a => E a && H a) + ε * evMass t (fun a => E a && H a))
        / ((1 - ε) * evMass c H + ε * evMass t H) := by
  unfold xuCondShare
  rw [xuMixMassSum ε c t (fun a => E a && H a), xuMixMassSum ε c t H]

/-- 第 56 针的 h = 0 分支（单独处理）：非负分量且 eps 在 [0,1] 时，若 c 侧与
    t 侧的 H 质量都为零，则混合后的 H 质量为零、E 与 H 的质量也为零（E 与 H
    蕴含 H），条件化份额等于除法约定值 0——这是一个**退化**，不是条件概率。
    合同"h = 0 单独处理"由本定理落实。 -/
theorem contamination_conditioning_degenerate
    {α : Type} [Fintype α] [DecidableEq α] (ε : ℚ) (c t : α → ℚ) (E H : α → Bool)
    (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (hc : ∀ a, 0 ≤ c a) (ht : ∀ a, 0 ≤ t a)
    (hc0 : evMass c H = 0) (ht0 : evMass t H = 0) :
    evMass (xuMixMass ε c t) H = 0 ∧ xuCondShare (xuMixMass ε c t) E H = 0 := by
  have hmixH : evMass (xuMixMass ε c t) H = 0 := by
    rw [xuMixMassSum ε c t H, hc0, ht0]
    ring
  have hmixnn : ∀ a : α, 0 ≤ xuMixMass ε c t a := by
    intro a
    have hk1 : 0 ≤ (1 - ε) * c a := mul_nonneg (by linarith) (hc a)
    have hk2 : 0 ≤ ε * t a := mul_nonneg hε (ht a)
    show 0 ≤ (1 - ε) * c a + ε * t a
    linarith
  have hsub : evMass (xuMixMass ε c t) (fun a => E a && H a) = 0 := by
    have hge : 0 ≤ evMass (xuMixMass ε c t) (fun a => E a && H a) := by
      show 0 ≤ (∑ a : α, (if E a && H a then xuMixMass ε c t a else 0))
      exact Finset.sum_nonneg (fun a _ => by
        by_cases hab : (E a && H a) = true
        · rw [if_pos hab]
          exact hmixnn a
        · rw [if_neg hab])
    have hle : evMass (xuMixMass ε c t) (fun a => E a && H a)
        ≤ evMass (xuMixMass ε c t) H := by
      show (∑ a : α, (if E a && H a then xuMixMass ε c t a else 0))
          ≤ (∑ a : α, (if H a then xuMixMass ε c t a else 0))
      exact Finset.sum_le_sum (fun a _ => xuIteAnd_le_right (xuMixMass ε c t) hmixnn E H a)
    exact le_antisymm (le_trans hle (le_of_eq hmixH)) hge
  refine ⟨hmixH, ?_⟩
  unfold xuCondShare
  rw [hsub, hmixH]
  norm_num

end Needle56ContaminationConditioning

/-! ## 第 57 针：conditioned_contamination_bound -/

section Needle57ConditionedContamination

/-- 第 57 针载体：干净源分量（次概率测度）——干净证据通过筛选的质量为 p，
    落在 false 槽；true（污染源）槽为 0。 -/
def xuScreenClean (p : ℚ) : Bool → ℚ := fun b => if b then 0 else p

/-- 第 57 针载体：污染源分量（次概率测度）——污染输入通过筛选的质量为 h，
    落在 true 槽；false（干净源）槽为 0。 -/
def xuScreenTainted (h : ℚ) : Bool → ℚ := fun b => if b then h else 0

/-- 第 57 针载体：源指示事件——b = true 表示"这条通过筛选的输入来自污染源"。 -/
def xuTaintedSource : Bool → Bool := fun b => b

/-- 第 57 针载体：通过事件——本载体上存活的质量都已通过筛选（H 恒真），
    筛选的吸收效应放在两个次概率分量的质量里。 -/
def xuPassAll : Bool → Bool := fun _ => true

/-- **第 57 针（XU，I.13）**：conditioned_contamination_bound——条件污染比的显式
    公式与上界。人话：干净通过率 p、污染通过率 h、先验污染比 eps 时，筛选后
    残余污染比恰为 eps_C = eps*h / ((1 - eps)*p + eps*h)（在 Bool 源载体上把
    第 56 针恒等式实例化后算出）；且干净侧通过率有下确界 rho <= p 时，
    eps_C <= eps*h / ((1 - eps)*rho + eps*h)（分母更大商更小）。诚实边界：
    历史文献里的 99.02% 筛选反例原始参数在仓内不可恢复，本件在
    `screening_leaves_contamination_ninety_nine_oh_two` 给出精确有理重构；
    上界不取等号的情形未单独陈述（等号机制已在第 55 针反例族中展示）。 -/
theorem conditioned_contamination_bound
    (ε p h ρ : ℚ) (hε : 0 ≤ ε) (hεlt : ε < 1) (hp : 0 < p) (hh : 0 ≤ h)
    (hρ : 0 < ρ) (hpρ : ρ ≤ p) :
    (xuCondShare (xuMixMass ε (xuScreenClean p) (xuScreenTainted h)) xuTaintedSource xuPassAll
      = ε * h / ((1 - ε) * p + ε * h)) ∧
    (ε * h / ((1 - ε) * p + ε * h) ≤ ε * h / ((1 - ε) * ρ + ε * h)) := by
  have hcH : evMass (xuScreenClean p) xuPassAll = p := by
    unfold evMass
    rw [sum_bool_eq]
    simp [xuScreenClean, xuPassAll]
  have htH : evMass (xuScreenTainted h) xuPassAll = h := by
    unfold evMass
    rw [sum_bool_eq]
    simp [xuScreenTainted, xuPassAll]
  have hcE : evMass (xuScreenClean p) (fun b => xuTaintedSource b && xuPassAll b) = 0 := by
    unfold evMass
    rw [sum_bool_eq]
    simp [xuScreenClean, xuTaintedSource, xuPassAll]
  have htE : evMass (xuScreenTainted h) (fun b => xuTaintedSource b && xuPassAll b) = h := by
    unfold evMass
    rw [sum_bool_eq]
    simp [xuScreenTainted, xuTaintedSource, xuPassAll]
  refine ⟨?_, ?_⟩
  · rw [contamination_conditioning_identity ε (xuScreenClean p) (xuScreenTainted h)
      xuTaintedSource xuPassAll, hcE, htE, hcH, htH]
    ring
  · have k1 : 0 < (1 - ε) * p := mul_pos (sub_pos.mpr hεlt) hp
    have k1' : 0 < (1 - ε) * ρ := mul_pos (sub_pos.mpr hεlt) hρ
    have k2 : 0 ≤ ε * h := mul_nonneg hε hh
    have hD1 : 0 < (1 - ε) * p + ε * h := by linarith
    have hD2 : 0 < (1 - ε) * ρ + ε * h := by linarith
    have hden : (1 - ε) * ρ + ε * h ≤ (1 - ε) * p + ε * h := by
      have hm : (1 - ε) * ρ ≤ (1 - ε) * p := mul_le_mul_of_nonneg_left hpρ (by linarith)
      linarith
    rw [div_eq_mul_one_div (ε * h) ((1 - ε) * p + ε * h),
      div_eq_mul_one_div (ε * h) ((1 - ε) * ρ + ε * h)]
    exact mul_le_mul_of_nonneg_left (one_div_le_one_div_of_le hD2 hden) k2

/-- 第 57 针的 99.02% 筛选反例（精确有理重构）：eps = 1/2、干净通过率 p = 1、
    污染通过率 h = 1/101 时，筛选后残余污染比恰为 1/102，干净存活率
    101/102 = 0.990196...（四舍五入 99.02%）。人话：哪怕干净输入百分之百通过、
    污染输入只有约 1% 的通过率，筛选后的存活流里**仍**留下精确 1/102 的污染——
    筛选不能把污染清零，这正是历史局部反例的读法。诚实边界：历史参数在仓内
    文本不可恢复，本实例是自建的精确重构，不冒称复现了原实例的参数。 -/
theorem screening_leaves_contamination_ninety_nine_oh_two :
    xuCondShare (xuMixMass (1 / 2) (xuScreenClean 1) (xuScreenTainted (1 / 101)))
        xuTaintedSource xuPassAll = 1 / 102 ∧
    (101 / 102 : ℚ) = 1 - 1 / 102 := by
  refine ⟨?_, by norm_num⟩
  rw [contamination_conditioning_identity (1 / 2) (xuScreenClean 1)
    (xuScreenTainted (1 / 101)) xuTaintedSource xuPassAll]
  have hcH : evMass (xuScreenClean 1) xuPassAll = 1 := by
    unfold evMass
    rw [sum_bool_eq]
    simp [xuScreenClean, xuPassAll]
  have htH : evMass (xuScreenTainted (1 / 101)) xuPassAll = 1 / 101 := by
    unfold evMass
    rw [sum_bool_eq]
    simp [xuScreenTainted, xuPassAll]
  have hcE : evMass (xuScreenClean 1) (fun b => xuTaintedSource b && xuPassAll b) = 0 := by
    unfold evMass
    rw [sum_bool_eq]
    simp [xuScreenClean, xuTaintedSource, xuPassAll]
  have htE : evMass (xuScreenTainted (1 / 101)) (fun b => xuTaintedSource b && xuPassAll b)
      = 1 / 101 := by
    unfold evMass
    rw [sum_bool_eq]
    simp [xuScreenTainted, xuTaintedSource, xuPassAll]
  rw [hcE, htE, hcH, htH]
  norm_num

end Needle57ConditionedContamination

/-! ## 第 58 针：nn_interval_certificate_sound -/

section Needle58NNCertificate

/-- **第 58 针（XU，I.13）**：nn_interval_certificate_sound——神经网络输出区间证书
    健全性的一般式。人话：任意 f : Q x Q -> Q，只要在指定域（ℚ x ℚ 的两坐标
    扰动球）上持有 eta 证书——半径 eta、常数 L，球内每点 f 的输出都落在
    [f anchor - L*eta, f anchor + L*eta] 带内（hstab，以拆分双边不等式给出）——
    且声明的区间 [lo, hi] 包住这条可达带（hband），那么证书就**传播**：球内
    任何点的真实输出都落在 [lo, hi] 内；同时区间在锚点处非空（lo <= f anchor
    <= hi）。锚 `nn_interval_certificate_sound_of_two_inputs_two_hidden_one_output`
    （`:604`，仅两输入两隐元一输出的指定网络）是本式在 f = out、L = lip 处的
    特例（见 `nn_interval_certificate_sound_of_general_certificate` 的重新导出）。
    诚实边界：网络特异性作为显式前提 hstab 引入，不声称任意网络自动具备
    eta 证书；不主张 L 是最小 Lipschitz 常数；可检查接受判据与外部证书格式
    的对接沿锚未覆盖片段第 4 条口径，仍开放。 -/
theorem nn_interval_certificate_sound
    (f : ℚ × ℚ → ℚ) (anchor : ℚ × ℚ) (η L lo hi : ℚ)
    (hη : 0 ≤ η) (hL : 0 ≤ L)
    (hstab : ∀ x : ℚ × ℚ, withinBall η x anchor →
      f anchor - L * η ≤ f x ∧ f x ≤ f anchor + L * η)
    (hband : lo ≤ f anchor - L * η ∧ f anchor + L * η ≤ hi) :
    (lo ≤ f anchor ∧ f anchor ≤ hi) ∧
      (∀ x : ℚ × ℚ, withinBall η x anchor → lo ≤ f x ∧ f x ≤ hi) := by
  have hLη : 0 ≤ L * η := mul_nonneg hL hη
  refine ⟨⟨by linarith [hband.1], by linarith [hband.2]⟩, ?_⟩
  intro x hx
  obtain ⟨h1, h2⟩ := hstab x hx
  exact ⟨le_trans hband.1 h1, le_trans h2 hband.2⟩

/-- 第 58 针的 eta 证书供给端：`Mandate/ReLUApprox.lean` 的片段网络（两输入、
    两隐元、一输出）确实持有指定域上的 eta 证书——证明只复用该文件已证的
    `out_stable`（`:135`），不重推逐层算术。这正是把一般式接到锚特例的桥。 -/
theorem nn_eta_certificate_of_relu_fragment (anchor : ℚ × ℚ) (η : ℚ) (hη : 0 ≤ η) :
    ∀ x : ℚ × ℚ, withinBall η x anchor →
      JurisLean.Mandate.ReLUApprox.out anchor - JurisLean.Mandate.ReLUApprox.lip * η
        ≤ JurisLean.Mandate.ReLUApprox.out x
      ∧ JurisLean.Mandate.ReLUApprox.out x
        ≤ JurisLean.Mandate.ReLUApprox.out anchor + JurisLean.Mandate.ReLUApprox.lip * η := by
  intro x hx
  obtain ⟨l1, u1, l2, u2⟩ := hx
  have hband := JurisLean.Mandate.ReLUApprox.out_stable hη l1 u1 l2 u2
  constructor
  · linarith [hband.1]
  · linarith [hband.2]

/-- 第 58 针的实例化收口：用一般式重新导出锚定理的结论——对片段网络，
    `RadiusCert` 证书一旦通过 `admitsRadiusCert` 接受检查（半径非负、区间包住
    out 锚点可达带），真实输出必落在声明区间内。锚 `:604` 的可靠性由一般式
    一行闭合，展示"指定域 eta 证书再传播"的完整链条。 -/
theorem nn_interval_certificate_sound_of_general_certificate
    {anchor : ℚ × ℚ} (c : RadiusCert anchor) (hc : admitsRadiusCert anchor c)
    {x : ℚ × ℚ} (hx : withinBall c.E x anchor) :
    c.lo ≤ JurisLean.Mandate.ReLUApprox.out x
      ∧ JurisLean.Mandate.ReLUApprox.out x ≤ c.hi := by
  obtain ⟨hE, hlo, hhi⟩ := hc
  exact (nn_interval_certificate_sound JurisLean.Mandate.ReLUApprox.out anchor c.E
    JurisLean.Mandate.ReLUApprox.lip c.lo c.hi hE
    (le_of_lt JurisLean.Mandate.ReLUApprox.lip_pos)
    (nn_eta_certificate_of_relu_fragment anchor c.E hE) ⟨hlo, hhi⟩).2 x hx

end Needle58NNCertificate

/-! ## 第 59 针：observational_ambiguity_preserved -/

section Needle59ObservationalAmbiguity

/-- 第 59 针载体（本件新建）：两个观测等价但目标不同的模型。 -/
inductive XUObsModel where
  | alpha : XUObsModel
  | beta : XUObsModel

/-- 第 59 针载体：观测函数——两个模型的观测完全一致（都观察到 true），
    这就是"观测等价"。 -/
def xuObservation : XUObsModel → Bool := fun _ => true

/-- 第 59 针载体：目标函数——两个模型的法律目标值不同（0 与 1）。 -/
def xuTargetValue : XUObsModel → ℚ :=
  fun m => match m with
    | XUObsModel.alpha => 0
    | XUObsModel.beta => 1

/-- 第 59 针载体：区间生产者样例——对任何观测都交出区间 [0, 1]。 -/
def xuAmbigInterval : Bool → ℚ × ℚ := fun _ => ((0 : ℚ), (1 : ℚ))

/-- **第 59 针（XU，I.13）**：observational_ambiguity_preserved——观测歧义保持。
    人话：如果区间生产者 I 是**可靠**的——对每个模型，I 依观测交出的区间都
    真的盖住该模型的目标值——那么只要存在两个观测相同而目标不同的模型，
    I 在这条观测上的区间就**不可能收成单点**（下界严格小于上界）：若收成
    单点，两个不同目标会被同一个数同时盖住，矛盾。所以"收成单点"必须有
    额外证书（区分两模型的信息），不能无证发生。锚
    `uncertainty_allowed_non_singleton_with_singleton_kernel`（`:763`）只是旧
    判断域（Judgment 三值）上的记账示例；本针对任意观测空间/目标陈述机制。
    非空洞性与 (0,1) 实例见后两条。 -/
theorem observational_ambiguity_preserved
    {M O : Type} (obs : M → O) (tgt : M → ℚ) (I : O → ℚ × ℚ)
    (hrel : ∀ m : M, (I (obs m)).1 ≤ tgt m ∧ tgt m ≤ (I (obs m)).2) :
    ∀ m₁ m₂ : M, obs m₁ = obs m₂ → tgt m₁ ≠ tgt m₂ →
      (I (obs m₁)).1 < (I (obs m₁)).2 := by
  intro m₁ m₂ hobs hne
  obtain ⟨hl₁, hh₁⟩ := hrel m₁
  obtain ⟨hl₂, hh₂⟩ := hrel m₂
  rw [← hobs] at hl₂ hh₂
  by_contra hnotlt
  have hle : (I (obs m₁)).1 ≤ (I (obs m₁)).2 := le_trans hl₁ hh₁
  have hsingle : (I (obs m₁)).1 = (I (obs m₁)).2 := le_antisymm hle (by linarith)
  apply hne
  linarith

/-- 第 59 针的非空洞性见证：两个观测等价而目标不同的模型确实存在
    （先证明类型有人住，再谈否定性结论）。 -/
theorem observational_ambiguity_is_not_vacuous :
    ∃ m₁ m₂ : XUObsModel, xuObservation m₁ = xuObservation m₂
      ∧ xuTargetValue m₁ ≠ xuTargetValue m₂ := by
  refine ⟨XUObsModel.alpha, XUObsModel.beta, rfl, ?_⟩
  intro hcon
  have hq : (0 : ℚ) = 1 := hcon
  norm_num at hq

/-- 第 59 针的可靠区间存在性见证：区间生产者 [0, 1] 对两模型的目标都可靠，
    于是与主定理合用后，区间被迫非退化（0 < 1），"不能无证收成单点"在活
    见证上兑现。 -/
theorem reliable_interval_exists_on_ambiguous_pair :
    ∀ m : XUObsModel,
      (xuAmbigInterval (xuObservation m)).1 ≤ xuTargetValue m
        ∧ xuTargetValue m ≤ (xuAmbigInterval (xuObservation m)).2 := by
  intro m
  cases m with
  | alpha => simp [xuTargetValue, xuAmbigInterval, xuObservation]
  | beta => simp [xuTargetValue, xuAmbigInterval, xuObservation]

/-- 第 59 针收口：在上述观测歧义对上，任何可靠区间（含 [0, 1]）都不能收成
    单点——由主定理一行实例化得出。 -/
theorem ambiguous_pair_forces_nonsingleton_interval :
    (xuAmbigInterval (xuObservation XUObsModel.alpha)).1
      < (xuAmbigInterval (xuObservation XUObsModel.alpha)).2 := by
  have hne : xuTargetValue XUObsModel.alpha ≠ xuTargetValue XUObsModel.beta := by
    intro hcon
    have hq : (0 : ℚ) = 1 := hcon
    norm_num at hq
  exact observational_ambiguity_preserved xuObservation xuTargetValue xuAmbigInterval
    reliable_interval_exists_on_ambiguous_pair XUObsModel.alpha XUObsModel.beta rfl hne

end Needle59ObservationalAmbiguity

end JurisLean.Seams.UnifiedNeedlesXU
