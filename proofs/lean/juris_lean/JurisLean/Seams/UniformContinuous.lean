import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.NoAtoms
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Tactic

/-!
# W1-1 / 针 54 连续版：Uniform[0,1] 勒贝格测度载体上的 ae_truth_not_universal_truth

出处与合同：
- `docs/spec/20261007-统一法律数学模型_附录I_Lean施工明细.md` §I.13 第 808 行（唯一权威）：
  针 54 XU `ae_truth_not_universal_truth`——"拟Uniform[0,1]、q(x)≡x≠0：概率1但0处假"。
- `docs/full-math/NEEDLE_STRENGTH_AUDIT.md` 针 54 行判**差额**：旧交付
  `Seams/UnifiedNeedlesXU.lean:179` 是 N 等分有理网格替身（零质量原子机制，
  模块自认"连续 Uniform[0,1] 版本开放"），连续勒贝格测度载体未建；W1-1 在案未施工。
- `docs/master-plan/20261010_统一法律数学模型_连续与语义全量施工方案.md` W1-1 行：
  真值事件 `{x | x ≠ 0}`，在 [0,1] 勒贝格测度下概率 1 而 0 点为假；
  有理网格版保留为旧件不动。

## 载体选择（volume vs 归一）

Uniform[0,1] 的标准载体 = `MeasureTheory.volume`（ℝ 上勒贝格测度）限制在闭单位区间
`Icc 0 1`。`Real.volume_Icc` 给出 `volume (Icc 0 1) = ENNReal.ofReal (1 - 0) = 1`，
限制测度的总质量恰为 1——**无需归一步骤**，`volume.restrict (Icc 0 1)` 本身已是概率
测度（`uniform01_is_probability`）。全部事件概率在 ℝ 层以区间长度精确计算
（`ENNReal.ofReal` 读数），不引入密度函数、期望算子或浮点采样。

## 机制说明（与有理网格替身的关系）

旧替身（`UnifiedNeedlesXU.lean:179`，保留不动）：N+1 个有理格点 i/N，质量函数
`xuGridMass N i = if i = 0 then 0 else 1/N`——0 号槽在载体中而质量被**指派**为 0
（零质量原子）。本件连续版：勒贝格测度**无原子**（mathlib 实例 `Real.noAtoms_volume`：
每个单点零测是导出性质，不是逐点指派）——真值事件 = 载体挖去一个零测点，测度仍是
全长 1。`rational_grid_atom_vs_lebesgue_no_atoms` 把两种机制并排陈述（网格侧以定义体
逐字重述 `gridMass` 保持零耦合，不 import 旧件）。

诚实边界（开放点，详见 .local/agent_W14_uniform_cont_report.md）：W1-1 若含更大范围
（一般密度函数、期望算子、条件期望等），超出针 54 最小连续载体的部分不在本件，
如实列开放。
-/

namespace JurisLean.Seams.UniformContinuous

open MeasureTheory Real Set

/-! ## 一、载体：volume 限制在闭单位区间（归一免做） -/

/-- W1-1 载体：Uniform[0,1] ＝ 勒贝格测度 volume 限制在闭单位区间 Icc 0 1 上。 -/
noncomputable def uniform01 : Measure ℝ := volume.restrict (Icc (0 : ℝ) 1)

/-- 载体总质量：闭单位区间长度恰 1（volume 层精确读数；Lebesgue/Basic.lean:89
`Real.volume_Icc`）。 -/
theorem volume_unit_interval : volume (Icc (0 : ℝ) 1) = 1 := by
  rw [Real.volume_Icc]
  simp

/-- Uniform[0,1] 是概率测度：限制测度在 univ 上的质量＝区间质量＝1——因长度恰 1，
无再归一步骤（`Measure.restrict_apply` + `volume_unit_interval`）。 -/
theorem uniform01_is_probability : IsProbabilityMeasure uniform01 := by
  constructor
  rw [uniform01, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
  exact volume_unit_interval

/-- 连续载体的无原子性：勒贝格测度无原子，其任意限制亦然
（mathlib `Measure.restrict.instNoAtoms`，源头实例 `Real.noAtoms_volume`
Lebesgue/Basic.lean:173）。 -/
theorem uniform01_no_atoms : NoAtoms uniform01 := by
  unfold uniform01
  infer_instance

/-! ## 二、区间事件的概率计算引理（测度＝长度，ℝ 层精确） -/

/-- 闭区间事件刻画：端点全在 [0,1] 内时，载体上取闭区间 [a,b] 的事件就是 Icc a b。 -/
theorem unit_interval_inter_Icc {a b : ℝ} (ha : 0 ≤ a) (hb : b ≤ 1) :
    {x ∈ Icc (0 : ℝ) 1 | a ≤ x ∧ x ≤ b} = Icc a b := by
  ext x
  constructor
  · rintro ⟨_, hax, hxb⟩
    exact ⟨hax, hxb⟩
  · rintro ⟨hax, hxb⟩
    exact ⟨⟨ha.trans hax, hxb.trans hb⟩, hax, hxb⟩

/-- 左开右闭区间事件刻画：端点全在 [0,1] 内时，载体上取 Ioc a b 事件就是 Ioc a b。 -/
theorem unit_interval_inter_Ioc {a b : ℝ} (ha : 0 ≤ a) (hb : b ≤ 1) :
    {x ∈ Icc (0 : ℝ) 1 | a < x ∧ x ≤ b} = Ioc a b := by
  ext x
  constructor
  · rintro ⟨⟨_, hx1⟩, hax, hxb⟩
    exact ⟨hax, hxb⟩
  · rintro ⟨hax, hxb⟩
    exact ⟨⟨(ha.trans_lt hax).le, hxb.trans hb⟩, hax, hxb⟩

/-- 开区间事件刻画：端点全在 [0,1] 内时，载体上取开区间 (a,b) 事件就是 Ioo a b。 -/
theorem unit_interval_inter_Ioo {a b : ℝ} (ha : 0 ≤ a) (hb : b ≤ 1) :
    {x ∈ Icc (0 : ℝ) 1 | a < x ∧ x < b} = Ioo a b := by
  ext x
  constructor
  · rintro ⟨⟨_, hx1⟩, hax, hxb⟩
    exact ⟨hax, hxb⟩
  · rintro ⟨hax, hxb⟩
    exact ⟨⟨(lt_of_le_of_lt ha hax).le, (hxb.trans_le hb).le⟩, hax, hxb⟩

/-- 闭区间事件在 Uniform[0,1] 下的概率＝长度（Lebesgue/Basic.lean:89
`Real.volume_Icc`，ENNReal.ofReal 精确读数）。 -/
theorem uniform_prob_Icc_event {a b : ℝ} (ha : 0 ≤ a) (hb : b ≤ 1) :
    volume {x ∈ Icc (0 : ℝ) 1 | a ≤ x ∧ x ≤ b} = ENNReal.ofReal (b - a) := by
  rw [unit_interval_inter_Icc ha hb, Real.volume_Icc]

/-- 左开右闭区间事件的概率＝长度（`Real.volume_Ioc`，Lebesgue/Basic.lean:113）。 -/
theorem uniform_prob_Ioc_event {a b : ℝ} (ha : 0 ≤ a) (hb : b ≤ 1) :
    volume {x ∈ Icc (0 : ℝ) 1 | a < x ∧ x ≤ b} = ENNReal.ofReal (b - a) := by
  rw [unit_interval_inter_Ioc ha hb, Real.volume_Ioc]

/-- 开区间事件的概率＝长度（`Real.volume_Ioo`，Lebesgue/Basic.lean:99）。 -/
theorem uniform_prob_Ioo_event {a b : ℝ} (ha : 0 ≤ a) (hb : b ≤ 1) :
    volume {x ∈ Icc (0 : ℝ) 1 | a < x ∧ x < b} = ENNReal.ofReal (b - a) := by
  rw [unit_interval_inter_Ioo ha hb, Real.volume_Ioo]

/-- 闭区间事件在概率测度 uniform01 本身上的读数（restrict_apply 化归 ℝ 层）。 -/
theorem uniform01_of_Icc_event {a b : ℝ} (ha : 0 ≤ a) (hb : b ≤ 1) :
    uniform01 {x ∈ Icc (0 : ℝ) 1 | a ≤ x ∧ x ≤ b} = ENNReal.ofReal (b - a) := by
  rw [uniform01, unit_interval_inter_Icc ha hb, Measure.restrict_apply measurableSet_Icc,
    Set.inter_eq_left.mpr (fun x hx => Set.mem_Icc.2 ⟨ha.trans hx.1, hx.2.trans hb⟩),
    Real.volume_Icc]

/-- 单点事件零测：{y ∈ [0,1] | y = x} 是子单集，无原子测度下零测
（`Set.Subsingleton.measure_zero` + NoAtoms 类机制，Typeclasses/NoAtoms.lean:43）。 -/
theorem volume_point_in_unit_interval (x : ℝ) :
    volume {y ∈ Icc (0 : ℝ) 1 | y = x} = 0 := by
  have hsub : {y ∈ Icc (0 : ℝ) 1 | y = x}.Subsingleton := by
    intro a ha b hb
    rw [ha.2, hb.2]
  exact Set.Subsingleton.measure_zero hsub volume

/-- 两两不交 Ioc 区间的有限并：测度＝长度之和（`measure_union`，
MeasureSpace.lean:112）。 -/
theorem volume_disjoint_Ioc_pair {a b c d : ℝ} (h : Disjoint (Ioc a b) (Ioc c d)) :
    volume (Ioc a b ∪ Ioc c d) = ENNReal.ofReal (b - a) + ENNReal.ofReal (d - c) := by
  rw [measure_union h measurableSet_Ioc, Real.volume_Ioc, Real.volume_Ioc]

/-- 有限个两两不交 Ioc 区间之并：测度＝长度之和（`measure_biUnion_finset`，
MeasureSpace.lean:179——有限加性的一般形式）。 -/
theorem volume_finite_disjoint_Ioc (s : Finset ℕ) (f : ℕ → ℝ)
    (hd : PairwiseDisjoint (↑s : Set ℕ) fun i => Ioc (f i) (f (i + 1))) :
    volume (⋃ i ∈ s, Ioc (f i) (f (i + 1)))
      = ∑ i ∈ s, ENNReal.ofReal (f (i + 1) - f i) := by
  rw [measure_biUnion_finset hd (fun i _ => measurableSet_Ioc)]
  exact Finset.sum_congr rfl fun i _ => Real.volume_Ioc

/-- N 等分 Ioc 单元各自的测度恰 1/N（连续版的"每槽质量"，与网格侧 1/N 对照）。 -/
theorem volume_Ioc_nth_cell (N : ℕ) (i : ℕ) :
    volume (Ioc ((i : ℝ) / (N : ℝ)) (((i : ℝ) + 1) / (N : ℝ)))
      = ENNReal.ofReal (1 / (N : ℝ)) := by
  have hlen : ((i : ℝ) + 1) / (N : ℝ) - (i : ℝ) / (N : ℝ) = 1 / (N : ℝ) := by
    rw [div_sub_div_same]
    ring
  rw [Real.volume_Ioc, hlen]

/-- N 等分 Ioc 单元两两不交（有限加性的前提，由端点严格递增导出）。 -/
theorem n_equal_Ioc_pairwise_disjoint (N : ℕ) :
    PairwiseDisjoint (↑(Finset.range N) : Set ℕ)
      fun i => Ioc ((i : ℝ) / (N : ℝ)) (((i : ℝ) + 1) / (N : ℝ)) := by
  intro i hi j hj hij
  refine disjoint_left.mpr fun z hzi hzj => ?_
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · have hiN : i < N := Finset.mem_range.mp (Finset.mem_coe.mp hi)
    have hN : 0 < N := Nat.lt_of_le_of_lt (Nat.zero_le i) hiN
    have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
    have h1 : z * (N : ℝ) ≤ ((i : ℝ) + 1) := (le_div_iff₀ hNpos).mp hzi.2
    have h2 : (j : ℝ) < z * (N : ℝ) := (div_lt_iff₀ hNpos).mp hzj.1
    have h4 : ((i : ℝ) + 1) ≤ (j : ℝ) := by exact_mod_cast hlt
    exact lt_irrefl ((i : ℝ) + 1) (lt_of_le_of_lt h4 (lt_of_lt_of_le h2 h1))
  · have hiN : i < N := Finset.mem_range.mp (Finset.mem_coe.mp hi)
    have hN : 0 < N := Nat.lt_of_le_of_lt (Nat.zero_le i) hiN
    have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
    have h1 : z * (N : ℝ) ≤ ((j : ℝ) + 1) := (le_div_iff₀ hNpos).mp hzj.2
    have h2 : (i : ℝ) < z * (N : ℝ) := (div_lt_iff₀ hNpos).mp hzi.1
    have h4 : ((j : ℝ) + 1) ≤ (i : ℝ) := by exact_mod_cast hgt
    exact lt_irrefl ((j : ℝ) + 1) (lt_of_le_of_lt h4 (lt_of_lt_of_le h2 h1))

/-- 连续版"N 等分网格"读数：N 个 Ioc 单元 (i/N,(i+1)/N] 之并的测度恰 1——
连续世界里等分格的总质量同样是 1，但质量由区间长度承载，不落在点上。 -/
theorem volume_n_equal_Ioc_partition (N : ℕ) (hN : 0 < N) :
    volume (⋃ i ∈ Finset.range N, Ioc ((i : ℝ) / (N : ℝ)) (((i : ℝ) + 1) / (N : ℝ))) = 1 := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  rw [measure_biUnion_finset (n_equal_Ioc_pairwise_disjoint N)
      (fun i _ => measurableSet_Ioc)]
  have hcell : ∀ i ∈ Finset.range N,
      volume (Ioc ((i : ℝ) / (N : ℝ)) (((i : ℝ) + 1) / (N : ℝ)))
        = ENNReal.ofReal (1 / (N : ℝ)) :=
    fun i _ => volume_Ioc_nth_cell N i
  rw [Finset.sum_congr rfl hcell,
    ← ENNReal.ofReal_sum_of_nonneg (fun i _ => le_of_lt (div_pos (by norm_num) hNpos))]
  have hsum : ∑ i ∈ Finset.range N, (1 / (N : ℝ)) = 1 := by
    simp [Finset.card_range]
    exact mul_inv_cancel₀ hNpos.ne'
  rw [hsum]
  simp

/-! ## 三、针 54 主定理（连续版） -/

/-- 真值事件刻画：{x ∈ [0,1] | x ≠ 0} ＝ Ioc 0 1（载体挖去左端点 0）。 -/
theorem truth_event_eq_Ioc : {x ∈ Icc (0 : ℝ) 1 | x ≠ 0} = Ioc (0 : ℝ) 1 := by
  ext x
  constructor
  · rintro ⟨⟨h0, h1⟩, hx⟩
    exact ⟨lt_of_le_of_ne h0 (Ne.symm hx), h1⟩
  · rintro ⟨h0, h1⟩
    exact ⟨⟨le_of_lt h0, h1⟩, ne_of_gt h0⟩

/-- 假点集刻画：{x ∈ [0,1] | x = 0} ＝ {0}（假点恰是载体左端点）。 -/
theorem falsity_event_eq_singleton : {x ∈ Icc (0 : ℝ) 1 | x = 0} = ({0} : Set ℝ) := by
  ext x
  constructor
  · rintro ⟨_, hx0⟩
    exact Set.mem_singleton_iff.2 hx0
  · intro hx
    have hx0 : x = 0 := Set.mem_singleton_iff.1 hx
    subst hx0
    exact ⟨by simp, rfl⟩

/-- 假点集零测（连续机制的落点：单点零测是定理，不是指派）。 -/
theorem falsity_event_volume_zero : volume {x ∈ Icc (0 : ℝ) 1 | x = 0} = 0 := by
  rw [falsity_event_eq_singleton]
  exact Real.volume_singleton

/-- 事件分解：真值事件 ∪ 假点集 ＝ 载体，两集不交，测度 1 + 0 ＝ 1
（`measure_union` 消费；Lebesgue/Basic.lean:126 `Real.volume_singleton`）。 -/
theorem uniform_event_split :
    {x ∈ Icc (0 : ℝ) 1 | x ≠ 0} ∪ {x ∈ Icc (0 : ℝ) 1 | x = 0} = Icc (0 : ℝ) 1 ∧
      Disjoint {x ∈ Icc (0 : ℝ) 1 | x ≠ 0} {x ∈ Icc (0 : ℝ) 1 | x = 0} ∧
      volume {x ∈ Icc (0 : ℝ) 1 | x ≠ 0} + volume {x ∈ Icc (0 : ℝ) 1 | x = 0} = 1 := by
  refine ⟨?_, ?_, ?_⟩
  · ext x
    by_cases hx0 : x = 0
    · simp [hx0]
    · simp [hx0]
  · refine disjoint_left.mpr fun z hz1 hz2 => ?_
    exact hz1.2 hz2.2
  · rw [truth_event_eq_Ioc, falsity_event_eq_singleton, Real.volume_Ioc,
      Real.volume_singleton]
    simp

/-- **针 54 主定理（连续版，附录 I:808）**：ae_truth_not_universal_truth——
    在连续 Uniform[0,1]（勒贝格测度限制在 Icc 0 1，总质量恰 1）上，真值事件
    {x ∈ [0,1] | q x}（q(x) ≡ x ≠ 0）的概率**恰为 1**，而假点 0 就在载体里、
    q 在它上面是假的；假点集是单点 {0}，零测来自勒贝格测度的无原子性（mathlib
    实例 `Real.noAtoms_volume`），不是质量函数的指派。人话：概率 1 真 ≠ 处处真，
    连续版机制＝无原子测度挖去一个零测点，全长不变。 -/
theorem ae_truth_not_universal_truth_uniform :
    -- (1) 载体归一：闭单位区间勒贝格测度恰 1（restrict 即概率测度，无再归一）
    volume (Icc (0 : ℝ) 1) = 1 ∧
    -- (2) 真值事件 {x ∈ [0,1] | x ≠ 0} 的概率恰为 1
    volume {x ∈ Icc (0 : ℝ) 1 | x ≠ 0} = 1 ∧
    -- (3) 假点集合零测（单点零测＝勒贝格无原子）
    volume {x ∈ Icc (0 : ℝ) 1 | x = 0} = 0 ∧
    -- (4) 假点在载体中且 q 在其上为假（0 ∈ [0,1]，(0:ℝ) ≠ 0 不成立）
    (0 ∈ Icc (0 : ℝ) 1 ∧ ¬ ((0 : ℝ) ≠ 0)) ∧
    -- (5) 事件刻画与机制：真值事件＝Ioc 0 1；假点集＝{0}；volume 无原子（实例读数）
    ({x ∈ Icc (0 : ℝ) 1 | x ≠ 0} = Ioc (0 : ℝ) 1 ∧
      {x ∈ Icc (0 : ℝ) 1 | x = 0} = ({0} : Set ℝ) ∧
      NoAtoms (volume : Measure ℝ)) := by
  refine ⟨volume_unit_interval, ?_, falsity_event_volume_zero,
    ⟨Set.mem_Icc.2 ⟨le_refl 0, by norm_num⟩, fun h => h rfl⟩,
    ⟨truth_event_eq_Ioc, falsity_event_eq_singleton, inferInstance⟩⟩
  rw [truth_event_eq_Ioc, Real.volume_Ioc]
  simp

/-- 概率测度 uniform01 本身上的针 54 读数（restrict_apply 化归 ℝ 层 volume）。 -/
theorem uniform01_truth_event : uniform01 {x ∈ Icc (0 : ℝ) 1 | x ≠ 0} = 1 := by
  rw [uniform01, truth_event_eq_Ioc, Measure.restrict_apply measurableSet_Ioc,
    Set.inter_eq_left.mpr (fun x hx => Set.mem_Icc.2 ⟨hx.1.le, hx.2⟩), Real.volume_Ioc]
  simp

/-! ## 四、机制对照：有理网格替身（零质量原子）vs 连续载体（无原子） -/

/-- 旧替身网格质量函数的逐字重述（`UnifiedNeedlesXU.lean` 中 `xuGridMass` 的定义体
    `if i = 0 then 0 else 1/N`）——零耦合引机制对照，旧件不动。 -/
def gridMass (N : ℕ) (i : ℕ) : ℚ := if i = 0 then 0 else 1 / (N : ℚ)

/-- 网格侧总质量（与旧件 `xuGridMassSum` 同值：N 个 1/N 槽加一个 0 质量槽）。 -/
theorem grid_mass_sum_one (N : ℕ) (hN : 0 < N) :
    ∑ i ∈ Finset.range (N + 1), gridMass N i = 1 := by
  show ∑ i ∈ Finset.range (N + 1), (if i = 0 then (0 : ℚ) else 1 / (N : ℚ)) = 1
  have hsplit : ∀ i ∈ Finset.range (N + 1),
      (if i = 0 then (0 : ℚ) else 1 / (N : ℚ)) + (if i = 0 then 1 / (N : ℚ) else 0)
        = 1 / (N : ℚ) := by
    intro i _
    by_cases h0 : i = 0 <;> simp [h0]
  have hdistr : (∑ i ∈ Finset.range (N + 1), (if i = 0 then (0 : ℚ) else 1 / (N : ℚ)))
      + ∑ i ∈ Finset.range (N + 1), (if i = 0 then 1 / (N : ℚ) else 0)
      = ∑ i ∈ Finset.range (N + 1), (1 / (N : ℚ)) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl hsplit
  have hone : ∑ i ∈ Finset.range (N + 1), (if i = 0 then 1 / (N : ℚ) else 0)
      = 1 / (N : ℚ) := by
    rw [Finset.sum_ite_eq']
    simp
  have htotal : ∑ i ∈ Finset.range (N + 1), (1 / (N : ℚ)) = 1 + 1 / (N : ℚ) := by
    have hNq : ((N : ℕ) : ℚ) ≠ 0 := by exact_mod_cast hN.ne'
    simp [Finset.card_range]
    rw [add_mul, mul_inv_cancel₀ hNq, one_mul]
  linarith

/-- **机制对照定理（替身 vs 连续版）**：同一命题（真值事件概率 1 而假点在载体中）
    的两种机制并排。网格替身机制：0 号槽在载体 range (N+1) 中、其质量**被质量函数
    指派**为 0（零质量原子，恰一个槽拿 0、N 个槽拿正原子质量）。连续版机制：
    勒贝格测度**无原子**——每个单点零测是导出性质（`Real.noAtoms_volume`），
    质量由区间长度承载（N 等分单元各恰 1/N、总测度 1，不落在任何点上）。 -/
theorem rational_grid_atom_vs_lebesgue_no_atoms (N : ℕ) (hN : 0 < N) :
    -- 网格侧：0 号槽在载体中且质量被指派为 0；总质量 1
    ((0 : ℕ) ∈ Finset.range (N + 1) ∧ gridMass N 0 = 0 ∧
      ∑ i ∈ Finset.range (N + 1), gridMass N i = 1) ∧
    -- 连续侧：无原子（每单点零测是定理）；N 等分单元各恰 1/N；总测度 1
    (NoAtoms (volume : Measure ℝ) ∧
      (∀ i ∈ Finset.range N,
        volume (Ioc ((i : ℝ) / (N : ℝ)) (((i : ℝ) + 1) / (N : ℝ)))
          = ENNReal.ofReal (1 / (N : ℝ))) ∧
      volume (⋃ i ∈ Finset.range N, Ioc ((i : ℝ) / (N : ℝ)) (((i : ℝ) + 1) / (N : ℝ)))
        = 1) := by
  refine ⟨⟨Finset.mem_range.mpr (by omega), by simp [gridMass], grid_mass_sum_one N hN⟩,
    ⟨inferInstance, fun i _ => volume_Ioc_nth_cell N i,
      volume_n_equal_Ioc_partition N hN⟩⟩

end JurisLean.Seams.UniformContinuous
