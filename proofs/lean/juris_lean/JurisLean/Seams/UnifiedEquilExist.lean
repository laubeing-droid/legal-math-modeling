import Mathlib
import JurisLean.External.FixedPointTheorems.kakutani
import JurisLean.External.GameTheory.Theorems.NashExistenceMixed
import JurisLean.Seams.UnifiedCADCore
import JurisLean.Seams.UnifiedNeedlesGapMid

/-!
# 针 30 余项（W16）：Kakutani 一般存在性 ＋ CAD 输出同一全部均衡关系

Z1 审计（NEEDLE_STRENGTH_AUDIT 针 30 行）判**差额**的三项缺失：
1. 一般有限博弈混合均衡**存在性**定理（Kakutani／上游 NashExistenceMixed 未消费）；
2. "从法律信息/行动菜单构造"的一般构造；
3. "CAD 输出同一全部均衡关系"接线。
W1-8（UnifiedNeedlesGapMid）已交任意玩家/混合/同一均衡关系（IsNash/
nash_iff_no_pure_dev_gain）。本件闭合上述三个余项。

## 路线（对附录 I:784 原句逐项）

合同句："拟直接从法律信息/行动菜单构造有限博弈并用Kakutani，CAD输出同一全部均衡关系"。

**Kakutani——真定理直用（非结构化复现）**：仓内
`External/FixedPointTheorems/kakutani.lean` 的 `kakutani_fixed_point`
（上游 elazarg/fixed-point-theorems-lean4@42d4b401 的 MIT 移植，经 Brouwer
全证明）就是一般拓扑 Kakutani 不动点定理：有限维赋范空间上非空紧凸集内
闭图集值映射（非空凸值、含于域）有不动点。本件在其上把 §8.2 的论证逐件落地：
单纯形积集 `simplexSet`（凸／紧／非空），最优回应集值映射 `brCorr`
（值⊆域；凸值＝最优回应行的凸组合仍最优，引擎 `euR_update_row_affine`；
非空＝有限个线性目标在单纯形顶点取到最大 `best_response_pure_vertex_exists`；
闭图＝有限和多元线性收益的连续性 `continuous_euR_update`），不动点＝Nash
均衡（`fixed_point_brCorr_iff_nash`）。主定理 `finite_legal_mixed_equilibrium_exists`：
任意有限玩家×有限非空行动×实收益表，混合均衡存在——**由 Kakutani 不动点
定理直接导出**。mathlib v4.30.0 本身无 Kakutani（grep 仅 Riesz–Markov–Kakutani
表示定理，无关），消费的正是本仓移植件。

**法律菜单构造**：`LegalEval`（合法利益/制裁的法律评价分型）→
`LegalActionMenu`（行动组合→各玩家法律评价）→ `uReal` 实收益表 →
`finite_legal_mixed_equilibrium_exists_of_menu`。构造直接从法律信息
（评价分型与量化）产出博弈收益，非任意实数表。

**上游消费（同一均衡双向）**：`legalGame u := KernelGame.ofEU` 从同一收益表
构造上游 `KernelGame`；`upstream_nash_iff` 证明上游
`mixedExtension.IsNash σ ↔ IsNashR (toRow σ)`（PMF 剖面 ↔ 实权重剖面，
混合偏差↔实单纯形行经 `pmfOfRow`/`toRow` 双向换算），
`finite_legal_mixed_equilibrium_exists_upstream` 经上游
`mixed_nash_exists_of_bounded`（Nash 映射＋Brouwer 路线的存在性）得到
同一 `IsNashR` 关系的存在性——Kakutani 与上游 Brouwer 两条存在性路线落在
**同一**全部均衡关系上。与 W1-8 的 ℚ 载体关系 `UnifiedNeedlesGapMid.IsNash`
经 `gapmid_nash_iff_real`（纯偏离特征化＋cast 桥）同一。

**CAD 输出同一全部均衡关系**：§8.2 多项式均衡描述
（σ_i≥0、Σσ_i=1、u_i(σ) ≥ u_i(a'_i,σ₋i) 逐纯偏离）编码为 UnifiedCADCore
的 `RealFormula n`（C0 完整编码载体，变量表 `Fin (card (I × Act))` 经
`Fintype.equivFin` 编址）：`cad_output_same_equilibrium_relation`——对任意
实赋值 ρ，`cadEquilFormula.denote ρ ↔ InSimplexR (rowOf ρ) ∧ IsNashR (rowOf ρ)`。
公式解集＝均衡全集（同一"全部均衡"关系，双向）；由存在性得
`cad_equil_solution_nonempty`（解集非空）。诚实边界：CAD 侧接线落在
C0 公式载体层（CAD 求解的输入公式），C1 单变量根证书／C2 投影检查器
不在本针句内，不冒称。

## 纪律

零 sorry／零自定义 axiom／零 `: True`／语句位闭命题；ℚ 侧（GapMid 桥、
CAD 多项式系数）用 ℚ，拓扑/Kakutani/上游侧用 ℝ（合同句"有界实收益"）；
引理名对 pinned mathlib v4.30.0 与仓内移植源核名。
-/

namespace JurisLean.Seams.UnifiedEquilExist

-- 证明位不依赖全部节变量；逐定理 omit 会改写语句内实例、破坏跨定理合一，
-- 文件级关闭该 linter（对证明内容零影响）。
set_option linter.unusedSectionVars false

noncomputable section

/-! ## 一、ℝ 载体镜像（W1-8 的 ℚ 载体在 ℝ 上的同一形态） -/

section RealCarrier

variable {I : Type} [Fintype I] [DecidableEq I] {Act : Type} [Fintype Act] [DecidableEq Act]

/-- 单行概率向量（ℝ 版）：非负且归一。 -/
def RowSimplexR (p : Act → ℝ) : Prop := (∀ a, 0 ≤ p a) ∧ (∑ a, p a = 1)

/-- 混合策略剖面（ℝ 版）：每玩家一条概率向量。 -/
def InSimplexR (σ : I → Act → ℝ) : Prop := ∀ i, RowSimplexR (σ i)

/-- 概率点（ℝ 版）。 -/
def pointR (b : Act) : Act → ℝ := fun a => if a = b then 1 else 0

/-- 纯剖面（ℝ 版）。 -/
def pureMR (p : I → Act) : I → Act → ℝ := fun i a => if a = p i then 1 else 0

theorem pointR_rowSimplex (b : Act) : RowSimplexR (pointR b) := by
  constructor
  · intro a
    simp only [pointR]
    split_ifs <;> norm_num
  · simp only [pointR, Fintype.sum_ite_eq']

theorem pureMR_rowSimplex (p : I → Act) (i : I) : RowSimplexR (pureMR p i) :=
  pointR_rowSimplex (p i)

theorem pureMR_inSimplex (p : I → Act) : InSimplexR (pureMR p) :=
  fun i => pureMR_rowSimplex p i

/-- 期望收益（ℝ 版）：`euR u σ i = Σ_a ∏_j σ_j(a_j) · u_i(a)`。 -/
def euR (u : (I → Act) → I → ℝ) (σ : I → Act → ℝ) (i : I) : ℝ :=
  ∑ a, (∏ j, σ j (a j)) * u a i

theorem euR_pureMR (u : (I → Act) → I → ℝ) (p : I → Act) (i : I) :
    euR u (pureMR p) i = u p i := by
  have hprod : ∀ a : I → Act,
      (∏ j, (if a j = p j then (1 : ℝ) else 0)) = if (∀ j, a j = p j) then 1 else 0 := by
    intro a
    by_cases hall : ∀ j, a j = p j
    · rw [if_pos hall]
      exact Finset.prod_eq_one (fun j _ => by rw [if_pos (hall j)])
    · rw [if_neg hall]
      simp only [not_forall] at hall
      obtain ⟨j₀, hj₀⟩ := hall
      exact Finset.prod_eq_zero (Finset.mem_univ j₀) (by rw [if_neg hj₀])
  have hstep : ∀ a : I → Act, (∏ j, pureMR p j (a j)) * u a i = if a = p then u p i else 0 := by
    intro a
    simp only [pureMR]
    rw [hprod a]
    by_cases hall : ∀ j, a j = p j
    · rw [if_pos hall, if_pos (funext hall), funext hall]
      ring
    · simp only [not_forall] at hall
      obtain ⟨j₀, hj₀⟩ := hall
      rw [if_neg (fun hxe => hj₀ (hxe j₀)), if_neg (fun hxe => hj₀ (congrFun hxe j₀))]
      ring
  show (∑ a, (∏ j, pureMR p j (a j)) * u a i) = u p i
  rw [Finset.sum_congr rfl (fun a _ => hstep a)]
  simp only [Fintype.sum_ite_eq']

/-- 点质量求值（ℝ 版）。 -/
theorem sum_pointR_weight (σ' : Act → ℝ) (b : Act) :
    ∑ a', σ' a' * (pointR a') b = σ' b := by
  have h : ∀ a', σ' a' * (pointR a') b = if b = a' then σ' a' else 0 := by
    intro a'
    simp only [pointR]
    split_ifs <;> ring
  calc ∑ a', σ' a' * (pointR a') b
      = ∑ a', if b = a' then σ' a' else 0 := Finset.sum_congr rfl (fun a' _ => h a')
    _ = σ' b := Fintype.sum_ite_eq b (fun a' => σ' a')

/-- 行因子分解：玩家 i 换行 τ 后的混合权重积按行分解
    （GapMid `eu_dev_linear` 证明内 hfac 的 ℝ 同型）。 -/
theorem prod_updateR_factor (σ : I → Act → ℝ) (i : I) (τ : Act → ℝ) (a : I → Act) :
    (∏ j, Function.update σ i τ j (a j))
      = τ (a i) * ∏ j ∈ Finset.univ \ ({i} : Finset I), σ j (a j) := by
  have hperj : ∀ j : I, Function.update σ i τ j (a j)
      = Function.update (fun k => σ k (a k)) i (τ (a i)) j := by
    intro j
    by_cases hji : j = i
    · subst hji
      rw [Function.update_apply, Function.update_apply, if_pos rfl, if_pos rfl]
    · rw [Function.update_apply, Function.update_apply, if_neg hji, if_neg hji]
  rw [Finset.prod_congr rfl (fun j _ => hperj j)]
  exact Finset.prod_update_of_mem (Finset.mem_univ i) (fun k => σ k (a k)) (τ (a i))

/-- 凸组合（线性）引理（ℝ 版）：换行后期望＝各纯偏离期望的 σ'-加权平均。 -/
theorem euR_dev_linear (u : (I → Act) → I → ℝ) (σ : I → Act → ℝ) (i : I) (σ' : Act → ℝ)
    (_hσ' : RowSimplexR σ') :
    euR u (Function.update σ i σ') i
      = ∑ a', σ' a' * euR u (Function.update σ i (pointR a')) i := by
  have hpoint : ∀ a' : Act, euR u (Function.update σ i (pointR a')) i
      = ∑ a, ((pointR a') (a i) * ∏ j ∈ Finset.univ \ ({i} : Finset I), σ j (a j)) * u a i := by
    intro a'
    simp only [euR, prod_updateR_factor]
  show (∑ a, (∏ j, Function.update σ i σ' j (a j)) * u a i)
      = ∑ a', σ' a' * euR u (Function.update σ i (pointR a')) i
  simp only [prod_updateR_factor, hpoint]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  have hterm : ∀ a' : Act,
      σ' a' * (((pointR a') (a i) * ∏ j ∈ Finset.univ \ ({i} : Finset I), σ j (a j)) * u a i)
        = (σ' a' * (pointR a') (a i))
          * ((∏ j ∈ Finset.univ \ ({i} : Finset I), σ j (a j)) * u a i) := fun a' => by ring
  rw [Finset.sum_congr rfl (fun a' _ => hterm a'), ← Finset.sum_mul, sum_pointR_weight]
  ring

/-- 同一"全部均衡"关系（ℝ 版，全偏差定义）：任意玩家任意混合偏差不获益。 -/
def IsNashR (u : (I → Act) → I → ℝ) (σ : I → Act → ℝ) : Prop :=
  ∀ (i : I) (σ' : Act → ℝ), RowSimplexR σ' →
    euR u (Function.update σ i σ') i ≤ euR u σ i

/-- 纯偏离特征化（ℝ 版；GapMid `nash_iff_no_pure_dev_gain` 的 ℝ 同型，
    CAD 多项式描述的偏差侧依据）。 -/
theorem nashR_iff_no_pure_dev_gain (u : (I → Act) → I → ℝ) (σ : I → Act → ℝ) :
    IsNashR u σ ↔ ∀ (i : I) (b : Act),
      euR u (Function.update σ i (pointR b)) i ≤ euR u σ i := by
  constructor
  · intro h i b
    exact h i (pointR b) (pointR_rowSimplex b)
  · intro h i σ' hσ'
    show euR u (Function.update σ i σ') i ≤ euR u σ i
    rw [euR_dev_linear u σ i σ' hσ']
    calc ∑ a', σ' a' * euR u (Function.update σ i (pointR a')) i
        ≤ ∑ a', σ' a' * euR u σ i :=
          Finset.sum_le_sum (fun a' _ =>
            mul_le_mul_of_nonneg_left (h i a') (hσ'.1 a'))
      _ = (∑ a', σ' a') * euR u σ i := (Finset.sum_mul _ _ _).symm
      _ = 1 * euR u σ i := by rw [hσ'.2]
      _ = euR u σ i := one_mul _

end RealCarrier

/-! ## 二、Kakutani 部件与存在性主定理（针 30 余项之一） -/

section Kakutani

variable {I : Type} [Fintype I] [DecidableEq I] {Act : Type} [Fintype Act] [DecidableEq Act]
  [Nonempty Act]


/-- 单纯形积集（§8.2"混合策略是单纯形积"）。 -/
def simplexSet : Set (I → Act → ℝ) := {σ | InSimplexR σ}

theorem simplexSet_nonempty : (simplexSet : Set (I → Act → ℝ)).Nonempty :=
  ⟨pureMR (fun _ => Classical.arbitrary Act), pureMR_inSimplex _⟩

theorem simplexSet_convex : Convex ℝ (simplexSet : Set (I → Act → ℝ)) := by
  rw [convex_iff_add_mem]
  intro x hx y hy a b ha hb hab
  simp only [simplexSet, Set.mem_setOf_eq] at hx hy ⊢
  intro i
  constructor
  · intro c
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact add_nonneg (mul_nonneg ha ((hx i).1 c)) (mul_nonneg hb ((hy i).1 c))
  · have hrow : ∑ c, (a • x + b • y) i c = a * ∑ c, x i c + b * ∑ c, y i c := by
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
        Finset.mul_sum]
    rw [hrow, (hx i).2, (hy i).2, mul_one, mul_one]
    exact hab

theorem simplexSet_isClosed : IsClosed (simplexSet : Set (I → Act → ℝ)) := by
  have h1 : IsClosed (⋂ p : I × Act, {σ : I → Act → ℝ | 0 ≤ σ p.1 p.2}) :=
    isClosed_iInter (fun p =>
      isClosed_le continuous_const
        ((continuous_apply p.2).comp (continuous_apply p.1)))
  have h2 : IsClosed (⋂ i : I, {σ : I → Act → ℝ | ∑ a, σ i a = 1}) :=
    isClosed_iInter (fun i =>
      isClosed_eq
        (continuous_finsetSum Finset.univ (fun a _ =>
          (continuous_apply a).comp (continuous_apply i)))
        continuous_const)
  have heq : (simplexSet : Set (I → Act → ℝ))
      = (⋂ p : I × Act, {σ : I → Act → ℝ | 0 ≤ σ p.1 p.2}) ∩
        (⋂ i : I, {σ : I → Act → ℝ | ∑ a, σ i a = 1}) := by
    ext σ
    simp only [simplexSet, Set.mem_setOf_eq, Set.mem_iInter, Set.mem_inter_iff]
    constructor
    · intro h
      exact ⟨fun p => (h p.1).1 p.2, fun i => (h i).2⟩
    · intro h i
      exact ⟨fun a => h.1 (i, a), h.2 i⟩
  rw [heq]
  exact h1.inter h2

theorem simplexSet_isBounded : Bornology.IsBounded (simplexSet : Set (I → Act → ℝ)) := by
  refine Bornology.IsBounded.subset
    (t := Metric.closedBall (0 : I → Act → ℝ) 1) Metric.isBounded_closedBall ?_
  intro σ hσ
  have hcoord : ∀ (i : I) (a : Act), |σ i a| ≤ 1 := by
    intro i a
    have hnonneg : 0 ≤ σ i a := (hσ i).1 a
    have hsum : σ i a ≤ ∑ a', σ i a' :=
      Finset.single_le_sum (fun a' _ => (hσ i).1 a') (Finset.mem_univ a)
    rw [(hσ i).2] at hsum
    exact abs_le.mpr ⟨by linarith, hsum⟩
  have hrow : ∀ i, ‖σ i‖ ≤ 1 := fun i =>
    (pi_norm_le_iff_of_nonneg zero_le_one).mpr (fun a => hcoord i a)
  simp only [Metric.mem_closedBall, dist_zero_right]
  exact (pi_norm_le_iff_of_nonneg zero_le_one).mpr hrow

theorem simplexSet_compact : IsCompact (simplexSet : Set (I → Act → ℝ)) :=
  Metric.isCompact_iff_isClosed_bounded.mpr
    ⟨simplexSet_isClosed, simplexSet_isBounded⟩


/-- 换行期望的连续性：`(σ, τ) ↦ euR u (update σ i τ) i`（Kakutani 闭图
    前提——有限和多元线性收益的连续性）。 -/
theorem continuous_euR_update (u : (I → Act) → I → ℝ) (i : I) :
    Continuous fun q : (I → Act → ℝ) × (Act → ℝ) => euR u (Function.update q.1 i q.2) i := by
  have hfac : ∀ (q : (I → Act → ℝ) × (Act → ℝ)) (a : I → Act),
      (∏ j, Function.update q.1 i q.2 j (a j)) * u a i
        = (∏ j, if j = i then q.2 (a j) else q.1 j (a j)) * u a i := by
    intro q a
    refine congrArg (fun t => t * u a i) ?_
    refine Finset.prod_congr rfl (fun j _ => ?_)
    by_cases hji : j = i
    · simp only [Function.update_apply, if_pos hji]
    · simp only [Function.update_apply, if_neg hji]
  simp only [euR, hfac]
  refine continuous_finsetSum Finset.univ (fun a _ => ?_)
  refine Continuous.mul ?_ continuous_const
  refine continuous_finsetProd Finset.univ (fun j _ => ?_)
  by_cases hji : j = i
  · simp only [if_pos hji]
    exact (continuous_apply (a j)).comp continuous_snd
  · simp only [if_neg hji]
    exact (continuous_apply (a j)).comp ((continuous_apply j).comp continuous_fst)

/-- 单方最优回应集值映射（Kakutani 载体）：τ ∈ brCorr σ 当且仅当
    τ 在单纯形积内且每玩家的 τ-行是对 σ₋ᵢ 的最优回应。 -/
def brCorr (u : (I → Act) → I → ℝ) (σ : (simplexSet : Set (I → Act → ℝ))) :
    Set (I → Act → ℝ) :=
  {τ : I → Act → ℝ |
    InSimplexR τ ∧ ∀ (i : I) (ρ : Act → ℝ), RowSimplexR ρ →
      euR u (Function.update (σ : I → Act → ℝ) i ρ) i
        ≤ euR u (Function.update (σ : I → Act → ℝ) i (τ i)) i}

/-- Kakutani 成分一（最优回应集非空）：每个玩家对任意他方行存在纯行动
    最优回应——有限个线性目标在单纯形顶点取到最大。 -/
theorem best_response_pure_vertex_exists (u : (I → Act) → I → ℝ) (σ : I → Act → ℝ) (i : I) :
    ∃ b : Act, ∀ ρ : Act → ℝ, RowSimplexR ρ →
      euR u (Function.update σ i ρ) i ≤ euR u (Function.update σ i (pointR b)) i := by
  obtain ⟨b, _, hmax⟩ := Finset.exists_max_image (Finset.univ : Finset Act)
    (fun b => euR u (Function.update σ i (pointR b)) i)
    Finset.univ_nonempty
  refine ⟨b, fun ρ hρ => ?_⟩
  rw [euR_dev_linear u σ i ρ hρ]
  calc ∑ a', ρ a' * euR u (Function.update σ i (pointR a')) i
      ≤ ∑ a', ρ a' * euR u (Function.update σ i (pointR b)) i :=
        Finset.sum_le_sum (fun a' _ =>
          mul_le_mul_of_nonneg_left (hmax a' (Finset.mem_univ a')) (hρ.1 a'))
    _ = (∑ a', ρ a') * euR u (Function.update σ i (pointR b)) i :=
          (Finset.sum_mul _ _ _).symm
    _ = euR u (Function.update σ i (pointR b)) i := by rw [hρ.2]; ring



/-- 换行期望对行的仿射性（Kakutani 成分二"凸值"的引擎：
    最优回应行的凸组合仍最优）。 -/
theorem euR_update_row_affine (u : (I → Act) → I → ℝ) (σ : I → Act → ℝ) (i : I)
    (r1 r2 : Act → ℝ) (a b : ℝ) :
    euR u (Function.update σ i (a • r1 + b • r2)) i
      = a * euR u (Function.update σ i r1) i + b * euR u (Function.update σ i r2) i := by
  simp only [euR, prod_updateR_factor]
  have hrow : ∀ c : Act, (a • r1 + b • r2) c = a * r1 c + b * r2 c := by
    intro c
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  simp only [hrow]
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun a' _ => ?_)
  ring

theorem brCorr_values (u : (I → Act) → I → ℝ) :
    ∀ x : (simplexSet : Set (I → Act → ℝ)),
      brCorr u x ⊆ simplexSet ∧ Convex ℝ (brCorr u x) ∧ (brCorr u x).Nonempty := by
  intro x
  refine ⟨?_, ?_, ?_⟩
  · intro τ hτ
    exact hτ.1
  · rw [convex_iff_add_mem]
    intro τ1 h1 τ2 h2 a b ha hb hab
    have hsx : InSimplexR (a • τ1 + b • τ2) := by
      intro i
      constructor
      · intro c
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        exact add_nonneg (mul_nonneg ha ((h1.1 i).1 c)) (mul_nonneg hb ((h2.1 i).1 c))
      · have hrow : ∑ c, (a • τ1 + b • τ2) i c = a * ∑ c, τ1 i c + b * ∑ c, τ2 i c := by
          simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
            Finset.mul_sum]
        rw [hrow, (h1.1 i).2, (h2.1 i).2, mul_one, mul_one]
        exact hab
    refine ⟨hsx, fun i ρ hρ => ?_⟩
    have hb1 := h1.2 i ρ hρ
    have hb2 := h2.2 i ρ hρ
    rw [show (a • τ1 + b • τ2) i = a • τ1 i + b • τ2 i from rfl,
      euR_update_row_affine u _ i (τ1 i) (τ2 i) a b]
    calc euR u (Function.update (x : I → Act → ℝ) i ρ) i
        = (a + b) * euR u (Function.update (x : I → Act → ℝ) i ρ) i := by rw [hab, one_mul]
      _ = a * euR u (Function.update (x : I → Act → ℝ) i ρ) i
            + b * euR u (Function.update (x : I → Act → ℝ) i ρ) i := by ring
      _ ≤ a * euR u (Function.update (x : I → Act → ℝ) i (τ1 i)) i
            + b * euR u (Function.update (x : I → Act → ℝ) i (τ2 i)) i :=
            add_le_add (mul_le_mul_of_nonneg_left hb1 ha)
              (mul_le_mul_of_nonneg_left hb2 hb)
  · have hex : ∀ i : I, ∃ b : Act, ∀ ρ : Act → ℝ, RowSimplexR ρ →
        euR u (Function.update (x : I → Act → ℝ) i ρ) i
          ≤ euR u (Function.update (x : I → Act → ℝ) i (pointR b)) i :=
      fun i => best_response_pure_vertex_exists u (x : I → Act → ℝ) i
    choose b hb using hex
    exact ⟨fun i => pointR (b i), fun i => pointR_rowSimplex _, fun i ρ hρ => hb i ρ hρ⟩

theorem brCorr_closedGraph (u : (I → Act) → I → ℝ) : closedGraph (brCorr u) := by
  have hA : IsClosed {p : ↥(simplexSet : Set (I → Act → ℝ)) × (I → Act → ℝ) |
      InSimplexR p.2} := by
    have h : IsClosed ((Prod.snd : ↥(simplexSet : Set (I → Act → ℝ)) × (I → Act → ℝ) →
        (I → Act → ℝ)) ⁻¹' (simplexSet : Set (I → Act → ℝ))) :=
      IsClosed.preimage continuous_snd simplexSet_isClosed
    simpa only [Set.preimage_setOf_eq] using h
  have hB : IsClosed {p : ↥(simplexSet : Set (I → Act → ℝ)) × (I → Act → ℝ) |
      ∀ (i : I) (ρ : Act → ℝ), RowSimplexR ρ →
        euR u (Function.update (p.1 : I → Act → ℝ) i ρ) i
          ≤ euR u (Function.update (p.1 : I → Act → ℝ) i (p.2 i)) i} := by
    have heqB : {p : ↥(simplexSet : Set (I → Act → ℝ)) × (I → Act → ℝ) |
        ∀ (i : I) (ρ : Act → ℝ), RowSimplexR ρ →
          euR u (Function.update (p.1 : I → Act → ℝ) i ρ) i
            ≤ euR u (Function.update (p.1 : I → Act → ℝ) i (p.2 i)) i}
        = ⋂ (i : I), ⋂ (ρ : {ρ : Act → ℝ | RowSimplexR ρ}),
            {p : ↥(simplexSet : Set (I → Act → ℝ)) × (I → Act → ℝ) |
              euR u (Function.update (p.1 : I → Act → ℝ) i (↑ρ : Act → ℝ)) i
                ≤ euR u (Function.update (p.1 : I → Act → ℝ) i (p.2 i)) i} := by
      ext p
      simp only [Set.mem_iInter, Set.mem_setOf_eq, Subtype.forall]
    rw [heqB]
    refine isClosed_iInter (fun i => isClosed_iInter (fun ρ => ?_))
    have hg2 : Continuous fun p :
        ↥(simplexSet : Set (I → Act → ℝ)) × (I → Act → ℝ) => (p.2 i : Act → ℝ) :=
      (continuous_apply i).comp continuous_snd
    have hg : Continuous fun p :
        ↥(simplexSet : Set (I → Act → ℝ)) × (I → Act → ℝ) =>
        ((p.1 : I → Act → ℝ), (p.2 i : Act → ℝ)) :=
      Continuous.prodMk (continuous_subtype_val.comp continuous_fst) hg2
    exact
      isClosed_le
        ((continuous_euR_update u i).comp
          (Continuous.prodMk (continuous_subtype_val.comp continuous_fst) continuous_const))
        ((continuous_euR_update u i).comp hg)
  have heq : {z : ↥(simplexSet : Set (I → Act → ℝ)) × (I → Act → ℝ) | z.2 ∈ brCorr u z.1}
      = {p : ↥(simplexSet : Set (I → Act → ℝ)) × (I → Act → ℝ) | InSimplexR p.2} ∩
        {p : ↥(simplexSet : Set (I → Act → ℝ)) × (I → Act → ℝ) |
          ∀ (i : I) (ρ : Act → ℝ), RowSimplexR ρ →
            euR u (Function.update (p.1 : I → Act → ℝ) i ρ) i
              ≤ euR u (Function.update (p.1 : I → Act → ℝ) i (p.2 i)) i} := rfl
  unfold closedGraph
  rw [heq]
  exact hA.inter hB

/-- Kakutani 成分四（不动点＝均衡）：brCorr 的不动点恰是 Nash 均衡
    （同一 `IsNashR` 关系）。 -/
theorem fixed_point_brCorr_iff_nash (u : (I → Act) → I → ℝ) (τ : I → Act → ℝ)
    (hτ : τ ∈ simplexSet) :
    τ ∈ brCorr u ⟨τ, hτ⟩ ↔ IsNashR u τ := by
  have hself : ∀ (i : I), Function.update
      ((⟨τ, hτ⟩ : ↥(simplexSet : Set (I → Act → ℝ))) : I → Act → ℝ) i (τ i)
      = ((⟨τ, hτ⟩ : ↥(simplexSet : Set (I → Act → ℝ))) : I → Act → ℝ) :=
    fun i => by simp
  constructor
  · intro h i ρ hρ
    have htle := h.2 i ρ hρ
    rw [hself i] at htle
    exact htle
  · intro h
    refine ⟨hτ, fun i ρ hρ => ?_⟩
    rw [hself i]
    exact h i ρ hρ

/-- **针 30 余项主定理（Kakutani 路线）**：任意有限玩家×有限非空行动×
    实收益表的有限博弈，混合策略 Nash 均衡存在——由仓内移植的一般拓扑
    Kakutani 不动点定理直接导出。 -/
theorem finite_legal_mixed_equilibrium_exists (u : (I → Act) → I → ℝ) :
    ∃ σ : I → Act → ℝ, InSimplexR σ ∧ IsNashR u σ := by
  obtain ⟨x, hx⟩ := kakutani_fixed_point (V := I → Act → ℝ)
    (simplexSet : Set (I → Act → ℝ)) simplexSet_convex simplexSet_compact simplexSet_nonempty
    (brCorr u) (brCorr_closedGraph u) (brCorr_values u)
  have hmem : x.1 ∈ brCorr u x := hx
  exact ⟨x.1, hmem.1, (fixed_point_brCorr_iff_nash u x.1 (hmem.1)).mp hmem⟩

end Kakutani

/-! ## 三、法律信息/行动菜单构造（针 30 余项之二） -/

section LegalMenu

/-- 法律评价分型：合法利益（有理编码）／制裁（违约、不法成本）。 -/
inductive LegalEval
  | lawful (v : ℚ)
  | sanction (c : ℚ)

/-- 法律评价的有理读数：合法利益取正值，制裁取负成本。 -/
def LegalEval.toQ : LegalEval → ℚ
  | .lawful v => v
  | .sanction c => -c

/-- 法律行动菜单：有限玩家 × 共同有限行动菜单 × 每个行动组合的法律评价
    （"从法律信息/行动菜单构造有限博弈"的法律信息侧输入——收益不是任意
    实数表，而是法律评价分型的量化读数）。 -/
structure LegalActionMenu (I Act : Type) where
  pay : (I → Act) → I → LegalEval

/-- 菜单的实收益表：法律评价读数的实嵌入。 -/
def LegalActionMenu.uReal {I Act : Type} (m : LegalActionMenu I Act) :
    (I → Act) → I → ℝ := fun a i => (m.pay a i).toQ

/-- **针 30（合同形）**：直接从法律信息/行动菜单构造有限博弈并用 Kakutani
    ——菜单型构造的混合均衡存在性。 -/
theorem finite_legal_mixed_equilibrium_exists_of_menu {I : Type} [Fintype I] [DecidableEq I]
    {Act : Type} [Fintype Act] [DecidableEq Act] [Nonempty Act]
    (m : LegalActionMenu I Act) :
    ∃ σ : I → Act → ℝ, InSimplexR σ ∧ IsNashR m.uReal σ :=
  finite_legal_mixed_equilibrium_exists m.uReal

end LegalMenu

/-! ## 四、上游消费：NashExistenceMixed 与同一均衡双向（针 30 余项之一收口） -/

section Upstream

variable {I : Type} [Fintype I] [DecidableEq I] {Act : Type} [Fintype Act] [DecidableEq Act]
  [Nonempty Act]

open GameTheory

/-- 从同一实收益表直接构造上游 `KernelGame`（战略式标准编码：
    策略=行动、结果=行动组合、核=点质量、收益=表值）。`@[reducible]`
    使实例合成能透见 Strategy/Outcome 即 Act／I → Act。 -/
@[reducible]
def legalGame (u : (I → Act) → I → ℝ) : KernelGame I where
  Strategy := fun _ => Act
  Outcome := I → Act
  utility := fun ω who => u ω who
  outcomeKernel := fun σ => PMF.pure σ

theorem legalGame_Strategy_eq (u : (I → Act) → I → ℝ) (i : I) :
    (legalGame u).Strategy i = Act := rfl

theorem legalGame_eu_pure (u : (I → Act) → I → ℝ) (s : I → Act) (i : I) :
    (legalGame u).eu s i = u s i := by
  simp only [KernelGame.eu, legalGame, Math.Probability.expect_pure]

/-- 上游混合剖面 → 实权重剖面。 -/
def toRow (σ : ∀ _ : I, PMF Act) : I → Act → ℝ := fun i a => (σ i a).toReal

theorem toRow_inSimplex (σ : ∀ _ : I, PMF Act) : InSimplexR (toRow σ) :=
  fun i => ⟨fun _ => ENNReal.toReal_nonneg, Math.Probability.pmf_toReal_sum_one (σ i)⟩

/-- 实单纯形行 → 上游混合策略（roundtrip 之源）。 -/
def pmfOfRow {ρ : Act → ℝ} (h1 : ∀ a, 0 ≤ ρ a) (h2 : ∑ a, ρ a = 1) : PMF Act :=
  PMF.ofFintype (fun a => ENNReal.ofReal (ρ a))
    (by rw [← ENNReal.ofReal_sum_of_nonneg (fun a _ => h1 a), h2, ENNReal.ofReal_one])

theorem pmfOfRow_toReal {ρ : Act → ℝ} (h1 : ∀ a, 0 ≤ ρ a) (h2 : ∑ a, ρ a = 1) (a : Act) :
    (pmfOfRow h1 h2 a).toReal = ρ a := by
  simp only [pmfOfRow, PMF.ofFintype_apply]
  exact ENNReal.toReal_ofReal (h1 a)

theorem toRow_update (σ : ∀ _ : I, PMF Act) (i : I) (τ : PMF Act) :
    toRow (Function.update σ i τ) = Function.update (toRow σ) i (fun a => (τ a).toReal) := by
  funext j a
  by_cases hji : j = i
  · subst hji
    simp [toRow]
  · simp [toRow, hji]

theorem toRow_update_pmf (σ : ∀ _ : I, PMF Act) (i : I) (ρ : Act → ℝ)
    (h1 : ∀ a, 0 ≤ ρ a) (h2 : ∑ a, ρ a = 1) :
    toRow (Function.update σ i (pmfOfRow h1 h2))
      = Function.update (toRow σ) i ρ := by
  rw [toRow_update σ i (pmfOfRow h1 h2)]
  exact congrArg (Function.update (toRow σ) i) (funext fun a => pmfOfRow_toReal h1 h2 a)

theorem legalGame_bound (u : (I → Act) → I → ℝ) (i : I) (ω : I → Act) :
    |(legalGame u).utility ω i| ≤ ∑ a, |u a i| := by
  show |u ω i| ≤ ∑ a, |u a i|
  exact Finset.single_le_sum (f := fun a => |u a i|)
    (fun a _ => abs_nonneg (u a i)) (Finset.mem_univ ω)

/-- 上游混合延拓期望＝ℝ 载体期望（同一收益表、同一剖面读数）。 -/
theorem legalGame_mixedExtension_eu (u : (I → Act) → I → ℝ) (σ : ∀ _ : I, PMF Act) (i : I) :
    (legalGame u).mixedExtension.eu σ i = euR u (toRow σ) i := by
  rw [GameTheory.KernelGame.mixedExtension_eu_of_bounded (legalGame u) σ i (legalGame_bound u i)]
  simp only [legalGame_eu_pure]
  rw [Math.Probability.expect_eq_sum]
  simp only [Math.PMFProduct.pmfPi_apply, ENNReal.toReal_prod]
  rfl

/-- **同一均衡双向**：上游 `mixedExtension.IsNash` ↔ ℝ 载体 `IsNashR`
    （PMF 偏差与实单纯形行偏差经 `pmfOfRow`/`toRow` 互相换算，
    偏差域重合，不是单向包含）。 -/
theorem upstream_nash_iff (u : (I → Act) → I → ℝ) (σ : ∀ _ : I, PMF Act) :
    (legalGame u).mixedExtension.IsNash σ ↔ IsNashR u (toRow σ) := by
  constructor
  · intro h i ρ hρ
    have hdev := h i (pmfOfRow hρ.1 hρ.2)
    have h1 : euR u (Function.update (toRow σ) i ρ) i
        = (legalGame u).mixedExtension.eu (Function.update σ i (pmfOfRow hρ.1 hρ.2)) i := by
      rw [legalGame_mixedExtension_eu]
      congr 1
      exact (toRow_update_pmf σ i ρ hρ.1 hρ.2).symm
    have h2 : euR u (toRow σ) i = (legalGame u).mixedExtension.eu σ i :=
      (legalGame_mixedExtension_eu u σ i).symm
    linarith [hdev, h1, h2]
  · intro h i p
    let p' : PMF Act := p
    have hprow : RowSimplexR (fun a => (p' a).toReal) :=
      ⟨fun _ => ENNReal.toReal_nonneg, Math.Probability.pmf_toReal_sum_one p'⟩
    have hdev := h i (fun a => (p' a).toReal) hprow
    have h1 : euR u (Function.update (toRow σ) i (fun a => (p' a).toReal)) i
        = (legalGame u).mixedExtension.eu (Function.update σ i p') i := by
      rw [legalGame_mixedExtension_eu]
      congr 1
      exact (toRow_update σ i p').symm
    have h2 : euR u (toRow σ) i = (legalGame u).mixedExtension.eu σ i :=
      (legalGame_mixedExtension_eu u σ i).symm
    show (legalGame u).mixedExtension.eu (Function.update σ i p') i
      ≤ (legalGame u).mixedExtension.eu σ i
    rw [← h1, ← h2]
    exact hdev

/-- **针 30 余项（上游路线）**：经上游 `mixed_nash_exists`
    （Nash 映射＋Brouwer 路线的存在性；本构造结果集有限，
    有限结果版与有界版同时可用）得到同一 `IsNashR` 关系的
    混合均衡存在性——与 Kakutani 路线（`finite_legal_mixed_equilibrium_exists`）
    落在同一全部均衡关系上。 -/
theorem finite_legal_mixed_equilibrium_exists_upstream (u : (I → Act) → I → ℝ) :
    ∃ σ : I → Act → ℝ, InSimplexR σ ∧ IsNashR u σ := by
  obtain ⟨σ, hσ⟩ := GameTheory.KernelGame.mixed_nash_exists_of_bounded
    (G := legalGame u) (ι := I) (C := fun who => ∑ a, |u a who|)
    (fun who ω => legalGame_bound u who ω)
  exact ⟨toRow σ, toRow_inSimplex σ, (upstream_nash_iff u σ).mp hσ⟩

end Upstream

/-! ## 五、GapMid ℚ 载体桥（与 W1-8 同一均衡关系的换算） -/

section GapMidBridge

variable {I : Type} [Fintype I] [DecidableEq I] {Act : Type} [Fintype Act] [DecidableEq Act]

/-- ℚ 剖面的实嵌入（收益表另配）。 -/
def castProfile (σ : I → Act → ℚ) : I → Act → ℝ := fun i a => (σ i a : ℝ)

theorem euR_cast (u : (I → Act) → I → ℚ) (σ : I → Act → ℚ) (i : I) :
    euR (fun a j => (u a j : ℝ)) (castProfile σ) i = (UnifiedNeedlesGapMid.eu u σ i : ℝ) := by
  simp only [euR, UnifiedNeedlesGapMid.eu, castProfile]
  rw [Rat.cast_sum]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  push_cast
  ring

theorem castProfile_update (σ : I → Act → ℚ) (i : I) (τ : Act → ℚ) :
    castProfile (Function.update σ i τ)
      = Function.update (castProfile σ) i (fun a => (τ a : ℝ)) := by
  funext j a
  by_cases hji : j = i
  · subst hji
    simp [castProfile]
  · simp [castProfile, hji]

theorem pointR_cast_eq (b : Act) : (fun a => (UnifiedNeedlesGapMid.point b a : ℝ)) = pointR b := by
  funext a
  simp only [UnifiedNeedlesGapMid.point, pointR]
  by_cases hab : a = b <;> simp [hab]

theorem castProfile_inSimplex (σ : I → Act → ℚ)
    (hs : UnifiedNeedlesGapMid.InSimplex σ) : InSimplexR (castProfile σ) := by
  intro i
  constructor
  · intro a
    exact Rat.cast_nonneg.mpr ((hs i).1 a)
  · show ∑ a, ((σ i a : ℚ) : ℝ) = 1
    rw [← Rat.cast_sum, (hs i).2]
    norm_num

/-- **与 W1-8 同一均衡关系（ℚ↔ℝ cast 桥）**：GapMid 的 `IsNash`
    （ℚ 载体、全偏差）与本文 `IsNashR`（ℝ 载体、全偏差）经纯偏离特征化
    ＋cast 同一——ℚ 有理偏差判定已含实偏差判定（线性目标在纯顶点取极值）。 -/
theorem gapmid_nash_iff_real (u : (I → Act) → I → ℚ) (σ : I → Act → ℚ) :
    UnifiedNeedlesGapMid.IsNash u σ ↔
      IsNashR (fun a j => (u a j : ℝ)) (castProfile σ) := by
  have hcast : ∀ (i : I) (b : Act),
      euR (fun a j => (u a j : ℝ))
          (Function.update (castProfile σ) i (pointR b)) i
        = (UnifiedNeedlesGapMid.eu u
            (Function.update σ i (UnifiedNeedlesGapMid.point b)) i : ℝ) := by
    intro i b
    rw [← euR_cast u (Function.update σ i (UnifiedNeedlesGapMid.point b)) i,
      castProfile_update, pointR_cast_eq]
  rw [UnifiedNeedlesGapMid.nash_iff_no_pure_dev_gain, nashR_iff_no_pure_dev_gain]
  constructor
  · intro h i b
    have h3 := h i b
    have h4 := hcast i b
    rw [h4, euR_cast u σ i]
    exact Rat.cast_le.mpr h3
  · intro h i b
    have h3 := h i b
    have h4 := hcast i b
    rw [h4, euR_cast u σ i] at h3
    exact Rat.cast_le.mp h3

end GapMidBridge

/-! ## 六、CAD 输出同一全部均衡关系（针 30 余项之三） -/

section CAD

variable {I : Type} [Fintype I] [DecidableEq I] {Act : Type} [Fintype Act] [DecidableEq Act]

open JurisLean.Seams.UnifiedCADCore

/-- CAD 变量表长度：玩家×行动对数。 -/
def cadVarN (I : Type) [Fintype I] (Act : Type) [Fintype Act] : ℕ :=
  Fintype.card (I × Act)

/-- 变量编址：玩家×行动对 → 表位。 -/
def cadIdx (I : Type) [Fintype I] (Act : Type) [Fintype Act] :
    I × Act ≃ Fin (cadVarN I Act) :=
  Fintype.equivFin (I × Act)

/-- 表赋值 → 实剖面。 -/
def rowOf {I : Type} [Fintype I] {Act : Type} [Fintype Act] (ρ : Fin (cadVarN I Act) → ℝ) :
    I → Act → ℝ := fun i a => ρ (cadIdx I Act (i, a))

theorem exists_rowOf_eq (σ : I → Act → ℝ) :
    ∃ ρ : Fin (cadVarN I Act) → ℝ, rowOf (I := I) (Act := Act) ρ = σ := by
  refine ⟨fun k => σ ((cadIdx I Act).symm k).1 ((cadIdx I Act).symm k).2, ?_⟩
  funext i a
  simp [rowOf]

/-- ℚ 收益表的实嵌入（CAD 节内简写）。 -/
def uR (u : (I → Act) → I → ℚ) : (I → Act) → I → ℝ := fun a i => (u a i : ℝ)

theorem qToR_apply (a : ℚ) : qToR a = (a : ℝ) := rfl

/-- 期望收益多项式：变量 x_{(j,a j)} 的多元多项式编码。 -/
def euPoly (u : (I → Act) → I → ℚ) (i : I) : MvPolynomial (Fin (cadVarN I Act)) ℚ :=
  ∑ a, (∏ j, MvPolynomial.X (cadIdx I Act (j, a j))) * MvPolynomial.C (u a i)

/-- 纯偏差行因子：玩家 i 偏到 b 时第 j 行的多项式因子。 -/
def devRowPoly (i : I) (b : Act) (j : I) (c : Act) :
    MvPolynomial (Fin (cadVarN I Act)) ℚ :=
  if j = i then MvPolynomial.C (if c = b then 1 else 0)
    else MvPolynomial.X (cadIdx I Act (j, c))

/-- 纯偏差期望多项式。 -/
def euDevPoly (u : (I → Act) → I → ℚ) (i : I) (b : Act) :
    MvPolynomial (Fin (cadVarN I Act)) ℚ :=
  ∑ a, (∏ j, devRowPoly i b j (a j)) * MvPolynomial.C (u a i)

theorem eval2_euPoly (u : (I → Act) → I → ℚ) (i : I) (ρ : Fin (cadVarN I Act) → ℝ) :
    MvPolynomial.eval₂ qToR ρ (euPoly u i) = euR (uR u) (rowOf (I := I) (Act := Act) ρ) i := by
  simp only [euPoly, rowOf, euR, uR, MvPolynomial.eval₂_sum, MvPolynomial.eval₂_prod,
    MvPolynomial.eval₂_X, MvPolynomial.eval₂_mul, MvPolynomial.eval₂_C, qToR_apply]

theorem eval2_devRowPoly (i : I) (b : Act) (j : I) (c : Act)
    (ρ : Fin (cadVarN I Act) → ℝ) :
    MvPolynomial.eval₂ qToR ρ (devRowPoly i b j c)
      = if j = i then (if c = b then (1 : ℝ) else 0) else ρ (cadIdx I Act (j, c)) := by
  by_cases hji : j = i
  · subst hji
    by_cases hcb : c = b
    · simp [devRowPoly, hcb]
    · simp [devRowPoly, hcb]
  · simp [devRowPoly, hji]

theorem eval2_euDevPoly (u : (I → Act) → I → ℚ) (i : I) (b : Act)
    (ρ : Fin (cadVarN I Act) → ℝ) :
    MvPolynomial.eval₂ qToR ρ (euDevPoly u i b)
      = euR (uR u) (Function.update (rowOf (I := I) (Act := Act) ρ) i (pointR b)) i := by
  have hrow : ∀ (σ : I → Act → ℝ) (τ : Act → ℝ) (j : I) (c : Act),
      Function.update σ i τ j c = if j = i then τ c else σ j c := by
    intro σ τ j c
    rw [Function.update_apply, ite_apply]
  simp only [euDevPoly, euR, uR, rowOf, MvPolynomial.eval₂_sum,
    MvPolynomial.eval₂_prod, MvPolynomial.eval₂_mul, MvPolynomial.eval₂_C, qToR_apply,
    eval2_devRowPoly, hrow, pointR]

/-- 公式合取列表构造子（空合取＝恒真原子 0 = 0）。 -/
def conjAll {n : ℕ} : List (RealFormula n) → RealFormula n
  | [] => RealFormula.atom ⟨CmpOp.eq, 0⟩
  | f :: fs => RealFormula.and f (conjAll fs)

theorem conjAll_denote {n : ℕ} (ρ : Fin n → ℝ) (l : List (RealFormula n)) :
    RealFormula.denote ρ (conjAll l) ↔ ∀ f ∈ l, RealFormula.denote ρ f := by
  induction l with
  | nil => simp [conjAll, RealFormula.denote, denoteAtom, cmpRel, polyDenote]
  | cons f fs ih => simp [conjAll, RealFormula.denote, ih]

/-- §8.2 多项式均衡系统的 C0 编码原子索引：
    非负原子（inl）＋归一原子（inr ∘ inl）＋逐纯偏离不等式原子（inr ∘ inr）。 -/
abbrev CadAtomIdx (I : Type) (Act : Type) := (I × Act) ⊕ (I ⊕ (I × Act))

/-- 逐索引原子。 -/
def cadAtom (u : (I → Act) → I → ℚ) : CadAtomIdx I Act → RealFormula (cadVarN I Act)
  | .inl ia => RealFormula.atom ⟨CmpOp.le, -(MvPolynomial.X (cadIdx I Act ia))⟩
  | .inr (.inl i) => RealFormula.atom ⟨CmpOp.eq,
      (∑ a, MvPolynomial.X (cadIdx I Act (i, a))) - MvPolynomial.C 1⟩
  | .inr (.inr ib) => RealFormula.atom ⟨CmpOp.le, euDevPoly u ib.1 ib.2 - euPoly u ib.1⟩

/-- 原子列表（全域枚举）。 -/
def cadAtomList (u : (I → Act) → I → ℚ) : List (RealFormula (cadVarN I Act)) :=
  (Finset.univ : Finset (CadAtomIdx I Act)).toList.map (cadAtom u)

/-- **CAD 侧输入公式**：混合均衡多项式系统的 RealFormula 编码。 -/
def cadEquilFormula (u : (I → Act) → I → ℚ) : RealFormula (cadVarN I Act) :=
  conjAll (cadAtomList u)

theorem denote_nonneg_atom (ia : I × Act) (u : (I → Act) → I → ℚ)
    (ρ : Fin (cadVarN I Act) → ℝ) :
    RealFormula.denote ρ (cadAtom u (.inl ia))
      ↔ 0 ≤ rowOf (I := I) (Act := Act) ρ ia.1 ia.2 := by
  simp only [cadAtom, RealFormula.denote, denoteAtom, cmpRel, polyDenote, rowOf,
    MvPolynomial.eval₂_neg, MvPolynomial.eval₂_X, neg_nonpos]

theorem denote_norm_atom (i : I) (u : (I → Act) → I → ℚ) (ρ : Fin (cadVarN I Act) → ℝ) :
    RealFormula.denote ρ (cadAtom u (.inr (.inl i)))
      ↔ ∑ a, rowOf (I := I) (Act := Act) ρ i a = 1 := by
  simp only [cadAtom, RealFormula.denote, denoteAtom, cmpRel, polyDenote, rowOf,
    MvPolynomial.eval₂_sub, MvPolynomial.eval₂_sum, MvPolynomial.eval₂_X,
    MvPolynomial.eval₂_C, qToR_apply, sub_eq_zero]
  norm_num

set_option maxHeartbeats 1000000 in
theorem denote_dev_atom (u : (I → Act) → I → ℚ) (ib : I × Act)
    (ρ : Fin (cadVarN I Act) → ℝ) :
    RealFormula.denote ρ (cadAtom u (.inr (.inr ib)))
      ↔ euR (uR u) (Function.update (rowOf (I := I) (Act := Act) ρ) ib.1 (pointR ib.2)) ib.1
        ≤ euR (uR u) (rowOf (I := I) (Act := Act) ρ) ib.1 := by
  simp only [cadAtom, RealFormula.denote, denoteAtom, cmpRel, polyDenote,
    MvPolynomial.eval₂_sub, eval2_euDevPoly, eval2_euPoly, sub_nonpos]

set_option maxHeartbeats 1000000 in
/-- **CAD 输出同一全部均衡关系（针 30 余项之三）**：公式的解集恰为
    均衡全集——对任意实赋值 ρ，`cadEquilFormula u` 在 ρ 成立当且仅当
    ρ 编码的剖面在单纯形积内且是 Nash 均衡（同一 `IsNashR` 全部均衡
    关系，双向）。 -/
theorem cad_output_same_equilibrium_relation (u : (I → Act) → I → ℚ)
    (ρ : Fin (cadVarN I Act) → ℝ) :
    RealFormula.denote ρ (cadEquilFormula u) ↔
      InSimplexR (rowOf (I := I) (Act := Act) ρ) ∧ IsNashR (uR u) (rowOf ρ) := by
  rw [cadEquilFormula, conjAll_denote]
  constructor
  · intro h
    have hn : ∀ ia : I × Act, 0 ≤ rowOf (I := I) (Act := Act) ρ ia.1 ia.2 := by
      intro ia
      have hmem : cadAtom u (.inl ia) ∈ cadAtomList u :=
        List.mem_map_of_mem (Finset.mem_toList.mpr (Finset.mem_univ (Sum.inl (ia : I × Act))))
      exact (denote_nonneg_atom ia u ρ).mp (h _ hmem)
    have hsum : ∀ i : I, ∑ a, rowOf (I := I) (Act := Act) ρ i a = 1 := by
      intro i
      have hmem : cadAtom u (.inr (.inl i)) ∈ cadAtomList u :=
        List.mem_map_of_mem (Finset.mem_toList.mpr (Finset.mem_univ (Sum.inr (Sum.inl (i : I)))))
      exact (denote_norm_atom i u ρ).mp (h _ hmem)
    have hdev : ∀ (i : I) (b : Act),
        euR (uR u) (Function.update (rowOf (I := I) (Act := Act) ρ) i (pointR b)) i
          ≤ euR (uR u) (rowOf (I := I) (Act := Act) ρ) i := by
      intro i b
      have hmem : cadAtom u (.inr (.inr (i, b))) ∈ cadAtomList u :=
        List.mem_map_of_mem (Finset.mem_toList.mpr (Finset.mem_univ (Sum.inr (Sum.inr ((i, b) : I × Act)))))
      exact (denote_dev_atom u (i, b) ρ).mp (h _ hmem)
    exact ⟨fun i => ⟨fun a => hn (i, a), hsum i⟩,
      nashR_iff_no_pure_dev_gain _ _ |>.mpr hdev⟩
  · intro ⟨hsim, hnash⟩ f hf
    rcases List.mem_map.mp hf with ⟨ix, _, rfl⟩
    rcases ix with (ia | i | ib)
    · exact (denote_nonneg_atom ia u ρ).mpr ((hsim ia.1).1 ia.2)
    · exact (denote_norm_atom i u ρ).mpr ((hsim i).2)
    · exact (denote_dev_atom u ib ρ).mpr
        (nashR_iff_no_pure_dev_gain _ _ |>.mp hnash ib.1 ib.2)

set_option maxHeartbeats 1000000 in
theorem cad_equil_solution_nonempty {I : Type} [Fintype I] [DecidableEq I]
    {Act : Type} [Fintype Act] [DecidableEq Act] [Nonempty Act] (u : (I → Act) → I → ℚ) :
    ∃ ρ : Fin (cadVarN I Act) → ℝ, RealFormula.denote ρ (cadEquilFormula u) := by
  obtain ⟨σ, hsim, hnash⟩ := finite_legal_mixed_equilibrium_exists (u := uR u)
  obtain ⟨ρ, hρ⟩ := exists_rowOf_eq (I := I) (Act := Act) σ
  refine ⟨ρ, ?_⟩
  have hiff := cad_output_same_equilibrium_relation u ρ
  rw [hρ] at hiff
  exact hiff.mpr ⟨hsim, hnash⟩

end CAD

end

end JurisLean.Seams.UnifiedEquilExist
