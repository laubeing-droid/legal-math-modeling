import Mathlib.Tactic

/-
Unified CAD multivariate increment, layer O+ (appendix I.0.1 C2/C4 miniatures
on the bivariate quadratic disk fragment over ℚ).  This file extends the
layer-O deliverable `Seams/UnifiedCAD.lean` (univariate quadratic, three
checker-first obligations) by the two remaining obligations that can still
be closed with exact rational algebra:

1. C2 MICRO (BIVARIATE PROJECTION) — `CAD2Proj` is the projection of the
   disk constraint (x−cx)²+(y−cy)² ≤ t onto the x axis, obtained by explicit
   elimination of y that uses ONLY (y−cy)² ≥ 0 (the nonnegativity premise is
   discharged by `mul_self_nonneg`, never assumed).  `CAD2_proj_sound` :
   satisfiability of the original constraint at x implies the projection
   condition (soundness).  `CAD2_proj_disk_complete` records that on the
   pure disk class this explicit elimination is even exact.  The honest
   counterexample `CAD2_sys_proj_incomplete` pins the INCOMPLETE direction
   of the FRAGMENT projection: on the composite class "disk ∧ degenerate
   y-equality (y²+k=0)" the fragment projection (which only projects the
   disk conjunct) allows an x that passes the projection with an empty fiber —
   y²+1=0 has no solution over ℚ.  A full I.0.1.3 elimp projection would
   also project the y-polynomial's discriminant / leading coefficients and
   catch this empty fiber; that full recipe remains open.
2. C4 MICRO (REFERENCE GENERATOR FOR THE PROJECTED CASE) — `CAD2BuildWitness`
   takes x and returns the reference output: `some cy` when the projection
   condition holds (an explicit existence witness for y), `none` otherwise.
   `CAD2_build_accepted` : whenever the projection condition holds, the
   generator's output passes the checker `CAD2CheckWitness` (acceptance =
   substitution into the original constraint; the checker never calls a
   solver).  `CAD2_build_none_fail_closed` : the none branch really is the
   failing-projection branch (fail-closed).

C5 DISCLAIMER, honestly: the QEPCAD adapter is an external-tool interface
obligation and is NOT closed inside Lean; this file delivers only the C2/C4
multivariate miniatures above.  Everything is exact algebra over ℚ (layer-O
discipline); no claim is made about real-closed-field sectors, Sturm or
subresultant checkers, full projection recipes, or QEPCAD certificates.
-/

namespace JurisLean.Seams.UnifiedCAD2

/-! ## 一、C0′ 微型：双变量圆盘约束编码与投影算子 -/

/-- 圆盘约束左端：(x−cx)² + (y−cy)²（层O 同款乘积展开形）。 -/
def cad2Lhs (cx cy x y : ℚ) : ℚ := (x - cx) * (x - cx) + (y - cy) * (y - cy)

/-- 圆盘约束可满足谓词：(x−cx)² + (y−cy)² ≤ t；t 承担 r² 的代数输入角色
    （任意有理数，含退化输入，不作非负预设）。 -/
def cad2Sat (cx cy t x y : ℚ) : Prop := cad2Lhs cx cy x y ≤ t

/-- **C2 投影算子**：双变量圆盘约束到 x 轴的投影——从 y 的存在性显式消元；
    消元只使用平方非负，不调用任何求解器。 -/
def CAD2Proj (cx t x : ℚ) : Prop := (x - cx) * (x - cx) ≤ t

/-! ## 二、C2 健全性：原约束可满足 ⇒ 投影条件成立 -/

/-- 逐点形：单点满足原约束 ⇒ 投影条件成立（非负性前提由 `mul_self_nonneg`
    现场证明，不外挂假设）。 -/
theorem CAD2_proj_point_sound (cx cy t x y : ℚ)
    (h : cad2Sat cx cy t x y) : CAD2Proj cx t x := by
  simp only [cad2Sat, cad2Lhs, CAD2Proj] at h ⊢
  have hy : (0:ℚ) ≤ (y - cy) * (y - cy) := mul_self_nonneg (y - cy)
  linarith

/-- **C2 健全性（可满足形）**：存在 y 使原约束在 x 处成立 ⇒ x 的投影条件成立。 -/
theorem CAD2_proj_sound (cx cy t x : ℚ)
    (h : ∃ y : ℚ, cad2Sat cx cy t x y) : CAD2Proj cx t x := by
  obtain ⟨y, hy⟩ := h
  exact CAD2_proj_point_sound cx cy t x y hy

/-- 纯圆盘类上该显式消元是精确的：投影条件成立 ⇒ 取 y = cy 即为存在见证
    （完备性只对单一圆盘约束成立；反例类见下节）。 -/
theorem CAD2_proj_disk_complete (cx cy t x : ℚ)
    (h : CAD2Proj cx t x) : ∃ y : ℚ, cad2Sat cx cy t x y := by
  refine ⟨cy, ?_⟩
  simp only [cad2Sat, cad2Lhs, sub_self, mul_zero, add_zero]
  exact h

/-! ## 三、C2 反例：片段投影的不完备方向（诚实钉死） -/

/-- 反例类：圆盘约束联立 y 的退化等式 y² + k = 0（复合双变量二次片段）。 -/
def cad2SysSat (cx cy t k x y : ℚ) : Prop :=
  cad2Sat cx cy t x y ∧ y * y + k = 0

/-- **片段投影**：只投影圆盘合取支，丢弃 y 等式支——被丢弃的部分正是反例所在；
    I.0.1.3 的完整 elimp 配方还会投影该 y 多项式的判别式/首项系数（本文件不做）。 -/
def CAD2ProjSys (cx cy t k x : ℚ) : Prop := CAD2Proj cx t x

/-- 复合类上的片段投影仍然健全（丢合取支不破坏健全性）。 -/
theorem CAD2_sys_proj_sound (cx cy t k x : ℚ)
    (h : ∃ y : ℚ, cad2SysSat cx cy t k x y) : CAD2ProjSys cx cy t k x := by
  obtain ⟨y, hy⟩ := h
  exact CAD2_proj_point_sound cx cy t x y hy.1

/-- **反例定理（不完备方向）**：存在复合约束与 x，满足片段投影条件，
    但没有任何 y 满足原式——y²+1=0 在 ℚ（乃至任何有序域）无解。
    该反例只钉死本片段投影的不完备方向，不是对完整 CAD 投影配方的否定。 -/
theorem CAD2_sys_proj_incomplete :
    ∃ (cx cy t k x : ℚ),
      CAD2ProjSys cx cy t k x ∧ ¬ ∃ y : ℚ, cad2SysSat cx cy t k x y := by
  refine ⟨0, 0, 1, 1, 0, ?_, ?_⟩
  · simp only [CAD2ProjSys, CAD2Proj]
    norm_num
  · intro hex
    obtain ⟨y, hy⟩ := hex
    simp only [cad2SysSat] at hy
    have heq : y * y + 1 = 0 := hy.2
    have hy2 : (0:ℚ) ≤ y * y := mul_self_nonneg y
    linarith

/-! ## 四、C4 微型：投影情形的参考生成器与检查器 -/

/-- 检查器（命题形）：接受 = 把候选见证代入原约束验证。不调用任何求解器。 -/
def CAD2CheckWitness (cx cy t x y : ℚ) : Prop := cad2Sat cx cy t x y

/-- **参考生成器**：投影条件成立时输出存在见证 y = cy（some 分支），
    否则输出 none（显式失败分支）。非递归全函数。 -/
def CAD2BuildWitness (cx cy t x : ℚ) : Option ℚ :=
  if (x - cx) * (x - cx) ≤ t then some cy else none

/-- **C4 全性**：每个输入都产出"some 见证或 none"之一（非递归全函数，
    可定义性即终止证明；层O `buildCAD2_total` 同款读法）。 -/
theorem CAD2_build_total (cx cy t x : ℚ) :
    (∃ y :ℚ, CAD2BuildWitness cx cy t x = some y) ∨
      CAD2BuildWitness cx cy t x = none := by
  by_cases h : (x - cx) * (x - cx) ≤ t
  · left
    refine ⟨cy, ?_⟩
    simp only [CAD2BuildWitness]
    rw [if_pos h]
  · right
    simp only [CAD2BuildWitness]
    rw [if_neg h]

/-- **C4 生成器输出必被检查器接受**：投影条件成立时，生成器输出 some cy，
    且该输出通过检查器的代入验证（无偷缩可完成域；层O `buildCAD2_accepted`
    的多变量投影形）。 -/
theorem CAD2_build_accepted (cx cy t x : ℚ) (h : CAD2Proj cx t x) :
    CAD2BuildWitness cx cy t x = some cy ∧ CAD2CheckWitness cx cy t x cy := by
  have hcond : (x - cx) * (x - cx) ≤ t := h
  refine ⟨?_, ?_⟩
  · simp only [CAD2BuildWitness]
    rw [if_pos hcond]
  · simp only [CAD2CheckWitness, cad2Sat, cad2Lhs, sub_self, mul_zero, add_zero]
    exact h

/-- **none 分支 fail-closed**：生成器输出 none 时，投影条件确实不成立
    （失败分支不承载正常载荷）。 -/
theorem CAD2_build_none_fail_closed (cx cy t x : ℚ)
    (h : CAD2BuildWitness cx cy t x = none) : ¬ CAD2Proj cx t x := by
  intro hp
  rw [(CAD2_build_accepted cx cy t x hp).1] at h
  exact Option.noConfusion h

/-! ## 五、STATUS -/

/- STATUS（诚实边界）：
- 已闭合（本文件，全部精确有理代数；本地状态 CI_NOT_RUN，以 CI 模块构建为准）：
  C2 微型健全性 `CAD2_proj_sound`；纯圆盘类精确性 `CAD2_proj_disk_complete`；
  片段投影不完备方向反例 `CAD2_sys_proj_incomplete`；
  C4 微型生成器全性/输出必被接受/none fail-closed
  （`CAD2_build_total` / `CAD2_build_accepted` / `CAD2_build_none_fail_closed`）。
- 未闭合：多维 CAD 完整投影配方（I.0.1.3 elimp 截断族/导数/子结式/首项系数）、
  Sturm/子结式检查器、sections/sectors 覆盖与互斥、量词消去等价（C2/C3/C4 全量）；
  本文件的反例类只钉死片段投影的不完备方向。
- C5：QEPCAD 适配是外部工具接口义务，不在 Lean 内闭合，本文件不交付；
  全链统一消费（Opt/Nash/SCM）同样不在本文件范围。
- 本文件未加入根 `JurisLean.lean`；按仓库规则，CI 模块构建通过前保持 CI_NOT_RUN。 -/

end JurisLean.Seams.UnifiedCAD2
