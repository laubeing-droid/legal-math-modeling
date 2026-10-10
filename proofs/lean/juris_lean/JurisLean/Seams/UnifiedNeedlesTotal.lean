import Mathlib.Tactic
import JurisLean.Seams.Unified
import JurisLean.Seams.UnifiedNeedlesS3b

/-!
# 总名针（第 60 针，附录 I.13；UnifiedNeedlesTotal）

本件承接 `docs/spec/20261007-统一法律数学模型_附录I_Lean施工明细.md` §I.13 第 60 针
（总名 `unified_legal_derivation_on_declared_fragment`）的升级合同：在旧锚
`Seams/Unified.lean:259`（固定实例的五约合取）之上，给出**共同中间见证＋全静态
链／事件链＋精度传播**的总定理形态。

## 一、总名针的语义（人话）

旧 T2 说：声明片段 `UnifiedModel` 上五件事同时成立。本针把它升级为两面总定理：

1. **静态链＋事件链＋时间/不确定性面（旧五约）**：中间见证就是同一个
   `M : UnifiedModel V Rel`——五约全部只读这一个共同载体；全静态链
   （SourceNorms → AdjudicationBridge → PayoffEquilibrium）与事件链
   （InstitutionalEffects 步进 + PrecedentFlow 反馈）分别由五约的
   `UnifiedChainCorrespondence` 与 `UnifiedFiniteProcessComposition` 承载。
   证据位直接调用旧定理；语句位内联旧五约合取（不在类型位嵌套定理应用）。
2. **精度传播面**：数量 AST 的整叶有理嵌入与无除片段整值性（针 25 的第 (i)/(iii)
   支）作为独立载体面并入总定理——统一模型的数值读数不引入舍入面。

## 二、实际适用域与开放义务（如实声明）

- 载体域：`UnifiedModel V Rel`（有限、带 DecidableEq）；精度面在其自有的
  `QtyAst/QtyVal` 载体上独立成立，不冒称与 UnifiedModel 字段互相嵌入。
- 针波八族（S0S1/S2/S3b/S4/S5/S6S7/XT 与修复中的 S3a/XU）的逐针闭合状态由
  `docs/full-math/BINDING_217_and_60.md` 与施工台账承载，本件不替它背书。
- 旧 T2 的"固定实例"读法不变：本升级不冒称五约在声明片段之外成立。

## 三、档位

零 `sorry`／零 `admit`／零自定义 `axiom`；本件 `CI_NOT_RUN`（本地不编译 Lean，
fail-closed），以 Actions 模块轮为唯一编译权威。
-/

namespace JurisLean.Seams.UnifiedNeedlesTotal

open JurisLean.Seams

/-! ## 第一面：旧五约（共同中间见证 M；全静态链与事件链的载体） -/

/-- 总名第一面：五约在声明片段上同时成立，全部只读同一个共同中间见证
`M : UnifiedModel V Rel`。证据位直接调用旧定理（语句位内联合取，
不嵌定理应用）。 -/
theorem total_legacy_five_contracts {V Rel : Type} [DecidableEq Rel]
    (M : UnifiedModel V Rel) :
    UnifiedNonDegenerate ∧ UnifiedInterpretationPreserved V Rel M ∧
      UnifiedChainCorrespondence V Rel M ∧ UnifiedFiniteProcessComposition V Rel M ∧
      UnifiedTimeAndUncertaintyPreserved V Rel M :=
  JurisLean.Seams.unified_legal_derivation_on_declared_fragment M

/-! ## 第二面：精度传播（数量 AST 的无舍入面，独立载体） -/

/-- 总名第二面：精度传播——整叶有理嵌入（定义事实）与无除片段整值性
（结构归纳，针 25 第 (i)/(iii) 支）独立于模型层成立，并入总读数。 -/
theorem total_precision_no_rounding :
    (∀ k : ℤ, UnifiedNeedlesS3b.qtyDenote (.intLit k)
        = some ⟨(k : ℚ), ""⟩) ∧
    (∀ a : UnifiedNeedlesS3b.QtyAst, UnifiedNeedlesS3b.divFree a = true →
        ∀ z : UnifiedNeedlesS3b.QtyVal, UnifiedNeedlesS3b.qtyDenote a = some z →
          ∃ n : ℤ, z.val = (n : ℚ)) :=
  ⟨UnifiedNeedlesS3b.qtyDenote_intLit,
    fun a hfree z h => UnifiedNeedlesS3b.qtyDenote_divFree_int_valued a hfree z h⟩

/-! ## 第三面：总定理（第 60 针本体） -/

/-- **第 60 针（总，I.13；BINDING 行 60）**：`unified_legal_derivation_on_declared_fragment`
的升级合同——共同中间见证（同一 `M` 承载五约）＋全静态链／事件链（五约的
(3)/(4) 支）＋精度传播（数量 AST 无舍入面）在声明片段上同时成立。诚实声明：
精度面是独立载体面，不冒称嵌入 UnifiedModel 字段。 -/
theorem unified_legal_derivation_on_declared_fragment {V Rel : Type} [DecidableEq Rel]
    (M : UnifiedModel V Rel) :
    (UnifiedNonDegenerate ∧ UnifiedInterpretationPreserved V Rel M ∧
      UnifiedChainCorrespondence V Rel M ∧ UnifiedFiniteProcessComposition V Rel M ∧
      UnifiedTimeAndUncertaintyPreserved V Rel M) ∧
    ((∀ k : ℤ, UnifiedNeedlesS3b.qtyDenote (.intLit k) = some ⟨(k : ℚ), ""⟩) ∧
      (∀ a : UnifiedNeedlesS3b.QtyAst, UnifiedNeedlesS3b.divFree a = true →
        ∀ z : UnifiedNeedlesS3b.QtyVal, UnifiedNeedlesS3b.qtyDenote a = some z →
          ∃ n : ℤ, z.val = (n : ℚ))) :=
  ⟨total_legacy_five_contracts M, total_precision_no_rounding⟩

end JurisLean.Seams.UnifiedNeedlesTotal
