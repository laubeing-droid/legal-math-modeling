import JurisLean.Seams.Representation
import JurisLean.Seams.SourceNorms
import JurisLean.Seams.AdjudicationBridge
import JurisLean.Seams.InstitutionalEffects
import JurisLean.Seams.PayoffEquilibrium
import JurisLean.Seams.PrecedentFlow
import JurisLean.Seams.Temporal
import JurisLean.Seams.Uncertainty
import JurisLean.Seams.BoundaryClosure
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic

/-!
# T2 —— 统一法律推导的缝合总定理（构造顺序 §一 T2）

`JurisLean.Seams.unified_legal_derivation_on_declared_fragment`：一条陈述同时交付
(1) 非退化的存在见证、(2) 逐层解释保持、(3) 声明片段内的全链对应、(4) 有限过程复合、
(5) 时间与不确定性保持。五个合取支**全部由引用已证的缝件定理交付**，本件不重证任何一条，
也不把任何一条改写成较弱的说法。

## §法律语义
"法律统一"在这里只有一件小事：把已经分别证好的七层结论，收到**同一个声明片段**上，
使得"层与层之间的假设能对上"这件事本身是可检查的。检查的产物是一个结构
`UnifiedModel`：它的每一个字段都是某一层的**载体或该层定理自己声明的前提**，
定理所要求的假设必须一次交齐，缺一条就构造不出这个片段。

统一的是**层次链的理论统一**，不是工程统一：没有任何一个真实案件、任何一部真实法律
被本件裁判或认定；也没有把 juris-calculus 整体声称为已验证。

## §数学对象
共享法律对象域取 `Fin 2`——这是 S0 唯一已证非退化的域（玩具域），本件不假装它代表
任何真实法律状态集。在此域上真正共用的只有两层：S0 的表示片段与 S1 的 Horn 系统
（以及 XT 的事件载荷、XU 的质量载体）。其余层的载体**不**相同，本件把它们登记为
片段的具名字段，而不是伪造桥梁：

- 错位登记 #1（裁判·论点通道）：论点载体是 `Arg`（`DungDefinitions.lean:14`，即 `String`），
  与 `Fin 2` 无等式；`V Rel : Type` 两个类型参数就是这一事实的签名体现。
- 错位登记 #2（裁判·评价通道）：结论载体 `V` 独立。
- 错位登记 #3（机构效果）：关系载体 `Rel` 独立；账本是 `List (FormationRecord Rel)`。
- 错位登记 #4（收益）：`Case / Role / LegalStatus` 是 S4 文件内的固定归纳类型，无法参数化。
- 错位登记 #5（前例）：载体是 `VersionEnv / AuthorizedDecision`，与冻结内核的
  `normEnv : String` 无定义关系（见 `Seams/PrecedentFlow.lean` 文件头）。
- 错位登记 #6（时间）：四套时间载体 `Nat`（`evidenceAdmissible_iff`）、`Int`（`trunc`）、
  `String`（ISO 日期）、关系型（`DayInterval`）互不相通；这一条**不是散文**，
  它由 `Temporal.no_unified_time_carrier_yet` 在合取支 (5) 里作为定理交付。
- 错位登记 #7（不确定性）：质量载体是 `ℚ`，与 `Fin 2`、`String`、`VersionEnv` 均无桥。

## §证与不证
[已证·引用] (1) `Representation.joint_legal_model_exists`、`AdjudicationBridge.trial_boundary`、
`Uncertainty.uncertainty_allowed_non_singleton_with_singleton_kernel`；
(2) `Representation.representation_observations_preserved`、
`Representation.joint_legal_model_is_isomorphic_to_domain`、
`PayoffEquilibrium.legal_payoff_preserved_swapDocket`、
`PrecedentFlow.precedent_update_preserves_norm_structure`；
(3) `SourceNorms.horn_closure_semantic_iff`、`AdjudicationBridge.grounded_equivalence`、
`AdjudicationBridge.unique_verdict_iff_stable_kernel_singletons`、
`PayoffEquilibrium.external_equilibrium_reflects_legal`；
(4) `InstitutionalEffects.projection_of_append_matches_step`、
`InstitutionalEffects.performance_not_creation`、`AdjudicationBridge.two_valued_exclusion`、
`PrecedentFlow.update_is_not_noop`、`PrecedentFlow.unauthorized_output_is_not_a_norm`；
(5) `Temporal.legal_time_nonanticipation`、`Temporal.aggregate_add_arrival_insensitive`、
`Temporal.no_unified_time_carrier_yet`、
`Uncertainty.finite_positive_support_truth_bridge`、
`Uncertainty.xuc_conditioning_denominator_is_clean_mass`。

[不证] 本件不含任何新的数学论证：五个合取支的证明项就是上述定理作用于片段字段。
[不证] 不声称层间存在跨层的传递（例如"前例更新改变 Horn 闭包"），只声称各层结论在
同一份假设清单下同时成立。[不证] 不声称 `𝔐` 覆盖了未声明的载体或层。

## §未覆盖片段
1. **概率层（S3，`Seams/Probability.lean`）的数值传递**：该缝件目前为红，本件不导入它，
   因此"概率层数值在各层之间可搬运"**不在**本片段内。合取支 (5) 用到的
   `Uncertainty.finite_positive_support_truth_bridge` 与
   `xuc_conditioning_denominator_is_clean_mass` 是 `Seams/Uncertainty.lean` 内部在 `ℚ`
   有限和上的等式，**不是** S3 的传递结果，不得读成 S3 已并入。
2. **闭环缝件（S6，`Seams/FullProcess.lean`）**：无判定，本件不导入它。于是"运行轨迹成环、
   回执都由语义导出产生"这句**不在**本片段内；本件的 (4) 只到"有限过程可复合"为止。
3. 真实法律领域（合同、登记、时效、指导性案例）的任何认定：一律未覆盖。
4. 跨层载体的等同（错位登记 #1–#7）：未覆盖，且 #6 已由定理否定当前的统一通道。
5. 多于两层的联合模型、一般 `α` 上的非退化性（需分离性公设）：未覆盖（见 S0 文件头）。

## §档位
`UnifiedModel` 是[构造性定义]；五条合取支与两条配套定理都是[引用已证]，
本件内没有 `sorry`、`admit`、`native_decide` 伪证，也没有新增 `axiom`。
按仓库边界约定，Lean 权威认定在 CI；本地编译仅为自检，称 provisional。
-/

open BigOperators
open JurisLean.FullMath.Probability (evMass)

namespace JurisLean.Seams

/-- 统一模型 𝔐 的**声明片段**：七层各自的载体（互不假装相等，见文件头错位登记）
    加上每一层自己的定理前提。少给任何一条前提，这个片段就构造不出来——
    这正是"跨缝假设已对齐"的可检查形式。 -/
structure UnifiedModel (V Rel : Type) [DecidableEq Rel] where
  /-- L1 源规范层（S1）：与 S0 共用 `Fin 2` 的正 Horn 系统，以及一个待判原子 -/
  norms : HornSystem (Fin 2)
  atom : Fin 2
  /-- L2 裁判层·论点通道（S2）。载体错位登记 #1：`Arg = String`。 -/
  aaf : DungAAF
  pol : AdjudicationBridge.TerminalPolicy aaf
  disputed : Arg
  hBaseConflictFree : AdjudicationBridge.baseConflictFree pol
  round : Nat
  hPolicyClosed : AdjudicationBridge.policyClosed pol round
  hBaseInGrounded : AdjudicationBridge.baseInGrounded pol
  /-- L2 裁判层·评价通道（S2）。载体错位登记 #2。 -/
  evalDom : AdjudicationBridge.EvalDomain V
  candidate : V
  hAdmissibleNonempty : ∃ S : Set V, AdjudicationBridge.Admissible evalDom S
  hCollapse : AdjudicationBridge.collapsesToKernel evalDom
  /-- L5 机构效果层（S5）。载体错位登记 #3。 -/
  ledger : InstitutionalEffects.Ledger Rel
  eventId : String
  relFormed : Rel
  relObserved : Rel
  performEventId : String
  obligor : String
  performAmount : Nat
  /-- L7 前例层（S7）。载体错位登记 #5：`VersionEnv`/`AuthorizedDecision`。 -/
  env : PrecedentFlow.VersionEnv
  ad : PrecedentFlow.AuthorizedDecision
  hwf : PrecedentFlow.EnvWf env ad
  atDay : Int
  production : PrecedentFlow.BackflowProduction
  hUnauthorized : ¬ PrecedentFlow.authorized production
  /-- XT 时间层。载体错位登记 #6：日标签是 `Int`，不是 `Nat`/`String`/`DayInterval`。 -/
  asOf : Int
  past : List (Int × Fin 2)
  future₁ : List (Int × Fin 2)
  future₂ : List (Int × Fin 2)
  hFuture₁ : ∀ x ∈ future₁, asOf < x.1
  hFuture₂ : ∀ x ∈ future₂, asOf < x.1
  someLate : Int × Fin 2
  /-- XU 不确定层。载体错位登记 #7：质量在 `ℚ` 上。 -/
  weight : Fin 2 → ℚ
  truthAssessment : Fin 2 → KernelV3.TruthJudgment
  hWeightPos : ∀ a, 0 < weight a
  hWeightTotal : ∑ a : Fin 2, weight a = 1
  contaminated : Uncertainty.ContaminatedCase

/-- 契约 (1)：统一模型**不退化**。三支都是"存在"式的正面见证，全部引用。 -/
def UnifiedNonDegenerate : Prop :=
  (∃ (p q : Representation.Joint Representation.layerStatus Representation.layerRegister),
      p ≠ q ∧ ∃ i : Representation.layerStatus.ι,
        Representation.jointObs₁ Representation.layerStatus Representation.layerRegister i p ≠
          Representation.jointObs₁ Representation.layerStatus Representation.layerRegister i q) ∧
    ((∃ v : Fin 3, AdjudicationBridge.stableKernel AdjudicationBridge.trialDomain = {v}) ∧
      ∃ x y z : Fin 3,
        x ∈ AdjudicationBridge.allowedSet AdjudicationBridge.trialDomain ∧
          y ∈ AdjudicationBridge.allowedSet AdjudicationBridge.trialDomain ∧
          x ≠ y ∧ z ∈ AdjudicationBridge.allowedSet AdjudicationBridge.trialDomain ∧
          z ∉ AdjudicationBridge.stableKernel AdjudicationBridge.trialDomain) ∧
    ((¬ ∃! v, Uncertainty.uncertaintyAllowed KernelV3.Judgment.established v) ∧
      ∃! v, Uncertainty.uncertaintyKernel KernelV3.Judgment.established v)

/-- 非退化性不是修辞：把三支具体见证并排交出。 -/
theorem unified_model_is_not_vacuous : UnifiedNonDegenerate :=
  ⟨Representation.joint_legal_model_exists, AdjudicationBridge.trial_boundary,
    Uncertainty.uncertainty_allowed_non_singleton_with_singleton_kernel⟩

/-- 契约 (2)：逐层解释保持。四支分别来自 S0（两支）、S4、S7。 -/
def UnifiedInterpretationPreserved (V Rel : Type) [DecidableEq Rel]
    (M : UnifiedModel V Rel) : Prop :=
  (∀ (a : Fin 2) (i : Representation.layerStatus.ι),
      Representation.obsModel Representation.layerStatus i
        (Representation.layerStatus.enc a) = Representation.layerStatus.obs i a) ∧
    (∃ e : Equiv (Fin 2)
        (Representation.Joint Representation.layerStatus Representation.layerRegister),
        e.toFun = Representation.jointDiag Representation.layerStatus
          Representation.layerRegister ∧
          e.invFun = Representation.jointRetract Representation.layerStatus
            Representation.layerRegister) ∧
    (∀ (role : PayoffEquilibrium.Role) (c : PayoffEquilibrium.Case),
        PayoffEquilibrium.payoffOf role (PayoffEquilibrium.swapDocket c) =
          PayoffEquilibrium.payoffOf role c) ∧
    ((∀ v ∈ (PrecedentFlow.precedentUpdate M.ad M.env).versions,
        SourceVersionRecord.intervalValid v) ∧
      (∀ v : SourceVersionRecord, PrecedentFlow.isTouchedBy M.ad M.env v →
        supersessionWellFormed
          { oldSnap := v.snapshot, newSnap := M.ad.decision.newSnapshot : SupersessionEdge }) ∧
      (∀ v : SourceVersionRecord, v ∈ M.env.versions →
        v.status = VersionStatus.retracted ∨ v.status = VersionStatus.superseded →
          ∃ w ∈ (PrecedentFlow.precedentUpdate M.ad M.env).versions,
            w.snapshot = v.snapshot ∧ ¬ versionApplicableAt w M.atDay))

/-- 契约 (3)：声明片段内的全链对应。四条对应式（S1、S2 两支、S4）。 -/
def UnifiedChainCorrespondence (V Rel : Type) [DecidableEq Rel]
    (M : UnifiedModel V Rel) : Prop :=
  (M.atom ∈ SourceNorms.closureAt M.norms ↔ SourceNorms.entailed M.norms M.atom) ∧
    (AdjudicationBridge.FinalDerivable M.pol M.disputed ↔
      M.disputed ∈ DungAAF.grounded M.aaf) ∧
    (AdjudicationBridge.allowedSet M.evalDom = {M.candidate} ↔
      AdjudicationBridge.stableKernel M.evalDom = {M.candidate}) ∧
    PayoffEquilibrium.IsApproxNash (PayoffEquilibrium.legalPay 10)
      ((0 : ℚ) + 2 * (1 : ℚ)) PayoffEquilibrium.ActC.sue PayoffEquilibrium.ActR.refuse

/-- 契约 (4)：有限过程复合。账本折叠＝逐步语义（S5 两支）、轮次两值不塌（S2）、
    前例更新非恒等且未授权产出进不了规范层（S7 两支）。 -/
def UnifiedFiniteProcessComposition (V Rel : Type) [DecidableEq Rel]
    (M : UnifiedModel V Rel) : Prop :=
  (InstitutionalEffects.forms
      (InstitutionalEffects.next M.ledger
        (InstitutionalEffects.SeamEvent.formative M.eventId M.relFormed)) M.relObserved ↔
      (M.relObserved = M.relFormed ∨ InstitutionalEffects.forms M.ledger M.relObserved)) ∧
    (InstitutionalEffects.forms
      (InstitutionalEffects.next M.ledger
        (InstitutionalEffects.SeamEvent.performance M.performEventId M.obligor M.relFormed
          M.performAmount)) M.relObserved ↔
      InstitutionalEffects.forms M.ledger M.relObserved) ∧
    (AdjudicationBridge.FinalDerivable M.pol M.disputed →
      ¬ AdjudicationBridge.FinalDefeated M.pol M.disputed) ∧
    PrecedentFlow.applicableEffectiveFroms PrecedentFlow.envOld PrecedentFlow.tSwap ≠
      PrecedentFlow.applicableEffectiveFroms
        (PrecedentFlow.precedentUpdate PrecedentFlow.demoAuthorized PrecedentFlow.envOld)
        PrecedentFlow.tSwap ∧
    ¬ ∃ (e : PrecedentFlow.NormLayerEntry), e.declared = M.production

/-- 契约 (5)：时间与不确定性保持，**并含时间载体不可统一这一负面事实**。 -/
def UnifiedTimeAndUncertaintyPreserved (V Rel : Type) [DecidableEq Rel]
    (M : UnifiedModel V Rel) : Prop :=
  (Temporal.trunc M.asOf (M.past ++ M.future₁) = Temporal.trunc M.asOf (M.past ++ M.future₂)) ∧
    (Temporal.aggregate (· + ·) 0 (Temporal.insertLate M.someLate M.past) =
      Temporal.aggregate (· + ·) 0 (M.someLate :: M.past)) ∧
    (evMass M.weight (Uncertainty.truthEvent M.truthAssessment) = 1 ↔
      ∀ a : Fin 2, (M.truthAssessment a).truth = true) ∧
    (evMass (Uncertainty.caseMassOnBool M.contaminated) id =
      Uncertainty.cleanEvidenceMass M.contaminated.weight M.contaminated.inputs) ∧
    ((∃ x : Int, Int.toNat x = 0 ∧ x < 0) ∧
      ¬ (∀ a b : Int, Int.toNat a ≤ Int.toNat b → a ≤ b))

/-- **T2 主定理**：在声明片段 `UnifiedModel` 上，五件事同时成立。
    合取支 (1) 由 `unified_model_is_not_vacuous` 交出，(2)–(5) 的证明项只是 8 个缝件模块
    共 21 条已设定理作用于片段字段；本件内没有任何新的数学论证。 -/
theorem unified_legal_derivation_on_declared_fragment
    {V Rel : Type} [DecidableEq Rel] (M : UnifiedModel V Rel) :
    UnifiedNonDegenerate ∧ UnifiedInterpretationPreserved V Rel M ∧
      UnifiedChainCorrespondence V Rel M ∧ UnifiedFiniteProcessComposition V Rel M ∧
      UnifiedTimeAndUncertaintyPreserved V Rel M :=
  ⟨unified_model_is_not_vacuous,
    ⟨Representation.representation_observations_preserved Representation.layerStatus
        ⟨Representation.layerStatus_roundTrip, Representation.layerStatus_coverage⟩,
      Representation.joint_legal_model_is_isomorphic_to_domain,
      PayoffEquilibrium.legal_payoff_preserved_swapDocket,
      PrecedentFlow.precedent_update_preserves_norm_structure M.env M.ad M.hwf M.atDay⟩,
    ⟨SourceNorms.horn_closure_semantic_iff M.norms M.atom,
      AdjudicationBridge.grounded_equivalence M.pol M.round M.hPolicyClosed M.hBaseInGrounded
        M.disputed,
      AdjudicationBridge.unique_verdict_iff_stable_kernel_singletons M.evalDom M.candidate
        M.hAdmissibleNonempty M.hCollapse,
      PayoffEquilibrium.external_equilibrium_reflects_legal (PayoffEquilibrium.legalPay 10)
        PayoffEquilibrium.extPay 0 1 PayoffEquilibrium.ActC.sue PayoffEquilibrium.ActR.refuse
        PayoffEquilibrium.withinEta_legal_external PayoffEquilibrium.extPay_nash⟩,
    ⟨InstitutionalEffects.projection_of_append_matches_step M.ledger M.eventId M.relFormed
        M.relObserved,
      InstitutionalEffects.performance_not_creation M.ledger M.performEventId M.obligor
        M.relFormed M.performAmount M.relObserved,
      fun h1 h2 => AdjudicationBridge.two_valued_exclusion M.pol M.hBaseConflictFree M.disputed
        h1 h2,
      PrecedentFlow.update_is_not_noop,
      PrecedentFlow.unauthorized_output_is_not_a_norm M.production M.hUnauthorized⟩,
    ⟨Temporal.legal_time_nonanticipation M.asOf M.past M.future₁ M.future₂ M.hFuture₁
        M.hFuture₂,
      Temporal.aggregate_add_arrival_insensitive M.past M.someLate,
      Uncertainty.finite_positive_support_truth_bridge M.weight M.truthAssessment M.hWeightPos
        M.hWeightTotal,
      Uncertainty.xuc_conditioning_denominator_is_clean_mass M.contaminated,
      Temporal.no_unified_time_carrier_yet⟩⟩

/-- **本件不是全称主张**（镜像 `BoundaryClosure.delimitation_is_not_general`，`:608`）：
    上面 (4) 里"未授权产出不是规范"是**类型层**的拒绝，只对 `NormLayerEntry` 的构造子集成立。
    本条正面交出一个片段外的写法，故任何"六类失真在整个代码库中无法表达"的读法都被否定。 -/
theorem unified_claim_is_not_general :
    ∃ (f : ULM.Outcome Nat → ULM.Outcome Nat),
      ∀ (e : ULM.FailureCore), f (.failure e) = ULM.Outcome.complete (42 : Nat) :=
  BoundaryClosure.delimitation_is_not_general

end JurisLean.Seams
