import Mathlib.Data.Finset.Basic
import Mathlib.Tactic
import JurisLean.FullMath.Numeric.Intervals
import JurisLean.Seams.BurdenStatutes
import JurisLean.Seams.Transitions
import JurisLean.Seams.Probability
import JurisLean.Seams.UnifiedInstance

/-!
# G6 —— 一条法定链条：民诉法解释第 91 条 → Horn 闭包 → 采纳 → 证明标准档 → 数额

## 一、本件为什么必须存在（这是**第一件**把五跳写在一起的 Lean 件）
此前的事实障碍是：`Seams/Probability.lean`（L5 证明标准／数额面）与
`Seams/ClaimBasis.lean`（L2 请求面）互相零 import，全仓没有任何一条陈述说过
"同一个案件从举证责任条款出发，经过闭包、经过可采纳性、经过法定标准档，落成一个数额"。
本件把 `Seams/Probability.lean`、`Seams/Transitions.lean`、`Seams/BurdenStatutes.lean`、
`Seams/UnifiedInstance.lean` 放进**同一个 import 闭包**，并让每一跳都是一个**具名函数或具名定理**。
（`Seams/ClaimBasis.lean` 由 `Seams/UnifiedInstance.lean:10` 带进同一闭包，于是 `Probability`
与 `ClaimBasis` 之间"互相零 import"这一障碍，在本件里第一次不再阻断同一次编译；
但本件**不**引用 `ClaimBasis` 的任何定理，请求地位面（`Status`／`Stage`）仍不是本链的一跳，
见 §未覆盖第 12 项。）
链条的载体只有一个：`JurisLean.Seams.UnifiedInstance.instanceM : UnifiedModel (Fin 3) (Fin 1)`
（`Seams/UnifiedInstance.lean:550`）。凡 `instanceM` 接不上的那一跳，本件**不**另造一个平行的
硬编码世界去凑链，而是把缺的那一跳写成具名 `def … : Prop` 义务，并在能判的地方
**证明它当前不成立**（见 §七与 §八）。"链在某处悄悄换了主体"正是本件要消灭的失败模式，
所以 §六 把两处主体错位做成定理，而不是留给注释。

## 二、五跳的载体与本件用的具名件（逐跳）
1. **举证责任分配**（民诉法解释第 91 条第 (一)(二) 项 ＋ 第 90 条第 2 款）。
   本件**不重述** `Seams/BurdenStatutes.lean` 已证的条文要件定理，只引用：
   `art91_burden_follows_assertion:109`、`art91_clause_partition:115`、
   `art91_two_clauses_exhaust_the_four_poles:123`、
   `art90_adverse_when_burdened_party_has_gap:153`、
   `art108_phrase_is_high_probability_not_paraphrase:406`、`art108_high_probability_yields_existence:440`。
   本件新增的是**接点**：`chainNormClass`、`chainBurdenedParty`、`chainGap`、`chainAtomOfClass`。
2. **请求原子与 Horn 闭包**（民法典第 585 条第 2 款 ＋ 法释〔2023〕13号第 65 条第 2 款的门槛形状）。
   引用 `Seams/Transitions.lean` 的 `claimCase`、`namedClosure:57`、`admissibleFromHorn:62`、
   `reduction_claim_derived_obligation:313`、`horn_derived_is_admissible:110`、
   `conflict_args_eq_or:333`、`reduction_in_args:323`、`no_adjustment_in_args:327`、
   `attack_no_adjustment_to_reduction:344`、`conflict_not_final_derivable_obligation:436`，
   以及 `SourceNorms.horn_closure_semantic_iff:171`；本实例一侧引用
   `UnifiedInstance.normsM:287`、`zero_in_closureM:307`、`one_in_closureM:312`、`atomM_entailed:318`。
3. **可采纳与终端策略**（第 105 条"必须作出判断并公开结果"作读法锚）。
   引用 `AdjudicationBridge.TerminalPolicy:129`、`FinalDerivable:387`、`adoptedStep:165`、
   `grounded_support_correspondence:508`、`two_valued_exclusion:401`；本实例一侧引用
   `UnifiedInstance.policyClosed_polM_zero:442`、`baseConflictFree_polM:458`、
   `disputedM_is_grounded:465`、`aafM_attacks_eq_empty:351`。
4. **证明标准档位**（第 108 条第 1 款"高度可能性" vs 第 109 条"排除合理怀疑"）。
   **事实纠正（写在这里，不留给注释）**：任务书称 `ProofStandard` 类型在
   `Seams/Probability.lean`。本件读盘核实：`Seams/Probability.lean` **没有** `ProofStandard`。
   仓内三个互不相通的"标准"载体是
   ① `JurisLean.Seams.BurdenStatutes.ProofStandardName`（条文具名两档，`:495`，本件用它）；
   ② `JurisLean.FullMath.Burden.Standard`（数值门槛＋范围串，`FullMath/Burden/Standards.lean:34`，
      配 `gate:48`）；③ `JurisLean.ULM.ProofStandard`（`standardId/domain/version` 三元元数据，
      `ULM12Procedure.lean:7`）。本件**只**用 ①，②③ 登记为未接（§未覆盖第 6 项）。
   引用 `art108_art109_phrases_are_distinct:1086`、`standard_tier_is_a_hierarchy:1041`、
   `standard_tiers_cannot_be_merged:1059`、`standard_tier_two_way_decision:1071`、
   `standardGate:593`、`StandardNamedAt:599`、`EvalDomainLawful:616`、
   `standard109_named_at_implies_collapse:648`。
5. **数额面**（法释〔2023〕13号第 64 条第 2 款的双侧举证 ＋ 第 65 条的 30% 门槛）。
   引用 `Probability.reductionGate:531`、`reductionFloor:538`、`choose:568`、`Allow:552`、
   `lossBasedData:670`、`lossBasedData_facts:683`、`reduction_admits_declared_conditions:573`、
   `TwoSidedBurden.BurdenRecord:797`、`openGateData:822`、`openGateData_gate:827`、
   `twoSidedGate:812`、`twoSidedGate_false_of_no_compliant_proof:832`、`AllowOf:802`、`AllowTwo:816`、
   `compliant_side_changes_extension:838`。区间载体 `FullMath.Numeric.Iv`／`Iv.mem` 只做
   **在册登记**（`chainIntervalCarrier`、`chainIntervalMem`），本件不给它与 `Amount := ℤ`
   之间的任何等式（§未覆盖第 5 项）。

## 三、本件**不**做什么
- 不认定任何真实案件、任何真实条文的适用结果；所有载体都是仓内既有夹具。
- 不新增第三个证明标准档（第 108 条第 3 款"另有规定从其规定"仍是出口条款，不是档位）。
- 不把 `instanceM.performAmount : Nat` 与数额面的 `Amount := ℤ` 说成同一载体：
  两处都是 100 这个数字，但那是两个独立夹具**各自**选的数，本件把它做成
  `chain_amount_faces_meet_only_numerically` 并明确标注为数值巧合（§五第 3 条）。
- 不改 `Seams/Unified.lean` 的 `UnifiedModel` 字段表（改契约属 Owner 授权）；
  缺栏位这一事实只以义务 `def` 与判定式定理登记。
- 不动 `KernelV3` 冻结段、`LegalModelV2.lean:134 Relation`、`ApplicableNormQuery`、`对象定义v3` 档案。
- 不声称端到端条文链已闭合：本件交付的是"第一件把五跳写在一起的件"，
  两处接不上已写成定理（§七）。

## 四、档位
`SEAM_G6_LOCAL_BUILD_PROVISIONAL / CI_NOT_RUN`（fail-closed）。零 `sorry`、零 `admit`、
零 `native_decide`、零自定义 `axiom`；没有把结论写进前提，没有为过编译改窄任何复用的陈述。
本件**已**在本地 `lake build JurisLean.Seams.StatuteChain` 绿过一次（3 次尝试，末次 `LAKE_EXIT=0`，
日志 `_seams_build_logs/precheck3_StatuteChain.log`），但那是**临时预检**不是认定；
本件**未**入根 `JurisLean.lean`，Lean 权威认定只走绑定 subject SHA 的 CI。
条文文字：[一手已核]（承 `BurdenStatutes` 头注的核验记录）；把某款读成某谓词：[建模选择]；
本件新增的法律归类读法：[代拟稿]；定理：[待 CI]。
本件所有 `name:LINE` 与 `file:LINE` 坐标都在落笔**之后**重新对盘复算过一遍
（81 条具名引用＋10 条文件锚，复算脚本逐条比对声明行）。
注意：本轮施工期间 `Seams/BurdenStatutes.lean` 与 `Seams/UnifiedInstance.lean` 正被并行修改
（分别已增长 +5 与 +3~+8 行），坐标会随下一次插入再漂移；行号是指针不是事实，
引用前先重取。
-/

open JurisLean.Seams.AdjudicationBridge
-- 名称解析说明：`instanceM` 声明在 `JurisLean.Seams.UnifiedInstance` 里
-- （`Seams/UnifiedInstance.lean:550`），与本草稿所在的 `JurisLean.Seams.StatuteChain`
-- 是兄弟命名空间，故裸名 `instanceM` 在本件不可见。打开该命名空间只是把已有的全名接上，
-- 不改变任何被引用对象的身份，也不改任何陈述文本。
open JurisLean.Seams.UnifiedInstance

namespace JurisLean.Seams.StatuteChain

/-! ## 〇、载体读数与换载体的等式（每一条都是 `rfl`，为了让后面的 `rw` 能匹配上）-/

/-- 中文说明（第 1 跳的规范类读数）：本链待判的那条主张——"约定违约金过分高于损失，
    请求酌减"（民法典第 585 条第 2 款）——按第 91 条规范说归入**第 (二) 项**
    （主张法律关系**变更**的基本事实）。[代拟稿]：条文只写"变更、消灭或者权利受到妨害"，
    把酌减请求读成"主张法律关系变更"是本件宣告的归类，不是条文措辞。 -/
def chainNormClass : BurdenStatutes.NormClass := BurdenStatutes.NormClass.altering

/-- 中文说明（第 1 跳的负担方）：第 90 条第 2 款那个单数的"负有举证证明责任的当事人"，
    在本链里是提出酌减请求的一方（第 90 条第 1 款前段："……所依据的事实"）。
    [建模选择]：与法释〔2023〕13号第 64 条第 2 款"违约方……应当承担举证责任"同侧。 -/
def chainBurdenedParty : BurdenStatutes.BurdenParty := BurdenStatutes.BurdenParty.proponent

/-- 中文说明（第 1 跳的缺口取值）：本件**不认定**真实卷宗里违约方是否完成第 64 条第 2 款
    的举证，故取第 90 条第 2 款第一支"未能提供证据"作保守值，让 fail-closed 落在缺证一侧。
    [代拟稿] -/
def chainGap : BurdenStatutes.ProductionStatus := BurdenStatutes.ProductionStatus.notProduced

/-- 中文说明（第 1 跳 → L1 载体的接点）：第 91 条的规范类落到本实例 L1 原子上的读法。
    第 (一) 项 `constitutive` → 原子 `0`（"请求权成立的要件已成就"）；
    第 (二) 项三目 → 原子 `1`（"可依法请求酌减"）＝ `instanceM.atom`。
    方向刻意取"规范类 → 原子"：对归纳类型 `NormClass` 作模式匹配是本仓既有写法
    （见 `BurdenStatutes.art91IsClauseOne`），反过来对 `Fin 2` 取值作条件判定要走 `Fin.val`
    的化简，本件不引入那条不可控路径。[建模选择] -/
def chainAtomOfClass : BurdenStatutes.NormClass → Fin 2
  | .constitutive => 0
  | .altering => 1
  | .extinguishing => 1
  | .impeding => 1

/-- 中文证明（载体等式）：本实例的 L1 栏就是 `UnifiedInstance.normsM`。 -/
theorem chain_norms_eq : instanceM.norms = UnifiedInstance.normsM := rfl

/-- 中文证明（载体等式）：本实例的待判原子就是 `1`。 -/
theorem chain_atom_eq : instanceM.atom = (1 : Fin 2) := rfl

/-- 中文证明（载体等式）：本实例的 L2 框架就是 `UnifiedInstance.aafM`。 -/
theorem chain_aaf_eq : instanceM.aaf = UnifiedInstance.aafM := rfl

/-- 中文证明（载体等式）：本实例的终端策略就是 `UnifiedInstance.polM`。 -/
theorem chain_pol_eq : instanceM.pol = UnifiedInstance.polM := rfl

/-- 中文证明（载体等式）：本实例的争议论点就是 `UnifiedInstance.claimReduction`。 -/
theorem chain_disputed_eq : instanceM.disputed = UnifiedInstance.claimReduction := rfl

/-- 中文证明（载体等式）：本实例的评价域就是 `UnifiedInstance.verdictDomain`。 -/
theorem chain_evalDom_eq : instanceM.evalDom = UnifiedInstance.verdictDomain := rfl

/-- 中文证明（本实例论点集的字面形）：`aafM.args` 一栏按 `Seams/UnifiedInstance.lean:348`
    写字面 `Finset`，不取闭包像——这一栏的写法本身就是 §七第 2 条义务的成因。 -/
theorem chain_aaf_args_eq :
    instanceM.aaf.args =
      ({UnifiedInstance.claimReduction, UnifiedInstance.claimNoAdjustment} : Finset Arg) :=
  rfl

/-- 中文证明（可采纳评价的刻画，搬到本实例的载体上）：`instanceM` 的评价域
    恰有**一个**可采纳评价 `{0}`。本式是 `UnifiedInstance.verdictDomain_admissible:139`
    的换载体写法，后面各跳的判定都靠它。 -/
theorem chain_admissible_iff (S : Set (Fin 3)) :
    Admissible instanceM.evalDom S ↔ S = ({0} : Set (Fin 3)) :=
  UnifiedInstance.verdictDomain_admissible S

/-- 中文证明（稳定核的刻画）：本实例评价域的稳定核是单点 `{0}`。 -/
theorem chain_stableKernel_eq : stableKernel instanceM.evalDom = ({0} : Set (Fin 3)) :=
  UnifiedInstance.verdictDomain_stableKernel

/-- 中文证明（核里有 `0`，写在实例载体上）：下面几条反复用的成员事实。 -/
theorem chain_zero_in_kernel : (0 : Fin 3) ∈ stableKernel instanceM.evalDom := by
  rw [chain_stableKernel_eq]
  exact UnifiedInstance.zero_mem_singleton

/-! ## 一、第 1 跳：举证责任分配（第 91 条两项 ＋ 第 90 条第 2 款）-/

/-- 中文证明（**第 1 跳·分配落在本实例的待判原子上**）：三件事同时成立——
    ①本链的规范类落在第 91 条第 (二) 项（`art91_clause_partition` 的第 2 支）；
    ②负担挂在提出者身上（`art91_burden_follows_assertion`，两款共同形式）；
    ③负担方自己留有第 90 条第 2 款那支缺口时，不利后果为真
    （`art90_adverse_when_burdened_party_has_gap` 的第 1 支）。
    三条都是**引用**，本件不重证其中任何一条。 [待 CI] -/
theorem chain_art91_allocation_hop :
    BurdenStatutes.art91IsClauseOne chainNormClass = false ∧
      BurdenStatutes.art91BurdenOf chainNormClass chainBurdenedParty = chainBurdenedParty ∧
        BurdenStatutes.art90AdverseOn chainBurdenedParty chainBurdenedParty chainGap = true :=
  ⟨BurdenStatutes.art91_clause_partition.2.1,
    BurdenStatutes.art91_burden_follows_assertion chainNormClass chainBurdenedParty,
    BurdenStatutes.art90_adverse_when_burdened_party_has_gap.1⟩

/-- 中文证明（第 1 跳的两款穷尽性在本链规范类上的读数）：
    `art91_two_clauses_exhaust_the_four_poles` 给出"落在两款之一"的判定，
    本件同时能指出落在**哪**一款。 -/
theorem chain_art91_clause_is_decidable :
    (BurdenStatutes.art91IsClauseOne chainNormClass = true ∨
        BurdenStatutes.art91IsClauseOne chainNormClass = false) ∧
      BurdenStatutes.art91IsClauseOne chainNormClass = false :=
  ⟨BurdenStatutes.art91_two_clauses_exhaust_the_four_poles chainNormClass,
    BurdenStatutes.art91_clause_partition.2.1⟩

/-- 中文证明（**第 1 跳的落点**）：本链的规范类经 `chainAtomOfClass` 落的原子，
    正是本实例的待判原子 `instanceM.atom`。这一式是第 1 跳与第 2 跳之间的**接点**——
    没有它，"举证责任分配"与"Horn 闭包"就是两个类型上的故事。 -/
theorem chain_atom_is_the_clause_two_slot : chainAtomOfClass chainNormClass = instanceM.atom :=
  rfl

/-! ## 二、第 2 跳：请求原子与 Horn 闭包（L1）-/

/-- 中文证明（**第 2 跳·闭包与语义两侧同真，且两侧由已证等值式相连**）：
    ①要件原子 `0` 在 `instanceM.norms` 的迭代闭包里（`UnifiedInstance.zero_in_closureM`）；
    ②待判原子 `instanceM.atom` 也在闭包里（`UnifiedInstance.one_in_closureM`）；
    ③它是语义后承（`UnifiedInstance.atomM_entailed`）；
    ④"进闭包 ↔ 被蕴含"正是 `SourceNorms.horn_closure_semantic_iff:171` 在本实例上的取值。
    法律读法：民法典第 585 条第 2 款的请求以"要件成就"为前提（`UnifiedInstance.ruleM:295` 那条
    以 `0` 为前提、结论为 `1` 的规则）。 -/
theorem chain_L1_closure_hop :
    (0 : Fin 2) ∈ SourceNorms.closureAt instanceM.norms ∧
      instanceM.atom ∈ SourceNorms.closureAt instanceM.norms ∧
        SourceNorms.entailed instanceM.norms instanceM.atom ∧
          (instanceM.atom ∈ SourceNorms.closureAt instanceM.norms ↔
            SourceNorms.entailed instanceM.norms instanceM.atom) :=
  ⟨UnifiedInstance.zero_in_closureM, UnifiedInstance.one_in_closureM,
    UnifiedInstance.atomM_entailed,
    SourceNorms.horn_closure_semantic_iff instanceM.norms instanceM.atom⟩

/-- 中文证明（**第 2 跳·缝件一侧的支持位**，载体取 `Transitions.claimCase`，不是 `instanceM`）：
    酌减请求在 S1→S2 缝件的 Horn 闭包里（`Transitions.reduction_claim_derived_obligation:313`），
    经该件的桥定理 `horn_derived_is_admissible:110` 得到它的命名像**在支持位上为真**。
    法律读法：支持性是**从下层算出来的**，不是外部旗标——本式就是那句话在本链上的实例。 -/
theorem chain_L1_derived_support_true :
    Transitions.admissibleFromHorn Transitions.claimCase Transitions.encode
      (Transitions.encode Transitions.ClauseAtom.reductionClaim) = true :=
  Transitions.horn_derived_is_admissible Transitions.claimCase Transitions.encode
    Transitions.ClauseAtom.reductionClaim Transitions.reduction_claim_derived_obligation

/-! ## 三、第 3 跳：可采纳与终端策略（L2）-/

/-- 中文证明（**第 3 跳·本实例的争议论点被终端策略采纳**）：
    走条件桥 `grounded_support_correspondence:508`（正向需片段 `policyClosed`，
    本实例那一栏由 `UnifiedInstance.policyClosed_polM_zero:442` 交出，这里直接取
    `instanceM.hPolicyClosed` 字段），原料是 `UnifiedInstance.disputedM_is_grounded:465`。
    法律读法：本案每条主张都有明文规则直接指定采纳（`polM.conclusive = aafM.args`），
    且无例外／抗辩规范打成的攻击边（`aafM.attacks = ∅`，即第 91 条那套分配没有对抗材料介入）。 -/
theorem chain_L2_finalDerivable : FinalDerivable instanceM.pol instanceM.disputed :=
  grounded_support_correspondence instanceM.pol 0 instanceM.hPolicyClosed instanceM.disputed
    UnifiedInstance.disputedM_is_grounded

/-- 中文证明（**第 3 跳·两值不塌**）：同一论点不可能既被终端策略最终采纳又被最终驳倒。
    本式把假设交给**本实例自己声明的**片段 `instanceM.hBaseConflictFree`
    （即 `UnifiedInstance.baseConflictFree_polM:458`），引用
    `AdjudicationBridge.two_valued_exclusion:401`。 -/
theorem chain_L2_not_defeated : ¬ FinalDefeated instanceM.pol instanceM.disputed := by
  intro h
  exact two_valued_exclusion instanceM.pol instanceM.hBaseConflictFree instanceM.disputed
    chain_L2_finalDerivable h

/-- 中文证明（第 3 跳的合并形）：采纳成立、驳倒不成立，两支同时是本实例的定理。 -/
theorem chain_L2_hop :
    FinalDerivable instanceM.pol instanceM.disputed ∧
      ¬ FinalDefeated instanceM.pol instanceM.disputed :=
  ⟨chain_L2_finalDerivable, chain_L2_not_defeated⟩

/-! ## 四、第 4 跳：证明标准档位（第 108 条第 1 款 vs 第 109 条）-/

/-- 中文证明（**公理①对本实例成立**）：存在可采纳评价
    （`UnifiedInstance.verdictDomain_admissibleNonempty:157`），且每个可采纳评价都非空白——
    因为可采纳评价只能是 `{0}`（`chain_admissible_iff`）。
    引用 `BurdenStatutes.hasNonblankAdmissibleEvaluation:560`（条文锚：第 105 条＋第 108 条第 1、2 款）。 -/
theorem chain_tier_part_one :
    BurdenStatutes.hasNonblankAdmissibleEvaluation instanceM.evalDom :=
  ⟨UnifiedInstance.verdictDomain_admissibleNonempty, by
    intro S hS
    have hS0 : S = ({0} : Set (Fin 3)) := (chain_admissible_iff S).mp hS
    rw [hS0]
    exact ⟨0, UnifiedInstance.zero_mem_singleton⟩⟩

/-- 中文证明（**公理②弱交封闭对本实例成立**）：两个可采纳评价都只能是 `{0}`，
    它们的交仍是 `{0}`。这里手工展开 `{0} ∩ {0} = {0}` 的两个包含（写法取自
    `BurdenStatutes.disjointVerdict_holds_part_two:743`），不用本件未核对过的 `Set.inter_self`。
    条文锚：第 93 条第 1 款（七项免证事实的叠合稳定性）＋第 92 条第 1 款（自认）。 -/
theorem chain_tier_part_two : BurdenStatutes.admissibleWeakInterClosed instanceM.evalDom := by
  intro S T hS hT _
  have hS0 : S = ({0} : Set (Fin 3)) := (chain_admissible_iff S).mp hS
  have hT0 : T = ({0} : Set (Fin 3)) := (chain_admissible_iff T).mp hT
  have hinter : (({0} : Set (Fin 3)) ∩ ({0} : Set (Fin 3)) = ({0} : Set (Fin 3))) := by
    refine Set.Subset.antisymm ?_ ?_
    · exact fun x hx => Set.mem_of_mem_inter_left hx
    · exact fun x hx => Set.mem_inter hx hx
  rw [hS0, hT0, hinter]
  exact (chain_admissible_iff _).mpr rfl

/-- 中文证明（**公理③·108 档挂得上**）：每个可采纳评价都与稳定核有公共结论（这里就是 `0`）。
    引用 `BurdenStatutes.StandardNamedAt:599` 与 `standardGate:593` 的第 108 条第 1 款那一支。 -/
theorem chain_tier_attaches_108 :
    BurdenStatutes.StandardNamedAt BurdenStatutes.ProofStandardName.highProbability108
      instanceM.evalDom := by
  intro S hS
  have hS0 : S = ({0} : Set (Fin 3)) := (chain_admissible_iff S).mp hS
  have hmem : (0 : Fin 3) ∈ S := by
    rw [hS0]
    exact UnifiedInstance.zero_mem_singleton
  exact ⟨0, hmem, chain_zero_in_kernel⟩

/-- 中文证明（**公理③·109 档也挂得上**，理由正是"可采纳评价只有一个"）：
    109 档要求 `S` 含于**每一个**可采纳评价；本实例只有一个可采纳评价 `{0}`，
    而它就是 `S` 本身，条件折叠成 `{0} ⊆ {0}`。 -/
theorem chain_tier_attaches_109 :
    BurdenStatutes.StandardNamedAt BurdenStatutes.ProofStandardName.excludesReasonableDoubt109
      instanceM.evalDom := by
  intro S hS T hT
  have hS0 : S = ({0} : Set (Fin 3)) := (chain_admissible_iff S).mp hS
  have hT0 : T = ({0} : Set (Fin 3)) := (chain_admissible_iff T).mp hT
  have hsub : S ⊆ T := by
    intro x hx
    rw [hS0] at hx
    rw [hT0]
    exact hx
  exact hsub

/-- 中文证明（**第 4 跳·本实例的评价域是"依法"的**）：`BurdenStatutes.EvalDomainLawful:616`
    的三条候选公理在 `instanceM.evalDom` 上同时成立。此前 `EvalDomainLawful` 只在
    `BurdenStatutes` 自造的夹具（`fullInterDomain`）与被挡住的见证（`trialDomain`）上被讨论过，
    **从未**落到 `UnifiedModel` 的字段上。 -/
theorem chain_tier_hop :
    BurdenStatutes.EvalDomainLawful instanceM.evalDom ∧
      BurdenStatutes.attachesNamedStandard instanceM.evalDom :=
  ⟨⟨chain_tier_part_one, chain_tier_part_two,
      ⟨BurdenStatutes.ProofStandardName.highProbability108, chain_tier_attaches_108⟩⟩,
    ⟨BurdenStatutes.ProofStandardName.highProbability108, chain_tier_attaches_108⟩⟩

/-- 中文证明（**第 4 跳的实质回报：`instanceM` 的 `hCollapse` 那一栏现在是被推出来的**）：
    把评价族挂名到第 109 条那一档，经
    `BurdenStatutes.standard109_named_at_implies_collapse:648` 就得到 `collapsesToKernel`。
    法律读法：唯一判决不是本实例"字段里写着的假设"，而是"跨评价强度判据"的后果——
    这正是 `BurdenStatutes` 头注对"三组规则判据填不上空隙"那一诊断的正向补充。 -/
theorem chain_collapse_from_the_109_tier : collapsesToKernel instanceM.evalDom :=
  BurdenStatutes.standard109_named_at_implies_collapse instanceM.evalDom
    chain_tier_attaches_109

/-- 中文证明（**档位差在本实例的载体上仍是可区分的谓词**）：`Fin 3` 的幂集上存在一个集合，
    满足 108 档（与核有公共结论 `0`）却不满足 109 档（不含于可采纳评价 `{0}`）。
    与本式对照的是上面两条：在**可采纳评价**上两档同时成立，因为本实例只有一个可采纳评价。
    ⇒ 档位差的见证只能落在"评价族至少有两个"或 `CredProfile` 上，不能只在 `instanceM.evalDom` 上找。 -/
theorem chain_tier_gates_are_distinct_on_the_carrier :
    ∃ S : Set (Fin 3),
      BurdenStatutes.standardGate BurdenStatutes.ProofStandardName.highProbability108
        instanceM.evalDom S ∧
        ¬ BurdenStatutes.standardGate BurdenStatutes.ProofStandardName.excludesReasonableDoubt109
          instanceM.evalDom S := by
  refine ⟨({0, 1} : Set (Fin 3)), ?_, ?_⟩
  · exact ⟨0, by simp, chain_zero_in_kernel⟩
  · intro h
    -- `standardGate` 的第 109 档那一支是"含于每个可采纳评价"；先把展开后的形写成具名 `have`，
    -- 再在可采纳评价 `{0}` 处实例化（照 `BurdenStatutes.standard109_named_at_implies_collapse:648`
    -- 证明里那条 `have hg` 的写法）
    have hg : ∀ T : Set (Fin 3), Admissible instanceM.evalDom T →
        ({0, 1} : Set (Fin 3)) ⊆ T := h
    have hsub : ({0, 1} : Set (Fin 3)) ⊆ ({0} : Set (Fin 3)) :=
      hg ({0} : Set (Fin 3)) ((chain_admissible_iff _).mpr rfl)
    have h1 : (1 : Fin 3) ∈ ({0} : Set (Fin 3)) := hsub (by simp)
    exact absurd h1 (by simp)

/-- 中文证明（**第 4 跳的条文侧材料，载体取 `BurdenStatutes.CredProfile`**）：
    两档构成严格层级（`standard_tier_is_a_hierarchy:1041`）且不可合并
    （`standard_tiers_cannot_be_merged:1059`）。本式的载体**不是** `instanceM`：
    `UnifiedModel` 的字段表（`Seams/Unified.lean:96`）里没有任何 `CredProfile` 形制的栏，
    已登记为 §未覆盖第 3 项。 -/
theorem chain_tier_material_is_a_strict_hierarchy :
    (∀ ρ : BurdenStatutes.CredProfile,
        BurdenStatutes.standardMeets
          BurdenStatutes.ProofStandardName.excludesReasonableDoubt109 ρ = true →
          BurdenStatutes.standardMeets BurdenStatutes.ProofStandardName.highProbability108 ρ = true) ∧
      ¬ ∀ ρ : BurdenStatutes.CredProfile,
          BurdenStatutes.standardMeets BurdenStatutes.ProofStandardName.highProbability108 ρ = true ↔
            BurdenStatutes.standardMeets
              BurdenStatutes.ProofStandardName.excludesReasonableDoubt109 ρ = true :=
  ⟨BurdenStatutes.standard_tier_is_a_hierarchy, BurdenStatutes.standard_tiers_cannot_be_merged⟩

/-- 中文证明（**第 4 跳的认定后果：达标 → 认定该事实存在**）：
    取仓内夹具 `BurdenStatutes.CredProfile.cAllAccepted`，它在 108 档达标
    （`standard_tier_two_way_decision:1071` 的第 1 支），把**这个 Bool 读数**喂给
    `BurdenStatutes.art108Finding`（第 108 条第 1、2 款的判定顺序），
    于是第 1 款那一支发动，认定结论是"存在"
    （`art108_high_probability_yields_existence:440`）。
    本条把"档位达标"与"事实认定"接成**一项陈述**而不是两段散文。
    [代拟稿]：达标读数与 `art108Finding` 第 1 个输入的口径同一，是本件的建模选择。 -/
theorem chain_art108_finding_fires :
    BurdenStatutes.standardMeets BurdenStatutes.ProofStandardName.highProbability108
        BurdenStatutes.CredProfile.cAllAccepted = true ∧
      BurdenStatutes.art108Finding
        (BurdenStatutes.standardMeets BurdenStatutes.ProofStandardName.highProbability108
          BurdenStatutes.CredProfile.cAllAccepted) false =
        BurdenStatutes.FactFinding.foundToExist := by
  have h1 : BurdenStatutes.standardMeets BurdenStatutes.ProofStandardName.highProbability108
      BurdenStatutes.CredProfile.cAllAccepted = true :=
    (BurdenStatutes.standard_tier_two_way_decision).1
  refine ⟨h1, ?_⟩
  rw [h1]
  exact BurdenStatutes.art108_high_probability_yields_existence false

/-- 中文证明（第 4 跳的措辞锚点，两条都由 `BurdenStatutes` 已证）：
    第 108 条第 1 款原词"高度可能性"既不等于台账里那条转述"高度盖然性"，
    也不等于第 109 条原词"排除合理怀疑"。本件把这两个**文本事实**作为链条的条文前提交出。 -/
theorem chain_phrases_are_distinct :
    BurdenStatutes.art108_officialPhrase ≠
      BurdenStatutes.art108_paraphraseFoundInMasterPlan ∧
      BurdenStatutes.art108_officialPhrase ≠ ("排除合理怀疑" : String) :=
  ⟨BurdenStatutes.art108_phrase_is_high_probability_not_paraphrase,
    BurdenStatutes.art108_art109_phrases_are_distinct⟩

/-! ## 五、第 5 跳：数额面（第 64 条第 2 款的双侧举证 → 闸门 → 准许关系）-/

/-- 中文说明（数额面的区间载体·**只做在册登记**）：区间面在 `ℚ` 上，载体是
    `FullMath/Numeric/Intervals.lean:16` 的 `JurisLean.FullMath.Numeric.Iv`
    （`lo hi : ℚ` 加端点序），成员判定是 `Iv.mem:24`。本件**不**给它与
    `Probability.Amount := ℤ` 之间的任何映射，也不把该件的 `seen_span_not_global_bound:146`
    读成法律结论。登记在此是为了让 §未覆盖第 5 项有可指的名字。[构造性定义] -/
def chainIntervalCarrier : Type := JurisLean.FullMath.Numeric.Iv

/-- 中文说明（区间面成员判定在本件里的名字；本件不用它做任何定理）。 -/
def chainIntervalMem : ℚ → chainIntervalCarrier → Prop := JurisLean.FullMath.Numeric.Iv.mem

/-- 中文证明（**第 5 跳·举证要件确实改变数额面的准入**）：四件事同时成立——
    ①底数据（约定 300、损失 100、有请求、非恶意、违约方已举证）开闸
    （`TwoSidedBurden.openGateData_gate:827`）；
    ②守约方一侧（法释〔2023〕13号第 64 条第 2 款后句"非违约方主张约定的违约金合理的，
    也应当提供相应的证据"）未完成举证时，**双向**闸门关
    （`twoSidedGate_false_of_no_compliant_proof:832`）；
    ③④同一个额（下界）在现有 `AllowOf` 下仍被准许、在 `AllowTwo` 下**不再**被准许
    （`compliant_side_changes_extension:838` 两支）。
    法律读法：**在数额面上**举证要件是有输入的，并且改变外延；
    与本实例采纳面的对照见 `chain_art90_gate_has_input_witness`（2026-10-03 G6 轮后两面对齐）。 -/
theorem chain_amount_hop :
    Probability.reductionGate Probability.TwoSidedBurden.openGateData = true ∧
      Probability.TwoSidedBurden.twoSidedGate
        (⟨Probability.TwoSidedBurden.openGateData, false⟩ :
          Probability.TwoSidedBurden.BurdenRecord Unit) = false ∧
        Probability.TwoSidedBurden.AllowOf
          (⟨Probability.TwoSidedBurden.openGateData, false⟩ :
            Probability.TwoSidedBurden.BurdenRecord Unit)
          (Probability.reductionFloor Probability.TwoSidedBurden.openGateData) ∧
          ¬ Probability.TwoSidedBurden.AllowTwo
            (⟨Probability.TwoSidedBurden.openGateData, false⟩ :
              Probability.TwoSidedBurden.BurdenRecord Unit)
            (Probability.reductionFloor Probability.TwoSidedBurden.openGateData) :=
  ⟨Probability.TwoSidedBurden.openGateData_gate,
    Probability.TwoSidedBurden.twoSidedGate_false_of_no_compliant_proof
      Probability.TwoSidedBurden.openGateData,
    Probability.TwoSidedBurden.compliant_side_changes_extension.1,
    Probability.TwoSidedBurden.compliant_side_changes_extension.2⟩

/-- 中文证明（**第 5 跳·选择函数给出的额总被准许关系接受**）：
    直接取 `Probability.reduction_admits_declared_conditions:573` 在开闸底数据上的值。
    法律读法：准许关系是**关系**不是钳制函数（P-098 的立场）；第 65 条第 2 款的 30% 门槛
    只是准入条件，不是计算规则。 -/
theorem chain_amount_declared_choice_admitted :
    Probability.Allow Probability.TwoSidedBurden.openGateData
      (Probability.choose Probability.TwoSidedBurden.openGateData) :=
  Probability.reduction_admits_declared_conditions Probability.TwoSidedBurden.openGateData

/-- 中文证明（第 5 跳与本实例数额栏的关系·**只是数值巧合**）：
    本实例唯一的数额栏 `instanceM.performAmount`（`Seams/Unified.lean:120` 声明为 `Nat`）
    与数额面的下界 `Probability.reductionFloor Probability.lossBasedData : Amount`（`ℤ`）
    都是 100。本式**只**说"两处各自写了 100 这个数字"，**不**说这两个 100 是同一笔钱：
    一个属于 L5 履行事件、一个属于违约金酌减夹具，中间没有任何声明的载体映射
    （对齐 `Seams/Unified.lean` 的错位登记 #3、#7，见 §未覆盖第 4 项）。
    第 2 支取 `lossBasedData_facts:683` 的第 2 合取支。 -/
theorem chain_amount_faces_meet_only_numerically :
    instanceM.performAmount = (100 : Nat) ∧
      Probability.reductionFloor Probability.lossBasedData = (100 : Probability.Amount) :=
  ⟨rfl, Probability.lossBasedData_facts.2.1⟩

/-! ## 六、主体同一性检查（本件存在的理由：不许链在中途换主体）-/

/-- 中文证明（标签在字符串层确实相同）：缝件的命名像 `encode ClauseAtom.reductionClaim`
    与本实例的争议论点 `instanceM.disputed` 是同一个字面量。这是两条链**唯一**重合的地方。 -/
theorem chain_seam_label_eq :
    Transitions.encode Transitions.ClauseAtom.reductionClaim = instanceM.disputed := rfl

/-- 中文证明（另一标签也相同）。 -/
theorem chain_seam_label2_eq :
    Transitions.encode Transitions.ClauseAtom.noAdjustment = UnifiedInstance.claimNoAdjustment :=
  rfl

/-- 中文证明（**两份框架的论点集相同**）：S1→S2 缝件的 `conflictAAF.args`
    ＝ `Transitions.namedClosure claimCase encode`（闭包的像）＝ 本实例的字面论点集。
    正向用 `Transitions.conflict_args_eq_or:333` 穷尽像的元素
    （该穷尽性靠 `HornSystem.horn_result_subset_univ`，闭包走不出 `claimCase.univ`），
    反向用 `Transitions.reduction_in_args:323` 与 `no_adjustment_in_args:327`。 -/
theorem chain_seam_args_eq_instance_args :
    Transitions.conflictAAF.args = instanceM.aaf.args := by
  refine Finset.ext ?_
  intro a
  refine ⟨?_, ?_⟩
  · intro ha
    rcases Transitions.conflict_args_eq_or a ha with rfl | rfl
    · rw [chain_seam_label_eq, chain_disputed_eq, chain_aaf_args_eq]
      exact Finset.mem_insert_self UnifiedInstance.claimReduction
        {UnifiedInstance.claimNoAdjustment}
    · rw [chain_seam_label2_eq, chain_aaf_args_eq]
      exact Finset.mem_insert_of_mem (Finset.mem_singleton_self
        UnifiedInstance.claimNoAdjustment)
  · intro ha
    rw [chain_aaf_args_eq] at ha
    rcases Finset.mem_insert.mp ha with rfl | hx
    · rw [← chain_disputed_eq, ← chain_seam_label_eq]
      exact Transitions.reduction_in_args
    · rcases Finset.mem_singleton.mp hx with rfl
      rw [← chain_seam_label2_eq]
      exact Transitions.no_adjustment_in_args

/-- 中文证明（**论点集相同、攻击结构不同，于是结论相反**）：本实例的攻击边为空
    （`UnifiedInstance.aafM_attacks_eq_empty:351`），缝件含互斥边
    （`Transitions.attack_no_adjustment_to_reduction:344`）；因此同一标签在缝件侧
    `¬ FinalDerivable`（`Transitions.conflict_not_final_derivable_obligation:436`），
    在本实例侧 `FinalDerivable`（`chain_L2_finalDerivable`）。
    ⇒ 论点集相等**不**意味着链条主体相同：攻击结构不同就是主体不同。
    本件把这条反面教材做成定理，因为"链在某处换了主体"正是本件要消灭的失败模式。 -/
theorem chain_subject_divergence :
    Transitions.conflictAAF.args = instanceM.aaf.args ∧
      Transitions.conflictAAF.attacks ≠ instanceM.aaf.attacks ∧
        FinalDerivable instanceM.pol instanceM.disputed ∧
          ¬ FinalDerivable Transitions.conflictPolicy
            (Transitions.encode Transitions.ClauseAtom.reductionClaim) := by
  refine ⟨chain_seam_args_eq_instance_args, ?_, chain_L2_finalDerivable,
    Transitions.conflict_not_final_derivable_obligation⟩
  intro heq
  have hpair : (Transitions.encode Transitions.ClauseAtom.noAdjustment,
      Transitions.encode Transitions.ClauseAtom.reductionClaim) ∈
      Transitions.conflictAAF.attacks :=
    Transitions.attack_no_adjustment_to_reduction
  rw [heq] at hpair
  have hnil : instanceM.aaf.attacks = (∅ : Finset (Arg × Arg)) :=
    UnifiedInstance.aafM_attacks_eq_empty
  rw [hnil] at hpair
  exact notMemEmptyFinset _ hpair

/-! ## 七、两跳闭合（2026-10-03 G6 轮：`polM` 支持位改由 Horn 侧判定算出）-/

/-- 中文说明（本实例唯一可**从 𝔐 读出**的命名映射）：`UnifiedModel` 的字段表里只有
    `disputed : Arg` 这一个 `Arg` 形式的载体栏，没有"原子 → 论点"的映射栏，
    故本件能写出的、最贴近 𝔐 自身数据的读法就是把两个 L1 原子都命名为 `instanceM.disputed`。 -/
def chainNamingM : Fin 2 → Arg := fun _ => instanceM.disputed

/-- 中文说明（支持位的新形态）：`polM.admissibleSupport` 现在**就是** Horn 闭包侧那台
    Bool 判定（`Transitions.admissibleFromHorn normsM (fun _ => disputedM)`），
    不再是常真函数。法律读法：可采纳性回到"该论点是否由已证立的规范闭包产生"，
    与 §5.5 链的第 2→3 跳同源。 -/
theorem chain_pol_support_is_horn_derived :
    instanceM.pol.admissibleSupport =
      Transitions.admissibleFromHorn instanceM.norms chainNamingM := rfl

/-- 中文证明（两点的具象读数，机器可核）：
    `claimReduction`（争议论点＝闭包命名像的唯一元素）支持位为真；
    `claimNoAdjustment` 不在命名像里（`claimReduction_ne_noAdjustment`），支持位为假。
    这正是第 90 条第 2 款"证据不足以证明其事实主张 ⇒ 承担不利后果"在采纳面上的入口：
    支持位为假的论点不再被 `adoptedStep` 采纳。 -/
theorem chain_pol_support_on_two_labels :
    instanceM.pol.admissibleSupport UnifiedInstance.claimReduction = true ∧
      instanceM.pol.admissibleSupport UnifiedInstance.claimNoAdjustment = false := by
  constructor
  · show Transitions.admissibleFromHorn instanceM.norms chainNamingM
        UnifiedInstance.claimReduction = true
    have hmem : UnifiedInstance.claimReduction ∈
        Transitions.namedClosure instanceM.norms chainNamingM :=
      Finset.mem_image.mpr ⟨1, UnifiedInstance.one_in_closureM, rfl⟩
    exact decide_eq_true hmem
  · have hnotmem : ¬ UnifiedInstance.claimNoAdjustment ∈
        Transitions.namedClosure instanceM.norms chainNamingM := by
      intro hmem
      rcases Finset.mem_image.mp hmem with ⟨x, _, hnx⟩
      -- `chainNamingM x` 与 `claimReduction` 可定义相等（常函数映射到争议论点）。
      exact absurd hnx (fun he => UnifiedInstance.claimReduction_ne_noAdjustment he)
    show Transitions.admissibleFromHorn instanceM.norms chainNamingM
        UnifiedInstance.claimNoAdjustment = false
    exact decide_eq_false hnotmem

/-- 义务·**已闭合**（**第 2 跳 → 第 3 跳**，2026-10-03 G6 轮）：
    本实例的支持位现在**就是** Horn 闭包侧那台判定机器——
    `polM.admissibleSupport := Transitions.admissibleFromHorn normsM (fun _ => disputedM)`
    （`Seams/UnifiedInstance.lean`，`disputedM` 已提前定义），
    而本式右面的 `instanceM.norms`/`chainNamingM` 与左面是同一批对象的投影，
    故等式由 `rfl`（定义级）成立。 -/
def chain_naming_hop_closes : Prop :=
  instanceM.pol.admissibleSupport = Transitions.admissibleFromHorn instanceM.norms chainNamingM

/-- 中文证明：定义级等式（两侧都归结到 `admissibleFromHorn normsM (fun _ => disputedM)`）。 -/
theorem chain_naming_hop_closes_witness : chain_naming_hop_closes := rfl

/-- 义务·**已闭合**（**第 1 跳 → 第 3 跳**，2026-10-03 G6 轮）。
    第 90 条第 2 款："在作出判决前，当事人未能提供证据或者证据不足以证明其事实主张的，
    由负有举证证明责任的当事人承担不利的后果。"[一手已核]
    该不利后果在终端策略里的形式是"可采纳支持为假 ⇒ 该论点不被采纳"
    （`AdjudicationBridge.adoptedStep:165` 的第二个合取项 `pol.admissibleSupport a`）。
    本式要的"论点集里存在一个支持位为假的论点"现在由 `claimNoAdjustment` 交出：
    它不在 Horn 闭包的命名像里（像只含 `claimReduction`），支持位为假。 -/
def chain_art90_gate_has_input : Prop :=
  ∃ a : Arg, a ∈ instanceM.aaf.args ∧ instanceM.pol.admissibleSupport a = false

/-- 中文证明：见证即 `claimNoAdjustment`——在论点集里（字面 `Finset` 的第二元素），
    且支持位为假（`chain_pol_support_on_two_labels` 的右支）。 -/
theorem chain_art90_gate_has_input_witness : chain_art90_gate_has_input := by
  refine ⟨UnifiedInstance.claimNoAdjustment, ?_, chain_pol_support_on_two_labels.2⟩
  show UnifiedInstance.claimNoAdjustment ∈
      ({UnifiedInstance.claimReduction, UnifiedInstance.claimNoAdjustment} : Finset Arg)
  exact Finset.mem_insert_of_mem (Finset.mem_singleton_iff.mpr rfl)

/-! ## 八、链谓词与封顶陈述 -/

/-- 中文说明（**条文链谓词** `StatuteChainOn`）：一个载体 `M` 把这条链说出来，
    当且仅当下列六支同时成立。每一支都是本件已证定理的陈述形；写成 `Prop` 是为了
    让"链"本身可点名引用、可被下一版逐支加强（缺哪一支就少哪一支，不含糊）。
    第 6 支是**主体检查**：它把"缝件侧与实例侧同标签、不同攻击结构"写进链里，
    使任何"链已贯通"的读法都必须同时承认那一支里的否定。 -/
def StatuteChainOn (M : UnifiedModel (Fin 3) (Fin 1)) : Prop :=
  (BurdenStatutes.art91IsClauseOne chainNormClass = false ∧
      BurdenStatutes.art91BurdenOf chainNormClass chainBurdenedParty = chainBurdenedParty ∧
        chainAtomOfClass chainNormClass = M.atom) ∧
    (M.atom ∈ SourceNorms.closureAt M.norms ∧ SourceNorms.entailed M.norms M.atom) ∧
    (FinalDerivable M.pol M.disputed ∧ ¬ FinalDefeated M.pol M.disputed) ∧
    (BurdenStatutes.EvalDomainLawful M.evalDom ∧
      BurdenStatutes.StandardNamedAt
        BurdenStatutes.ProofStandardName.excludesReasonableDoubt109 M.evalDom ∧
        collapsesToKernel M.evalDom) ∧
    (Probability.reductionGate Probability.TwoSidedBurden.openGateData = true ∧
      Probability.Allow Probability.TwoSidedBurden.openGateData
        (Probability.choose Probability.TwoSidedBurden.openGateData)) ∧
    (Transitions.encode Transitions.ClauseAtom.reductionClaim = M.disputed ∧
      Transitions.conflictAAF.attacks ≠ M.aaf.attacks ∧
        ¬ FinalDerivable Transitions.conflictPolicy
          (Transitions.encode Transitions.ClauseAtom.reductionClaim))

/-- 中文证明（**链在 `instanceM` 上逐支成立**）：六支分别由
    `chain_art91_allocation_hop`＋`chain_atom_is_the_clause_two_slot`（第 1 跳）、
    `chain_L1_closure_hop`（第 2 跳）、`chain_L2_hop`（第 3 跳）、
    `chain_tier_hop`＋`chain_tier_attaches_109`＋`chain_collapse_from_the_109_tier`（第 4 跳）、
    `chain_amount_hop`＋`chain_amount_declared_choice_admitted`（第 5 跳）、
    `chain_seam_label_eq`＋`chain_subject_divergence`（主体检查）交出。
    本件不重证上述任何一条。 -/
theorem statuteChain_on_instanceM : StatuteChainOn instanceM :=
  ⟨⟨chain_art91_allocation_hop.1, chain_art91_allocation_hop.2.1,
      chain_atom_is_the_clause_two_slot⟩,
    ⟨UnifiedInstance.one_in_closureM, UnifiedInstance.atomM_entailed⟩,
    ⟨chain_L2_hop.1, chain_L2_hop.2⟩,
    ⟨chain_tier_hop.1, chain_tier_attaches_109, chain_collapse_from_the_109_tier⟩,
    ⟨chain_amount_hop.1, chain_amount_declared_choice_admitted⟩,
    ⟨chain_seam_label_eq, chain_subject_divergence.2.1,
      chain_subject_divergence.2.2.2⟩⟩

/-- **本件的封顶陈述（G6 的判定对象，2026-10-03 G6 轮闭合）**：存在
    `UnifiedModel (Fin 3) (Fin 1)` 的一个闭合项，它就是 `Seams/UnifiedInstance.lean` 的
    `instanceM`；在它上面第 1 跳（举证责任分配 → 待判原子）、第 2 跳（Horn 闭包 ↔ 语义后承）、
    **第 2→3 跳（命名映射：支持位＝Horn 侧判定，`chain_naming_hop_closes_witness`）**、
    **第 1→3 跳的举证入口（`chain_art90_gate_has_input_witness`：`claimNoAdjustment`
    支持位为假，第 90 条第 2 款的不利后果有了机器入口）**、
    第 3 跳（终端策略采纳且两值不塌）、第 4 跳（评价域依法＋109 档推出收缩性）、
    第 5 跳（数额面的闸门与准许关系）以及主体检查全部作为定理成立。
    ⇒ "同一条条文链从举证责任条款走到数额"这句话由本式逐支交出。
    诚实边界：两跳的闭合靠的是把 `polM.admissibleSupport` 定义为 Horn 侧判定
    （定义级 `rfl`），闭包侧的成员判定走具名见证而非把 `closureAt` 整体 `decide`
    （§5.3 卡点仍在，见 §未覆盖第 2 项的全称版本）。 -/
theorem statuteChain_reaches_the_one_closed_instance :
    ∃ (M : UnifiedModel (Fin 3) (Fin 1)),
      M = instanceM ∧ StatuteChainOn M ∧ chain_naming_hop_closes ∧
        chain_art90_gate_has_input :=
  ⟨instanceM, rfl, statuteChain_on_instanceM, chain_naming_hop_closes_witness,
    chain_art90_gate_has_input_witness⟩

/-! ## §未覆盖片段（逐条：本链**没有**走到哪里，以及为什么）

1. **第 1 跳 → 第 3 跳（举证缺口进入采纳面）**：**2026-10-03 G6 轮已闭合**——
   `polM.admissibleSupport` 改由 Horn 侧判定算出后，`chain_art90_gate_has_input_witness`
   交出 `claimNoAdjustment` 这个支持位为假的论点，第 90 条第 2 款的不利后果有了机器入口。
   仍未做的是**逐案材料化**：`UnifiedModel` 仍没有 `ProductionStatus`／`BurdenAllocation`
   形式的栏，缺口位现在是"Horn 闭包是否产生该论点"，不是"本案证据清单是否不足"。
2. **第 2 跳 → 第 3 跳（命名映射）**：**2026-10-03 G6 轮已闭合（定义级）**——
   `polM.admissibleSupport := Transitions.admissibleFromHorn normsM (fun _ => disputedM)`，
   `chain_naming_hop_closes_witness` 由 `rfl` 成立。**未证**的是反向全称版本
   `∀ n : Fin 2 → Arg, instanceM.pol.admissibleSupport =
   Transitions.admissibleFromHorn instanceM.norms n → n = chainNamingM`
   （以及"除 `chainNamingM` 外都不成立"）——它需要把
   `SourceNorms.closureAt instanceM.norms` 精确算成 `{0, 1}`，正是
   `Seams/UnifiedInstance.lean` 头注 §5.3 登记的 `decide` 卡点
   （`FiniteMonotoneSystem.iter` ＋ `HornSystem.TH` 的 `filter/image`）。
3. **第 4 跳的档位差与 𝔐 之间没有栏位**：`standard_tiers_cannot_be_merged` 的载体是
   `BurdenStatutes.CredProfile`，`art108Finding` 的载体是 `Bool × Bool`，
   而 `UnifiedModel` 没有 `CredProfile`／`FactFinding` 形制的栏，
   也没有第 109 条那五类（欺诈、胁迫、恶意串通、口头遗嘱、赠与）的事实类别栏
   （`ExceptionalMatter` 与 𝔐 之间无映射）。本件在 `Fin 3` 的幂集上证了两档作为谓词可区分
   （`chain_tier_gates_are_distinct_on_the_carrier`），但**没有**认定"本案事实属哪一类"——
   那一问需要法律判断，本件不虚构。
4. **第 5 跳的载体与本实例的数额栏不同型**：`instanceM.performAmount : Nat`（L5 履行事件）
   vs `Probability.Amount := ℤ`（违约金面）。`chain_amount_faces_meet_only_numerically`
   只登记两处都写 100 这个**数值巧合**；`Nat → ℤ` 在本件是裸的 `Nat.cast`，
   不是任何声明的载体等同（对齐 `Seams/Unified.lean` 错位登记 #3、#7）。
   "约定额／损失基础"两栏在 `UnifiedModel` 里根本不存在，所以 `overThirtyThreshold`
   那一支（第 65 条第 2 款的 30% 门槛）在本链上只对 `Probability` 自己的夹具成立。
5. **区间面未接**：`chainIntervalCarrier := JurisLean.FullMath.Numeric.Iv`（`ℚ` 上）
   与 `Probability.Amount := ℤ` 之间本件零定理；该件的 `seen_span_not_global_bound`
   （`FullMath/Numeric/Intervals.lean:146`）说的是"见过的候选范围不是全局界"，
   本件不复用、不外推。
6. **另两个"证明标准"载体未接**：`JurisLean.FullMath.Burden.Standard`
   （`FullMath/Burden/Standards.lean:34`，带数值 `threshold : ℚ` 与 `gate:48`）与
   `JurisLean.ULM.ProofStandard`（`ULM12Procedure.lean:7`，只有 `standardId/domain/version`）
   与本件用的 `BurdenStatutes.ProofStandardName` 之间没有任何等式或翻译；
   三者同名而异义，本件只用第一个。不得声称"证明标准已被统一"。
7. **第 108 条第 3 款"法律对于待证事实所应达到的证明标准另有规定的，从其规定"**：
   仍是出口条款，本件不做成第三个构造子，也不认定任何"另有规定"。
8. **第 64 条第 3 款的"驳回"表达**：法释〔2023〕13号第 64 条第 3 款实定"仅以合同约定
   不得调整为由主张不予调整的，人民法院不予支持"。承 `Seams/Transitions.lean` 头注 §三
   的登记，缝件只建成"互斥且无明文采纳 ⇒ 未决"，本件**没有**把它升级成"驳回"，
   因此本链在缝件一侧的第 3 跳仍是 `¬ FinalDerivable` 而不是 `FinalDefeated`。
9. **第 92 条自认与第 93 条免证七项**：本件一处都没用到（第 93 条第 1 款第 (五) 项
   与 `presumptionRuleFires` 的接点留在 `BurdenStatutes.art93_overturn_entry_matches_seam:388`），
   所以本链**不含**免证事实、自认与生效裁判确认事实进入闭包的那条支路。
10. **`collapsesToKernel` 的一般性**：本件在第 4 跳得到它**在本实例上**由 109 档推出；
    `BurdenStatutes.lawful_does_not_imply_collapse:980` 已证三条候选公理推不出一般收缩性，
    本件不改变那一结论，也不把本实例的收缩性外推到任何真实评价域。
11. **编译状态**：本件已在**本地** `lake build` 绿过一次（临时预检，`LAKE_EXIT=0`），
    但**从未**在 CI 编译（`CI_NOT_RUN`，fail-closed）。
    全部判定以绑定 subject SHA 的 CI 轮次为准；本件也未入根 `JurisLean.lean`，
    因为新模块须在 CI 的模块矩阵先过一遍才准入根（AGENTS.md §Lean Workflow）。
12. **请求地位面（L2 claim 面）未成为一跳**：`Seams/ClaimBasis.lean` 只随
    `Seams/UnifiedInstance.lean:10` 间接进入本件的 import 闭包，本件**没有**引用
    `ClaimBasis.Status`／`ClaimBasis.Stage`／`ClaimBasis.fires:95` 中的任何一个，
    因此"酌减请求的法律地位（存续／不得强制实现／中止）"这一问在本链上仍是空位：
    `UnifiedModel` 既没有 `ClaimBasis.Status` 形制的栏，第 3 跳的 `FinalDerivable`
    与该地位面之间也没有已证的字典（`AdjudicationBridge` 头注把"不在 `FinalDerivable`
    与 `KernelV3.Judgment` 之间建双向字典"列为硬红线，同一限制对本面成立）。
    本件只解决了"两者能否同批编译"，没有解决"两者是否说同一件事"。
-/

/-! ## 九、数额跨载体桥（G4：`Nat` 履行面 ↔ `ℤ` 违约金面，此前只有裸 cast、无声明） -/

/-- 数额桥（G4"消除一名多类型无桥"·数额那一格，并补本件 §未覆盖第 4 项"裸 `Nat.cast` 无声明载体"）：
    L5 履行面的债务额是 `Nat`（`instanceM.performAmount`、`InstitutionalEffects.Debt.amount`），
    违约金面是 `Probability.Amount := ℤ`。此前两者之间只有一个**裸 `Nat.cast`**，没有任何被**声明**、
    且证了性质的载体换算。这里把该换算具名，并交出两条它的应有事实。
    诚实边界：本桥只做**单向具名换算 + 序的反射**，不声称两量纲语义等同（一个欠额、一个违约金），
    也不声称类型等同；下面的 `amountBridge_subtraction_disagrees` 恰恰证明两面在减法下**不等价**。 -/
def amountBridge : Nat → Probability.Amount := fun n => (n : ℤ)

/-- 具名桥**反射序**：搬到违约金面可比大小，且与 `Nat` 上的序完全一致（`abbrev Amount := ℤ` 可 unfold，走 `Nat.cast_le`）。 -/
theorem amountBridge_order_iff (a b : Nat) :
    amountBridge a ≤ amountBridge b ↔ a ≤ b := by
  unfold amountBridge
  exact Nat.cast_le

/-- 桥**不是同构的证据**：`Nat` 的减是截断的、`ℤ` 的不是。`3 - 5 = 0`（`Nat`）搬到对面还是 `0`，
    而两侧各自搬过去再减是 `-2`。这一格差异正是"两面的数额不能当同一个数"的机器见证，
    也是本桥只做单向换算、不冒充等价的理由。 -/
theorem amountBridge_subtraction_disagrees :
    amountBridge (3 - 5 : Nat) ≠ amountBridge 3 - amountBridge 5 := by
  decide

end JurisLean.Seams.StatuteChain
