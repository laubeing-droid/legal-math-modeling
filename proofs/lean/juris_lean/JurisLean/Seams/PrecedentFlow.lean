import Mathlib.Data.Finset.Basic
import Mathlib.Tactic
import JurisLean.TemporalApplicability
import JurisLean.Genealogy.Part1
import JurisLean.Genealogy.Part4
import JurisLean.FiniteMonotoneIteration

/-!
S7（L4 判例流 → L1/L6 规范层回流缝合件）—— 前例驱动的 `V → V'` 更新、更新的非恒等性、
反单调回流不收敛、P-066 续造权限的四元组类型层拒绝。

## §法律语义（人话）

"指导性案例被参照之后，法源本身变了没有"是判例流能否回流到规范层的核心问题。法律实务里回流
确实发生：某版本裁判依据被后续前例认定与参照口径不一致，于是它从"可适用"变成"已被取代"，同时
前例确立的新版本进入法源清单。这件事在数学上就是一个**环境更新** `V → V'`。

仓内目前**写不出**这件事，原因不是缺定理，而是缺载体：

1. 选择签名 `A(J,V,q,H,t)` 的 `V` 位是 `ApplicableNormQuery.normEnv : String`
   （`LegalModelV2.lean:171`），而该结构唯一的定理 `applicable_norm_history_participates`
   （`LegalModelV2.lean:242`）只让 `H` 参与同一性，`V` 是被全称量词绑住且从不改写的字符串。
   于是"V 字段不变"这句话**没有信息量**：任何更新都无法在该签名上被表达。
2. `KernelV3.lean:229` 的 `applicableNorm` 只读 `history.factTime`，`eventTimes : List Nat`
   从不被读取；`JurisLean/TemporalApplicability.lean`（109 行）里有完整版本机制
   （`VersionStatus / SourceVersionRecord / effectiveAt / versionApplicableAt / SupersessionEdge`
   及六条失效定理），却**没有任何产生新 `SourceVersionRecord` 的函数**。

所以本件的动作是：**新建载体，不动冻结内核**。更新函数定义在 `SourceVersionRecord` 列表
（本件的 `VersionEnv`）上，触发条件直接取 P-019 已有的 `bindingEffect`
（`Genealogy/Part1.lean:154`：`.shallRefer` 且未被区分 ⇒ `.shouldFollow`）：`mayReference`
或已被区分时更新恒等——沉默的前例不产生回流。本件**不**声称冻结内核被扩展，也**不**声称
`applicableNorm` 现在读 `eventTimes`。

第二条线是**回流的收敛性**。回流是反单调的：已参照则撤回旧结论，未参照则采纳，两点状态空间上
就是 `z' = 1 - z`。本件把它写成显式迭代并证明相邻两步永不相等（轨道 2-周期，不是最终固定）。
仓内 `FiniteMonotoneIteration.lean` 只有单调通道（`step_monotone :15` ⇒ `iter_mono :39` ⇒
`fixed_at_card :103`），反单调步在类型上就进不去。这个"能表达/不能表达"的对照是法律要点：
**回流不保证收敛，而既有迭代机器也无法保证它收敛**——不是它没证到，是它写不出。

第三条线是 P-066 **续造权限**：检测到漏洞不等于谁都能填。权限按（主体, 程序, 缺口, 范围）四件事
分别问；四件吻合才持有 `Competence` 见证，而进入规范层的构造子**强制**要求该见证，于是
"未经授权的产出"在类型层不是规范。

## §数学对象

- `VersionEnv`：`versions : List SourceVersionRecord`（复用 `TemporalApplicability.lean:21`，
  记录、状态、区间、`SupersessionEdge` 一律不重定义）。
- `Actor / Procedure / Scope`（本件自写枚举，**代拟稿**）× `P066.GapSignal`
  （`Genealogy/Part4.lean:265`，缺口种类**复用台账**）→
  `Competence : Actor → Procedure → GapSignal → Scope → Type`、`authorized`、`NormLayerEntry`。
- `BackflowProduction`：四元组声明 + 规范编号。`PrecedentDecision`：产出 +
  `binding : P019.PrecedentBinding` + `distinguishingReason : Bool` + `newSnapshot / newRecord /
  supersedes`。绑定级别与效力**取自 P-019**（`Part1.lean:143/148/154`），本件只消费不重定义。
- `AuthorizedDecision`：前例决策 + 与产出四元组索引完全吻合的见证；`V → V'` 的**唯一入口**。
- `updateFires / hitsSupersession / supersedeRecord / precedentUpdate`；
  `EnvWf`（环境假设的显式命名结构）；`isTouchedBy`（更新真正改写某记录的条件）。
- `effectiveAtBool / applicableAtBool / applicableVersions / applicableCount /
  applicableEffectiveFroms`：时点查询；`applicableAtBool_true_iff` 把计算读回声明侧
  `versionApplicableAt`。
- `backflowStep / backflowIter`（`Bool` 上 `z' = 1 - z`）、`backflowSetStep`（同形于
  `FiniteMonotoneSystem.step` 的反单调集合步）、`monotoneAccStep / monotoneIter`（单调对照）。

## §证与不证

**证（A）** `precedent_update_preserves_norm_structure`，三项合取：
①更新后环境每条记录 `intervalValid` 仍成立（`intervalValid_supersedeRecord`：更新只改 `status`
字段，区间投影不动）；②每条被真正改写的记录所生成的 `SupersessionEdge` 满足仓内
`supersessionWellFormed`（`:51`，即非自指；依据 `EnvWf.fresh`）；
③原本 `retracted`/`superseded` 的记录在更新后仍有同快照记录且仍不可适用——不可适用一侧
**直接复用**仓内 `retracted_source_invalidates`（`:85`）与 `superseded_source_invalidates`（`:92`），
本件不重证"非 active 即不可适用"。另附 `update_touched_record_invalid`（被改写者确实失效）、
`update_introduces_applicable_record`（新版本在自身区间内即适用）、
`update_is_noop_when_silent`（未触发时整个环境一字不改）。

**证（B）** `update_is_not_noop` 与 `update_changes_applicable_roster`：`envOld` 与
`precedentUpdate demoAuthorized envOld` 在同一时点 60 的可适用版本表**不同**
（生效起点表 `[0] ≠ [50]`，从而版本表也不同）；`update_changes_applicable_count` 给出时点 30 上
可适用数 `1 ≠ 0`（旧版本被取代、新版本尚未生效）。`update_silent_when_may_reference` 说明
差异由 P-019 的绑定级别驱动。**不证**：不在 `ApplicableNormQuery` / `KernelV3.applicableNorm`
上证任何事——冻结签名表达不了 V 的变化，本件的构造落在**新载体**上，且 `normEnv : String`
与本件 `VersionEnv` 之间没有桥（见 §未覆盖片段）。

**证（C）** `feedback_need_not_converge`：`∃ z, ∀ n, backflowIter (n+1) z ≠ backflowIter n z`
（事实上 `∀ z n` 都成立，见 `backflow_no_fixed_step`），配 `backflowIter_period_two`（2-周期）与
`backflowStep_has_no_fixed_point`（无不动点）。**另一种读法是错的**：因为 `1 - x` 在两点空间上是
对合，轨道会回到起点，所以 `∃ n, backflowIter n z = z` 为真——但"回到起点"不是收敛，
收敛要求**最终固定**，被 `backflow_no_fixed_step` 逐段否定。
对照面三条：`monotoneIter_one_step_stable`（同点集上单调步一步固定，正是仓内 `iter_stable`（`:46`）
假设成立的形态）、`backflowSetStep_not_mono`（该集合形单步不保序）、
`backflowSetStep_not_a_system`（不存在以它为 `step` 字段的 `FiniteMonotoneSystem Bool`，
被违反的正是 `FiniteMonotoneIteration.lean:11` 结构的 `step_monotone` 字段 `:15`）。
**边界纪律**：按 `docs/master-plan/06_六类边界绑定表.md` 的要求，本条登记为**局部反例**，
不充当六类界定定理中的任何一类。

**证（D）** `unauthorized_output_is_not_a_norm`：`NormLayerEntry` 只有一个构造子 `.backflow`，
其索引要求与产出四元组完全吻合的 `Competence` 见证，故 `norm_layer_entry_authorized`
（∀ 条目所申报产出都被授权）与拒绝形式同时成立。这是**类型层**事实（构造子穷尽 + `cases`），
不是运行时检查。配套 `competence_shape`（见证必为最高法/指导性案例程序/全国）、
`lower_court_draft_unauthorized` + `lower_court_draft_is_not_a_norm_layer_entry`（拒绝确实咬得住）、
`backflow_entry_is_not_vacuous`（授权侧非空，拒绝不是空洞）、
`unauthorized_production_has_no_update_input`（耦合 07 卷第②条：未授权产出连更新入口都进不去）。

**证（E）** `observation_gate_does_not_determine_effectivity`（观察闸门与生效区间各自独立，
复用 `future_information_blocked` `:79`）、`late_publication_still_effective_in_interval`
（**本载体的缺口**：`versionApplicableAt` 从不读 `publicationDay`，故"公布在 t 之后"与
"在 t 可适用"可同时成立——把缺口钉成定理，不是修复）、
`update_does_not_reach_before_effective_from`（回流不溯及，复用 `:73`）。
三条都只用 `Int` 算术。

**不证（总）**：不证回流的任何正向收敛/固定点存在性；不证结构保持对非列表形环境语义成立；
不把 `bindingEffect` 三值读成对真实指导性案例效力的认定；不重述 P-014 位阶全序
（`Part1.lean:39-41` 已声明 `source_grade_total` 不蕴含全序）；不主张本件统一了四种时间表示。

## §未覆盖片段

- **`V` 的本体未接**：`normEnv : String` 仍是字符串，本件用 `VersionEnv` 平行承载；
  `String → List SourceVersionRecord` 的解析语义未定义，两者之间**没有桥**，
  因此"更新后的 `V'` 等于某个字符串环境"无法陈述。
- **`KernelV3.applicableNorm` 仍不读 `eventTimes`**（`KernelV3.lean:229`），本件没有也不打算
  把它接到 `VersionEnv`；"选择签名真的读版本环境"仍是独立目标。
- **授权的规范来源未认定**：`Competence` 的构造子集合是代拟稿，未把任何真实法条编号写成公理，
  "谁授权"未被认定。
- **四种时间表示未统一**：`P015.NormProvision.enactedDay : Nat`、`LegalModelV2.Event.atDay : Int`、
  `KernelV3.EventHistory.factTime : Nat`、`TimePoint` 仍并存且互不 convertible；本件只在 `Int`
  上陈述时态，§证与不证（E）不修复这一点。
- **链式取代**（`V → V' → V''`）的结合性/幂等性未证；`supersedes` 是名单而非闭包；
  `corrected` 记录的更正语义未建模（本件只保证它不被覆盖）；回溯适用与溯及力规则未建模。

## §档位

无 `sorry`、无 `admit`、无 `native_decide`、无新 `axiom`、无 `: True :=` 逃避式定理；
`decide` 只用于 `Bool` / `Int` / 枚举与短字符串字面量的闭式归约。
本地编译不等于 Lean PASS，全部结论待 CI 模块矩阵认定。

- `precedent_update_preserves_norm_structure` [已证，认定待 CI]（结构保持，非"回流正确"）
- `update_is_not_noop` / `update_changes_applicable_roster` / `update_changes_applicable_count`
  [已证，具体见证]
- `feedback_need_not_converge` 与 `backflowSetStep_not_a_system` [已证，局部反例；
  按边界表纪律**不**充当六类界定定理]
- `monotoneIter_one_step_stable` [已证，形态对照]
- `unauthorized_output_is_not_a_norm` [已证，类型层构造子拒绝]
- `Competence` 构造子集合与其法律对应 [代拟稿]
- 真实前例绑定级别的认定、`normEnv : String` 与 `VersionEnv` 的桥、链式取代、溯及力 [未覆盖]
-/

namespace JurisLean.Seams.PrecedentFlow

open JurisLean.Genealogy.Part1 (P019)
open JurisLean.Genealogy.Part4 (P066)

section AuthorizationCarrier

/-- 中文说明：**[代拟稿]** 续造主体。枚举是本件的构造，不代表任何机关认定。 -/
inductive Actor where
  | supremeCourt
  | highCourt
  | intermediateCourt
deriving DecidableEq, Repr

/-- 中文说明：**[代拟稿]** 续造所经程序。 -/
inductive Procedure where
  | guidingCaseProcedure
  | ordinaryAdjudication
deriving DecidableEq, Repr

/-- 中文说明：**[代拟稿]** 效力范围。 -/
inductive Scope where
  | nationwide
  | withinJurisdiction
  | withinSingleCase
deriving DecidableEq, Repr

/-- 中文说明：**四元授权** `Competence actor procedure gap scope`。**[代拟稿]**，诚实点照原话记下：
    Dong & Roy, *Dynamic Logic of Legal Competences*, JLLI 30(4):701–724, 2021,
    DOI `10.1007/s10849-021-09340-z` 把 power 定义在**有向的规范位置** `⟨j,k,ψ/φ⟩` 之上，
    其文本中 procedure / gap / scope 三词的出现次数为 0 / 0 / 2——该文**没有**四元位置的
    competence 概念。以下四元组与构造子集合都是本项目的代拟稿，不是对该文的忠实读法，
    也不认定任何真实授权规范；可向该文主张的只有两点：竞合（Kompetenz）改变规范的定性，
    以及"能力 Können ≠ 许可 Dürfen"。构造子只有一条（最高法 × 指导性案例程序 × 全国范围），
    其余四元组因此是空类型——这正是下面类型层拒绝成立的原因。
    缺口种类复用台账 `P066.GapSignal`（`Genealogy/Part4.lean:265`），本件不重定义缺口。 -/
inductive Competence : Actor → Procedure → P066.GapSignal → Scope → Type where
  | guidingCaseFill (g : P066.GapSignal) :
      Competence .supremeCourt .guidingCaseProcedure g .nationwide

/-- 中文说明：**续造产出的四元组声明**加规范编号（(D) 的输入侧，也是 (A) 决策的载荷）。 -/
structure BackflowProduction where
  actor : Actor
  procedure : Procedure
  gap : P066.GapSignal
  scope : Scope
  content : LegalId .norm

/-- 中文说明：产出是否被授权——存在与产出四元组**完全吻合**的见证（类型层陈述，非运行时检查）。 -/
def authorized (pr : BackflowProduction) : Prop :=
  Nonempty (Competence pr.actor pr.procedure pr.gap pr.scope)

/-- 中文说明：**规范层条目**：唯一构造子 `.backflow` 的索引要求携带与四元组吻合的 `Competence`
    见证。类型层不存在"无见证进入规范层"的构造子。 -/
inductive NormLayerEntry where
  | backflow (pr : BackflowProduction)
      (c : Competence pr.actor pr.procedure pr.gap pr.scope) : NormLayerEntry

/-- 中文说明：读出条目所申报的产出四元组。 -/
def NormLayerEntry.declared : NormLayerEntry → BackflowProduction
  | .backflow pr _ => pr

end AuthorizationCarrier

section Carrier

/-- 中文说明：**回流环境**（本件新载体）：以 `SourceVersionRecord` 列表承载法源版本集。
    它与冻结载体 `ApplicableNormQuery.normEnv : String`（`LegalModelV2.lean:171`）无定义关系。 -/
structure VersionEnv where
  versions : List SourceVersionRecord

/-- 中文说明：**前例决策**（提案形态）：绑定级别与区分理由取 P-019 的载体，
    是否触发回流由 `updateFires` 读 `bindingEffect` 决定。 -/
structure PrecedentDecision where
  production : BackflowProduction
  binding : P019.PrecedentBinding
  distinguishingReason : Bool
  newSnapshot : LegalId .snapshot
  newRecord : SourceVersionRecord
  supersedes : List (LegalId .snapshot)

/-- 中文说明：**授权决策**：前例决策 + 与产出四元组完全吻合的 `Competence` 见证。
    本件的 `V → V'` 只以此为入口，故未授权决策在类型层没有更新通道可读
    （对应 `docs/master-plan/07_四问法律代拟卷_20261001.md` 对 S7 的第②条要求）。 -/
structure AuthorizedDecision where
  decision : PrecedentDecision
  witness : Competence decision.production.actor decision.production.procedure
              decision.production.gap decision.production.scope

/-- 中文说明：**回流是否触发**：只有 `.shouldFollow`（"应当参照"且未被区分）才触发；
    `mayReference` 或已被区分时为 `false`。判定完全由 P-019 的 `bindingEffect`
    （`Genealogy/Part1.lean:154`）给出，本件不自立效力标准。 -/
def updateFires (d : PrecedentDecision) : Bool :=
  match P019.bindingEffect d.binding d.distinguishingReason with
  | .shouldFollow => true
  | _ => false

/-- 中文说明：快照是否在被取代名单里（按 payload 比较，不引入新的序关系）。 -/
def snapBelongs (snap : LegalId .snapshot) : List (LegalId .snapshot) → Bool
  | [] => false
  | s :: rest => (s.payload == snap.payload) || snapBelongs snap rest

/-- 中文说明：某记录是否命中本前例的取代名单。 -/
def hitsSupersession (d : PrecedentDecision) (v : SourceVersionRecord) : Bool :=
  snapBelongs v.snapshot d.supersedes

/-- 中文说明：**单条记录的取代动作**：命中且原本 in force（`status = .active`）才降为
    `.superseded`；`retracted / corrected / superseded` 原样返回——失效状态既不被回流覆盖，
    也不被"复活"。只改 `status` 字段，其余四个字段不动。 -/
def supersedeRecord (d : PrecedentDecision) (v : SourceVersionRecord) : SourceVersionRecord :=
  if hitsSupersession d v = true then
    if v.status = VersionStatus.active then { v with status := VersionStatus.superseded } else v
  else v

/-- 中文说明：**环境更新 `V → V'`**：触发时把被取代记录降级并登记前例确立的新版本；未触发时
    恒等。入口是 `AuthorizedDecision`。注意它没有时点参数：何时生效只由记录自身的区间承载。 -/
def precedentUpdate (ad : AuthorizedDecision) (E : VersionEnv) : VersionEnv :=
  if updateFires ad.decision = true then
    { versions := ad.decision.newRecord :: E.versions.map (supersedeRecord ad.decision) }
  else E

/-- 中文说明：**环境假设的显式命名结构**（(A) 全部保留定理的唯一前提）。
  ① `intervals`：原环境每条记录区间良态；② `newRecordValid`：新版本记录区间良态；
  ③ `newRecordActive`：新版本登记时为 `active`（是否生效仍由区间判定）；
  ④ `fresh`：新快照不在原环境中（不重复登记，并因此保证 supersession 边非自指）；
  ⑤ `recordMatchesSnapshot`：`newRecord.snapshot = newSnapshot`。 -/
structure EnvWf (E : VersionEnv) (ad : AuthorizedDecision) where
  intervals : ∀ v ∈ E.versions, SourceVersionRecord.intervalValid v
  newRecordValid : ad.decision.newRecord.intervalValid
  newRecordActive : ad.decision.newRecord.status = VersionStatus.active
  fresh : ∀ v ∈ E.versions, v.snapshot ≠ ad.decision.newSnapshot
  recordMatchesSnapshot : ad.decision.newRecord.snapshot = ad.decision.newSnapshot

/-- 中文说明：更新**确实改写**某条记录的条件：记录在环境中、命中名单、且原本 active。 -/
def isTouchedBy (ad : AuthorizedDecision) (E : VersionEnv) (v : SourceVersionRecord) : Prop :=
  v ∈ E.versions ∧ hitsSupersession ad.decision v = true ∧ v.status = VersionStatus.active

end Carrier

section StructuralPreservation

/-- 中文说明：更新后的版本表（触发分支）。 -/
theorem update_versions_fires (ad : AuthorizedDecision) (E : VersionEnv)
    (hh : updateFires ad.decision = true) :
    (precedentUpdate ad E).versions =
      ad.decision.newRecord :: E.versions.map (supersedeRecord ad.decision) := by
  unfold precedentUpdate
  rw [if_pos hh]

/-- 中文说明：未触发时更新对整个环境是恒等（沉默前例，`V' = V`）。 -/
theorem update_is_noop_when_silent (ad : AuthorizedDecision) (E : VersionEnv)
    (hh : updateFires ad.decision ≠ true) : precedentUpdate ad E = E := by
  unfold precedentUpdate
  rw [if_neg hh]

/-- 中文说明：未触发时版本表也不变（`update_is_noop_when_silent` 的投影形式）。 -/
theorem update_versions_silent (ad : AuthorizedDecision) (E : VersionEnv)
    (hh : updateFires ad.decision ≠ true) : (precedentUpdate ad E).versions = E.versions := by
  rw [update_is_noop_when_silent ad E hh]

/-- 中文说明：取代动作保持区间良态——只改 `status`，而 `intervalValid`
    （`TemporalApplicability.lean:55`）只看 `effectiveFrom / effectiveTo`。 -/
theorem intervalValid_supersedeRecord (d : PrecedentDecision) (v : SourceVersionRecord)
    (hv : SourceVersionRecord.intervalValid v) :
    SourceVersionRecord.intervalValid (supersedeRecord d v) := by
  unfold supersedeRecord
  split
  · split <;> assumption
  · assumption

/-- 中文说明：取代动作不改快照。 -/
theorem supersedeRecord_snapshot (d : PrecedentDecision) (v : SourceVersionRecord) :
    (supersedeRecord d v).snapshot = v.snapshot := by
  unfold supersedeRecord
  split
  · split <;> rfl
  · rfl

/-- 中文说明：未命中名单的记录不被改写。 -/
theorem supersedeRecord_keeps_unhit (d : PrecedentDecision) (v : SourceVersionRecord)
    (hh : hitsSupersession d v ≠ true) : supersedeRecord d v = v := by
  unfold supersedeRecord
  rw [if_neg hh]

/-- 中文说明：非 active 的记录不被改写。 -/
theorem supersedeRecord_keeps_nonActive (d : PrecedentDecision) (v : SourceVersionRecord)
    (ha : v.status ≠ VersionStatus.active) : supersedeRecord d v = v := by
  unfold supersedeRecord
  split
  · split
    · contradiction
    · rfl
  · rfl

/-- 中文说明：命中且原本 active 的记录被降为 `superseded`。 -/
theorem supersedeRecord_drops_hit_active (d : PrecedentDecision) (v : SourceVersionRecord)
    (hh : hitsSupersession d v = true) (ha : v.status = VersionStatus.active) :
    supersedeRecord d v = { v with status := VersionStatus.superseded } := by
  unfold supersedeRecord
  rw [if_pos hh, if_pos ha]

/-- 中文说明：取代动作的两分支穷尽形态：要么原样，要么降为 `superseded`。 -/
theorem supersedeRecord_status_dichotomy (d : PrecedentDecision) (v : SourceVersionRecord) :
    supersedeRecord d v = v ∨
      (supersedeRecord d v).status = VersionStatus.superseded := by
  by_cases hh : hitsSupersession d v = true
  · by_cases ha : v.status = VersionStatus.active
    · right
      rw [supersedeRecord_drops_hit_active d v hh ha]
    · left
      exact supersedeRecord_keeps_nonActive d v ha
  · left
    exact supersedeRecord_keeps_unhit d v hh

/-- 中文说明：**保持①（区间良态）**：更新后环境里每条记录都区间良态。新版本记录靠
    `EnvWf.newRecordValid`，被改写的旧记录靠 `intervalValid_supersedeRecord`。 -/
theorem update_preserves_intervalValid (E : VersionEnv) (ad : AuthorizedDecision)
    (hwf : EnvWf E ad) :
    ∀ v ∈ (precedentUpdate ad E).versions, SourceVersionRecord.intervalValid v := by
  by_cases hh : updateFires ad.decision = true
  · intro v hv
    rw [update_versions_fires ad E hh] at hv
    rcases List.mem_cons.mp hv with rfl | hv
    · exact hwf.newRecordValid
    · obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hv
      exact intervalValid_supersedeRecord ad.decision w (hwf.intervals w hw)
  · intro v hv
    rw [update_versions_silent ad E hh] at hv
    exact hwf.intervals v hv

/-- 中文说明：**保持②（边良态）**：凡被更新真正改写的记录，其所生成的 supersession 边
    `⟨旧快照, 新快照⟩` 满足仓内 `supersessionWellFormed`（`TemporalApplicability.lean:51`，
    即非自指）。依据是 `EnvWf.fresh`：旧快照在原环境中而新快照不在。 -/
theorem update_edges_wellFormed (E : VersionEnv) (ad : AuthorizedDecision)
    (hwf : EnvWf E ad) (v : SourceVersionRecord) (hv : isTouchedBy ad E v) :
    supersessionWellFormed
      { oldSnap := v.snapshot, newSnap := ad.decision.newSnapshot : SupersessionEdge } :=
  hwf.fresh v hv.1

/-- 中文说明：**保持③（失效仍失效）**：原环境中已 `retracted` 或 `superseded` 的记录，
    更新后仍有同快照记录且仍不可适用。不可适用一侧**直接复用**仓内
    `retracted_source_invalidates`（`TemporalApplicability.lean:85`）与
    `superseded_source_invalidates`（`:92`），本件不重证"非 active 即不可适用"。 -/
theorem update_preserves_invalidated_records (E : VersionEnv) (ad : AuthorizedDecision)
    (v : SourceVersionRecord) (t : Int) (hv : v ∈ E.versions)
    (h : v.status = VersionStatus.retracted ∨ v.status = VersionStatus.superseded) :
    ∃ w ∈ (precedentUpdate ad E).versions,
      w.snapshot = v.snapshot ∧ ¬ versionApplicableAt w t := by
  refine ⟨supersedeRecord ad.decision v, ?_, supersedeRecord_snapshot ad.decision v, ?_⟩
  · by_cases hh : updateFires ad.decision = true
    · rw [update_versions_fires ad E hh]
      exact List.mem_map.mpr ⟨v, hv, rfl⟩
    · rw [update_versions_silent ad E hh]
      exact hv
  · cases supersedeRecord_status_dichotomy ad.decision v with
    | inl heq =>
      rw [heq]
      cases h with
      | inl hr => exact retracted_source_invalidates v t hr
      | inr hs => exact superseded_source_invalidates v t hs
    | inr hst => exact superseded_source_invalidates _ t hst

/-- 中文说明：被改写记录在更新后确实**不可适用**，状态为 `superseded`
    （旧证书失去效力；失效判定仍复用仓内 `:92`）。 -/
theorem update_touched_record_invalid (E : VersionEnv) (ad : AuthorizedDecision)
    (v : SourceVersionRecord) (t : Int) (hfire : updateFires ad.decision = true)
    (hv : isTouchedBy ad E v) :
    ∃ w ∈ (precedentUpdate ad E).versions,
      w.snapshot = v.snapshot ∧ w.status = VersionStatus.superseded ∧
        ¬ versionApplicableAt w t := by
  have hmem : supersedeRecord ad.decision v ∈ (precedentUpdate ad E).versions := by
    rw [update_versions_fires ad E hfire]
    exact List.mem_map.mpr ⟨v, hv.1, rfl⟩
  have hstat : (supersedeRecord ad.decision v).status = VersionStatus.superseded := by
    rw [supersedeRecord_drops_hit_active ad.decision v hv.2.1 hv.2.2]
  have hsnap : (supersedeRecord ad.decision v).snapshot = v.snapshot := by
    rw [supersedeRecord_drops_hit_active ad.decision v hv.2.1 hv.2.2]
  exact ⟨supersedeRecord ad.decision v, hmem, hsnap, hstat,
    superseded_source_invalidates _ t hstat⟩

/-- 中文说明：新版本被登记后，凡时点落在其生效区间内即适用（两支分别来自查询假设与
    `EnvWf.newRecordActive`）。 -/
theorem update_introduces_applicable_record (E : VersionEnv) (ad : AuthorizedDecision)
    (hwf : EnvWf E ad) (hfire : updateFires ad.decision = true) (t : Int)
    (ht : effectiveAt ad.decision.newRecord t) :
    ∃ w ∈ (precedentUpdate ad E).versions, versionApplicableAt w t := by
  refine ⟨ad.decision.newRecord, ?_, ht, hwf.newRecordActive⟩
  rw [update_versions_fires ad E hfire]
  exact List.mem_cons_self _ _

/-- 中文说明：**本件主定理（A）**：授权前例驱动的 `V → V'` 保持既有已声明的结构——
    区间良态、supersession 边非自指、失效记录继续失效。
    强度注：这是**结构保持**，不是"回流结论正确"，也不声称更新后的环境在法律上更好。 -/
theorem precedent_update_preserves_norm_structure (E : VersionEnv) (ad : AuthorizedDecision)
    (hwf : EnvWf E ad) (t : Int) :
    (∀ v ∈ (precedentUpdate ad E).versions, SourceVersionRecord.intervalValid v) ∧
      (∀ v : SourceVersionRecord, isTouchedBy ad E v →
          supersessionWellFormed
            { oldSnap := v.snapshot, newSnap := ad.decision.newSnapshot : SupersessionEdge }) ∧
      (∀ v : SourceVersionRecord, v ∈ E.versions →
          v.status = VersionStatus.retracted ∨ v.status = VersionStatus.superseded →
            ∃ w ∈ (precedentUpdate ad E).versions,
              w.snapshot = v.snapshot ∧ ¬ versionApplicableAt w t) :=
  ⟨update_preserves_intervalValid E ad hwf, update_edges_wellFormed E ad hwf,
    fun v hv h => update_preserves_invalidated_records E ad v t hv h⟩

end StructuralPreservation

section Query

/-- 中文说明：生效区间的布尔读法（只读 `effectiveFrom / effectiveTo`，与
    `TemporalApplicability.lean:30` 的 `effectiveAt` 同形）。 -/
def effectiveAtBool (v : SourceVersionRecord) (t : Int) : Bool :=
  (decide (v.effectiveFrom ≤ t)) &&
    match v.effectiveTo with
    | none => true
    | some u => decide (t ≤ u)

/-- 中文说明：可适用判据的布尔形态：区间内**且**状态为 `active`。 -/
def applicableAtBool (v : SourceVersionRecord) (t : Int) : Bool :=
  effectiveAtBool v t &&
    match v.status with
    | .active => true
    | _ => false

/-- 中文说明：环境在时点 `t` 的可适用版本表。 -/
def applicableVersions (E : VersionEnv) (t : Int) : List SourceVersionRecord :=
  E.versions.filter (fun v => applicableAtBool v t)

/-- 中文说明：可适用版本数（`Nat`，比较不需要字符串归约）。 -/
def applicableCount (E : VersionEnv) (t : Int) : Nat :=
  (applicableVersions E t).length

/-- 中文说明：可适用版本的**生效起点表**——不读快照字符串的可区分粗查询，
    用来把"适用版本变了"写成不依赖字符串归约的判定。 -/
def applicableEffectiveFroms (E : VersionEnv) (t : Int) : List Int :=
  (applicableVersions E t).map SourceVersionRecord.effectiveFrom

/-- 中文说明：布尔查询与声明侧 `versionApplicableAt`（`TemporalApplicability.lean:41`）对齐。
    这条是本件把计算结果读回已声明语义的唯一桥梁；缺它则查询只是语法。 -/
theorem applicableAtBool_true_iff (v : SourceVersionRecord) (t : Int) :
    applicableAtBool v t = true ↔ versionApplicableAt v t := by
  cases v with
  | mk snap pub effFrom effTo st =>
    cases st with
    | active =>
      cases effTo with
      | none =>
        simp only [applicableAtBool, effectiveAtBool, versionApplicableAt, effectiveAt]
        simp
      | some u =>
        simp only [applicableAtBool, effectiveAtBool, versionApplicableAt, effectiveAt]
        simp
    | superseded =>
      refine ⟨fun h => absurd h (by simp [applicableAtBool, effectiveAtBool]),
        fun h => by cases h.2⟩
    | retracted =>
      refine ⟨fun h => absurd h (by simp [applicableAtBool, effectiveAtBool]),
        fun h => by cases h.2⟩
    | corrected =>
      refine ⟨fun h => absurd h (by simp [applicableAtBool, effectiveAtBool]),
        fun h => by cases h.2⟩

/-- 中文说明：查询结果的成员读数：记录在结果里 ⟺ 它在环境里且判据为真。 -/
theorem mem_applicableVersions (E : VersionEnv) (t : Int) (v : SourceVersionRecord) :
    v ∈ applicableVersions E t ↔ v ∈ E.versions ∧ applicableAtBool v t = true := by
  simp only [applicableVersions]
  exact List.mem_filter

/-- 中文说明：不在生效区间 ⇒ 不可适用（`versionApplicableAt` 的第一支）。 -/
theorem not_applicable_of_not_effective (v : SourceVersionRecord) (t : Int)
    (h : ¬ effectiveAt v t) : ¬ versionApplicableAt v t :=
  fun happ => h happ.1

end Query

section NotNoop

/-- 中文说明：见证快照（旧版本）。 -/
def oldSnap : LegalId .snapshot :=
  { payload := "old_v1" }

/-- 中文说明：见证快照（前例确立的新版本）。 -/
def newSnap : LegalId .snapshot :=
  { payload := "new_v2" }

/-- 中文说明：见证记录——旧版本，自第 0 天起无限期有效，状态 `active`。 -/
def oldV : SourceVersionRecord :=
  { snapshot := oldSnap, publicationDay := 0, effectiveFrom := 0,
    effectiveTo := none, status := .active }

/-- 中文说明：见证记录——新版本，第 100 天公布、第 50 天起生效，登记时 `active`。 -/
def newV : SourceVersionRecord :=
  { snapshot := newSnap, publicationDay := 100, effectiveFrom := 50,
    effectiveTo := none, status := .active }

/-- 中文说明：见证环境——只含旧版本。 -/
def envOld : VersionEnv :=
  { versions := [oldV] }

/-- 中文说明：见证产出（最高法 × 指导性案例程序 × 非故意漏洞 × 全国范围；
    缺口种类取自 `P066.GapSignal`）。 -/
def demoProduction : BackflowProduction :=
  { actor := .supremeCourt, procedure := .guidingCaseProcedure,
    gap := .unintentionalGap, scope := .nationwide, content := { payload := "n-1" } }

/-- 中文说明：见证决策——"应当参照"且未被区分（P-019 下即 `.shouldFollow`）。 -/
def demoDecision : PrecedentDecision :=
  { production := demoProduction, binding := .shallRefer, distinguishingReason := false,
    newSnapshot := newSnap, newRecord := newV, supersedes := [oldSnap] }

/-- 中文说明：见证的**授权**决策（携带代拟稿 `Competence` 构造子）。 -/
def demoAuthorized : AuthorizedDecision :=
  ⟨demoDecision, Competence.guidingCaseFill .unintentionalGap⟩

/-- 中文说明：见证决策——同样的版本变动，但只是"可以引用"（P-019 下即 `.nonBinding`）。 -/
def silentDecision : PrecedentDecision :=
  { demoDecision with binding := .mayReference }

/-- 中文说明：沉默决策的授权形态（四元组与见证不变，只换绑定级别）。 -/
def silentAuthorized : AuthorizedDecision :=
  ⟨silentDecision, Competence.guidingCaseFill .unintentionalGap⟩

/-- 中文说明：见证时点——新版本已生效（`50 ≤ 60`），用于比较"版本换人"。 -/
def tSwap : Int := 60

/-- 中文说明：见证时点——新版本尚未生效（`50 > 30`），用于比较"可适用数减少"。 -/
def tPending : Int := 30

/-- 中文说明：`shouldFollow` 触发回流（P-019 的闭式归约，`shall_refer_without_reason_follows`）。 -/
theorem updateFires_demo : updateFires demoDecision = true := rfl

/-- 中文说明：`mayReference` 不触发（`may_reference_nonbinding`）。 -/
theorem updateFires_silent_demo : updateFires silentDecision = false := rfl

/-- 中文说明：时点 60 处，更新前的可适用版本是旧版本。 -/
theorem applicable_at_swap_before : applicableVersions envOld tSwap = [oldV] := rfl

/-- 中文说明：时点 60 处，更新后的可适用版本是**新版本**（旧版本已被取代）。 -/
theorem applicable_at_swap_after :
    applicableVersions (precedentUpdate demoAuthorized envOld) tSwap = [newV] := rfl

/-- 中文说明：同一时点的生效起点读数（更新前）。 -/
theorem applicable_froms_swap_before : applicableEffectiveFroms envOld tSwap = [0] := rfl

/-- 中文说明：同一时点的生效起点读数（更新后）。 -/
theorem applicable_froms_swap_after :
    applicableEffectiveFroms (precedentUpdate demoAuthorized envOld) tSwap = [50] := rfl

/-- 中文说明：时点 30 处，更新前恰有 1 个可适用版本。 -/
theorem applicable_count_pending_before : applicableCount envOld tPending = 1 := rfl

/-- 中文说明：时点 30 处，更新后**没有**可适用版本（旧版本被取代，新版本尚未生效）。 -/
theorem applicable_count_pending_after :
    applicableCount (precedentUpdate demoAuthorized envOld) tPending = 0 := rfl

/-- 中文说明：**本件主定理（B）**：更新不是恒等——同一时点的可适用版本生效起点表在更新前后
    不同（`[0] ≠ [50]`）。这是仓内**当前写不出**的正面陈述，原因见文件头 §法律语义：
    `normEnv : String`（`LegalModelV2.lean:171`）里的 `V` 被 `:242` 全称绑住且从不改写，
    `KernelV3.lean:229` 的 `applicableNorm` 又从不读 `eventTimes`，所以在冻结签名上
    "V 变了"没有表达通道。本件因此把构造放在**新载体** `VersionEnv` 上，
    **不**声称冻结内核被扩展。 -/
theorem update_is_not_noop :
    applicableEffectiveFroms envOld tSwap ≠
      applicableEffectiveFroms (precedentUpdate demoAuthorized envOld) tSwap := by
  intro h
  rw [applicable_froms_swap_before, applicable_froms_swap_after] at h
  exact absurd h (by decide)

/-- 中文说明：**（B）的强形式**：可适用版本表本身也换了（由生效起点表的可区分性推出，
    不需要对快照字符串作判定）。 -/
theorem update_changes_applicable_roster :
    applicableVersions envOld tSwap ≠
      applicableVersions (precedentUpdate demoAuthorized envOld) tSwap := by
  intro h
  exact update_is_not_noop (congrArg applicableEffectiveFroms h)

/-- 中文说明：**（B）的可数形式**：同一更新使可适用版本数由 1 变 0。 -/
theorem update_changes_applicable_count :
    applicableCount envOld tPending = 1 ∧
      applicableCount (precedentUpdate demoAuthorized envOld) tPending = 0 :=
  ⟨applicable_count_pending_before, applicable_count_pending_after⟩

/-- 中文说明：**（B）的对照面**：把绑定级别换成 `mayReference`（P-019 的 `.nonBinding`），
    同一环境、同一时点的查询结果一字不改——变化的驱动因素是**参照义务**，
    不是"有前例出现"。 -/
theorem update_silent_when_may_reference :
    applicableVersions (precedentUpdate silentAuthorized envOld) tSwap =
      applicableVersions envOld tSwap := by
  rw [update_is_noop_when_silent silentAuthorized envOld (by decide)]

end NotNoop

section BackflowNonConvergence

/-- 中文说明：两点状态空间上的**反单调**回流单步：`z' = 1 - z`（`Bool` 上即取反）。
    法律读法："已参照则该结论撤回，未参照则采纳该结论"。 -/
def backflowStep : Bool → Bool := fun b => !b

/-- 中文说明：回流的显式迭代（本件自写；仓内没有可复用的反单调迭代器，
    理由见 `backflowSetStep_not_a_system`）。 -/
def backflowIter : Nat → Bool → Bool
  | 0, b => b
  | n + 1, b => backflowStep (backflowIter n b)

/-- 中文说明：单步展开式。 -/
theorem backflowIter_succ (n : Nat) (b : Bool) :
    backflowIter (n + 1) b = backflowStep (backflowIter n b) := rfl

/-- 中文说明：`backflowStep` 是对合（两次即回到原点），故轨道 2-周期。 -/
theorem backflowStep_is_involution (b : Bool) : backflowStep (backflowStep b) = b := by
  cases b <;> rfl

/-- 中文说明：轨道 2-周期性 `iter (n+2) z = iter n z`。这条同时说明**另一种读法是错的**：
    轨道会回到起点，所以 `∃ n, iter n z = z` 为真，但那不是收敛——收敛要求最终固定，
    被 `backflow_no_fixed_step` 逐段否定。 -/
theorem backflowIter_period_two :
    ∀ (n : Nat) (b : Bool), backflowIter (n + 2) b = backflowIter n b := by
  intro n
  induction n with
  | zero =>
      intro b
      show backflowStep (backflowStep b) = b
      exact backflowStep_is_involution b
  | succ k ih =>
      intro b
      have h1 : (k + 1 + 2 : Nat) = (k + 2) + 1 := by omega
      rw [h1, backflowIter_succ, ih]

/-- 中文说明：取反保持不等（两点空间上显然，写成引理供迭代归纳复用）。 -/
theorem backflowStep_ne {x y : Bool} (h : x ≠ y) : backflowStep x ≠ backflowStep y := by
  cases x <;> cases y <;> simp_all [backflowStep]

/-- 中文说明：**相邻两步永不相等**（任意起点、任意段）。这是"无最终固定"的直接形态，
    也逐段否定了仓内 `iter_stable`（`FiniteMonotoneIteration.lean:46`）的假设形态。 -/
theorem backflow_no_fixed_step :
    ∀ (b : Bool) (n : Nat), backflowIter (n + 1) b ≠ backflowIter n b := by
  intro b n
  induction n with
  | zero =>
      show backflowStep b ≠ b
      cases b <;> decide
  | succ k ih =>
      show backflowStep (backflowIter (k + 1) b) ≠ backflowIter (k + 1) b
      rw [backflowIter_succ k b]
      refine backflowStep_ne ?_
      exact ih

/-- 中文说明：**本件主定理（C）**：回流不必收敛——存在初始状态使相邻迭代永不相等。
    按 `docs/master-plan/06_六类边界绑定表.md` 的纪律，这条登记为**局部反例**，
    只否定"任意回流都收敛"，**不**充当六类界定定理中的任何一类，也不声称回流在别的
    更强意义下不收敛（它其实 2-周期，见 `backflowIter_period_two`）。 -/
theorem feedback_need_not_converge :
    ∃ z : Bool, ∀ n : Nat, backflowIter (n + 1) z ≠ backflowIter n z :=
  ⟨false, fun n => backflow_no_fixed_step false n⟩

/-- 中文说明：回流单步**没有不动点**（任何"取固定点即收敛"的论证在此不可用）。 -/
theorem backflowStep_has_no_fixed_point : ¬ ∃ b : Bool, backflowStep b = b := by
  rintro ⟨b, hb⟩
  cases b <;> exact absurd hb (by decide)

/-- 中文说明：不存在"某段之后稳定"的起点与时点——`iter_stable` 的假设在本轨道上处处为假。 -/
theorem backflow_has_no_stable_stage :
    ¬ ∃ (b : Bool) (n : Nat), backflowIter n b = backflowIter (n + 1) b := by
  rintro ⟨b, n, hn⟩
  exact backflow_no_fixed_step b n hn.symm

/-- 中文说明：**单调对照（同一两点状态空间）**：累加步 `z ↦ z ∨ seed` 单调，一步即固定，
    这正是仓内 `iter_mono`（`:39`）⇒ `fixed_at_card`（`:103`）能收的那一侧。与 `backflowStep`
    的 2-周期并置就是回流问题的法律要点：**能不能收敛，取决于回流是不是单调的，
    而不是取决于"有没有前例"**。 -/
def monotoneAccStep (seed : Bool) (z : Bool) : Bool := z || seed

/-- 中文说明：单调对照侧的显式迭代。 -/
def monotoneIter : Nat → Bool → Bool → Bool
  | 0, _, z => z
  | n + 1, seed, z => monotoneAccStep seed (monotoneIter n seed z)

/-- 中文说明：单调侧一步稳定：`iter 1 = iter 2`（仓内 `iter_stable` 的假设在此**成立**，
    与 `backflow_has_no_stable_stage` 形成对照）。 -/
theorem monotoneIter_one_step_stable (seed z : Bool) :
    monotoneIter 2 seed z = monotoneIter 1 seed z := by
  show monotoneAccStep seed (monotoneAccStep seed z) = monotoneAccStep seed z
  cases seed <;> cases z <;> rfl

/-- 中文说明：**反单调的集合形单步**（与 `FiniteMonotoneSystem.step` 同形）：
    "已采纳则清空，未采纳则采纳"。 -/
def backflowSetStep : Finset Bool → Finset Bool :=
  fun S => if (true : Bool) ∈ S then ∅ else {true}

/-- 中文说明：该单步不保序：`∅ ⊆ {true}`，但像反向（`{true} ⊄ ∅`）。 -/
theorem backflowSetStep_not_mono :
    ¬ ∀ S T : Finset Bool, S ⊆ T → backflowSetStep S ⊆ backflowSetStep T := by
  intro hall
  have h1 : backflowSetStep (∅ : Finset Bool) = ({true} : Finset Bool) := by
    simp [backflowSetStep]
  have h2 : backflowSetStep ({true} : Finset Bool) = (∅ : Finset Bool) := by
    simp [backflowSetStep]
  have hsub : backflowSetStep (∅ : Finset Bool) ⊆ backflowSetStep ({true} : Finset Bool) :=
    hall (∅ : Finset Bool) ({true} : Finset Bool) (Finset.empty_subset _)
  rw [h1, h2] at hsub
  exact Finset.not_mem_empty true (hsub (Finset.mem_singleton.mpr (rfl : (true : Bool) = true)))

/-- 中文说明：**既有迭代机器表达不了反单调回流**（(C) 的对照定理）：不存在以 `backflowSetStep`
    为 `step` 字段的 `FiniteMonotoneSystem Bool`——被违反的正是
    `FiniteMonotoneIteration.lean:11` 那个结构的 `step_monotone` 字段（`:15`），
    而 `iter_mono`（`:39`）与 `fixed_at_card`（`:103`）都只从该字段导出。
    因此回流的收敛性问题落在仓内单调迭代通道之外。 -/
theorem backflowSetStep_not_a_system :
    ¬ ∃ sys : FiniteMonotoneSystem Bool, sys.step = backflowSetStep := by
  rintro ⟨sys, hsys⟩
  refine backflowSetStep_not_mono ?_
  intro S T hST
  rw [← hsys, ← hsys]
  exact sys.step_monotone hST

end BackflowNonConvergence

section CompetenceRejection

/-- 中文说明：见证的形状——任何见证的主体必为最高法、程序必为指导性案例程序、范围必为全国。
    这是构造子集合的**穷尽性读数**，不是法律论证。 -/
theorem competence_shape {a : Actor} {p : Procedure} {g : P066.GapSignal} {s : Scope}
    (c : Competence a p g s) :
    a = Actor.supremeCourt ∧ p = Procedure.guidingCaseProcedure ∧ s = Scope.nationwide := by
  cases c with
  | guidingCaseFill => exact ⟨rfl, rfl, rfl⟩

/-- 中文说明：**规范层条目都带授权**（(D) 的正面形态）：每个条目所申报的产出都被授权。 -/
theorem norm_layer_entry_authorized (e : NormLayerEntry) : authorized e.declared := by
  cases e with
  | backflow pr c => exact ⟨c⟩

/-- 中文说明：**本件主定理（D）**：未经授权的产出**不是**规范——若某产出的四元组无见证，
    就不存在任何规范层条目申报它。证明只用构造子穷尽性与 `cases`，是**类型层**事实
    （构造子层面的拒绝），不是运行时检查，也不判定任何内容。 -/
theorem unauthorized_output_is_not_a_norm (pr : BackflowProduction)
    (hpr : ¬ authorized pr) : ¬ ∃ (e : NormLayerEntry), e.declared = pr := by
  rintro ⟨e, he⟩
  have hw : authorized e.declared := norm_layer_entry_authorized e
  rw [he] at hw
  exact hpr hw

/-- 中文说明：见证产出——下级法院经普通审判程序、限单一案件的续造（代拟稿意义上无见证）。 -/
def lowerCourtDraft : BackflowProduction :=
  { actor := .intermediateCourt, procedure := .ordinaryAdjudication,
    gap := .unintentionalGap, scope := .withinSingleCase, content := { payload := "n-2" } }

/-- 中文说明：**拒绝确实咬得住**：下级法院产出的四元组无见证（`Competence` 构造子不覆盖它）。 -/
theorem lower_court_draft_unauthorized : ¬ authorized lowerCourtDraft := by
  rintro ⟨c⟩
  obtain ⟨h1, _, _⟩ := competence_shape c
  exact absurd h1 (by decide)

/-- 中文说明：拒绝侧的完整陈述：该产出没有任何规范层形式（(D) 的具体实例）。 -/
theorem lower_court_draft_is_not_a_norm_layer_entry :
    ¬ ∃ (e : NormLayerEntry), e.declared = lowerCourtDraft :=
  unauthorized_output_is_not_a_norm lowerCourtDraft lower_court_draft_unauthorized

/-- 中文说明：**非空洞性**：授权侧确有见证，故 `NormLayerEntry` 不是空类型——
    拒绝定理不是因为"什么都不存在"而空洞成立。 -/
theorem backflow_entry_is_not_vacuous : Nonempty NormLayerEntry :=
  ⟨.backflow demoProduction (Competence.guidingCaseFill .unintentionalGap)⟩

/-- 中文说明：**授权与更新的耦合**（07 卷对 S7 的第②条）：本件的 `V → V'` 入口是
    `AuthorizedDecision`，其字段就是见证，故未授权产出连更新入口都进不去——
    "这是提案不是规范"由类型本身读出，不靠事后检查。强度注：这条只是把已有入口说清楚。 -/
theorem unauthorized_production_has_no_update_input (pr : BackflowProduction)
    (hpr : ¬ authorized pr) :
    ¬ ∃ (ad : AuthorizedDecision), ad.decision.production = pr := by
  rintro ⟨ad, had⟩
  exact hpr ⟨ad.witness⟩

end CompetenceRejection

section TimeBoundary

/-- 中文说明：见证记录（E 节）：第 100 天公布、第 0 天起生效、状态 `active`。 -/
def pubLaterV : SourceVersionRecord :=
  { snapshot := newSnap, publicationDay := 100, effectiveFrom := 0,
    effectiveTo := none, status := .active }

/-- 中文说明：**（E）界限一**：观察闸门（`observationAllowed`，`TemporalApplicability.lean:37`）
    拦住"as-of 早于公布日"的未来信息（复用仓内 `future_information_blocked`，`:79`），
    但同一条记录的**生效区间判定**完全不因此改变——两个条件在本载体里各自独立，
    没有被任何字段连起来。证明只用 `Int` 算术。 -/
theorem observation_gate_does_not_determine_effectivity :
    ∃ (v : SourceVersionRecord) (t asOfDay : Int),
      ¬ observationAllowed v.publicationDay asOfDay ∧ effectiveAt v t := by
  refine ⟨pubLaterV, 60, 50, ?_, ?_⟩
  · exact future_information_blocked 100 50 (by omega)
  · exact ⟨by omega, trivial⟩

/-- 中文说明：**（E）界限二（本载体的已知缺口）**：`versionApplicableAt` 只读生效区间与状态，
    **从不读 `publicationDay`**。于是"前例更晚才存在"（公布日在 `t` 之后）与
    "前例在 `t` 可适用"可以同时成立。这条把缺口钉成定理，**不是**修复它：要堵它需给适用判定
    增加"公布/作出时点"这一参与条件，那是独立目标，也不涉及四种时间表示的统一。 -/
theorem late_publication_still_effective_in_interval :
    ∃ (v : SourceVersionRecord) (t : Int), versionApplicableAt v t ∧ t < v.publicationDay :=
  ⟨pubLaterV, 60, ⟨⟨by omega, trivial⟩, rfl⟩, by omega⟩

/-- 中文说明：**（E）界限三**：更新引入的新版本，对早于其生效起点的时点**不适用**
    （复用仓内 `before_effective_interval_not_effective`，`TemporalApplicability.lean:73`）——
    回流不溯及既往在本载体里是**区间事实**，不是更新事实：`precedentUpdate` 没有时点参数，
    把 `t` 塞进更新也得不到溯及力结论。 -/
theorem update_does_not_reach_before_effective_from (E : VersionEnv) (ad : AuthorizedDecision)
    (hwf : EnvWf E ad) (hfire : updateFires ad.decision = true) (t : Int)
    (ht : t < ad.decision.newRecord.effectiveFrom) :
    ∃ w ∈ (precedentUpdate ad E).versions,
      w.snapshot = ad.decision.newSnapshot ∧ ¬ versionApplicableAt w t := by
  refine ⟨ad.decision.newRecord, ?_, hwf.recordMatchesSnapshot,
    not_applicable_of_not_effective _ _
      (before_effective_interval_not_effective _ _ ht)⟩
  rw [update_versions_fires ad E hfire]
  exact List.mem_cons_self _ _

end TimeBoundary

end JurisLean.Seams.PrecedentFlow
