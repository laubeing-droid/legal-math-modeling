import Mathlib.Tactic
import JurisLean.Seams.UnifiedFourteenFamilies
import JurisLean.Seams.UnifiedNeedlesS0S1

/-!
W1-6 差额针 05/06/08 —— 材料级联合见证、冲突排除分支枚举、法律 Horn 实例化及来源树。

出处：`docs/master-plan/20261010_统一法律数学模型_连续与语义全量施工方案.md` W1-6 行
（评审第 2 条）；`docs/master-plan/20261010_接续方案评审_Codex_R1.md` 第 2 条表
（05/06/08 行：十四族仍是三值状态载荷、冲突排除分支枚举开放、法律 Horn 实例化及
来源树另接）；原合同权威为
`docs/spec/20261007-统一法律数学模型_附录I_Lean施工明细.md` I.13 表
:759（针 05 joint_legal_model_exists）、:760（针 06 applicability_matches_source_semantics
的冲突排除分支枚举合同）、:762（针 08 horn_closure_semantic_iff 的"法律规则实例化及
来源树另接"合同）。本件消费 `UnifiedFourteenFamilies.lean` 头注 §三 为 05/06/08
预留的全部接口，并对照 `UnifiedNeedlesS0S1.lean` :87–92 的自认缺口逐条闭合。

## 一、法律语义（人话）

- **针 05（材料级 joint_legal_model_exists）**：`UnifiedNeedlesS0S1.joint_legal_model_exists`
  的每族载荷是三值状态（缺/已声明/有分歧），其头注 :87–88 自认"不是各族完整材料内容"。
  本件在同一法律对象层 `CaseDocket` 上定义**材料内容层**片段（观测值 = 主体列表 ×
  逐字段材料布尔表）与**推导层**片段（观测值 = 任一原子是否在该案卷 Horn 网络闭包内），
  经同一锚引理 `Representation.joint_model_is_not_collapsed`（旧引理保留不动）交出
  非退化联合见证；并给出"材料级＞状态级"的显式消费链：状态层（旧三值 `familyNet` 观测）
  把满料见证案与"银行结算材料缺失"变体案压扁成同一个三值载荷，而材料层与推导层
  都把它们分开——变体案上 `loanEntitlement` 确实不可推导（由避开坏集的显式模型见证）。
- **针 06（冲突排除分支枚举）**：对十四族的每一族，按其实际材料布尔表枚举三个合法
  分支：缺料（brAbsent）/ 一致（brConsistent）/ 分歧（brDivergent），证三分**完备**
  （任一案卷必落恰一支）与**互斥**（分支两两不可共存）；分支判据由计算性分类器
  `famBranchOf` 逐字面求值并与语义谓词双侧互译。下游规则触发表：29 条规则的通用
  触发引理 + 通用阻断引理（前提缺料则结论不可推导，由避开坏集的模型见证），对
  L01 借款债权、L06 继承中止、L11 行政瑕疵三个规则头交出完整的"当且仅当"触发表；
  对 UnifiedFourteenFamilies **故意开放**的原子 `adminFinalDisposition`，本件把
  `witness_admin_branch_open` 从满料见证案推广到**任一案卷**：任何分支下，全部
  10 个冲突点原子都不进 Horn 闭包——分支枚举覆盖此类开点。
- **针 08（法律 Horn 实例化及来源树）**：把 UnifiedFourteenFamilies 的 29 条规则经
  `hornOf` 实例化为推导：通用引理证"每条规则的材料前提都在卷 ⇒ 结论入闭包"与
  "推导树上每一步要么落在已声明在卷材料、要么落在规则表内某条具名法源规则的结论"；
  旗舰端到端定理在满料见证案上对 R07→R08→R10 跨族链（L14 公益资格 → L05 违法
  认定 → 公共修复费用）交出**双树**：材料侧 HProvN 高度 3 带来源推导树 + 法源侧
  LTagN 高度 2 来源树，证两侧引用集的叶全部落在已声明在卷材料或规则法源上，
  并证两树与 Horn 闭包三方一致。

## 二、数学对象

- 逐族材料原子表：`familyMatoms`（57 个材料原子按族分组，与 `materialHolds` 的
  求值分支一一对应）、`familyMatsList`（族材料布尔表 = 原子表逐项求值）、
  `allMaterialAtomList`（57 元全表，附长度自检）。
- 针 05：`variantDocket`（满料见证案挖去 matBankSettlementMatched 的变体案）、
  `docketMatLayer`/`docketHornLayer`（同一 `CaseDocket` 上的两层声明片段）、
  `statePayload`/`stateOf`/`finToFam`（材料网络 → 旧三值状态载体的提升）、
  `isModel_avoiding_gen`（避开坏集模型见证的一般形：规则结论落坏集只需其前提
  撞坏集，不必像旧 `isModel_avoiding` 那样要求所有规则结论都避开坏集）、
  `variant_model`/`variant_loan_not_closure`（变体案上 loanEntitlement 不可推导）、
  旗舰 `joint_legal_model_exists_material` 与
  `material_level_strictly_finer_than_state_level`。
- 针 06：`FamBranch`（缺/一致/分歧三分）、`brIsAbsent`/`brIsConsistent`/
  `brIsDivergent`（语义谓词）、`famBranchOf`（计算性分类器）、
  `rule_fires_of_materials`（材料前提全在卷 ⇒ 结论入闭包，对任一案卷）、
  `conclusion_blocked_of_missing_premise`（前提缺料 ⇒ 结论不可推导的通用引理）、
  三个规则头的内核级触发表检查与三张分支表、`failureish_model`/
  `failureish_not_closure_any` 及 10 个冲突点原子的任一案卷不可推导定理。
- 针 08：`matInitEnt`、`ecoChildC`/`ecoCited`/`ecoProvSet`（R07→R08→R10 链的
  引用集）、`ecoRemediationCosts_prov`（HProvN 高度 3 推导树）、
  `ecoRemediationCosts_ltag`（LTagN 高度 2 来源树）、`eco_prov_trace`/
  `eco_sources_declared`/`eco_cited_nonempty`/`eco_prov_steps_named`、
  `horn_ltag_consistency`（任一 HProvN 树与任一 LTagN 树对同一原子的三方一致）、
  `hprovN_lands_on_table_or_fact`（推导树每步落在规则表结论或初始事实）、
  旗舰 `legal_horn_instantiation_end_to_end`。

## 三、本件证什么、不证什么

**证**：上述全部定理，零 sorry / 零自定义 axiom / 零 True 逃避。
**不证/开放**（如实列出）：
- 针 05 的"总入口见证"以满料见证案 `fullDocket` 与变体案 `variantDocket` 为具体
  载体；不主张对**所有**案卷的一致性见证（那是逐案卷的全域量化，另接）。
  旧引理 `Representation.lean:366` 的 `Fin 2` 版与 `UnifiedNeedlesS0S1.lean`
  的三值版一律保留不删；本件新见证全部走新材料。
- `docketHornLayer` 的 `dec` 是常值（同 `UnifiedNeedlesS0S1.registerLayer` 的
  处理），本件不为其声称 RoundTrip；推导层的分离由 `hornLayer_separates` 的
  观测差承担。
- 针 06 的"当且仅当"触发表只对 L01（R01）、L06（R19）、L11（R23）三个规则头
  逐字面交出；其余 26 条规则头的触发表是同两个通用引理（触发/阻断）的机械
  实例，不在本件逐条展开。三分枚举、互斥与 10 个冲突点排除对所有十四族与
  任一案卷成立。
- 例外/阻则槽（可废止规则）不在 Horn 片段内（`SourceNorms.lean` 头注边界照旧）；
  缺版本/真实规范冲突的分别报告不在本件（同 `UnifiedNeedlesS0S1` :89–90）。
- 法源标签为合成网络的登记值（合同 :713 字段载体），不构成对真实条文效力时点
  的认定；`variantDocket` 与 `badVariant`/`badL01Absent` 是合成网络内的具体
  案卷与原子集，不是现实个案材料。
- `finToFam` 的末支 catch-all 对 `Fin 14` 的合法取值（val < 14）不可达，
  仅为方程编译器的全匹配要求而设。

## 四、档位

全部定理 [已证，认定待 CI]；本机不编译 Lean，CI 是唯一 Lean 权威，当前
CI_NOT_RUN（fail-closed）。`decide`/`rfl` 只用于 Bool/Nat/枚举/List 的闭式
归约（内核级规则表全查与旧件同一模式）；无 `native_decide`；经典逻辑只经
`by_contra` 使用 Lean 标准库公理，无自定义公理。
-/

namespace JurisLean.Seams.UnifiedNeedlesGap05

open JurisLean.Seams.UnifiedFourteenFamilies
open JurisLean.Seams.UnifiedHornIT
open JurisLean.Seams.SourceNorms
open JurisLean.Seams.Representation
open JurisLean.Seams.UnifiedNeedlesS0S1 (MaterialPayload CaseMaterials defaultKey familyNet)

open Atom

/-! ## 〇、共同底座：逐族材料原子表（与 `materialHolds` 求值分支一一对应） -/

/-- 逐族材料原子表：十四族 57 个材料原子按 §10.2.2 表分组（表行序）。 -/
def familyMatoms : Fam → List Atom
  | .L01Contract => [matContractSigned, matBankSettlementMatched,
      matReconciliationUnpaid, matGuaranteeByGOpen]
  | .L02Property => [matRegistryD, matMortgageRegistered, matOtherTitles,
      matRealizationRecord]
  | .L03Tort => [matWorkInstruction, matDamageCorroboration, matNotWorkInjury]
  | .L04Medical => [matTreatmentAtM, matRecordsWithheld, matPreExistingChecks]
  | .L05Environment => [matSamplingMatch, matExceedance, matPondTesting,
      matEcoCostDocs, matNoExculpation, matInNewLawPeriod]
  | .L06FamilySuccession => [matMarriageRegistered, matNoSpousalJointBasis,
      matCDeathRecord, matHeirIdentityOnFile, matHeirsNotYetJoined]
  | .L07Labor => [matWageBasisOnFile, matOvertimeUnsupported]
  | .L08CorporateBankruptcy => [matSeparateAccounts, matInsolvencyShown,
      matAcceptanceDecided]
  | .L09Ip => [matCreationChain, matLicenseExpired, matPostTermUse,
      matNoWillfulnessGravity]
  | .L10Criminal => [matLoanAcquisitionProven, matIntentOnlyConfession,
      matGenuineBusinessShown, matCriminalTrialDone]
  | .L11Admin => [matPenaltyServedWithBasis, matFactualDisputes, matHearingMissed,
      matRecordContradictions]
  | .L12ReviewCompensation => [matDetentionX, matReviewFiledInTime,
      matReturnDamageRecords, matRemoteProfitUnsupported, matDifferentAct]
  | .L13ProcedureExecutionRemedy => [matStayEventsKept, matPriorCarJudgment,
      matNamedErrorAlleged, matDependentClaimFiled, matPriorCaseUnconcluded]
  | .L14ArbitrationMaritimePublic => [matMaritimeContractWithClause, matCarrierCustody,
      matCargoDamage, matExemptionMaterials, matNQualified]

/-- 族材料布尔表 = 逐族材料原子表逐项求值（单一事实来源，不另造第二张表）。 -/
def familyMatsList (f : Fam) (d : CaseDocket) : List Bool :=
  (familyMatoms f).map (fun a => materialHolds a d)

/-- 全部 57 个材料原子的扁平表（14 段拼接）。 -/
def allMaterialAtomList : List Atom :=
  familyMatoms Fam.L01Contract ++ familyMatoms Fam.L02Property ++
    familyMatoms Fam.L03Tort ++ familyMatoms Fam.L04Medical ++
    familyMatoms Fam.L05Environment ++ familyMatoms Fam.L06FamilySuccession ++
    familyMatoms Fam.L07Labor ++ familyMatoms Fam.L08CorporateBankruptcy ++
    familyMatoms Fam.L09Ip ++ familyMatoms Fam.L10Criminal ++
    familyMatoms Fam.L11Admin ++ familyMatoms Fam.L12ReviewCompensation ++
    familyMatoms Fam.L13ProcedureExecutionRemedy ++
    familyMatoms Fam.L14ArbitrationMaritimePublic

/-- 材料全表自检：十四族材料原子共 57 个（内核级计数）。 -/
theorem allMaterialAtomList_length : allMaterialAtomList.length = 57 := by rfl

/-- 每族材料原子表非空（分支互斥性要用的最小事实）。 -/
theorem familyMatoms_ne_nil (f : Fam) : familyMatoms f ≠ [] := by
  cases f <;> decide

/-- `familyWitness` 的逐族见证原子确实属于该族材料原子表（表头一致性）。 -/
theorem familyWitness_mem (f : Fam) : familyWitness f ∈ familyMatoms f := by
  cases f <;> simp [familyMatoms, familyWitness]

/-- 内核级全查：29 条规则的结论都是推导原子——在任何案卷上 `materialHolds`
    恒为 false（推导原子不是输入材料）。 -/
theorem rule_concl_holds_false (r : LawRule) (hr : r ∈ familyRuleList) (d : CaseDocket) :
    materialHolds r.horn.conclusion d = false := by
  have hchk : familyRuleList.all
      (fun x => decide (materialHolds x.horn.conclusion d = false)) = true := by rfl
  exact of_decide_eq_true (List.all_eq_true.mp hchk r hr)

/-- 内核级全查：29 条规则的结论都不是任何材料原子（阻断引理用）。 -/
theorem rule_concl_not_material_atom (r : LawRule) (hr : r ∈ familyRuleList) :
    r.horn.conclusion ∉ allMaterialAtomList := by
  have hchk : familyRuleList.all
      (fun x => decide (x.horn.conclusion ∉ allMaterialAtomList)) = true := by rfl
  exact of_decide_eq_true (List.all_eq_true.mp hchk r hr)

/-! ## 一、针 05：材料级 joint_legal_model_exists -/

/-- 变体案卷：满料见证案挖去 `matBankSettlementMatched`（对账无清偿条目材料缺失），
    其余逐字段照旧——这正是三值状态层看不见、材料层看得见的那一格。 -/
def variantDocket : CaseDocket :=
  { fullDocket with
    m01 :=
      ⟨fullDocket.m01.parties, fullDocket.m01.contractSigned, false,
        fullDocket.m01.reconciliationUnpaid, fullDocket.m01.guaranteeByGOpen⟩ }

/-- 材料网络 → 旧三值状态载荷的逐族提升：见证材料在卷即"已声明"，否则"缺"
    （读法照 `MaterialPayload` 的声明语义）。 -/
def statePayload (f : Fam) (d : CaseDocket) : MaterialPayload :=
  if materialHolds (familyWitness f) d = true then MaterialPayload.declared
  else MaterialPayload.absent

/-- `Fin 14` 下标 → 族标签读出（供 `stateOf` 喂旧 `familyNet` 的 `Fin 14` 指标，
    调用点传 `i.val`）；末支 catch-all 对合法下标（val < 14）不可达，仅满足全匹配。 -/
def finToFam (i : ℕ) : Fam :=
  match i with
  | 0 => Fam.L01Contract
  | 1 => Fam.L02Property
  | 2 => Fam.L03Tort
  | 3 => Fam.L04Medical
  | 4 => Fam.L05Environment
  | 5 => Fam.L06FamilySuccession
  | 6 => Fam.L07Labor
  | 7 => Fam.L08CorporateBankruptcy
  | 8 => Fam.L09Ip
  | 9 => Fam.L10Criminal
  | 10 => Fam.L11Admin
  | 11 => Fam.L12ReviewCompensation
  | 12 => Fam.L13ProcedureExecutionRemedy
  | 13 => Fam.L14ArbitrationMaritimePublic
  | _ => Fam.L01Contract

/-- 旧三值载体上的案卷提升（对照 `UnifiedNeedlesS0S1.CaseMaterials`）。 -/
def stateOf (d : CaseDocket) : CaseMaterials :=
  ⟨defaultKey, fun i => statePayload (finToFam i.val) d⟩

/-- 提升的逐族求值：满料见证案与变体案在三值状态层逐族相同（见证材料位都未动）。 -/
theorem statePayload_variant_agrees (f : Fam) :
    statePayload f fullDocket = statePayload f variantDocket := by
  cases f <;> rfl

/-- 旧 `familyNet` 观测读出的计算式：读的就是提升后的逐族三值载荷。 -/
theorem stateObs_via_familyNet (d : CaseDocket) (i : Fin 14) :
    familyNet.obs i (stateOf d) = statePayload (finToFam i.val) d := rfl

/-- **状态层压扁两案**：三值状态层把满料见证案与变体案逐位看成同一载荷。 -/
theorem state_layer_collapses_variant (i : Fin 14) :
    familyNet.obs i (stateOf fullDocket) = familyNet.obs i (stateOf variantDocket) := by
  rw [stateObs_via_familyNet, stateObs_via_familyNet]
  exact statePayload_variant_agrees _

/-- **案卷级压扁**：两案的三值状态载体整体相等（消费逐族相同）。 -/
theorem stateOf_collapse : stateOf fullDocket = stateOf variantDocket := by
  unfold stateOf
  rw [CaseMaterials.mk.injEq]
  exact ⟨rfl, funext fun i => statePayload_variant_agrees (finToFam i.val)⟩

/-- **材料内容层片段**：观测值 = 主体列表 × 逐字段材料布尔表——正是三值状态层
    丢弃的那部分内容；表示侧把案卷 16 个字段逐一装箱，往返是结构 eta。 -/
def docketMatLayer : Fragment CaseDocket where
  β := SharedQuantities × (Fam → ProcRecord) ×
    Fam01Mats × Fam02Mats × Fam03Mats × Fam04Mats × Fam05Mats × Fam06Mats ×
    Fam07Mats × Fam08Mats × Fam09Mats × Fam10Mats × Fam11Mats × Fam12Mats ×
    Fam13Mats × Fam14Mats
  ι := Fam
  γ := List Party × List Bool
  obs := fun f d => (familyParties d f, familyMatsList f d)
  enc := fun d =>
    (d.qty, d.procOf, d.m01, d.m02, d.m03, d.m04, d.m05, d.m06, d.m07, d.m08,
      d.m09, d.m10, d.m11, d.m12, d.m13, d.m14)
  dec := fun c =>
    match c with
    | (q, pr, m01, m02, m03, m04, m05, m06, m07, m08, m09, m10, m11, m12, m13, m14) =>
      ⟨q, pr, m01, m02, m03, m04, m05, m06, m07, m08, m09, m10, m11, m12, m13, m14⟩

/-- 材料内容层往返（结构 eta 级，同 `familyNet_roundTrip` 的处理方式）。 -/
theorem docketMatLayer_roundTrip : RoundTrip docketMatLayer := fun _ => rfl

/-- **推导层片段**：观测值 = 任一原子是否在该案卷 Horn 网络闭包内。
    `dec` 取常值（同旧 `registerLayer` 的处理），本件不为其声称 RoundTrip。 -/
def docketHornLayer : Fragment CaseDocket where
  β := Bool
  ι := Atom
  γ := Bool
  obs := fun (a : Atom) (d : CaseDocket) => decide (a ∈ closureAt (hornOf d))
  enc := fun d => decide (loanEntitlement ∈ closureAt (hornOf d))
  dec := fun _ => fullDocket

/-- **材料层分开两案**：L01 材料布尔表在变体案上确实少了一个 true。 -/
theorem matLayer_separates :
    docketMatLayer.obs Fam.L01Contract fullDocket ≠
      docketMatLayer.obs Fam.L01Contract variantDocket := by
  intro h
  simp only [docketMatLayer] at h
  have hsnd : familyMatsList Fam.L01Contract fullDocket =
      familyMatsList Fam.L01Contract variantDocket := congrArg Prod.snd h
  have h2 : familyMatsList Fam.L01Contract fullDocket = [true, true, true, true] := rfl
  have h3 : familyMatsList Fam.L01Contract variantDocket = [true, false, true, true] := rfl
  rw [h2, h3] at hsnd
  exact absurd hsnd (by decide)

/-- **避开坏集模型见证的一般形**：初始事实避开坏集、且每条"结论落坏集"的规则
    其前提都撞坏集 ⇒ 全域去坏集是模型。（推广旧 `isModel_avoiding`：不要求
    所有规则结论都避开坏集，只要求撞坏集的规则被坏集前提挡住。） -/
theorem isModel_avoiding_gen {α : Type} [DecidableEq α] [Fintype α] (sys : HornSystem α)
    (bad : Finset α)
    (hdisj : Disjoint sys.initialFacts bad)
    (hblock : ∀ r ∈ sys.rules, r.conclusion ∈ bad → r.premises ∩ bad ≠ ∅) :
    isModel sys (Finset.univ \ bad) := by
  refine ⟨?_, ?_⟩
  · intro x hx
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ x,
      fun hmem => Finset.disjoint_left.mp hdisj hx hmem⟩
  · intro r hr hprem
    by_contra hcon
    have hcb : r.conclusion ∈ bad := by
      by_contra h9
      exact hcon (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, h9⟩)
    obtain ⟨p, hp⟩ := Finset.nonempty_iff_ne_empty.mpr (hblock r hr hcb)
    exact (Finset.mem_sdiff.mp (hprem (Finset.mem_inter.mp hp).1)).2
      (Finset.mem_inter.mp hp).2

/-- 变体案的坏集：缺失的那份对账材料 + 只能由它推出的两级结论。 -/
def badVariant : Finset Atom :=
  {matBankSettlementMatched, loanEntitlement, mortgageSecuredPriority}

/-- 内核级全查：变体案坏集的阻断表——每条"结论落坏集"的规则其前提都撞坏集。 -/
theorem variant_hblock_check :
    familyRuleList.all (fun r => !decide (r.horn.conclusion ∈ badVariant) ||
      !decide ((r.horn.premises ∩ badVariant) = ∅)) = true := by rfl

/-- 变体案坏集与初始事实不相交（缺失材料不在卷、推导原子非输入）。 -/
theorem variant_hdisj :
    Disjoint (hornOf variantDocket).initialFacts badVariant := by
  rw [Finset.disjoint_left]
  intro x hx hb
  have h1 : materialHolds x variantDocket = true := (Finset.mem_filter.mp hx).2
  rcases Finset.mem_insert.mp hb with rfl | hb
  · have h0 : materialHolds matBankSettlementMatched variantDocket = false := rfl
    rw [h0] at h1
    exact Bool.noConfusion h1
  rcases Finset.mem_insert.mp hb with rfl | hb
  · have h0 : materialHolds loanEntitlement variantDocket = false := rfl
    rw [h0] at h1
    exact Bool.noConfusion h1
  rcases Finset.mem_singleton.mp hb with rfl
  · have h0 : materialHolds mortgageSecuredPriority variantDocket = false := rfl
    rw [h0] at h1
    exact Bool.noConfusion h1

/-- 阻断表从内核 Bool 检查读成规则级命题。 -/
theorem variant_hblock :
    ∀ r ∈ familyRuleList, r.horn.conclusion ∈ badVariant →
      r.horn.premises ∩ badVariant ≠ ∅ := by
  intro r hr hcon
  have hchk := List.all_eq_true.mp variant_hblock_check r hr
  simp only [Bool.or_eq_true, not_decide_eq_true] at hchk
  rcases hchk with h9 | h9
  · exact absurd hcon h9
  · exact h9

/-- **变体案的避开坏集模型**：全域去掉坏集是 `hornOf variantDocket` 的模型。 -/
theorem variant_model : isModel (hornOf variantDocket) (Finset.univ \ badVariant) := by
  refine isModel_avoiding_gen (hornOf variantDocket) badVariant variant_hdisj ?_
  intro rh hrh hcon
  obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hrh
  exact variant_hblock r (List.mem_toFinset.mp hr) hcon

/-- **推导层分开两案**：变体案上 `loanEntitlement` 不可推导——对账材料缺失时
    借款债权在三值状态层仍标"已声明"，但规则链确实推不出来。 -/
theorem variant_loan_not_closure : loanEntitlement ∉ closureAt (hornOf variantDocket) := by
  intro hmem
  obtain ⟨_, hnot⟩ := Finset.mem_sdiff.mp
    (closure_only_entailed (hornOf variantDocket) hmem (Finset.univ \ badVariant)
      variant_model)
  exact hnot (Finset.mem_insert_of_mem (Finset.mem_insert_self loanEntitlement _))

/-- 推导层观测差：闭包成员位的判据性读出。 -/
theorem hornLayer_separates :
    docketHornLayer.obs loanEntitlement fullDocket ≠
      docketHornLayer.obs loanEntitlement variantDocket := by
  intro h
  simp only [docketHornLayer] at h
  have h1 : decide (loanEntitlement ∈ closureAt familyHorn) = true :=
    decide_eq_true loanEntitlement_mem
  have h2 : decide (loanEntitlement ∈ closureAt (hornOf variantDocket)) = false :=
    decide_eq_false variant_loan_not_closure
  rw [h1, h2] at h
  exact Bool.noConfusion h

/-- **29 条规则经 hornOf 实例化（满料见证案）**：规则表内每条规则的结论都进闭包
    （经已建立的四态清单覆盖 + 内核级覆盖检查）。 -/
theorem all_rule_concl_in_closure :
    ∀ r ∈ familyRuleList, r.horn.conclusion ∈ closureAt familyHorn := by
  intro r hr
  have hchk : familyRuleList.all (fun x => decide (x.horn.conclusion ∈
      (witnessEstablished ++ witnessProcedural).toFinset)) = true := by rfl
  have hmem : r.horn.conclusion ∈ (witnessEstablished ++ witnessProcedural).toFinset :=
    of_decide_eq_true (List.all_eq_true.mp hchk r hr)
  rcases List.mem_append.mp (List.mem_toFinset.mp hmem) with h9 | h9
  · exact witness_established_ok _ h9
  · exact witness_procedural_ok _ h9

/-- **针 05 旗舰（材料级 joint_legal_model_exists；附录I:759 升级交付）**：
    满料见证案上十四族材料全非空、hornOf 网络非退化（初始事实非空、规则非空、
    29 条结论全部入闭包）、四态联合输出良定义；联合载体非退化（旧锚引理在新
    材料层上实例化，旧引理保留不删）；并附"材料级＞状态级"条款——状态层压扁
    两案、材料层与推导层都分开它们。 -/
theorem joint_legal_model_exists_material :
    (∀ f : Fam,
        materialHolds (familyWitness f) fullDocket = true ∧
        familyParties fullDocket f ≠ []) ∧
    (familyHorn.initialFacts.Nonempty ∧ familyHorn.rules.Nonempty ∧
      ∀ r ∈ familyRuleList, r.horn.conclusion ∈ closureAt familyHorn) ∧
    -- 以下十一合取即 `UnifiedFourteenFamilies.witness_joint_evaluation` 的命题原文：
    -- 裸定理名是证明项而非 Prop，不能直接作 `∧` 操作数，故展开书写（命题恒等）。
    (∀ a ∈ witnessOutput.established, a ∈ closureAt familyHorn) ∧
    (∀ a ∈ witnessOutput.notEstablished, a ∉ closureAt familyHorn) ∧
    (∀ a ∈ witnessOutput.pendingByLaw,
        holdOf a ∈ closureAt familyHorn ∧ a ∉ closureAt familyHorn) ∧
    (∀ a ∈ witnessOutput.procedural, a ∈ closureAt familyHorn) ∧
    (∀ f : Fam,
        materialHolds (familyWitness f) fullDocket = true ∧
        familyParties fullDocket f ≠ []) ∧
    (fullDocket.procOf Fam.L01Contract).stage ≠
      (fullDocket.procOf Fam.L03Tort).stage ∧
    (fullDocket.procOf Fam.L07Labor).forum ≠
      (fullDocket.procOf Fam.L14ArbitrationMaritimePublic).forum ∧
    (loanEntitlement ∈ closureAt familyHorn ∧ loanFinalDecree ∉ closureAt familyHorn) ∧
    0 < witnessOutput.unmetBalance ∧
    (familyRuleList.all (fun r => srcInForce r.src) = true) ∧
    (adminFinalDisposition ∉ closureAt familyHorn) ∧
    (∃ (p q : Joint docketMatLayer docketHornLayer), p ≠ q ∧ ∃ i : docketMatLayer.ι,
      jointObs₁ docketMatLayer docketHornLayer i p ≠
        jointObs₁ docketMatLayer docketHornLayer i q) ∧
    (stateOf fullDocket = stateOf variantDocket ∧
      docketMatLayer.obs Fam.L01Contract fullDocket ≠
        docketMatLayer.obs Fam.L01Contract variantDocket ∧
      (loanEntitlement ∈ closureAt familyHorn ∧
        loanEntitlement ∉ closureAt (hornOf variantDocket))) :=
  ⟨witness_completeness_ok,
    ⟨⟨matContractSigned, Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩⟩,
      ⟨ruleLoanEntitlement.horn, rule_horn_mem ruleLoanEntitlement (by simp [familyRuleList])⟩,
      all_rule_concl_in_closure⟩,
    -- 十一合取支逐项供给（与 `UnifiedFourteenFamilies.witness_joint_evaluation` 的
    -- 证明项逐字段同形）：
    witness_established_ok,
    witness_not_established_ok,
    witness_pending_ok,
    witness_procedural_ok,
    witness_completeness_ok,
    witness_stages_not_shared,
    witness_forums_separate,
    witness_entitlement_not_finality,
    witness_shortfall_ok,
    all_rules_sources_in_force,
    witness_admin_branch_open,
    joint_model_is_not_collapsed docketMatLayer docketHornLayer fullDocket variantDocket
      docketMatLayer_roundTrip ⟨Fam.L01Contract, matLayer_separates⟩,
    ⟨stateOf_collapse, matLayer_separates, loanEntitlement_mem, variant_loan_not_closure⟩⟩

/-- **材料级＞状态级（显式消费链）**：旧三值 `familyNet` 观测在两案上逐位相等
    （状态层不可分）；材料内容层与推导层都分开两案；且状态读出确由材料定义
    （材料决定状态是恒等式，状态丢材料信息是严格损失）。 -/
theorem material_level_strictly_finer_than_state_level :
    (∀ i : Fin 14,
        familyNet.obs i (stateOf fullDocket) = familyNet.obs i (stateOf variantDocket)) ∧
    (docketMatLayer.obs Fam.L01Contract fullDocket ≠
      docketMatLayer.obs Fam.L01Contract variantDocket) ∧
    (docketHornLayer.obs loanEntitlement fullDocket ≠
      docketHornLayer.obs loanEntitlement variantDocket) ∧
    (∀ f : Fam, statePayload f fullDocket = statePayload f variantDocket) :=
  ⟨state_layer_collapses_variant, matLayer_separates, hornLayer_separates,
    statePayload_variant_agrees⟩

/-! ## 二、针 06：冲突排除分支枚举 -/

/-- 单族分支：缺料 / 一致 / 分歧（材料分歧）。 -/
inductive FamBranch where
  | brAbsent
  | brConsistent
  | brDivergent
deriving DecidableEq

/-- 分支语义谓词：该族材料原子全部不在卷。 -/
def brIsAbsent (f : Fam) (d : CaseDocket) : Prop :=
  ∀ a ∈ familyMatoms f, materialHolds a d = false

/-- 分支语义谓词：该族材料原子全部在卷。 -/
def brIsConsistent (f : Fam) (d : CaseDocket) : Prop :=
  ∀ a ∈ familyMatoms f, materialHolds a d = true

/-- 分支语义谓词：该族材料既有在卷也有缺（材料分歧）。 -/
def brIsDivergent (f : Fam) (d : CaseDocket) : Prop :=
  ∃ a₁ ∈ familyMatoms f, ∃ a₂ ∈ familyMatoms f,
    materialHolds a₁ d = true ∧ materialHolds a₂ d = false

/-- 计算性分支分类器：布尔表全真 ⇒ 一致；全假 ⇒ 缺料；否则分歧。 -/
def famBranchOf (f : Fam) (d : CaseDocket) : FamBranch :=
  if (familyMatsList f d).all id = true then FamBranch.brConsistent
  else if (familyMatsList f d).all (fun b => !b) = true then FamBranch.brAbsent
  else FamBranch.brDivergent

/-- **枚举完备**：任一案卷在任何族上必落三分支之一（无遗漏分支）。 -/
theorem famBranch_partition (f : Fam) (d : CaseDocket) :
    brIsAbsent f d ∨ brIsConsistent f d ∨ brIsDivergent f d := by
  by_cases hcon : brIsConsistent f d
  · exact Or.inr (Or.inl hcon)
  by_cases hab : brIsAbsent f d
  · exact Or.inl hab
  refine Or.inr (Or.inr ?_)
  have htf : ∃ a ∈ familyMatoms f, materialHolds a d = false := by
    by_contra hall
    push_neg at hall
    refine hcon (fun a ha => ?_)
    cases h9 : materialHolds a d with
    | true => rfl
    | false => exact absurd h9 (hall a ha)
  have htr : ∃ a ∈ familyMatoms f, materialHolds a d = true := by
    by_contra hall
    push_neg at hall
    refine hab (fun a ha => ?_)
    cases h9 : materialHolds a d with
    | false => rfl
    | true => exact absurd h9 (hall a ha)
  obtain ⟨a₁, h₁m, h₁f⟩ := htf
  obtain ⟨a₂, h₂m, h₂t⟩ := htr
  exact ⟨a₂, h₂m, a₁, h₁m, h₂t, h₁f⟩

/-- **互斥一**：缺料与一致不可共存（每族材料表非空）。 -/
theorem brAbsent_not_consistent (f : Fam) (d : CaseDocket)
    (ha : brIsAbsent f d) (hc : brIsConsistent f d) : False := by
  obtain ⟨a, ham⟩ := List.exists_mem_of_ne_nil (familyMatoms f) (familyMatoms_ne_nil f)
  exact Bool.noConfusion ((ha a ham).symm.trans (hc a ham))

/-- **互斥二**：缺料与分歧不可共存。 -/
theorem brAbsent_not_divergent (f : Fam) (d : CaseDocket)
    (ha : brIsAbsent f d) (hd : brIsDivergent f d) : False := by
  obtain ⟨a₁, h₁m, _, _, ht, _⟩ := hd
  exact Bool.noConfusion ((ha a₁ h₁m).symm.trans ht)

/-- **互斥三**：一致与分歧不可共存。 -/
theorem brConsistent_not_divergent (f : Fam) (d : CaseDocket)
    (hc : brIsConsistent f d) (hd : brIsDivergent f d) : False := by
  obtain ⟨a₁, h₁m, a₂, h₂m, _, hf⟩ := hd
  exact Bool.noConfusion ((hc a₂ h₂m).symm.trans hf)

/-- 分类器 ↔ 语义谓词（一致支）。 -/
theorem famBranchOf_eq_consistent_iff (f : Fam) (d : CaseDocket) :
    famBranchOf f d = FamBranch.brConsistent ↔ brIsConsistent f d := by
  unfold famBranchOf
  by_cases h1 : (familyMatsList f d).all id = true
  · rw [if_pos h1, eq_self_iff_true, true_iff]
    intro a ha
    exact List.all_eq_true.mp h1 (materialHolds a d) (List.mem_map.mpr ⟨a, ha, rfl⟩)
  · rw [if_neg h1]
    constructor
    · intro heq
      by_cases h2 : (familyMatsList f d).all (fun b => !b) = true
      · rw [if_pos h2] at heq
        exact FamBranch.noConfusion heq
      · rw [if_neg h2] at heq
        exact FamBranch.noConfusion heq
    · intro hall
      exact absurd (by
        rw [List.all_eq_true]
        intro b hb
        obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hb
        exact hall a ha) h1

/-- 分类器 ↔ 语义谓词（缺料支）。 -/
theorem famBranchOf_eq_absent_iff (f : Fam) (d : CaseDocket) :
    famBranchOf f d = FamBranch.brAbsent ↔ brIsAbsent f d := by
  unfold famBranchOf
  by_cases h1 : (familyMatsList f d).all id = true
  · rw [if_pos h1]
    refine iff_of_false (fun heq => FamBranch.noConfusion heq) ?_
    intro hall
    obtain ⟨a, ham⟩ := List.exists_mem_of_ne_nil (familyMatoms f) (familyMatoms_ne_nil f)
    have hmem : materialHolds a d ∈ familyMatsList f d :=
      List.mem_map.mpr ⟨a, ham, rfl⟩
    exact Bool.noConfusion ((hall a ham).symm.trans (List.all_eq_true.mp h1 _ hmem))
  · rw [if_neg h1]
    by_cases h2 : (familyMatsList f d).all (fun b => !b) = true
    · rw [if_pos h2, eq_self_iff_true, true_iff]
      intro a ha
      have h9 : (!materialHolds a d) = true :=
        List.all_eq_true.mp h2 (materialHolds a d) (List.mem_map.mpr ⟨a, ha, rfl⟩)
      rw [Bool.not_eq_true'] at h9
      exact h9
    · rw [if_neg h2]
      refine iff_of_false (fun heq => FamBranch.noConfusion heq) ?_
      intro habs
      apply h2
      rw [List.all_eq_true]
      intro b hb
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hb
      rw [habs a ha]
      rfl

/-- 分类器 ↔ 语义谓词（分歧支）。 -/
theorem famBranchOf_eq_divergent_iff (f : Fam) (d : CaseDocket) :
    famBranchOf f d = FamBranch.brDivergent ↔ brIsDivergent f d := by
  unfold famBranchOf
  by_cases h1 : (familyMatsList f d).all id = true
  · rw [if_pos h1]
    refine iff_of_false (fun heq => FamBranch.noConfusion heq) ?_
    intro hd
    obtain ⟨a₁, _, a₂, h₂m, _, hf⟩ := hd
    have hfa : materialHolds a₂ d = true :=
      List.all_eq_true.mp h1 (materialHolds a₂ d) (List.mem_map.mpr ⟨a₂, h₂m, rfl⟩)
    exact Bool.noConfusion (hf.symm.trans hfa)
  · rw [if_neg h1]
    by_cases h2 : (familyMatsList f d).all (fun b => !b) = true
    · rw [if_pos h2]
      refine iff_of_false (fun heq => FamBranch.noConfusion heq) ?_
      intro hd
      obtain ⟨a₁, h₁m, _, _, ht, _⟩ := hd
      have h9 : (!materialHolds a₁ d) = true :=
        List.all_eq_true.mp h2 (materialHolds a₁ d) (List.mem_map.mpr ⟨a₁, h₁m, rfl⟩)
      rw [Bool.not_eq_true'] at h9
      exact Bool.noConfusion (h9.symm.trans ht)
    · rw [if_neg h2, eq_self_iff_true, true_iff]
      have htf : ∃ a ∈ familyMatoms f, materialHolds a d = false := by
        by_contra h9
        push_neg at h9
        refine h1 (List.all_eq_true.mpr fun b hb => ?_)
        obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hb
        cases hb2 : materialHolds a d with
        | true => rfl
        | false => exact absurd hb2 (h9 a ha)
      have htr : ∃ a ∈ familyMatoms f, materialHolds a d = true := by
        by_contra h9
        push_neg at h9
        refine h2 (List.all_eq_true.mpr fun b hb => ?_)
        obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hb
        cases hb2 : materialHolds a d with
        | false => rfl
        | true => exact absurd hb2 (h9 a ha)
      obtain ⟨a₁, h₁m, h₁f⟩ := htf
      obtain ⟨a₂, h₂m, h₂t⟩ := htr
      exact ⟨a₂, h₂m, a₁, h₁m, h₂t, h₁f⟩

/-- **分支枚举总表**：完备 + 互斥 + 分类器与语义谓词双侧互译（对任一族任一案卷）。 -/
theorem famBranch_partition_and_exclusive (f : Fam) (d : CaseDocket) :
    (brIsAbsent f d ∨ brIsConsistent f d ∨ brIsDivergent f d) ∧
    (brIsAbsent f d → brIsConsistent f d → False) ∧
    (brIsAbsent f d → brIsDivergent f d → False) ∧
    (brIsConsistent f d → brIsDivergent f d → False) ∧
    (famBranchOf f d = FamBranch.brConsistent ↔ brIsConsistent f d) ∧
    (famBranchOf f d = FamBranch.brAbsent ↔ brIsAbsent f d) ∧
    (famBranchOf f d = FamBranch.brDivergent ↔ brIsDivergent f d) :=
  ⟨famBranch_partition f d, brAbsent_not_consistent f d, brAbsent_not_divergent f d,
    brConsistent_not_divergent f d, famBranchOf_eq_consistent_iff f d,
    famBranchOf_eq_absent_iff f d, famBranchOf_eq_divergent_iff f d⟩

/-- 见证案求值：满料见证案在全部十四族上都走"一致"分支（内核级逐字面求值）。 -/
theorem famBranch_fullDocket_all_consistent :
    ∀ f : Fam, famBranchOf f fullDocket = FamBranch.brConsistent := by
  intro f
  cases f <;> rfl

/-- 见证案求值：变体案的 L01 走"分歧"分支（4 份材料 3 真 1 缺）。 -/
theorem famBranch_variant_L01_divergent :
    famBranchOf Fam.L01Contract variantDocket = FamBranch.brDivergent := rfl

/-- 规则表内规则属于任一案卷的 Horn 网络（`rule_horn_mem` 的任一案卷版）。 -/
theorem rule_horn_mem_general (d : CaseDocket) (r : LawRule) (hr : r ∈ familyRuleList) :
    r.horn ∈ (hornOf d).rules :=
  Finset.mem_image.mpr ⟨r, List.mem_toFinset.mpr hr, rfl⟩

/-- 闭包引入的任一案卷版：规则前提全在闭包 ⇒ 结论在闭包。 -/
theorem memByRule_general (d : CaseDocket) (r : LawRule) (hr : r ∈ familyRuleList)
    (hp : ∀ p ∈ r.horn.premises, p ∈ closureAt (hornOf d)) :
    r.horn.conclusion ∈ closureAt (hornOf d) :=
  (closure_is_model (hornOf d)).2 r.horn (rule_horn_mem_general d r hr) hp

/-- **下游触发通用引理**：规则的材料前提全部在卷 ⇒ 结论进该案卷闭包
    （29 条规则逐条适用，即"29 条规则经 hornOf 实例化"的触发半边）。 -/
theorem rule_fires_of_materials (d : CaseDocket) (r : LawRule) (hr : r ∈ familyRuleList)
    (h : ∀ p ∈ r.horn.premises, materialHolds p d = true) :
    r.horn.conclusion ∈ closureAt (hornOf d) :=
  memByRule_general d r hr (fun p hp =>
    (closure_is_model (hornOf d)).1 (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h p hp⟩))

/-- **下游阻断通用引理**：某前提材料在该案卷缺料，且没有任何规则以该材料原子为
    结论（内核级全查给出），且引用集检查表成立 ⇒ 该规则结论在该案卷不可推导
    （避开坏集模型见证：坏集 = {缺失前提, 结论}）。 -/
theorem conclusion_blocked_of_missing_premise (d : CaseDocket) (r : LawRule)
    (hrules : r.horn ∈ (hornOf d).rules)
    (p : Atom) (hpmat : p ∈ r.horn.premises) (hmiss : materialHolds p d = false)
    (hpmat0 : p ∈ allMaterialAtomList)
    (hc : Atom) (hcnotmat : ∀ d' : CaseDocket, materialHolds hc d' = false)
    (hcheck : familyRuleList.all (fun r' => !decide (r'.horn.conclusion = hc) ||
        (decide (p ∈ r'.horn.premises) || decide (hc ∈ r'.horn.premises))) = true) :
    hc ∉ closureAt (hornOf d) := by
  intro hmem
  have hdisj : Disjoint (hornOf d).initialFacts {p, hc} := by
    rw [Finset.disjoint_left]
    intro x hx hb
    have h1 : materialHolds x d = true := (Finset.mem_filter.mp hx).2
    rcases Finset.mem_insert.mp hb with rfl | hb
    · rw [hmiss] at h1
      exact Bool.noConfusion h1
    rcases Finset.mem_singleton.mp hb with rfl
    · rw [hcnotmat d] at h1
      exact Bool.noConfusion h1
  have hmodel : isModel (hornOf d) (Finset.univ \ {p, hc}) := by
    refine isModel_avoiding_gen (hornOf d) {p, hc} hdisj ?_
    intro rh hrh hcon
    obtain ⟨r', hr', rfl⟩ := Finset.mem_image.mp hrh
    intro hempty
    rcases Finset.mem_insert.mp hcon with hcp | hcon
    · exfalso
      have hm : r'.horn.conclusion ∈ allMaterialAtomList := by rw [hcp]; exact hpmat0
      exact rule_concl_not_material_atom r' (List.mem_toFinset.mp hr') hm
    · rcases Finset.mem_singleton.mp hcon with hcp
      have hchk := List.all_eq_true.mp hcheck r' (List.mem_toFinset.mp hr')
      rw [hcp] at hchk
      have hself : decide (hc = hc) = true := decide_eq_true rfl
      rw [hself] at hchk
      simp only [Bool.not_true, Bool.false_or, Bool.or_eq_true] at hchk
      rcases hchk with h9 | h9
      · exact hempty (Finset.mem_inter.mpr ⟨of_decide_eq_true h9,
          Finset.mem_insert_self p {hc}⟩)
      · exact hempty (Finset.mem_inter.mpr ⟨of_decide_eq_true h9,
          Finset.mem_insert_of_mem (Finset.mem_singleton_self hc)⟩)
  obtain ⟨_, hnot⟩ := Finset.mem_sdiff.mp
    (closure_only_entailed (hornOf d) hmem (Finset.univ \ {p, hc}) hmodel)
  exact hnot (Finset.mem_insert_of_mem (Finset.mem_singleton_self hc))

/-- R01 头触发表内核检查：只有 R01 以 loanEntitlement 为结论，且其三前提都在卷。 -/
theorem loan_missing_premise_check (p : Atom) (hp : p ∈ ruleLoanEntitlement.horn.premises) :
    familyRuleList.all (fun r' => !decide (r'.horn.conclusion = loanEntitlement) ||
      (decide (p ∈ r'.horn.premises) || decide (loanEntitlement ∈ r'.horn.premises))) = true := by
  have h3 : p = matContractSigned ∨ p = matBankSettlementMatched ∨
      p = matReconciliationUnpaid := by
    simpa [ruleLoanEntitlement, LawRule.horn] using hp
  rcases h3 with rfl | rfl | rfl <;> rfl

/-- R23 头触发表内核检查（L11 行政瑕疵——故意开放原子所在族）。 -/
theorem admin_missing_premise_check (p : Atom) (hp : p ∈ ruleAdminDefects.horn.premises) :
    familyRuleList.all (fun r' => !decide (r'.horn.conclusion = adminDefectsEstablished) ||
      (decide (p ∈ r'.horn.premises) || decide (adminDefectsEstablished ∈ r'.horn.premises))) = true := by
  have h3 : p = matPenaltyServedWithBasis ∨ p = matHearingMissed ∨
      p = matRecordContradictions := by
    simpa [ruleAdminDefects, LawRule.horn] using hp
  rcases h3 with rfl | rfl | rfl <;> rfl

/-- R19 头触发表内核检查（L06 继承中止——跨族链 R20/R21 的源头）。 -/
theorem stay_missing_premise_check (p : Atom) (hp : p ∈ ruleStaySuccession.horn.premises) :
    familyRuleList.all (fun r' => !decide (r'.horn.conclusion = stayForSuccession) ||
      (decide (p ∈ r'.horn.premises) || decide (stayForSuccession ∈ r'.horn.premises))) = true := by
  have h2 : p = matCDeathRecord ∨ p = matHeirsNotYetJoined := by
    simpa [ruleStaySuccession, LawRule.horn] using hp
  rcases h2 with rfl | rfl <;> rfl

/-- **L01 借款债权触发表（当且仅当）**：三分支全覆盖——一致支触发、缺料支不触发、
    分歧支的 8 种材料模式由右侧三联式精确分类。 -/
theorem loanEntitlement_fires_iff (d : CaseDocket) :
    loanEntitlement ∈ closureAt (hornOf d) ↔
      (materialHolds matContractSigned d = true ∧
        materialHolds matBankSettlementMatched d = true ∧
        materialHolds matReconciliationUnpaid d = true) := by
  constructor
  · intro hmem
    refine ⟨?_, ?_, ?_⟩
    · by_contra hm
      have hmiss : materialHolds matContractSigned d = false := by
        cases h9 : materialHolds matContractSigned d with
        | false => rfl
        | true => exact absurd h9 hm
      exact absurd hmem
        (conclusion_blocked_of_missing_premise d ruleLoanEntitlement
          (rule_horn_mem_general d ruleLoanEntitlement (by simp [familyRuleList]))
          matContractSigned (by simp [ruleLoanEntitlement, LawRule.horn]) hmiss
          (by simp [allMaterialAtomList, familyMatoms]) loanEntitlement (fun _ => rfl)
          (loan_missing_premise_check matContractSigned
            (by simp [ruleLoanEntitlement, LawRule.horn])))
    · by_contra hm
      have hmiss : materialHolds matBankSettlementMatched d = false := by
        cases h9 : materialHolds matBankSettlementMatched d with
        | false => rfl
        | true => exact absurd h9 hm
      exact absurd hmem
        (conclusion_blocked_of_missing_premise d ruleLoanEntitlement
          (rule_horn_mem_general d ruleLoanEntitlement (by simp [familyRuleList]))
          matBankSettlementMatched (by simp [ruleLoanEntitlement, LawRule.horn]) hmiss
          (by simp [allMaterialAtomList, familyMatoms]) loanEntitlement (fun _ => rfl)
          (loan_missing_premise_check matBankSettlementMatched
            (by simp [ruleLoanEntitlement, LawRule.horn])))
    · by_contra hm
      have hmiss : materialHolds matReconciliationUnpaid d = false := by
        cases h9 : materialHolds matReconciliationUnpaid d with
        | false => rfl
        | true => exact absurd h9 hm
      exact absurd hmem
        (conclusion_blocked_of_missing_premise d ruleLoanEntitlement
          (rule_horn_mem_general d ruleLoanEntitlement (by simp [familyRuleList]))
          matReconciliationUnpaid (by simp [ruleLoanEntitlement, LawRule.horn]) hmiss
          (by simp [allMaterialAtomList, familyMatoms]) loanEntitlement (fun _ => rfl)
          (loan_missing_premise_check matReconciliationUnpaid
            (by simp [ruleLoanEntitlement, LawRule.horn])))
  · rintro ⟨h1, h2, h3⟩
    exact rule_fires_of_materials d ruleLoanEntitlement (by simp [familyRuleList]) (by
      intro p hp
      rcases Finset.mem_insert.mp hp with rfl | hp
      · exact h1
      rcases Finset.mem_insert.mp hp with rfl | hp
      · exact h2
      rcases Finset.mem_singleton.mp hp with rfl
      · exact h3)

/-- **L11 行政瑕疵触发表（当且仅当）**：覆盖 `adminFinalDisposition` 所在族的
    全部下游模式——三前提模式决定触发，与终局处分无关。 -/
theorem adminDefects_fires_iff (d : CaseDocket) :
    adminDefectsEstablished ∈ closureAt (hornOf d) ↔
      (materialHolds matPenaltyServedWithBasis d = true ∧
        materialHolds matHearingMissed d = true ∧
        materialHolds matRecordContradictions d = true) := by
  constructor
  · intro hmem
    refine ⟨?_, ?_, ?_⟩
    · by_contra hm
      have hmiss : materialHolds matPenaltyServedWithBasis d = false := by
        cases h9 : materialHolds matPenaltyServedWithBasis d with
        | false => rfl
        | true => exact absurd h9 hm
      exact absurd hmem
        (conclusion_blocked_of_missing_premise d ruleAdminDefects
          (rule_horn_mem_general d ruleAdminDefects (by simp [familyRuleList]))
          matPenaltyServedWithBasis (by simp [ruleAdminDefects, LawRule.horn]) hmiss
          (by simp [allMaterialAtomList, familyMatoms]) adminDefectsEstablished
          (fun _ => rfl)
          (admin_missing_premise_check matPenaltyServedWithBasis
            (by simp [ruleAdminDefects, LawRule.horn])))
    · by_contra hm
      have hmiss : materialHolds matHearingMissed d = false := by
        cases h9 : materialHolds matHearingMissed d with
        | false => rfl
        | true => exact absurd h9 hm
      exact absurd hmem
        (conclusion_blocked_of_missing_premise d ruleAdminDefects
          (rule_horn_mem_general d ruleAdminDefects (by simp [familyRuleList]))
          matHearingMissed (by simp [ruleAdminDefects, LawRule.horn]) hmiss
          (by simp [allMaterialAtomList, familyMatoms]) adminDefectsEstablished
          (fun _ => rfl)
          (admin_missing_premise_check matHearingMissed
            (by simp [ruleAdminDefects, LawRule.horn])))
    · by_contra hm
      have hmiss : materialHolds matRecordContradictions d = false := by
        cases h9 : materialHolds matRecordContradictions d with
        | false => rfl
        | true => exact absurd h9 hm
      exact absurd hmem
        (conclusion_blocked_of_missing_premise d ruleAdminDefects
          (rule_horn_mem_general d ruleAdminDefects (by simp [familyRuleList]))
          matRecordContradictions (by simp [ruleAdminDefects, LawRule.horn]) hmiss
          (by simp [allMaterialAtomList, familyMatoms]) adminDefectsEstablished
          (fun _ => rfl)
          (admin_missing_premise_check matRecordContradictions
            (by simp [ruleAdminDefects, LawRule.horn])))
  · rintro ⟨h1, h2, h3⟩
    exact rule_fires_of_materials d ruleAdminDefects (by simp [familyRuleList]) (by
      intro p hp
      rcases Finset.mem_insert.mp hp with rfl | hp
      · exact h1
      rcases Finset.mem_insert.mp hp with rfl | hp
      · exact h2
      rcases Finset.mem_singleton.mp hp with rfl
      · exact h3)

/-- **L06 继承中止触发表（当且仅当）**：跨族链 R20/R21 的源头规则。 -/
theorem stayForSuccession_fires_iff (d : CaseDocket) :
    stayForSuccession ∈ closureAt (hornOf d) ↔
      (materialHolds matCDeathRecord d = true ∧
        materialHolds matHeirsNotYetJoined d = true) := by
  constructor
  · intro hmem
    refine ⟨?_, ?_⟩
    · by_contra hm
      have hmiss : materialHolds matCDeathRecord d = false := by
        cases h9 : materialHolds matCDeathRecord d with
        | false => rfl
        | true => exact absurd h9 hm
      exact absurd hmem
        (conclusion_blocked_of_missing_premise d ruleStaySuccession
          (rule_horn_mem_general d ruleStaySuccession (by simp [familyRuleList]))
          matCDeathRecord (by simp [ruleStaySuccession, LawRule.horn]) hmiss
          (by simp [allMaterialAtomList, familyMatoms]) stayForSuccession (fun _ => rfl)
          (stay_missing_premise_check matCDeathRecord
            (by simp [ruleStaySuccession, LawRule.horn])))
    · by_contra hm
      have hmiss : materialHolds matHeirsNotYetJoined d = false := by
        cases h9 : materialHolds matHeirsNotYetJoined d with
        | false => rfl
        | true => exact absurd h9 hm
      exact absurd hmem
        (conclusion_blocked_of_missing_premise d ruleStaySuccession
          (rule_horn_mem_general d ruleStaySuccession (by simp [familyRuleList]))
          matHeirsNotYetJoined (by simp [ruleStaySuccession, LawRule.horn]) hmiss
          (by simp [allMaterialAtomList, familyMatoms]) stayForSuccession (fun _ => rfl)
          (stay_missing_premise_check matHeirsNotYetJoined
            (by simp [ruleStaySuccession, LawRule.horn])))
  · rintro ⟨h1, h2⟩
    exact rule_fires_of_materials d ruleStaySuccession (by simp [familyRuleList]) (by
      intro p hp
      rcases Finset.mem_insert.mp hp with rfl | hp
      · exact h1
      rcases Finset.mem_singleton.mp hp with rfl
      · exact h2)

/-- L01 缺料分支的坏集：四份 L01 材料 + 只能由它们推出的三级结论。 -/
def badL01Absent : Finset Atom :=
  {matContractSigned, matBankSettlementMatched, matReconciliationUnpaid,
    matGuaranteeByGOpen, loanEntitlement, guarantorStanding,
    gEnforcementAfterExhaustion, mortgageSecuredPriority}

/-- 内核级全查：L01 缺料坏集的阻断表。 -/
theorem l01_absent_hblock_check :
    familyRuleList.all (fun r => !decide (r.horn.conclusion ∈ badL01Absent) ||
      !decide ((r.horn.premises ∩ badL01Absent) = ∅)) = true := by rfl

/-- L01 缺料坏集与初始事实不相交。 -/
theorem l01_absent_hdisj (d : CaseDocket) (habs : brIsAbsent Fam.L01Contract d) :
    Disjoint (hornOf d).initialFacts badL01Absent := by
  rw [Finset.disjoint_left]
  intro x hx hb
  have h1 : materialHolds x d = true := (Finset.mem_filter.mp hx).2
  rcases Finset.mem_insert.mp hb with rfl | hb
  · exact Bool.noConfusion
      ((habs matContractSigned (by simp [familyMatoms])).symm.trans h1)
  rcases Finset.mem_insert.mp hb with rfl | hb
  · exact Bool.noConfusion
      ((habs matBankSettlementMatched (by simp [familyMatoms])).symm.trans h1)
  rcases Finset.mem_insert.mp hb with rfl | hb
  · exact Bool.noConfusion
      ((habs matReconciliationUnpaid (by simp [familyMatoms])).symm.trans h1)
  rcases Finset.mem_insert.mp hb with rfl | hb
  · exact Bool.noConfusion
      ((habs matGuaranteeByGOpen (by simp [familyMatoms])).symm.trans h1)
  rcases Finset.mem_insert.mp hb with rfl | hb
  · have h0 : materialHolds loanEntitlement d = false := rfl
    rw [h0] at h1
    exact Bool.noConfusion h1
  rcases Finset.mem_insert.mp hb with rfl | hb
  · have h0 : materialHolds guarantorStanding d = false := rfl
    rw [h0] at h1
    exact Bool.noConfusion h1
  rcases Finset.mem_insert.mp hb with rfl | hb
  · have h0 : materialHolds gEnforcementAfterExhaustion d = false := rfl
    rw [h0] at h1
    exact Bool.noConfusion h1
  rcases Finset.mem_singleton.mp hb with rfl
  · have h0 : materialHolds mortgageSecuredPriority d = false := rfl
    rw [h0] at h1
    exact Bool.noConfusion h1

/-- **L01 缺料分支的下游排除**：借款债权与其上的抵押优先都不触发
    （R01/R02/R03/R04 四级连锁被四份缺失材料挡住）。 -/
theorem l01_absent_downstream (d : CaseDocket) (habs : brIsAbsent Fam.L01Contract d) :
    loanEntitlement ∉ closureAt (hornOf d) ∧
      mortgageSecuredPriority ∉ closureAt (hornOf d) := by
  have hmodel : isModel (hornOf d) (Finset.univ \ badL01Absent) := by
    refine isModel_avoiding_gen (hornOf d) badL01Absent (l01_absent_hdisj d habs) ?_
    intro rh hrh hcon
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hrh
    have hchk := List.all_eq_true.mp l01_absent_hblock_check r (List.mem_toFinset.mp hr)
    simp only [Bool.or_eq_true, not_decide_eq_true] at hchk
    rcases hchk with h9 | h9
    · exact absurd hcon h9
    · exact h9
  refine ⟨fun hmem => ?_, fun hmem => ?_⟩
  · obtain ⟨_, hnot⟩ := Finset.mem_sdiff.mp
      (closure_only_entailed (hornOf d) hmem (Finset.univ \ badL01Absent) hmodel)
    exact hnot (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
      (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
        (Finset.mem_insert_self loanEntitlement _)))))
  · obtain ⟨_, hnot⟩ := Finset.mem_sdiff.mp
      (closure_only_entailed (hornOf d) hmem (Finset.univ \ badL01Absent) hmodel)
    exact hnot (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
      (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
        (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
          (Finset.mem_singleton_self mortgageSecuredPriority))))))))

/-- **冲突排除的一般形**：对任一案卷，避开全部失败原子的全域是真模型
    （失败原子既非输入、也无规则以其为结论——内核级全查）。 -/
theorem failureish_model (d : CaseDocket) :
    isModel (hornOf d)
      (Finset.univ \ Finset.univ.filter (fun a => failureish a && !materialHolds a d)) := by
  refine isModel_avoiding_gen (hornOf d) _ ?_ ?_
  · rw [Finset.disjoint_left]
    intro x hx hb
    have h1 : materialHolds x d = true := (Finset.mem_filter.mp hx).2
    have h2 : (failureish x && !materialHolds x d) = true := (Finset.mem_filter.mp hb).2
    rw [h1] at h2
    simp at h2
  · intro rh hrh hcon
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hrh
    exfalso
    have h2 : (failureish r.horn.conclusion && !materialHolds r.horn.conclusion d) = true :=
      (Finset.mem_filter.mp hcon).2
    simp only [Bool.and_eq_true] at h2
    have hf : failureish r.horn.conclusion = true := h2.1
    have hnot : (!failureish r.horn.conclusion) = true :=
      List.all_eq_true.mp rule_concl_not_failureish r (List.mem_toFinset.mp hr)
    have hfalse : failureish r.horn.conclusion = false := by
      rw [← Bool.not_eq_true']
      exact hnot
    rw [hfalse] at hf
    exact Bool.noConfusion hf

/-- **任一冲突点在任一案卷不可推导**（分支枚举对开点的覆盖判据）。 -/
theorem failureish_not_closure_any (d : CaseDocket) (a : Atom)
    (hbad : (failureish a && !materialHolds a d) = true) :
    a ∉ closureAt (hornOf d) := by
  intro hmem
  obtain ⟨_, hnot⟩ := Finset.mem_sdiff.mp
    (closure_only_entailed (hornOf d) hmem
      (Finset.univ \ Finset.univ.filter (fun x => failureish x && !materialHolds x d))
      (failureish_model d))
  exact hnot (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hbad⟩)

/-- **L01 分支表**：触发表 + 缺料支排除（债权与抵押优先）+ 一致支触发。 -/
theorem loan_branch_table (d : CaseDocket) :
    (loanEntitlement ∈ closureAt (hornOf d) ↔
      (materialHolds matContractSigned d = true ∧
        materialHolds matBankSettlementMatched d = true ∧
        materialHolds matReconciliationUnpaid d = true)) ∧
    (brIsAbsent Fam.L01Contract d → loanEntitlement ∉ closureAt (hornOf d)) ∧
    (brIsConsistent Fam.L01Contract d → loanEntitlement ∈ closureAt (hornOf d)) ∧
    (brIsAbsent Fam.L01Contract d → mortgageSecuredPriority ∉ closureAt (hornOf d)) := by
  refine ⟨loanEntitlement_fires_iff d, ?_, ?_, fun habs =>
    (l01_absent_downstream d habs).2⟩
  · intro habs hmem
    obtain ⟨h1, _, _⟩ := (loanEntitlement_fires_iff d).mp hmem
    exact Bool.noConfusion
      ((habs matContractSigned (by simp [familyMatoms])).symm.trans h1)
  · intro hcon
    exact (loanEntitlement_fires_iff d).mpr
      ⟨hcon matContractSigned (by simp [familyMatoms]),
        hcon matBankSettlementMatched (by simp [familyMatoms]),
        hcon matReconciliationUnpaid (by simp [familyMatoms])⟩

/-- **L11 分支表**：触发表 + 缺料支排除 + 一致支触发 + 行政终局处分在任何分支
    都不自动触发（冲突排除的枚举读法：开点保持开放）。 -/
theorem admin_branch_table (d : CaseDocket) :
    (adminDefectsEstablished ∈ closureAt (hornOf d) ↔
      (materialHolds matPenaltyServedWithBasis d = true ∧
        materialHolds matHearingMissed d = true ∧
        materialHolds matRecordContradictions d = true)) ∧
    (brIsAbsent Fam.L11Admin d → adminDefectsEstablished ∉ closureAt (hornOf d)) ∧
    (brIsConsistent Fam.L11Admin d → adminDefectsEstablished ∈ closureAt (hornOf d)) ∧
    (adminFinalDisposition ∉ closureAt (hornOf d)) := by
  refine ⟨adminDefects_fires_iff d, ?_, ?_,
    failureish_not_closure_any d adminFinalDisposition rfl⟩
  · intro habs hmem
    obtain ⟨h1, _, _⟩ := (adminDefects_fires_iff d).mp hmem
    exact Bool.noConfusion
      ((habs matPenaltyServedWithBasis (by simp [familyMatoms])).symm.trans h1)
  · intro hcon
    exact (adminDefects_fires_iff d).mpr
      ⟨hcon matPenaltyServedWithBasis (by simp [familyMatoms]),
        hcon matHearingMissed (by simp [familyMatoms]),
        hcon matRecordContradictions (by simp [familyMatoms])⟩

/-- **L06 分支表**：触发表 + 缺料支排除 + 一致支触发 + 下游跨族链
    （继承中止 ⇒ L01 借款案依法暂缓终局，R19→R21）。 -/
theorem succession_branch_table (d : CaseDocket) :
    (stayForSuccession ∈ closureAt (hornOf d) ↔
      (materialHolds matCDeathRecord d = true ∧
        materialHolds matHeirsNotYetJoined d = true)) ∧
    (brIsAbsent Fam.L06FamilySuccession d → stayForSuccession ∉ closureAt (hornOf d)) ∧
    (brIsConsistent Fam.L06FamilySuccession d →
      stayForSuccession ∈ closureAt (hornOf d)) ∧
    (stayForSuccession ∈ closureAt (hornOf d) →
      holdOnLoanFinal ∈ closureAt (hornOf d)) := by
  refine ⟨stayForSuccession_fires_iff d, ?_, ?_, ?_⟩
  · intro habs hmem
    obtain ⟨h1, _⟩ := (stayForSuccession_fires_iff d).mp hmem
    exact Bool.noConfusion
      ((habs matCDeathRecord (by simp [familyMatoms])).symm.trans h1)
  · intro hcon
    exact (stayForSuccession_fires_iff d).mpr
      ⟨hcon matCDeathRecord (by simp [familyMatoms]),
        hcon matHeirsNotYetJoined (by simp [familyMatoms])⟩
  · intro hst
    exact memByRule_general d ruleHoldLoan (by simp [familyRuleList]) (fun p hp => by
      rcases Finset.mem_singleton.mp hp with rfl
      exact hst)

/-- 冲突点逐个（任一案卷）：L11 行政终局处分——故意开放的原子，任何分支保持开放。 -/
theorem adminFinalDisposition_not_closure_any (d : CaseDocket) :
    adminFinalDisposition ∉ closureAt (hornOf d) :=
  failureish_not_closure_any d adminFinalDisposition rfl

/-- 冲突点逐个（任一案卷）：L07 加班请求。 -/
theorem overtimeClaimEstablished_not_closure_any (d : CaseDocket) :
    overtimeClaimEstablished ∉ closureAt (hornOf d) :=
  failureish_not_closure_any d overtimeClaimEstablished rfl

/-- 冲突点逐个（任一案卷）：L04 新增/加重损害。 -/
theorem medicalAddedDamageAward_not_closure_any (d : CaseDocket) :
    medicalAddedDamageAward ∉ closureAt (hornOf d) :=
  failureish_not_closure_any d medicalAddedDamageAward rfl

/-- 冲突点逐个（任一案卷）：L06 H 共同债务。 -/
theorem spousalJointDebt_not_closure_any (d : CaseDocket) :
    spousalJointDebt ∉ closureAt (hornOf d) :=
  failureish_not_closure_any d spousalJointDebt rfl

/-- 冲突点逐个（任一案卷）：L09 惩罚性赔偿。 -/
theorem ipPunitiveDamages_not_closure_any (d : CaseDocket) :
    ipPunitiveDamages ∉ closureAt (hornOf d) :=
  failureish_not_closure_any d ipPunitiveDamages rfl

/-- 冲突点逐个（任一案卷）：L10 诈骗定罪。 -/
theorem fraudConviction_not_closure_any (d : CaseDocket) :
    fraudConviction ∉ closureAt (hornOf d) :=
  failureish_not_closure_any d fraudConviction rfl

/-- 冲突点逐个（任一案卷）：L12 远端利润。 -/
theorem remoteProfitAward_not_closure_any (d : CaseDocket) :
    remoteProfitAward ∉ closureAt (hornOf d) :=
  failureish_not_closure_any d remoteProfitAward rfl

/-- 冲突点逐个（任一案卷）：L08 人格否认。 -/
theorem corporateVeilPierced_not_closure_any (d : CaseDocket) :
    corporateVeilPierced ∉ closureAt (hornOf d) :=
  failureish_not_closure_any d corporateVeilPierced rfl

/-- 冲突点逐个（任一案卷）：L01 借款实体终局。 -/
theorem loanFinalDecree_not_closure_any (d : CaseDocket) :
    loanFinalDecree ∉ closureAt (hornOf d) :=
  failureish_not_closure_any d loanFinalDecree rfl

/-- 冲突点逐个（任一案卷）：L13 依赖他案的终局。 -/
theorem dependentClaimFinalDecree_not_closure_any (d : CaseDocket) :
    dependentClaimFinalDecree ∉ closureAt (hornOf d) :=
  failureish_not_closure_any d dependentClaimFinalDecree rfl

/-! ## 三、针 08：法律 Horn 实例化及来源树 -/

/-- 在卷材料进初始事实（LTagN/HProvN 叶节点共用）。 -/
theorem matInitEnt (a : Atom) (h : materialHolds a fullDocket = true) :
    a ∈ familyHorn.initialFacts :=
  Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩

/-- R07→R08→R10 链的法源侧引用函数：每条规则节点记自己的具名法源 + 前提材料。 -/
def ecoChildC (p : Atom) : Finset SrcId :=
  match p with
  | .publicInterestStanding =>
    insert (SrcId.statute LawSource.ecoCode147) {SrcId.mat matNQualified}
  | .ecoViolationEstablished =>
    insert (SrcId.statute LawSource.ecoCode1075_1081)
      {SrcId.mat matSamplingMatch, SrcId.mat matExceedance,
        SrcId.mat matNoExculpation, SrcId.mat matInNewLawPeriod}
  | p => {SrcId.mat p}

/-- R07→R08→R10 链的完整引用集（来源树的确切形状：3 条具名法源 + 6 份在卷材料）。 -/
def ecoCited : Finset SrcId :=
  insert (SrcId.statute LawSource.ecoCode1080)
    (ruleEcoRemediation.horn.premises.biUnion ecoChildC)

/-- R07→R08→R10 链的材料侧溯源函数：跨族派生前提各自携带其推导所用叶子材料
    （材料侧对偶于法源侧引用函数 `ecoChildC`；材料前提以自身为来源）。 -/
def ecoChildM (p : Atom) : Finset Atom :=
  match p with
  | .publicInterestStanding => rulePublicStanding.horn.premises.biUnion matSrcOf
  | .ecoViolationEstablished => ruleEcoViolation.horn.premises.biUnion matSrcOf
  | _ => matSrcOf p

/-- R10 结论的材料侧溯源集（消费 `matSrcOf`；经 `ecoChildM` 收全六份在卷叶子材料）。 -/
def ecoProvSet : Finset Atom :=
  ruleEcoRemediation.horn.premises.biUnion ecoChildM

/-- **旗舰推导树（材料侧）**：`ecoRemediationCosts` 的高度 3 带来源 HProvN 推导
    （R10 顶节点，R07/R08 中间节点，6 份在卷材料为叶）。 -/
theorem ecoRemediationCosts_prov :
    HProvN familyHorn Atom matSrcOf 3 ecoProvSet ecoRemediationCosts := by
  refine HProvN.rule 2 ruleEcoRemediation.horn
    (rule_horn_mem ruleEcoRemediation (by simp [familyRuleList])) ecoChildM ?_
  intro p hp
  rcases Finset.mem_insert.mp hp with rfl | hp
  · exact HProvN.fact 2 matEcoCostDocs (matInitEnt _ rfl)
  rcases Finset.mem_insert.mp hp with rfl | hp
  · refine HProvN.rule 1 rulePublicStanding.horn
      (rule_horn_mem rulePublicStanding (by simp [familyRuleList])) matSrcOf ?_
    intro q hq
    rcases Finset.mem_singleton.mp hq with rfl
    exact HProvN.fact 1 matNQualified (matInitEnt _ rfl)
  rcases Finset.mem_singleton.mp hp with rfl
  · refine HProvN.rule 1 ruleEcoViolation.horn
      (rule_horn_mem ruleEcoViolation (by simp [familyRuleList])) matSrcOf ?_
    intro q hq
    rcases Finset.mem_insert.mp hq with rfl | hq
    · exact HProvN.fact 1 matSamplingMatch (matInitEnt _ rfl)
    rcases Finset.mem_insert.mp hq with rfl | hq
    · exact HProvN.fact 1 matExceedance (matInitEnt _ rfl)
    rcases Finset.mem_insert.mp hq with rfl | hq
    · exact HProvN.fact 1 matNoExculpation (matInitEnt _ rfl)
    rcases Finset.mem_singleton.mp hq with rfl
    · exact HProvN.fact 1 matInNewLawPeriod (matInitEnt _ rfl)

/-- **旗舰来源树（法源侧）**：`ecoRemediationCosts` 的高度 2 LTagN 树，
    引用集恰为 `ecoCited`（3 条具名法源 + 6 份在卷材料）。 -/
theorem ecoRemediationCosts_ltag : LTagN 2 ecoCited ecoRemediationCosts := by
  refine LTagN.rule 1 ruleEcoRemediation (by simp [familyRuleList]) ecoChildC ?_
  intro p hp
  rcases Finset.mem_insert.mp hp with rfl | hp
  · exact LTagN.fact 1 matEcoCostDocs (matInitEnt _ rfl)
  rcases Finset.mem_insert.mp hp with rfl | hp
  · refine LTagN.rule 0 rulePublicStanding (by simp [familyRuleList])
      (fun q => {SrcId.mat q}) ?_
    intro q hq
    rcases Finset.mem_singleton.mp hq with rfl
    exact LTagN.fact 0 matNQualified (matInitEnt _ rfl)
  rcases Finset.mem_singleton.mp hp with rfl
  · refine LTagN.rule 0 ruleEcoViolation (by simp [familyRuleList])
      (fun q => {SrcId.mat q}) ?_
    intro q hq
    rcases Finset.mem_insert.mp hq with rfl | hq
    · exact LTagN.fact 0 matSamplingMatch (matInitEnt _ rfl)
    rcases Finset.mem_insert.mp hq with rfl | hq
    · exact LTagN.fact 0 matExceedance (matInitEnt _ rfl)
    rcases Finset.mem_insert.mp hq with rfl | hq
    · exact LTagN.fact 0 matNoExculpation (matInitEnt _ rfl)
    rcases Finset.mem_singleton.mp hq with rfl
    · exact LTagN.fact 0 matInNewLawPeriod (matInitEnt _ rfl)

/-- 材料侧溯源健全的旗舰实例化：推导引用的每个来源都追到已声明在卷材料。 -/
theorem eco_prov_trace (s : Atom) (hs : s ∈ ecoProvSet) :
    ∃ b : Atom, b ∈ familyHorn.initialFacts ∧ s ∈ matSrcOf b :=
  hprovN_prov_sound familyHorn Atom matSrcOf 3 ecoProvSet ecoRemediationCosts
    ecoRemediationCosts_prov s hs

/-- 法源侧叶完备的旗舰实例化：来源树引用的每个来源要么是已声明在卷材料、
    要么是规则表内某条规则的具名法源。 -/
theorem eco_sources_declared (s : SrcId) (hs : s ∈ ecoCited) :
    (∃ b : Atom, b ∈ familyHorn.initialFacts ∧ s = SrcId.mat b) ∨
      (∃ r : LawRule, r ∈ familyRuleList ∧ s = SrcId.statute r.src) :=
  ltagN_declared 2 ecoCited ecoRemediationCosts ecoRemediationCosts_ltag s hs

/-- 引用集非空且两侧各有实员（防 declared/trace 空洞为真）。 -/
theorem eco_cited_nonempty :
    SrcId.statute LawSource.ecoCode1080 ∈ ecoCited ∧
      SrcId.statute LawSource.ecoCode147 ∈ ecoCited ∧
      SrcId.statute LawSource.ecoCode1075_1081 ∈ ecoCited ∧
      SrcId.mat matEcoCostDocs ∈ ecoCited ∧
      SrcId.mat matNQualified ∈ ecoCited := by
  refine ⟨Finset.mem_insert_self _ _, ?_, ?_, ?_, ?_⟩
  · refine Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr
      ⟨publicInterestStanding, (by simp [ruleEcoRemediation, LawRule.horn]), ?_⟩)
    simp only [ecoChildC]
    exact Finset.mem_insert_self _ _
  · refine Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr
      ⟨ecoViolationEstablished, (by simp [ruleEcoRemediation, LawRule.horn]), ?_⟩)
    simp only [ecoChildC]
    exact Finset.mem_insert_self _ _
  · refine Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr
      ⟨matEcoCostDocs, (by simp [ruleEcoRemediation, LawRule.horn]), ?_⟩)
    simp only [ecoChildC]
    exact Finset.mem_singleton_self _
  · refine Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr
      ⟨publicInterestStanding, (by simp [ruleEcoRemediation, LawRule.horn]), ?_⟩)
    simp only [ecoChildC]
    exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)

/-- **实例化健全**：旗舰树的每一步都是规则表内的具名法源规则，且全部法源
    在效力窗口内（内核级全查复用）。 -/
theorem eco_prov_steps_named :
    ruleEcoRemediation ∈ familyRuleList ∧
      rulePublicStanding ∈ familyRuleList ∧ ruleEcoViolation ∈ familyRuleList ∧
      (ruleEcoRemediation.src = LawSource.ecoCode1080 ∧
        rulePublicStanding.src = LawSource.ecoCode147 ∧
        ruleEcoViolation.src = LawSource.ecoCode1075_1081) ∧
      (familyRuleList.all (fun r => srcInForce r.src) = true) :=
  ⟨by simp [familyRuleList], by simp [familyRuleList], by simp [familyRuleList],
    ⟨rfl, rfl, rfl⟩, all_rules_sources_in_force⟩

/-- **与 LTagN 法源树一致（一般形）**：同一原子的任何 HProvN 推导树与任何
    LTagN 来源树，结论同进 Horn 闭包，且两侧引用集全部落在已声明在卷材料或
    规则表具名法源上——两套树形对同一结论给出一致的来源报告。 -/
theorem horn_ltag_consistency (n₁ n₂ : ℕ) (P : Finset Atom) (C : Finset SrcId) (a : Atom)
    (h₁ : HProvN familyHorn Atom matSrcOf n₁ P a) (h₂ : LTagN n₂ C a) :
    a ∈ closureAt familyHorn ∧
      (∀ s ∈ P, ∃ b : Atom, b ∈ familyHorn.initialFacts ∧ s ∈ matSrcOf b) ∧
      (∀ s ∈ C, (∃ b : Atom, b ∈ familyHorn.initialFacts ∧ s = SrcId.mat b) ∨
        (∃ r : LawRule, r ∈ familyRuleList ∧ s = SrcId.statute r.src)) :=
  ⟨family_horn_deriv_sound n₁ P a h₁, family_prov_sound n₁ P a h₁,
    ltagN_declared n₂ C a h₂⟩

/-- **实例化健全（一般形）**：任何 HProvN 推导树的叶子要么是初始事实，
    要么其结论恰是规则表内某条规则的结论——推导树不发明规则。 -/
theorem hprovN_lands_on_table_or_fact (n : ℕ) (P : Finset Atom) (a : Atom)
    (h : HProvN familyHorn Atom matSrcOf n P a) :
    (∃ r : LawRule, r ∈ familyRuleList ∧ r.horn.conclusion = a) ∨
      a ∈ familyHorn.initialFacts := by
  cases h with
  | fact _ b hb => exact Or.inr hb
  | rule _ rh hr _ _ =>
      obtain ⟨r₀, hr₂, rfl⟩ := Finset.mem_image.mp hr
      exact Or.inl ⟨r₀, List.mem_toFinset.mp hr₂, rfl⟩

/-- 满料见证案上 R07→R08→R10 链的六份叶子材料确实全部在卷（逐字面求值）。 -/
theorem eco_leaf_materials_on_file :
    materialHolds matEcoCostDocs fullDocket = true ∧
      materialHolds matNQualified fullDocket = true ∧
      materialHolds matSamplingMatch fullDocket = true ∧
      materialHolds matExceedance fullDocket = true ∧
      materialHolds matNoExculpation fullDocket = true ∧
      materialHolds matInNewLawPeriod fullDocket = true :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- R10 材料侧溯源集非空且含公益费用材料。 -/
theorem matEcoCostDocs_mem_ecoProvSet : matEcoCostDocs ∈ ecoProvSet := by
  refine Finset.mem_biUnion.mpr ⟨matEcoCostDocs,
    (by simp [ruleEcoRemediation, LawRule.horn]), ?_⟩
  simp only [ecoChildM]
  rw [matSrcOf_self matEcoCostDocs rfl]
  exact Finset.mem_singleton_self _

/-- **针 08 旗舰（法律 Horn 实例化及来源树端到端；附录I:762 另接交付）**：
    满料见证案 → 指定结论（`ecoRemediationCosts`，R07→R08→R10 跨族链）→
    完整来源树：材料侧 HProvN 高度 3 推导树（叶全落已声明在卷材料）+ 法源侧
    LTagN 高度 2 来源树（叶全落已声明材料或具名法源），三步均为规则表内
    具名且在效力窗口内的法源规则，并附两树对任意原子的一致性条款。 -/
theorem legal_horn_instantiation_end_to_end :
    (materialHolds matEcoCostDocs fullDocket = true ∧
      materialHolds matNQualified fullDocket = true ∧
      materialHolds matSamplingMatch fullDocket = true ∧
      materialHolds matExceedance fullDocket = true ∧
      materialHolds matNoExculpation fullDocket = true ∧
      materialHolds matInNewLawPeriod fullDocket = true) ∧
    ecoRemediationCosts ∈ closureAt familyHorn ∧
    (HProvN familyHorn Atom matSrcOf 3 ecoProvSet ecoRemediationCosts ∧
      (∀ s ∈ ecoProvSet, ∃ b : Atom, b ∈ familyHorn.initialFacts ∧ s ∈ matSrcOf b) ∧
      matEcoCostDocs ∈ ecoProvSet) ∧
    (LTagN 2 ecoCited ecoRemediationCosts ∧
      (∀ s ∈ ecoCited, (∃ b : Atom, b ∈ familyHorn.initialFacts ∧ s = SrcId.mat b) ∨
        (∃ r : LawRule, r ∈ familyRuleList ∧ s = SrcId.statute r.src)) ∧
      (SrcId.statute LawSource.ecoCode1080 ∈ ecoCited ∧
        SrcId.statute LawSource.ecoCode147 ∈ ecoCited ∧
        SrcId.statute LawSource.ecoCode1075_1081 ∈ ecoCited ∧
        SrcId.mat matEcoCostDocs ∈ ecoCited ∧
        SrcId.mat matNQualified ∈ ecoCited)) ∧
    (ruleEcoRemediation ∈ familyRuleList ∧
      rulePublicStanding ∈ familyRuleList ∧ ruleEcoViolation ∈ familyRuleList ∧
      (ruleEcoRemediation.src = LawSource.ecoCode1080 ∧
        rulePublicStanding.src = LawSource.ecoCode147 ∧
        ruleEcoViolation.src = LawSource.ecoCode1075_1081) ∧
      (familyRuleList.all (fun r => srcInForce r.src) = true)) ∧
    (∀ (n₁ n₂ : ℕ) (P : Finset Atom) (C : Finset SrcId) (a : Atom),
      HProvN familyHorn Atom matSrcOf n₁ P a → LTagN n₂ C a →
        a ∈ closureAt familyHorn ∧
        (∀ s ∈ P, ∃ b : Atom, b ∈ familyHorn.initialFacts ∧ s ∈ matSrcOf b) ∧
        (∀ s ∈ C, (∃ b : Atom, b ∈ familyHorn.initialFacts ∧ s = SrcId.mat b) ∨
          (∃ r : LawRule, r ∈ familyRuleList ∧ s = SrcId.statute r.src))) :=
  ⟨eco_leaf_materials_on_file, ecoRemediationCosts_mem,
    ⟨ecoRemediationCosts_prov, eco_prov_trace, matEcoCostDocs_mem_ecoProvSet⟩,
    ⟨ecoRemediationCosts_ltag, eco_sources_declared, eco_cited_nonempty⟩,
    eco_prov_steps_named, fun n₁ n₂ P C a h₁ h₂ => horn_ltag_consistency n₁ n₂ P C a h₁ h₂⟩

end JurisLean.Seams.UnifiedNeedlesGap05
