import Mathlib.Tactic
import JurisLean.Seams.SourceNorms
import JurisLean.Seams.UnifiedHornIT

/-!
十四族（L01–L14）实际材料与规则网络基础——把 `UnifiedNeedlesS0S1.lean` 的
三值状态载荷（其头注 :87 自认"每族载荷是三值状态，不是各族完整材料内容"）
升级为逐族实际材料载体 + 具名法源规则网络 + 溯源健全 + 四态联合输出。

出处：`docs/master-plan/20261010_统一法律数学模型_连续与语义全量施工方案.md` W1-3/W1-6 行
（评审第 2 条）；原合同权威为
`docs/spec/20261007-统一法律数学模型_全量施工方案.md` §10.2（:653–730，
尤其 :692"把这张表的实际材料和规则逐项实例化……不能只编造十四个标签或预填
十四个胜诉位"与 :713 制度前提与来源保留要求）。

## 一、法律语义（人话）

合同 §10.2.1/§10.2.2 给出一张合成制度网络的表：十四族争点共用同一批主体
（D/G/H/C/C1/C2/W/M/P/N/A/Q 及法院/执行机关）、同一批量（借款本金 P0、
到期工资 w、抵押净实现值 b、其余净财产 a，且保留 `a+b<P0+w` 的全允许集合，
不发明唯一系数）与各自独立的程序记录（法域/管辖/审级/送达/阶段——
不能有一个全网共用的 `stage=民事终审`）。每族的实际材料逐字段照表编码；
跨族规则只按表内实际关系接线（N 公益资格 L14→L05、破产受理 L08→L02/L07/L14、
继承中止 L06→L01/L13 等），不虚构。每个规则结论都带具名法源标签
（法源/条款/版本/效力时段按合同 :713 字段保留）。

法律输出不是布尔：本件按合同 :692 的四态联合输出编码——
明确成立（established，由 Horn 规则链**推导**入闭包）、未成立（notEstablished，
基于证明不足的不可推导，用显式模型见证，**不是** Established(¬p)）、
依法暂未决（pendingByLaw，程序中止原子在闭包而终局原子不在）、
过程效力与不足清偿（procedural 原子在闭包 + 净未偿额>0 的量层定理）。

## 二、数学对象

- 族与主体：`Fam`（L01–L14 枚举，`famToFin` 注入为针 05 消费面）、`Party`（主体枚举）。
- 共享量：`SharedQuantities`（P0/w/b/a + 正性与 `a+b<P0+w`、`b≤P0` 假设字段——
  数值保留全允许集合）；`shortfall_positive`/`no_double_debt` 为量层一般定理；
  `witnessQty` 只按表取 (100,10,20,10) 一个具体点。
- 程序记录：`Forum/TrialLevel/ProcStage/ProcRecord`；`fullProc` 每族各表；
  `witness_stages_not_shared` 证阶段不共用。
- 材料：`Fam01Mats`…`Fam14Mats` 逐字段照 §10.2.2 表（主体列表 + 在卷材料 Bool）；
  `CaseDocket` 装共享量、程序记录与十四族材料；`fullDocket` 为满料见证案。
- 原子与法源：`Atom`（57 个材料原子 + 29 个推导原子 + 10 个失败原子，全平铺）；
  `LawSource` 22 个具名法源 + `srcTag`（法源/条款/版本/效力窗口）+ `srcInForce`；
  `materialHolds`（材料原子→案卷 Bool 的求值桥）、`failureish`（失败原子标记）。
- 规则网络：`LawRule`（前提 Finset + 结论 + 具名法源）；`familyRuleList` 29 条；
  `hornOf`（任一案卷 → Horn 制度网络）与 `familyHorn`（满料见证案实例）。
- 溯源：材料侧**消费** `UnifiedHornIT.hprovN_prov_sound/hprovN_mem_closure`
  （`matSrcOf` 把在卷材料自身声明为来源；`loanEntitlement_prov` 是显式推导树，
  `loan_sources_trace` 证引用来源必追到已声明在卷材料）；规则侧**镜像**同一模式：
  `LTagN` 高度索引来源树推导，`ltagN_declared`（引用的来源要么是已声明在卷材料、
  要么是某条规则的具名法源——推导不能发明来源）与 `ltagN_mem_closure`（桥回 Horn 闭包）。
- 四态联合输出：`JointState`、`WitnessJointOutput`、四个具名输出清单、
  `witnessOutput` 与完整求值定理 `witness_joint_evaluation`。

## 三、Scope, honestly

**证**：上面全部定理，零 sorry/零自定义 axiom/零 True 逃避。其中"明确成立"
全部经规则链推导（`memByRule`，前提逐一在闭包内被检查）；"未成立"由显式模型
见证（`witness_model`：闭包含于任何避开失败原子的模型）——失败原子既不是初始
事实、也没有任何规则以它为结论（`rule_concl_not_failureish` 对 29 条规则表做
内核级全查），故其不可推导是被证明的语义事实，不是预填 False。
**不证/开放**（如实列出）：
- 针 05 的"全域见证"（以本网络为第一层替换 Fin 2 旧引理的总入口）在后续波收；
  本件交出 `Fam`/`famToFin` 注入、`familyWitness`+`witness_completeness_ok` 完整性。
- 针 42 非空轨迹：事件偏序由 `fullProc`/`ProcStage` 数据给出，`ℕ → State` 轨迹
  构造不在本件。
- 针 06 冲突排除分支枚举：行政终局处分原子 `adminFinalDisposition` **故意**没有任何
  规则以它为结论（`witness_admin_branch_open` 只证它当前不可推导）——分支枚举接口
  留给后续波，本件不预填任何一种终局处分。
- 针 08 法律 Horn 实例化及来源树：`LTagN`/`ltagN_declared`/`ltagN_mem_closure` 是
  来源树种子；`ltagN ↔ 语义后承` 的双侧桥、缺版本/真实冲突的分别报告不在本件。
- 例外/阻却槽（可废止）不在 Horn 片段内（`SourceNorms.lean` 头注已声明）；
  "未成立"的拒绝理由原子（Established(¬p) 侧）不建模。
- 各族数值只经 `SharedQuantities` 进规则；fish/eco 等不同损害账的分账细则在 doc 层，
  不另建量账类型。
- 合成边界（合同 :655 原话）：本网络**不是十四族的范围替代物，更不是现实个案结论**；
  时间/版本窗口为合成登记值（合同 :713 要求的字段载体），不构成对真实条文效力
  时点的认定。最终裁判不被外包成布尔输入：`CaseDocket` 无任何胜负字段，
  且 `witness_entitlement_not_finality` 证债权成立与终局裁判在网络中分离。

## 四、档位

全部定理 [已证，认定待 CI]；本机不编译 Lean，CI 是唯一 Lean 权威，当前
CI_NOT_RUN（fail-closed）。`decide` 只用于 Bool/Nat/枚举的闭式归约；
`rfl` 只用于本件内可定义展开的闭式计算；量层用 `linarith`/`ring`，不碰 Rat decide。
-/

namespace JurisLean.Seams.UnifiedFourteenFamilies

open JurisLean.Seams.SourceNorms
open JurisLean.Seams.UnifiedHornIT

/-! ## 一、十四族标签与主体（针 05 消费面：`Fam` → `Fin 14` 注入） -/

/-- 十四族整理标签（合同 §10.2.2 表行序 L01–L14；标签是整理索引，不是法律理论层数）。 -/
inductive Fam where
  | L01Contract
  | L02Property
  | L03Tort
  | L04Medical
  | L05Environment
  | L06FamilySuccession
  | L07Labor
  | L08CorporateBankruptcy
  | L09Ip
  | L10Criminal
  | L11Admin
  | L12ReviewCompensation
  | L13ProcedureExecutionRemedy
  | L14ArbitrationMaritimePublic
deriving DecidableEq

/-- 族索引注入（针 05 的 `familyNet : Fin 14` 消费面）：表行序号。 -/
def famToFin : Fam → Fin 14
  | .L01Contract => ⟨0, by decide⟩
  | .L02Property => ⟨1, by decide⟩
  | .L03Tort => ⟨2, by decide⟩
  | .L04Medical => ⟨3, by decide⟩
  | .L05Environment => ⟨4, by decide⟩
  | .L06FamilySuccession => ⟨5, by decide⟩
  | .L07Labor => ⟨6, by decide⟩
  | .L08CorporateBankruptcy => ⟨7, by decide⟩
  | .L09Ip => ⟨8, by decide⟩
  | .L10Criminal => ⟨9, by decide⟩
  | .L11Admin => ⟨10, by decide⟩
  | .L12ReviewCompensation => ⟨11, by decide⟩
  | .L13ProcedureExecutionRemedy => ⟨12, by decide⟩
  | .L14ArbitrationMaritimePublic => ⟨13, by decide⟩

/-- `famToFin` 注入：不同族映射到不同表行（经构造逐对判定）。 -/
theorem famToFin_injective {f₁ f₂ : Fam} (h : famToFin f₁ = famToFin f₂) : f₁ = f₂ := by
  cases f₁ <;> cases f₂ <;>
    simp only [famToFin, Fin.mk.injEq] at h <;> first | rfl | exact absurd h (by omega)

/-- 合成网络的主体枚举（合同 §10.2.1：D/G/H/C/C1/C2/W/M/P/N/A/Q 及法院、执行机关、公诉方）。 -/
inductive Party where
  | debtorD
  | guarantorG
  | spouseH
  | lenderC
  | heirC1
  | heirC2
  | employeeW
  | medicalM
  | copyrightP
  | envOrgN
  | adminA
  | reviewQ
  | courtJ
  | execX
  | prosecutor
deriving DecidableEq

/-! ## 二、共享量表（全允许集合，不发明唯一系数；合同 §10.2.1） -/

/-- 同一借款 `loan`、到期工资 `wage`、抵押净实现值、其余净财产——数值字段 +
    合同允许集合假设（正数且 `a+b<P0+w`；`b≤P0` 是"受担保部分不得超本金、
    不把本金扩成两份债务"的量层表达）。改任意正数并保持假设仍是见证。 -/
structure SharedQuantities where
  loanPrincipal : ℚ
  provenDueWage : ℚ
  collateralNet : ℚ
  otherNetAssets : ℚ
  hP0 : 0 < loanPrincipal
  hw : 0 < provenDueWage
  hb : 0 < collateralNet
  ha : 0 < otherNetAssets
  hb_le : collateralNet ≤ loanPrincipal
  hshort : collateralNet + otherNetAssets < loanPrincipal + provenDueWage

/-- **不足清偿**（一般形）：`a+b<P0+w` ⇒ 未受偿额 `P0+w-(a+b)>0`。
    金额不足保留未受偿，不是全额支付模型。 -/
theorem shortfall_positive (q : SharedQuantities) :
    0 < q.loanPrincipal + q.provenDueWage - (q.collateralNet + q.otherNetAssets) := by
  have h := q.hshort
  linarith

/-- **同一担保余额、不扩成两份债务**（一般形）：受担保部分 + 未受担保部分 = 本金
    （合同 §10.2.3 检查 2；§10.2.2 PROPERTY 行 109–110 条）。 -/
theorem no_double_debt (q : SharedQuantities) :
    q.collateralNet + (q.loanPrincipal - q.collateralNet) = q.loanPrincipal := by
  ring

/-- 见证案共享量：按表取 P0=100、w=10、b=20、a=10（允许集合内一个具体点）。 -/
def witnessQty : SharedQuantities where
  loanPrincipal := 100
  provenDueWage := 10
  collateralNet := 20
  otherNetAssets := 10
  hP0 := by norm_num
  hw := by norm_num
  hb := by norm_num
  ha := by norm_num
  hb_le := by norm_num
  hshort := by norm_num

/-! ## 三、程序记录（每程序独立的法域/管辖/审级/送达/阶段；合同 §10.2.1） -/

/-- 程序法域：民事/刑事/行政/海商仲裁/劳动仲裁/破产。 -/
inductive Forum where
  | civil
  | criminal
  | administrative
  | arbitrationMaritime
  | laborArbitration
  | bankruptcy
deriving DecidableEq

/-- 审级/程序层级：一审/二审/再审/仲裁/劳动仲裁/行政复议/破产受理。 -/
inductive TrialLevel where
  | firstInstance
  | secondInstance
  | retrial
  | arbitration
  | laborArbitration
  | adminReview
  | bankruptcyAcceptance
deriving DecidableEq

/-- 阶段：立案/审理中/已决/执行中/依法中止/受理审查。 -/
inductive ProcStage where
  | filing
  | trialPending
  | decided
  | executing
  | stayed
  | acceptancePending
deriving DecidableEq

/-- 单个程序的记录：法域 + 管辖案号 + 审级 + 送达 + 阶段。
    每个程序各持一份（`CaseDocket.procOf : Fam → ProcRecord`），
    不存在全网共用的 stage。 -/
structure ProcRecord where
  forum : Forum
  docketNo : Nat
  level : TrialLevel
  served : Bool
  stage : ProcStage
deriving DecidableEq

/-! ## 四、逐族实际材料载体（字段照 §10.2.2 表；主体列表 + 在卷材料 Bool） -/

/-- L01 CONTRACT：C/D 已核身份签署的借款与还款日；银行最终结算和同期收款确认
    同号同额；到期后对账无清偿条目且 D 有明确未付陈述；G 另签一般保证且
    保证期间未届满。 -/
structure Fam01Mats where
  parties : List Party
  contractSigned : Bool
  bankSettlementMatched : Bool
  reconciliationUnpaid : Bool
  guaranteeByGOpen : Bool

/-- L02 PROPERTY：B 登记簿显示 D 所有；C 抵押登记及其范围；其他资产各有权属资料；
    有实际变价记录 b。 -/
structure Fam02Mats where
  parties : List Party
  registryD : Bool
  mortgageRegistered : Bool
  otherTitles : Bool
  realizationRecord : Bool

/-- L03 TORT：D 雇员依工作指令装卸碰坏 W 私车；连续原始录像、车辆登记、修理单
    互证；该请求不是 W 工作人身伤害请求。 -/
structure Fam03Mats where
  parties : List Party
  workInstruction : Bool
  damageCorroboration : Bool
  notWorkInjury : Bool

/-- L04 MEDICAL：W 曾在 M 接受诊疗；M 控制且无正当理由不提供诊疗记录；
    独立治疗前/后检查显示所主张损害此前已有（新增/加重缺少积极连接的在卷记载）。 -/
structure Fam04Mats where
  parties : List Party
  treatmentAtM : Bool
  recordsWithheld : Bool
  preExistingChecks : Bool

/-- L05 ENVIRONMENT：排放口/采样时间/实测浓度对应可适用限值；超出限值的实测比较
    在卷；W 鱼塘损害与 N 公共生态损害各有检测与费用材料；D 未提出免责或无因果
    具体证据；行为在新法适用期间。 -/
structure Fam05Mats where
  parties : List Party
  samplingMatch : Bool
  exceedance : Bool
  pondTesting : Bool
  ecoCostDocs : Bool
  noExculpation : Bool
  inNewLawPeriod : Bool

/-- L06 FAMILY_SUCCESSION：G/H 婚姻登记；保证文书只有 G 签、资金指向 D 独立经营
    且无 H 追认/共同意思/家庭日常需要材料；C 死亡材料在卷；C1/C2 身份材料在卷；
    是否参加诉讼尚待表明。 -/
structure Fam06Mats where
  parties : List Party
  marriageRegistered : Bool
  noSpousalJointBasis : Bool
  cDeathRecord : Bool
  heirIdentityOnFile : Bool
  heirsNotYetJoined : Bool

/-- L07 LABOR：劳动合同、在岗记录、欠薪对账支持 w；加班主张无任何存在加班事实的
    具体材料，且未先证明 D 掌握记录而拒不提供（材料在卷记载这一状态）。 -/
structure Fam07Mats where
  parties : List Party
  wageBasisOnFile : Bool
  overtimeUnsupported : Bool

/-- L08 CORPORATE_BANKRUPTCY：G 提交 D/G 分立账户、财产清单、不混同记录；
    D 到期债务/现金不足/资产材料呈现在破产申请中；有权法院已作出受理决定。 -/
structure Fam08Mats where
  parties : List Party
  separateAccounts : Bool
  insolvencyShown : Bool
  acceptanceDecided : Bool

/-- L09 IP：P 作品创作与权利来源链；D 授权合同终期；期满后复制/使用、范围与损害
    记录；无故意且情节严重的充分材料（在卷记载这一状态）。 -/
structure Fam09Mats where
  parties : List Party
  creationChain : Bool
  licenseExpired : Bool
  postTermUse : Bool
  noWillfulnessGravity : Bool

/-- L10 CRIMINAL：银行和合同足以证明取得借款；故意部分只有供述；材料显示真实
    业务采购及随后经营失败；法定审理程序完成。 -/
structure Fam10Mats where
  parties : List Party
  loanAcquisitionProven : Bool
  intentOnlyConfession : Bool
  genuineBusinessShown : Bool
  criminalTrialDone : Bool

/-- L11 ADMIN：A 对 D 作出并送达处罚决定、有真实权限与法律类型依据；卷中有具体
    事实/程序违法争议；听证请求于告知后五日内提出而未组织；决定所据记录有实质矛盾。 -/
structure Fam11Mats where
  parties : List Party
  penaltyServedWithBasis : Bool
  factualDisputes : Bool
  hearingMissed : Bool
  recordContradictions : Bool

/-- L12 REVIEW_COMPENSATION：A 扣押 X；D 在法定期间向 Q 申请复议；扣押/保管/返还
    记录及 X 保管损坏修理费可核；远端商业机会利润主张无直接损失与因果材料；
    与在审处罚不同一行政行为。 -/
structure Fam12Mats where
  parties : List Party
  detentionX : Bool
  reviewFiledInTime : Bool
  returnDamageRecords : Bool
  remoteProfitUnsupported : Bool
  differentAct : Bool

/-- L13 PROCEDURE_EXECUTION_REMEDY：送达/申请/中止等事件均保留；W 车损前裁判及
    实际执行记录在卷；该裁判有具名事实/适法错误且仍有效；另有一依法须以他案
    结果为依据的请求在卷、他案尚未审结（合同 §10.2 叙事：民诉 153(5) 见证）。 -/
structure Fam13Mats where
  parties : List Party
  stayEventsKept : Bool
  priorCarJudgment : Bool
  namedErrorAlleged : Bool
  dependentClaimFiled : Bool
  priorCaseUnconcluded : Bool

/-- L14 ARBITRATION_MARITIME_PUBLIC：M/D 书面国内海运合同及有效商事仲裁约定；
    货物为 M 所有、收取运费、装箱承运；装卸记录显示保管期间损坏；其他原因及
    减免各有材料；N 的设区市以上民政登记、连续五年环保公益且无违法记录有证明。 -/
structure Fam14Mats where
  parties : List Party
  maritimeContractWithClause : Bool
  carrierCustody : Bool
  cargoDamage : Bool
  exemptionMaterials : Bool
  nQualified : Bool

/-- 联合案卷：共享量 + 每族独立程序记录 + 十四族实际材料。
    结构上没有任何"最终裁判/胜负"输入字段（红线：不把最终裁判外包成布尔输入）。 -/
structure CaseDocket where
  qty : SharedQuantities
  procOf : Fam → ProcRecord
  m01 : Fam01Mats
  m02 : Fam02Mats
  m03 : Fam03Mats
  m04 : Fam04Mats
  m05 : Fam05Mats
  m06 : Fam06Mats
  m07 : Fam07Mats
  m08 : Fam08Mats
  m09 : Fam09Mats
  m10 : Fam10Mats
  m11 : Fam11Mats
  m12 : Fam12Mats
  m13 : Fam13Mats
  m14 : Fam14Mats

/-- 见证案逐族程序记录（阶段各不相同：中止/执行/审理/已决/立案/受理审查并存，
    没有"全网共用 stage=民事终审"）。案号为合成登记值。 -/
def fullProc : Fam → ProcRecord :=
  fun f =>
    match f with
    | .L01Contract => ⟨Forum.civil, 101, TrialLevel.firstInstance, true, ProcStage.stayed⟩
    | .L02Property => ⟨Forum.civil, 102, TrialLevel.firstInstance, true, ProcStage.executing⟩
    | .L03Tort => ⟨Forum.civil, 103, TrialLevel.firstInstance, true, ProcStage.executing⟩
    | .L04Medical => ⟨Forum.civil, 104, TrialLevel.firstInstance, true, ProcStage.trialPending⟩
    | .L05Environment => ⟨Forum.civil, 105, TrialLevel.firstInstance, true, ProcStage.trialPending⟩
    | .L06FamilySuccession => ⟨Forum.civil, 106, TrialLevel.firstInstance, true, ProcStage.stayed⟩
    | .L07Labor => ⟨Forum.laborArbitration, 107, TrialLevel.laborArbitration, true, ProcStage.decided⟩
    | .L08CorporateBankruptcy => ⟨Forum.bankruptcy, 108, TrialLevel.bankruptcyAcceptance, true, ProcStage.decided⟩
    | .L09Ip => ⟨Forum.civil, 109, TrialLevel.firstInstance, true, ProcStage.trialPending⟩
    | .L10Criminal => ⟨Forum.criminal, 110, TrialLevel.firstInstance, true, ProcStage.decided⟩
    | .L11Admin => ⟨Forum.administrative, 111, TrialLevel.firstInstance, true, ProcStage.trialPending⟩
    | .L12ReviewCompensation => ⟨Forum.administrative, 112, TrialLevel.adminReview, true, ProcStage.filing⟩
    | .L13ProcedureExecutionRemedy => ⟨Forum.civil, 113, TrialLevel.retrial, true, ProcStage.filing⟩
    | .L14ArbitrationMaritimePublic =>
        ⟨Forum.arbitrationMaritime, 114, TrialLevel.arbitration, true, ProcStage.stayed⟩

/-- **满料见证案**（合同 §10.2.2 表：每格初态材料全部在卷；主体按表；
    数值取 witnessQty）。这是合成网络内的一个具体案卷，不是现实个案。 -/
def fullDocket : CaseDocket where
  qty := witnessQty
  procOf := fullProc
  m01 := ⟨[Party.lenderC, Party.debtorD, Party.guarantorG], true, true, true, true⟩
  m02 := ⟨[Party.debtorD, Party.lenderC], true, true, true, true⟩
  m03 := ⟨[Party.debtorD, Party.employeeW], true, true, true⟩
  m04 := ⟨[Party.employeeW, Party.medicalM], true, true, true⟩
  m05 := ⟨[Party.debtorD, Party.employeeW, Party.envOrgN], true, true, true, true, true, true⟩
  m06 := ⟨[Party.guarantorG, Party.spouseH, Party.lenderC, Party.heirC1, Party.heirC2],
    true, true, true, true, true⟩
  m07 := ⟨[Party.debtorD, Party.employeeW], true, true⟩
  m08 := ⟨[Party.debtorD, Party.guarantorG, Party.courtJ], true, true, true⟩
  m09 := ⟨[Party.copyrightP, Party.debtorD], true, true, true, true⟩
  m10 := ⟨[Party.guarantorG, Party.prosecutor, Party.courtJ], true, true, true, true⟩
  m11 := ⟨[Party.adminA, Party.debtorD], true, true, true, true⟩
  m12 := ⟨[Party.adminA, Party.reviewQ, Party.debtorD], true, true, true, true, true⟩
  m13 := ⟨[Party.courtJ, Party.execX, Party.employeeW], true, true, true, true, true⟩
  m14 := ⟨[Party.medicalM, Party.debtorD, Party.envOrgN], true, true, true, true, true⟩

/-- 见证案两个程序阶段确实不同（loan 案因继承中止 vs 车损案已入执行）。 -/
theorem witness_stages_not_shared :
    (fullDocket.procOf Fam.L01Contract).stage ≠ (fullDocket.procOf Fam.L03Tort).stage := by
  decide

/-- 劳动争议与海商仲裁分属不同法域（劳动仲裁前置按自己的程序，不套商事仲裁协议）。 -/
theorem witness_forums_separate :
    (fullDocket.procOf Fam.L07Labor).forum ≠
      (fullDocket.procOf Fam.L14ArbitrationMaritimePublic).forum := by
  decide

/-! ## 五、原子：材料 / 推导 / 失败 三段平铺 -/

/-- 网络原子：57 个材料原子（前缀 `mat`，逐字段对应 §10.2.2 表）+ 29 个推导原子
    （每条规则的结论）+ 10 个失败原子（表内"可失败"的争点位）。全平铺、无参数。 -/
inductive Atom where
  -- L01 CONTRACT
  | matContractSigned
  | matBankSettlementMatched
  | matReconciliationUnpaid
  | matGuaranteeByGOpen
  -- L02 PROPERTY
  | matRegistryD
  | matMortgageRegistered
  | matOtherTitles
  | matRealizationRecord
  -- L03 TORT
  | matWorkInstruction
  | matDamageCorroboration
  | matNotWorkInjury
  -- L04 MEDICAL
  | matTreatmentAtM
  | matRecordsWithheld
  | matPreExistingChecks
  -- L05 ENVIRONMENT
  | matSamplingMatch
  | matExceedance
  | matPondTesting
  | matEcoCostDocs
  | matNoExculpation
  | matInNewLawPeriod
  -- L06 FAMILY_SUCCESSION
  | matMarriageRegistered
  | matNoSpousalJointBasis
  | matCDeathRecord
  | matHeirIdentityOnFile
  | matHeirsNotYetJoined
  -- L07 LABOR
  | matWageBasisOnFile
  | matOvertimeUnsupported
  -- L08 CORPORATE_BANKRUPTCY
  | matSeparateAccounts
  | matInsolvencyShown
  | matAcceptanceDecided
  -- L09 IP
  | matCreationChain
  | matLicenseExpired
  | matPostTermUse
  | matNoWillfulnessGravity
  -- L10 CRIMINAL
  | matLoanAcquisitionProven
  | matIntentOnlyConfession
  | matGenuineBusinessShown
  | matCriminalTrialDone
  -- L11 ADMIN
  | matPenaltyServedWithBasis
  | matFactualDisputes
  | matHearingMissed
  | matRecordContradictions
  -- L12 REVIEW_COMPENSATION
  | matDetentionX
  | matReviewFiledInTime
  | matReturnDamageRecords
  | matRemoteProfitUnsupported
  | matDifferentAct
  -- L13 PROCEDURE_EXECUTION_REMEDY
  | matStayEventsKept
  | matPriorCarJudgment
  | matNamedErrorAlleged
  | matDependentClaimFiled
  | matPriorCaseUnconcluded
  -- L14 ARBITRATION_MARITIME_PUBLIC
  | matMaritimeContractWithClause
  | matCarrierCustody
  | matCargoDamage
  | matExemptionMaterials
  | matNQualified
  -- 推导原子（29 条规则的结论）
  | loanEntitlement
  | guarantorStanding
  | gEnforcementAfterExhaustion
  | mortgageSecuredPriority
  | carDamageLiability
  | medicalFaultPresumed
  | publicInterestStanding
  | ecoViolationEstablished
  | fishPrivateCompensation
  | ecoRemediationCosts
  | wageDueEstablished
  | noComminglingProven
  | bankruptcyAccepted
  | bankruptcyExecutionStay
  | bankruptcyCivilStay
  | arbitrationStayed
  | wageBankruptcyPriority
  | ipOrdinaryInfringement
  | stayForSuccession
  | stayDecreeIssued
  | holdOnLoanFinal
  | holdOnDependentClaim
  | adminDefectsEstablished
  | xReturnDue
  | xDamageCompensation
  | retrialAdmitted
  | executoryEffectKept
  | maritimeCarrierLiability
  | exemptionBurdenOnCarrier
  -- 失败原子（当前网络内不可推导；见 failureish 与 witness_model）
  | overtimeClaimEstablished
  | medicalAddedDamageAward
  | spousalJointDebt
  | ipPunitiveDamages
  | fraudConviction
  | remoteProfitAward
  | corporateVeilPierced
  | loanFinalDecree
  | dependentClaimFinalDecree
  | adminFinalDisposition
deriving DecidableEq, Fintype

/-- 裸构造子开箱：本件陈述与证明大量直接引用材料/状态原子。 -/
open Atom

/-! ## 六、具名法源（来源/条款/版本/效力时段按合同 :713 字段保留） -/

/-- 本网络登记的 22 个具名法源（条文号照 §10.2.2/§11 表；新增核查一手条款见
    合同 §10.2.3）。登记是为合成网络的可溯源性，不构成对真实条文效力时点的认定。 -/
inductive LawSource where
  | civilCode490_626
  | civilCode681_687
  | civilCode1165_1191
  | civilCode1222
  | ecoCode147
  | ecoCode1075_1081
  | ecoCode1080
  | laborContractLaw30
  | companyLaw23
  | bankruptcyLaw2_13
  | bankruptcyLaw19
  | bankruptcyLaw20
  | bankruptcyLaw109_110
  | bankruptcyLaw113
  | copyrightLaw52_54
  | civProcLaw153_1
  | civProcLaw153_5
  | civProcLaw210_217
  | adminPunishLaw63_64
  | stateCompensationLaw36
  | maritimeLaw43_57
  | maritimeLaw51
deriving DecidableEq, Fintype

/-- 法源标签：法源 + 条款 + 版本 + 效力窗口（合成网络的固定版本登记）。 -/
structure SourceTag where
  instrument : String
  article : String
  version : String
  effFrom : Nat
  effTo : Nat

/-- 逐法源标签登记（效力窗口含基准日 2026-08-15，与合同"全部相关新行为均在
    2026-08-15之后"的固定时间条件一致）。 -/
def srcTag : LawSource → SourceTag
  | .civilCode490_626 => ⟨"民法典", "第490条、第626条", "20210101 收录本", 20210101, 99991231⟩
  | .civilCode681_687 => ⟨"民法典", "第681条、第687条", "20210101 收录本", 20210101, 99991231⟩
  | .civilCode1165_1191 => ⟨"民法典", "第1165条、第1191条", "20210101 收录本", 20210101, 99991231⟩
  | .civilCode1222 => ⟨"民法典", "第1222条", "20210101 收录本", 20210101, 99991231⟩
  | .ecoCode147 => ⟨"生态环境法典", "第147条", "本轮核实文本", 20260101, 99991231⟩
  | .ecoCode1075_1081 => ⟨"生态环境法典", "第1075条、第1081条第1项", "本轮核实文本", 20260101, 99991231⟩
  | .ecoCode1080 => ⟨"生态环境法典", "第1080条", "本轮核实文本", 20260101, 99991231⟩
  | .laborContractLaw30 => ⟨"劳动合同法", "第30条", "现行文本", 20080101, 99991231⟩
  | .companyLaw23 => ⟨"公司法", "第23条", "20240701 修订本", 20240701, 99991231⟩
  | .bankruptcyLaw2_13 => ⟨"企业破产法", "第2条、第13条", "现行文本", 20070601, 99991231⟩
  | .bankruptcyLaw19 => ⟨"企业破产法", "第19条", "现行文本", 20070601, 99991231⟩
  | .bankruptcyLaw20 => ⟨"企业破产法", "第20条", "现行文本", 20070601, 99991231⟩
  | .bankruptcyLaw109_110 => ⟨"企业破产法", "第109条、第110条", "现行文本", 20070601, 99991231⟩
  | .bankruptcyLaw113 => ⟨"企业破产法", "第113条", "现行文本", 20070601, 99991231⟩
  | .copyrightLaw52_54 => ⟨"著作权法", "第52条、第54条", "20210601 修正本", 20210601, 99991231⟩
  | .civProcLaw153_1 => ⟨"民事诉讼法", "第153条第1款", "20240101 修正本", 20240101, 99991231⟩
  | .civProcLaw153_5 => ⟨"民事诉讼法", "第153条第5款", "20240101 修正本", 20240101, 99991231⟩
  | .civProcLaw210_217 => ⟨"民事诉讼法", "第210条、第217条", "20240101 修正本", 20240101, 99991231⟩
  | .adminPunishLaw63_64 => ⟨"行政处罚法", "第63条、第64条", "20210715 修订本", 20210715, 99991231⟩
  | .stateCompensationLaw36 => ⟨"国家赔偿法", "第36条", "现行文本", 20130101, 99991231⟩
  | .maritimeLaw43_57 => ⟨"海商法", "第43–49条、第55–57条", "本轮核实新文本", 20260101, 99991231⟩
  | .maritimeLaw51 => ⟨"海商法", "第51条", "本轮核实新文本", 20260101, 99991231⟩

/-- 效力窗口检查（基准日 20260815：窗口覆盖基准日即视为本网络内"可适用"）。 -/
def srcInForce (s : LawSource) : Bool :=
  decide ((srcTag s).effFrom ≤ 20260815) && decide (20260815 < (srcTag s).effTo)

/-- 溯源树的来源标识：在卷材料（以材料原子自身为编号）或规则法源。 -/
inductive SrcId where
  | mat (a : Atom)
  | statute (s : LawSource)
deriving DecidableEq

/-! ## 七、材料求值桥：材料原子 ↔ 案卷字段（逐字段照表） -/

/-- 材料求值桥：材料原子在某案卷是否在卷（推导/失败原子恒否——它们不是输入）。 -/
def materialHolds : Atom → CaseDocket → Bool
  | .matContractSigned, d => d.m01.contractSigned
  | .matBankSettlementMatched, d => d.m01.bankSettlementMatched
  | .matReconciliationUnpaid, d => d.m01.reconciliationUnpaid
  | .matGuaranteeByGOpen, d => d.m01.guaranteeByGOpen
  | .matRegistryD, d => d.m02.registryD
  | .matMortgageRegistered, d => d.m02.mortgageRegistered
  | .matOtherTitles, d => d.m02.otherTitles
  | .matRealizationRecord, d => d.m02.realizationRecord
  | .matWorkInstruction, d => d.m03.workInstruction
  | .matDamageCorroboration, d => d.m03.damageCorroboration
  | .matNotWorkInjury, d => d.m03.notWorkInjury
  | .matTreatmentAtM, d => d.m04.treatmentAtM
  | .matRecordsWithheld, d => d.m04.recordsWithheld
  | .matPreExistingChecks, d => d.m04.preExistingChecks
  | .matSamplingMatch, d => d.m05.samplingMatch
  | .matExceedance, d => d.m05.exceedance
  | .matPondTesting, d => d.m05.pondTesting
  | .matEcoCostDocs, d => d.m05.ecoCostDocs
  | .matNoExculpation, d => d.m05.noExculpation
  | .matInNewLawPeriod, d => d.m05.inNewLawPeriod
  | .matMarriageRegistered, d => d.m06.marriageRegistered
  | .matNoSpousalJointBasis, d => d.m06.noSpousalJointBasis
  | .matCDeathRecord, d => d.m06.cDeathRecord
  | .matHeirIdentityOnFile, d => d.m06.heirIdentityOnFile
  | .matHeirsNotYetJoined, d => d.m06.heirsNotYetJoined
  | .matWageBasisOnFile, d => d.m07.wageBasisOnFile
  | .matOvertimeUnsupported, d => d.m07.overtimeUnsupported
  | .matSeparateAccounts, d => d.m08.separateAccounts
  | .matInsolvencyShown, d => d.m08.insolvencyShown
  | .matAcceptanceDecided, d => d.m08.acceptanceDecided
  | .matCreationChain, d => d.m09.creationChain
  | .matLicenseExpired, d => d.m09.licenseExpired
  | .matPostTermUse, d => d.m09.postTermUse
  | .matNoWillfulnessGravity, d => d.m09.noWillfulnessGravity
  | .matLoanAcquisitionProven, d => d.m10.loanAcquisitionProven
  | .matIntentOnlyConfession, d => d.m10.intentOnlyConfession
  | .matGenuineBusinessShown, d => d.m10.genuineBusinessShown
  | .matCriminalTrialDone, d => d.m10.criminalTrialDone
  | .matPenaltyServedWithBasis, d => d.m11.penaltyServedWithBasis
  | .matFactualDisputes, d => d.m11.factualDisputes
  | .matHearingMissed, d => d.m11.hearingMissed
  | .matRecordContradictions, d => d.m11.recordContradictions
  | .matDetentionX, d => d.m12.detentionX
  | .matReviewFiledInTime, d => d.m12.reviewFiledInTime
  | .matReturnDamageRecords, d => d.m12.returnDamageRecords
  | .matRemoteProfitUnsupported, d => d.m12.remoteProfitUnsupported
  | .matDifferentAct, d => d.m12.differentAct
  | .matStayEventsKept, d => d.m13.stayEventsKept
  | .matPriorCarJudgment, d => d.m13.priorCarJudgment
  | .matNamedErrorAlleged, d => d.m13.namedErrorAlleged
  | .matDependentClaimFiled, d => d.m13.dependentClaimFiled
  | .matPriorCaseUnconcluded, d => d.m13.priorCaseUnconcluded
  | .matMaritimeContractWithClause, d => d.m14.maritimeContractWithClause
  | .matCarrierCustody, d => d.m14.carrierCustody
  | .matCargoDamage, d => d.m14.cargoDamage
  | .matExemptionMaterials, d => d.m14.exemptionMaterials
  | .matNQualified, d => d.m14.nQualified
  | _, _ => false

/-- 失败原子标记：10 个表内"可失败/依法未决/分支开放"的争点位。
    它们既不是任何案卷的输入材料（materialHolds 恒 false），也没有任何规则以它们
    为结论（`rule_concl_not_failureish` 对规则表做内核级全查）——其不可推导是
    被证明的语义事实，不是预填布尔。 -/
def failureish : Atom → Bool
  | .overtimeClaimEstablished => true
  | .medicalAddedDamageAward => true
  | .spousalJointDebt => true
  | .ipPunitiveDamages => true
  | .fraudConviction => true
  | .remoteProfitAward => true
  | .corporateVeilPierced => true
  | .loanFinalDecree => true
  | .dependentClaimFinalDecree => true
  | .adminFinalDisposition => true
  | _ => false

/-- 十四族完整性见证函数：每族交出一个满料在卷的材料原子（族归属由本函数的
    分支表定义性给出）。 -/
def familyWitness : Fam → Atom
  | .L01Contract => .matContractSigned
  | .L02Property => .matRegistryD
  | .L03Tort => .matWorkInstruction
  | .L04Medical => .matTreatmentAtM
  | .L05Environment => .matSamplingMatch
  | .L06FamilySuccession => .matMarriageRegistered
  | .L07Labor => .matWageBasisOnFile
  | .L08CorporateBankruptcy => .matSeparateAccounts
  | .L09Ip => .matCreationChain
  | .L10Criminal => .matLoanAcquisitionProven
  | .L11Admin => .matPenaltyServedWithBasis
  | .L12ReviewCompensation => .matDetentionX
  | .L13ProcedureExecutionRemedy => .matStayEventsKept
  | .L14ArbitrationMaritimePublic => .matMaritimeContractWithClause

/-- 每族主体列表读出。 -/
def familyParties (d : CaseDocket) : Fam → List Party
  | .L01Contract => d.m01.parties
  | .L02Property => d.m02.parties
  | .L03Tort => d.m03.parties
  | .L04Medical => d.m04.parties
  | .L05Environment => d.m05.parties
  | .L06FamilySuccession => d.m06.parties
  | .L07Labor => d.m07.parties
  | .L08CorporateBankruptcy => d.m08.parties
  | .L09Ip => d.m09.parties
  | .L10Criminal => d.m10.parties
  | .L11Admin => d.m11.parties
  | .L12ReviewCompensation => d.m12.parties
  | .L13ProcedureExecutionRemedy => d.m13.parties
  | .L14ArbitrationMaritimePublic => d.m14.parties

/-! ## 八、规则网络（Horn 式；每条规则带具名法源；跨族接线照表） -/

/-- 法律规则：前提（若干族材料/推导原子的合取）→ 结论（材料/状态原子），
    附具名法源标签。无否定槽/例外槽（纯 Horn 片段，边界同 SourceNorms）。 -/
structure LawRule where
  rid : Nat
  premises : Finset Atom
  conclusion : Atom
  src : LawSource
deriving DecidableEq, Fintype

/-- 投影为既有 `HornRule`（消费 SourceNorms/UnifiedHornIT 机器的接口）。 -/
def LawRule.horn (r : LawRule) : HornRule Atom := ⟨r.premises, r.conclusion⟩

/-- R01 [L01] 合同成立+银行结算同号同额+对账未偿 ⇒ 借款债权成立
    （表：§5.3 本证推出交付，再由合同/到期/清偿规则产生债权）。 -/
def ruleLoanEntitlement : LawRule :=
  { rid := 1
    premises := {Atom.matContractSigned, Atom.matBankSettlementMatched, Atom.matReconciliationUnpaid}
    conclusion := Atom.loanEntitlement
    src := LawSource.civilCode490_626 }

/-- R02 [L01] G 另签一般保证且保证期间未届满 ⇒ 保证责任成立
    （表：G 的保证责任尚须一般保证先诉及法定例外，不同于 D 的到期债务）。 -/
def ruleGuarantorStanding : LawRule :=
  { rid := 2, premises := {Atom.matGuaranteeByGOpen},
    conclusion := Atom.guarantorStanding, src := LawSource.civilCode681_687 }

/-- R03 [L01] 保证责任 ⇒ 对 G 的强制执行须先诉 D 及法定例外（一般保证先诉抗辩）。 -/
def ruleGAfterExhaustion : LawRule :=
  { rid := 3, premises := {Atom.guarantorStanding},
    conclusion := Atom.gEnforcementAfterExhaustion, src := LawSource.civilCode681_687 }

/-- R04 [L02←L01 跨族] 抵押登记+实际变价记录+同一借款债权 ⇒ 同一 loan 受担保部分
    优先受偿（表：破产 109–110 条使同一 loan 受担保部分优先、未足额部分进入普通
    债权，不把本金扩成两份债务）。 -/
def ruleMortgagePriority : LawRule :=
  { rid := 4
    premises := {Atom.matMortgageRegistered, Atom.matRealizationRecord, Atom.loanEntitlement}
    conclusion := Atom.mortgageSecuredPriority
    src := LawSource.bankruptcyLaw109_110 }

/-- R05 [L03] 工作指令+录像/登记/修理单互证 ⇒ 用人单位对车损的侵权责任
    （表：1165 及 1191 按用人单位责任条件派生车损给付；私车损失不混为工伤）。 -/
def ruleCarDamage : LawRule :=
  { rid := 5, premises := {Atom.matWorkInstruction, Atom.matDamageCorroboration},
    conclusion := Atom.carDamageLiability, src := LawSource.civilCode1165_1191 }

/-- R06 [L04] M 控制且无正当理由不提供诊疗记录 + 诊疗关系在卷 ⇒ 1222 过错推定成立
    （表：过错推定可以成立，但不直接推定全部因果和损失）。 -/
def ruleMedicalFault : LawRule :=
  { rid := 6, premises := {Atom.matTreatmentAtM, Atom.matRecordsWithheld},
    conclusion := Atom.medicalFaultPresumed, src := LawSource.civilCode1222 }

/-- R07 [L05←L14 跨族] N 公益资格材料（登记在 L14 表行）⇒ 公益诉讼当事人适格
    （表：N 依生态法典 147 条取得公益资格并走 ENV 公共分支）。 -/
def rulePublicStanding : LawRule :=
  { rid := 7, premises := {Atom.matNQualified},
    conclusion := Atom.publicInterestStanding, src := LawSource.ecoCode147 }

/-- R08 [L05] 采样/限值匹配+超限实测+无免责反证+新法期间 ⇒ 违法性认定成立
    （表：1075/1081(1) 从采样与规则匹配推出违法；不预填"已违法"布尔——
    此处是由四项在卷材料推导）。 -/
def ruleEcoViolation : LawRule :=
  { rid := 8
    premises := {Atom.matSamplingMatch, Atom.matExceedance, Atom.matNoExculpation, Atom.matInNewLawPeriod}
    conclusion := Atom.ecoViolationEstablished
    src := LawSource.ecoCode1075_1081 }

/-- R09 [L05] 鱼塘检测+违法性认定 ⇒ W 私益经营损失路径（表：1080 特别负担对 D
    发生作用；fish 与 eco 并存，私人经营损失和公共修复不互相替代）。 -/
def ruleFishPrivate : LawRule :=
  { rid := 9, premises := {Atom.matPondTesting, Atom.ecoViolationEstablished},
    conclusion := Atom.fishPrivateCompensation, src := LawSource.ecoCode1080 }

/-- R10 [L05←L14 跨族] 公共生态费用材料+公益适格+违法性 ⇒ 公共修复费用路径。 -/
def ruleEcoRemediation : LawRule :=
  { rid := 10
    premises := {Atom.matEcoCostDocs, Atom.publicInterestStanding, Atom.ecoViolationEstablished}
    conclusion := Atom.ecoRemediationCosts
    src := LawSource.ecoCode1080 }

/-- R11 [L07] 劳动合同/在岗/欠薪对账 ⇒ 已证明到期工资 w（表：到期工资获支持）。 -/
def ruleWageDue : LawRule :=
  { rid := 11, premises := {Atom.matWageBasisOnFile},
    conclusion := Atom.wageDueEstablished, src := LawSource.laborContractLaw30 }

/-- R12 [L08] 分立账户/不混同记录 ⇒ 公司法 23 财产独立证明完成
    （表：人格否认请求可以失败，但不解除 G 另签保证）。 -/
def ruleNoCommingling : LawRule :=
  { rid := 12, premises := {Atom.matSeparateAccounts},
    conclusion := Atom.noComminglingProven, src := LawSource.companyLaw23 }

/-- R13 [L08] 债务/现金不足材料+受理决定 ⇒ 破产程序已受理。 -/
def ruleBankruptcyAccepted : LawRule :=
  { rid := 13, premises := {Atom.matInsolvencyShown, Atom.matAcceptanceDecided},
    conclusion := Atom.bankruptcyAccepted, src := LawSource.bankruptcyLaw2_13 }

/-- R14 [L08→全案 跨族] 破产受理 ⇒ 执行程序中止（19 条）。 -/
def ruleExecStay : LawRule :=
  { rid := 14, premises := {Atom.bankruptcyAccepted},
    conclusion := Atom.bankruptcyExecutionStay, src := LawSource.bankruptcyLaw19 }

/-- R15 [L08] 破产受理 ⇒ D 有关民事程序按接管阶段中止（20 条）。 -/
def ruleCivilStay : LawRule :=
  { rid := 15, premises := {Atom.bankruptcyAccepted},
    conclusion := Atom.bankruptcyCivilStay, src := LawSource.bankruptcyLaw20 }

/-- R16 [L08→L14 跨族] 破产受理 ⇒ 海事仲裁中止，接管后恢复（表：破产 20 条会
    中止此仲裁）。 -/
def ruleArbStay : LawRule :=
  { rid := 16, premises := {Atom.bankruptcyAccepted},
    conclusion := Atom.arbitrationStayed, src := LawSource.bankruptcyLaw20 }

/-- R17 [L07←L08 跨族] 到期工资+破产受理 ⇒ 工资破产优先（113 条）。 -/
def ruleWagePriority : LawRule :=
  { rid := 17, premises := {Atom.wageDueEstablished, Atom.bankruptcyAccepted},
    conclusion := Atom.wageBankruptcyPriority, src := LawSource.bankruptcyLaw113 }

/-- R18 [L09] 权利链+许可终期+期满使用记录 ⇒ 普通侵权及停止使用有积极路径
    （表：原许可射程消失后普通侵权可有积极路径；无故意/严重材料则惩罚性
    赔偿要件不成立——见失败原子 ipPunitiveDamages）。 -/
def ruleIpInfringement : LawRule :=
  { rid := 18
    premises := {Atom.matCreationChain, Atom.matLicenseExpired, Atom.matPostTermUse}
    conclusion := Atom.ipOrdinaryInfringement
    src := LawSource.copyrightLaw52_54 }

/-- R19 [L06] C 死亡材料+继承人尚未表明参加 ⇒ 民诉 153(1) 中止要件成立。 -/
def ruleStaySuccession : LawRule :=
  { rid := 19, premises := {Atom.matCDeathRecord, Atom.matHeirsNotYetJoined},
    conclusion := Atom.stayForSuccession, src := LawSource.civProcLaw153_1 }

/-- R20 [L13←L06 跨族] 继承中止+中止事件保留记录 ⇒ 确定中止处分
    （表：程序规则给出中止而非实体二值答案）。 -/
def ruleStayDecree : LawRule :=
  { rid := 20, premises := {Atom.stayForSuccession, Atom.matStayEventsKept},
    conclusion := Atom.stayDecreeIssued, src := LawSource.civProcLaw153_1 }

/-- R21 [L01←L06 跨族] 继承中止 ⇒ loan 案实体终局暂不作成
    （表：确定中止处分与 loan 尚未作实体终结共存）。 -/
def ruleHoldLoan : LawRule :=
  { rid := 21, premises := {Atom.stayForSuccession},
    conclusion := Atom.holdOnLoanFinal, src := LawSource.civProcLaw153_1 }

/-- R22 [L13] 依赖他案的请求在卷+他案未审结 ⇒ 民诉 153(5) 中止，当前不得启动
    实体终局负担（合同 §10.2 叙事：先决结果未到，依法未决）。 -/
def ruleHoldDependent : LawRule :=
  { rid := 22, premises := {Atom.matDependentClaimFiled, Atom.matPriorCaseUnconcluded},
    conclusion := Atom.holdOnDependentClaim, src := LawSource.civProcLaw153_5 }

/-- R23 [L11] 处罚决定/权限依据+听证未组织+记录矛盾 ⇒ 行政程序瑕疵认定成立
    （表：63–64 听证与合法性审查实际运作；**不预填任何一种终局处分**——
    终局分支见针 06 接口）。 -/
def ruleAdminDefects : LawRule :=
  { rid := 23
    premises := {Atom.matPenaltyServedWithBasis, Atom.matHearingMissed, Atom.matRecordContradictions}
    conclusion := Atom.adminDefectsEstablished
    src := LawSource.adminPunishLaw63_64 }

/-- R24 [L12] 扣押+复议在期+返还/修理费可核 ⇒ 设备返还路径
    （表：返还 X 只是恢复处分/占有，不能再把 X 当凭空新增资产）。 -/
def ruleXReturn : LawRule :=
  { rid := 24
    premises := {Atom.matDetentionX, Atom.matReturnDamageRecords, Atom.matReviewFiledInTime}
    conclusion := Atom.xReturnDue
    src := LawSource.stateCompensationLaw36 }

/-- R25 [L12] 扣押+保管损坏修理费可核 ⇒ 实际损坏赔偿路径（国赔只补实际损坏）。 -/
def ruleXDamage : LawRule :=
  { rid := 25, premises := {Atom.matDetentionX, Atom.matReturnDamageRecords},
    conclusion := Atom.xDamageCompensation, src := LawSource.stateCompensationLaw36 }

/-- R26 [L13] 车损前裁判在卷+具名错误+事件保留 ⇒ 再审启动路径
    （表：210 申请再审；217 再审中止及例外）。 -/
def ruleRetrial : LawRule :=
  { rid := 26
    premises := {Atom.matPriorCarJudgment, Atom.matNamedErrorAlleged, Atom.matStayEventsKept}
    conclusion := Atom.retrialAdmitted
    src := LawSource.civProcLaw210_217 }

/-- R27 [L13] 再审启动 ⇒ 原裁判执行效力暂不停止（表：210 不自动停止；
    暂有执行效力不等于被计入规范允许裁判集——见共存定理）。 -/
def ruleExecEffect : LawRule :=
  { rid := 27, premises := {Atom.retrialAdmitted},
    conclusion := Atom.executoryEffectKept, src := LawSource.civProcLaw210_217 }

/-- R28 [L14] 承运占有+保管期损坏 ⇒ 承运人责任路径（表：新海商法 43–49 及 52/55–57；
    国内运输 52 条两项免责不适用）。 -/
def ruleMaritime : LawRule :=
  { rid := 28, premises := {Atom.matCarrierCustody, Atom.matCargoDamage},
    conclusion := Atom.maritimeCarrierLiability, src := LawSource.maritimeLaw43_57 }

/-- R29 [L14] 承运责任+减免材料在卷 ⇒ 免责事由负担与限额计算的分支入口。 -/
def ruleExemptionBurden : LawRule :=
  { rid := 29, premises := {Atom.maritimeCarrierLiability, Atom.matExemptionMaterials},
    conclusion := Atom.exemptionBurdenOnCarrier, src := LawSource.maritimeLaw51 }

/-- 规则总表（29 条；跨族接线：R04 L02←L01、R07 L05←L14、R10 L05←L14、
    R16 L08→L14、R17 L07←L08、R20 L13←L06、R21 L01←L06）。 -/
def familyRuleList : List LawRule :=
  [ruleLoanEntitlement, ruleGuarantorStanding, ruleGAfterExhaustion, ruleMortgagePriority,
    ruleCarDamage, ruleMedicalFault, rulePublicStanding, ruleEcoViolation, ruleFishPrivate,
    ruleEcoRemediation, ruleWageDue, ruleNoCommingling, ruleBankruptcyAccepted, ruleExecStay,
    ruleCivilStay, ruleArbStay, ruleWagePriority, ruleIpInfringement, ruleStaySuccession,
    ruleStayDecree, ruleHoldLoan, ruleHoldDependent, ruleAdminDefects, ruleXReturn,
    ruleXDamage, ruleRetrial, ruleExecEffect, ruleMaritime, ruleExemptionBurden]

/-- 规则总表的集合形。 -/
def familyRuleFinset : Finset LawRule :=
  Finset.univ.filter (fun r : LawRule => r ∈ familyRuleList)

/-- 对全部 29 条规则做内核级全查：每条规则的具名法源都在效力窗口内
    （合同 :713 效力时段字段的核验定理）。 -/
theorem all_rules_sources_in_force :
    familyRuleList.all (fun r => srcInForce r.src) = true := by rfl

/-- **一般求值入口**：任一案卷 → 其 Horn 制度网络（初始事实 = 在卷材料；
    规则表全案共用——规则是制度，材料是个案）。 -/
def hornOf (d : CaseDocket) : HornSystem Atom where
  univ := Finset.univ
  initialFacts := Finset.univ.filter (fun a => materialHolds a d)
  rules := familyRuleFinset.image (fun r : LawRule => r.horn)
  initialFacts_subset_univ := fun x _ => Finset.mem_univ x
  heads_subset_univ := fun r _ => Finset.mem_univ r.conclusion

/-- 满料见证案的 Horn 制度网络（本件全部求值定理的对象）。 -/
abbrev familyHorn : HornSystem Atom := hornOf fullDocket

/-! ## 九、闭包求值：29 条推导原子的实际规则链 -/

/-- 规则表内规则在 Horn 制度的规则集合内。 -/
theorem rule_horn_mem (r : LawRule) (hr : r ∈ familyRuleList) :
    r.horn ∈ familyHorn.rules :=
  Finset.mem_image.mpr ⟨r, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hr⟩, rfl⟩

/-- 材料前提进闭包：初始事实含于闭包（closure_is_model 左支）。 -/
theorem matCl (a : Atom) (h : materialHolds a fullDocket = true) :
    a ∈ closureAt familyHorn :=
  (SourceNorms.closure_is_model familyHorn).1 (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)

/-- 闭包引入：规则前提全在闭包 ⇒ 结论在闭包（closure_is_model 右支）。
    每一次应用都真检查前提，不是标签搬运。 -/
theorem memByRule (r : LawRule) (hr : r ∈ familyRuleList)
    (hp : ∀ p ∈ r.premises, p ∈ closureAt familyHorn) :
    r.conclusion ∈ closureAt familyHorn :=
  (SourceNorms.closure_is_model familyHorn).2 r.horn (rule_horn_mem r hr) hp

/-- R01。 -/
theorem loanEntitlement_mem : loanEntitlement ∈ closureAt familyHorn :=
  memByRule ruleLoanEntitlement (by simp [familyRuleList]) (by
    intro p hp
    rcases Finset.mem_insert.mp hp with rfl | hp
    · exact matCl Atom.matContractSigned rfl
    rcases Finset.mem_insert.mp hp with rfl | hp
    · exact matCl Atom.matBankSettlementMatched rfl
    rcases Finset.mem_singleton.mp hp with rfl
    exact matCl Atom.matReconciliationUnpaid rfl)

/-- R02。 -/
theorem guarantorStanding_mem : guarantorStanding ∈ closureAt familyHorn :=
  memByRule ruleGuarantorStanding (by simp [familyRuleList]) (by
    intro p hp
    rcases Finset.mem_singleton.mp hp with rfl
    exact matCl Atom.matGuaranteeByGOpen rfl)

/-- R03。 -/
theorem gEnforcementAfterExhaustion_mem : gEnforcementAfterExhaustion ∈ closureAt familyHorn :=
  memByRule ruleGAfterExhaustion (by simp [familyRuleList]) (by
    intro p hp
    rcases Finset.mem_singleton.mp hp with rfl
    exact guarantorStanding_mem)

/-- R07。 -/
theorem publicInterestStanding_mem : publicInterestStanding ∈ closureAt familyHorn :=
  memByRule rulePublicStanding (by simp [familyRuleList]) (by
    intro p hp
    rcases Finset.mem_singleton.mp hp with rfl
    exact matCl Atom.matNQualified rfl)

/-- R08。 -/
theorem ecoViolationEstablished_mem : ecoViolationEstablished ∈ closureAt familyHorn :=
  memByRule ruleEcoViolation (by simp [familyRuleList]) (by
    intro p hp
    rcases Finset.mem_insert.mp hp with rfl | hp
    · exact matCl Atom.matSamplingMatch rfl
    rcases Finset.mem_insert.mp hp with rfl | hp
    · exact matCl Atom.matExceedance rfl
    rcases Finset.mem_insert.mp hp with rfl | hp
    · exact matCl Atom.matNoExculpation rfl
    rcases Finset.mem_singleton.mp hp with rfl
    exact matCl Atom.matInNewLawPeriod rfl)

/-- R09。 -/
theorem fishPrivateCompensation_mem : fishPrivateCompensation ∈ closureAt familyHorn :=
  memByRule ruleFishPrivate (by simp [familyRuleList]) (by
    intro p hp
    rcases Finset.mem_insert.mp hp with rfl | hp
    · exact matCl Atom.matPondTesting rfl
    rcases Finset.mem_singleton.mp hp with rfl
    exact ecoViolationEstablished_mem)

/-- R10。 -/
theorem ecoRemediationCosts_mem : ecoRemediationCosts ∈ closureAt familyHorn :=
  memByRule ruleEcoRemediation (by simp [familyRuleList]) (by
    intro p hp
    rcases Finset.mem_insert.mp hp with rfl | hp
    · exact matCl Atom.matEcoCostDocs rfl
    rcases Finset.mem_insert.mp hp with rfl | hp
    · exact publicInterestStanding_mem
    rcases Finset.mem_singleton.mp hp with rfl
    exact ecoViolationEstablished_mem)

/-- R05。 -/
theorem carDamageLiability_mem : carDamageLiability ∈ closureAt familyHorn :=
  memByRule ruleCarDamage (by simp [familyRuleList]) (by
    intro p hp
    rcases Finset.mem_insert.mp hp with rfl | hp
    · exact matCl Atom.matWorkInstruction rfl
    rcases Finset.mem_singleton.mp hp with rfl
    exact matCl Atom.matDamageCorroboration rfl)

/-- R06。 -/
theorem medicalFaultPresumed_mem : medicalFaultPresumed ∈ closureAt familyHorn :=
  memByRule ruleMedicalFault (by simp [familyRuleList]) (by
    intro p hp
    rcases Finset.mem_insert.mp hp with rfl | hp
    · exact matCl Atom.matTreatmentAtM rfl
    rcases Finset.mem_singleton.mp hp with rfl
    exact matCl Atom.matRecordsWithheld rfl)

/-- R11。 -/
theorem wageDueEstablished_mem : wageDueEstablished ∈ closureAt familyHorn :=
  memByRule ruleWageDue (by simp [familyRuleList]) (by
    intro p hp
    rcases Finset.mem_singleton.mp hp with rfl
    exact matCl Atom.matWageBasisOnFile rfl)

/-- R12。 -/
theorem noComminglingProven_mem : noComminglingProven ∈ closureAt familyHorn :=
  memByRule ruleNoCommingling (by simp [familyRuleList]) (by
    intro p hp
    rcases Finset.mem_singleton.mp hp with rfl
    exact matCl Atom.matSeparateAccounts rfl)

/-- R13。 -/
theorem bankruptcyAccepted_mem : bankruptcyAccepted ∈ closureAt familyHorn :=
  memByRule ruleBankruptcyAccepted (by simp [familyRuleList]) (by
    intro p hp
    rcases Finset.mem_insert.mp hp with rfl | hp
    · exact matCl Atom.matInsolvencyShown rfl
    rcases Finset.mem_singleton.mp hp with rfl
    exact matCl Atom.matAcceptanceDecided rfl)

/-- R14。 -/
theorem bankruptcyExecutionStay_mem : bankruptcyExecutionStay ∈ closureAt familyHorn :=
  memByRule ruleExecStay (by simp [familyRuleList]) (by
    intro p hp
    rcases Finset.mem_singleton.mp hp with rfl
    exact bankruptcyAccepted_mem)

/-- R15。 -/
theorem bankruptcyCivilStay_mem : bankruptcyCivilStay ∈ closureAt familyHorn :=
  memByRule ruleCivilStay (by simp [familyRuleList]) (by
    intro p hp
    rcases Finset.mem_singleton.mp hp with rfl
    exact bankruptcyAccepted_mem)

/-- R16。 -/
theorem arbitrationStayed_mem : arbitrationStayed ∈ closureAt familyHorn :=
  memByRule ruleArbStay (by simp [familyRuleList]) (by
    intro p hp
    rcases Finset.mem_singleton.mp hp with rfl
    exact bankruptcyAccepted_mem)

/-- R17。 -/
theorem wageBankruptcyPriority_mem : wageBankruptcyPriority ∈ closureAt familyHorn :=
  memByRule ruleWagePriority (by simp [familyRuleList]) (by
    intro p hp
    rcases Finset.mem_insert.mp hp with rfl | hp
    · exact wageDueEstablished_mem
    rcases Finset.mem_singleton.mp hp with rfl
    exact bankruptcyAccepted_mem)

/-- R04。 -/
theorem mortgageSecuredPriority_mem : mortgageSecuredPriority ∈ closureAt familyHorn :=
  memByRule ruleMortgagePriority (by simp [familyRuleList]) (by
    intro p hp
    rcases Finset.mem_insert.mp hp with rfl | hp
    · exact matCl Atom.matMortgageRegistered rfl
    rcases Finset.mem_insert.mp hp with rfl | hp
    · exact matCl Atom.matRealizationRecord rfl
    rcases Finset.mem_singleton.mp hp with rfl
    exact loanEntitlement_mem)

/-- R18。 -/
theorem ipOrdinaryInfringement_mem : ipOrdinaryInfringement ∈ closureAt familyHorn :=
  memByRule ruleIpInfringement (by simp [familyRuleList]) (by
    intro p hp
    rcases Finset.mem_insert.mp hp with rfl | hp
    · exact matCl Atom.matCreationChain rfl
    rcases Finset.mem_insert.mp hp with rfl | hp
    · exact matCl Atom.matLicenseExpired rfl
    rcases Finset.mem_singleton.mp hp with rfl
    exact matCl Atom.matPostTermUse rfl)

/-- R19。 -/
theorem stayForSuccession_mem : stayForSuccession ∈ closureAt familyHorn :=
  memByRule ruleStaySuccession (by simp [familyRuleList]) (by
    intro p hp
    rcases Finset.mem_insert.mp hp with rfl | hp
    · exact matCl Atom.matCDeathRecord rfl
    rcases Finset.mem_singleton.mp hp with rfl
    exact matCl Atom.matHeirsNotYetJoined rfl)

/-- R20。 -/
theorem stayDecreeIssued_mem : stayDecreeIssued ∈ closureAt familyHorn :=
  memByRule ruleStayDecree (by simp [familyRuleList]) (by
    intro p hp
    rcases Finset.mem_insert.mp hp with rfl | hp
    · exact stayForSuccession_mem
    rcases Finset.mem_singleton.mp hp with rfl
    exact matCl Atom.matStayEventsKept rfl)

/-- R21。 -/
theorem holdOnLoanFinal_mem : holdOnLoanFinal ∈ closureAt familyHorn :=
  memByRule ruleHoldLoan (by simp [familyRuleList]) (by
    intro p hp
    rcases Finset.mem_singleton.mp hp with rfl
    exact stayForSuccession_mem)

/-- R22。 -/
theorem holdOnDependentClaim_mem : holdOnDependentClaim ∈ closureAt familyHorn :=
  memByRule ruleHoldDependent (by simp [familyRuleList]) (by
    intro p hp
    rcases Finset.mem_insert.mp hp with rfl | hp
    · exact matCl Atom.matDependentClaimFiled rfl
    rcases Finset.mem_singleton.mp hp with rfl
    exact matCl Atom.matPriorCaseUnconcluded rfl)

/-- R23。 -/
theorem adminDefectsEstablished_mem : adminDefectsEstablished ∈ closureAt familyHorn :=
  memByRule ruleAdminDefects (by simp [familyRuleList]) (by
    intro p hp
    rcases Finset.mem_insert.mp hp with rfl | hp
    · exact matCl Atom.matPenaltyServedWithBasis rfl
    rcases Finset.mem_insert.mp hp with rfl | hp
    · exact matCl Atom.matHearingMissed rfl
    rcases Finset.mem_singleton.mp hp with rfl
    exact matCl Atom.matRecordContradictions rfl)

/-- R24。 -/
theorem xReturnDue_mem : xReturnDue ∈ closureAt familyHorn :=
  memByRule ruleXReturn (by simp [familyRuleList]) (by
    intro p hp
    rcases Finset.mem_insert.mp hp with rfl | hp
    · exact matCl Atom.matDetentionX rfl
    rcases Finset.mem_insert.mp hp with rfl | hp
    · exact matCl Atom.matReturnDamageRecords rfl
    rcases Finset.mem_singleton.mp hp with rfl
    exact matCl Atom.matReviewFiledInTime rfl)

/-- R25。 -/
theorem xDamageCompensation_mem : xDamageCompensation ∈ closureAt familyHorn :=
  memByRule ruleXDamage (by simp [familyRuleList]) (by
    intro p hp
    rcases Finset.mem_insert.mp hp with rfl | hp
    · exact matCl Atom.matDetentionX rfl
    rcases Finset.mem_singleton.mp hp with rfl
    exact matCl Atom.matReturnDamageRecords rfl)

/-- R26。 -/
theorem retrialAdmitted_mem : retrialAdmitted ∈ closureAt familyHorn :=
  memByRule ruleRetrial (by simp [familyRuleList]) (by
    intro p hp
    rcases Finset.mem_insert.mp hp with rfl | hp
    · exact matCl Atom.matPriorCarJudgment rfl
    rcases Finset.mem_insert.mp hp with rfl | hp
    · exact matCl Atom.matNamedErrorAlleged rfl
    rcases Finset.mem_singleton.mp hp with rfl
    exact matCl Atom.matStayEventsKept rfl)

/-- R27。 -/
theorem executoryEffectKept_mem : executoryEffectKept ∈ closureAt familyHorn :=
  memByRule ruleExecEffect (by simp [familyRuleList]) (by
    intro p hp
    rcases Finset.mem_singleton.mp hp with rfl
    exact retrialAdmitted_mem)

/-- R28。 -/
theorem maritimeCarrierLiability_mem : maritimeCarrierLiability ∈ closureAt familyHorn :=
  memByRule ruleMaritime (by simp [familyRuleList]) (by
    intro p hp
    rcases Finset.mem_insert.mp hp with rfl | hp
    · exact matCl Atom.matCarrierCustody rfl
    rcases Finset.mem_singleton.mp hp with rfl
    exact matCl Atom.matCargoDamage rfl)

/-- R29。 -/
theorem exemptionBurdenOnCarrier_mem : exemptionBurdenOnCarrier ∈ closureAt familyHorn :=
  memByRule ruleExemptionBurden (by simp [familyRuleList]) (by
    intro p hp
    rcases Finset.mem_insert.mp hp with rfl | hp
    · exact maritimeCarrierLiability_mem
    rcases Finset.mem_singleton.mp hp with rfl
    exact matCl Atom.matExemptionMaterials rfl)

/-! ## 十、未成立侧：显式模型见证（NotEstablished ≠ Established(¬p)） -/

/-- 失败原子入"坏集"：非在卷材料且被标记。 -/
theorem inBad (f : Atom)
    (h : (failureish f && !materialHolds f fullDocket) = true) :
    f ∈ Finset.univ.filter (fun a => failureish a && !materialHolds a fullDocket) :=
  Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩

/-- 内核级全查：29 条规则表中没有任何规则的结论是失败原子——失败原子不可推导
    不是标注出来的，而是对整张规则表的计算性验证。 -/
theorem rule_concl_not_failureish :
    familyRuleList.all (fun r => !failureish r.conclusion) = true := by rfl

/-- 规则表内任何规则的结论都不在坏集（由上一条的内核全查 + 失败原子非材料）。 -/
theorem rule_concl_avoid_bad (r : LawRule) (hr : r ∈ familyRuleList) :
    r.horn.conclusion ∉ Finset.univ.filter (fun a => failureish a && !materialHolds a fullDocket) := by
  intro hm
  have hfalse : failureish r.conclusion = false := by
    simpa using List.all_eq_true.mp rule_concl_not_failureish r hr
  have h2 : (failureish r.conclusion && !materialHolds r.conclusion fullDocket) = true :=
    (Finset.mem_filter.mp hm).2
  rw [hfalse] at h2
  simp at h2

/-- 初始事实与坏集不相交（初始事实都是真材料，材料原子的 failureish 恒 false）。 -/
theorem initial_bad_disjoint :
    Disjoint familyHorn.initialFacts
      (Finset.univ.filter (fun a => failureish a && !materialHolds a fullDocket)) := by
  rw [Finset.disjoint_left]
  intro a ha hb
  have h1 : materialHolds a fullDocket = true := (Finset.mem_filter.mp ha).2
  have h2 : (failureish a && !materialHolds a fullDocket) = true :=
    (Finset.mem_filter.mp hb).2
  rw [h1] at h2
  simp at h2

/-- 一般引理：避开坏集的全域是一个模型（初始事实避开坏集 + 规则结论避开坏集）。 -/
theorem isModel_avoiding {α : Type} [DecidableEq α] [Fintype α] (sys : HornSystem α)
    (bad : Finset α)
    (hdisj : Disjoint sys.initialFacts bad)
    (havoid : ∀ r ∈ sys.rules, r.conclusion ∉ bad) :
    SourceNorms.isModel sys (Finset.univ \ bad) := by
  refine ⟨?_, ?_⟩
  · intro x hx
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ x,
      fun hmem => Finset.disjoint_left.mp hdisj hx hmem⟩
  · intro r hr _
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, havoid r hr⟩

/-- 见证模型：全域去掉失败原子是 `familyHorn` 的一个模型——失败原子的不可推导
    由此成为有语义见证的定理，不是标签。 -/
theorem witness_model :
    SourceNorms.isModel familyHorn (Finset.univ \
      (Finset.univ.filter (fun a => failureish a && !materialHolds a fullDocket))) := by
  refine isModel_avoiding familyHorn _ initial_bad_disjoint ?_
  intro rh hrh
  obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hrh
  exact rule_concl_avoid_bad r hr

/-- 坏集内原子不可推导：若可推导则落入每个模型，与见证模型矛盾。 -/
theorem not_in_closure_of_bad (f : Atom)
    (hf : f ∈ Finset.univ.filter (fun a => failureish a && !materialHolds a fullDocket)) :
    f ∉ closureAt familyHorn := by
  intro hmem
  have hent := SourceNorms.closure_only_entailed familyHorn hmem
  exact absurd hf
    (Finset.mem_sdiff.mp (hent (Finset.univ \
      (Finset.univ.filter (fun a => failureish a && !materialHolds a fullDocket)))
      witness_model)).2

/-- 失败原子逐个（L07 加班请求：无加班事实材料且无掌握拒不提供证明——
    妨碍推定不得作出）。 -/
theorem overtimeClaim_not_closure : overtimeClaimEstablished ∉ closureAt familyHorn :=
  not_in_closure_of_bad _ (inBad Atom.overtimeClaimEstablished rfl)

/-- 失败原子逐个（L04 新增/加重损害：1222 推定不直接推定全部因果和损失）。 -/
theorem medicalAddedDamage_not_closure : medicalAddedDamageAward ∉ closureAt familyHorn :=
  not_in_closure_of_bad _ (inBad Atom.medicalAddedDamageAward rfl)

/-- 失败原子逐个（L06 H 共同债务：1064 路径缺少要件，请求可失败）。 -/
theorem spousalJointDebt_not_closure : spousalJointDebt ∉ closureAt familyHorn :=
  not_in_closure_of_bad _ (inBad Atom.spousalJointDebt rfl)

/-- 失败原子逐个（L09 惩罚性赔偿：无故意且情节严重的充分材料）。 -/
theorem ipPunitive_not_closure : ipPunitiveDamages ∉ closureAt familyHorn :=
  not_in_closure_of_bad _ (inBad Atom.ipPunitiveDamages rfl)

/-- 失败原子逐个（L10 诈骗定罪：非仅供述+正常经营替代共同阻止）。 -/
theorem fraudConviction_not_closure : fraudConviction ∉ closureAt familyHorn :=
  not_in_closure_of_bad _ (inBad Atom.fraudConviction rfl)

/-- 失败原子逐个（L12 远端利润：无直接损失和因果材料不当然支持）。 -/
theorem remoteProfit_not_closure : remoteProfitAward ∉ closureAt familyHorn :=
  not_in_closure_of_bad _ (inBad Atom.remoteProfitAward rfl)

/-- 失败原子逐个（L08 人格否认：财产独立证明完成则请求失败）。 -/
theorem corporateVeil_not_closure : corporateVeilPierced ∉ closureAt familyHorn :=
  not_in_closure_of_bad _ (inBad Atom.corporateVeilPierced rfl)

/-- 失败原子逐个（L01 loan 实体终局：因继承中止暂不作成——注意其状态是
    依法暂未决而非证明不足，四态归类的 hold 原子见 `holdOf`）。 -/
theorem loanFinalDecree_not_closure : loanFinalDecree ∉ closureAt familyHorn :=
  not_in_closure_of_bad _ (inBad Atom.loanFinalDecree rfl)

/-- 失败原子逐个（L13 依赖他案的请求：先决未到，依法未决）。 -/
theorem dependentClaimFinal_not_closure : dependentClaimFinalDecree ∉ closureAt familyHorn :=
  not_in_closure_of_bad _ (inBad Atom.dependentClaimFinalDecree rfl)

/-- 失败原子逐个（L11 行政终局处分：**故意开放**——冲突排除分支枚举为针 06
    预留接口；本件只证它当前不可推导，不预填任何一种终局处分）。 -/
theorem adminFinalDisposition_not_closure : adminFinalDisposition ∉ closureAt familyHorn :=
  not_in_closure_of_bad _ (inBad Atom.adminFinalDisposition rfl)

/-! ## 十一、溯源健全：消费 HProvN（材料侧）+ 镜像 LTagN（法源侧） -/

/-- 材料来源声明：在卷材料原子以自身为来源编号；非材料原子不直接声明来源。 -/
def matSrcOf (a : Atom) : Finset Atom :=
  if materialHolds a fullDocket = true then {a} else ∅

theorem matSrcOf_self (a : Atom) (h : materialHolds a fullDocket = true) :
    matSrcOf a = {a} := by simp [matSrcOf, h]

/-- **消费 UnifiedHornIT.hprovN_prov_sound**（材料侧溯源健全的一般形）：
    任何推导所引用的来源必追到某条已声明在卷材料——推导不能发明材料来源。 -/
theorem family_prov_sound :
    ∀ (n : ℕ) (P : Finset Atom) (a : Atom),
      HProvN familyHorn Atom matSrcOf n P a →
        ∀ s ∈ P, ∃ b : Atom, b ∈ familyHorn.initialFacts ∧ s ∈ matSrcOf b :=
  hprovN_prov_sound familyHorn Atom matSrcOf

/-- **消费 UnifiedHornIT.hprovN_mem_closure**：带来源推导 ⇒ 闭包成员。 -/
theorem family_horn_deriv_sound :
    ∀ (n : ℕ) (P : Finset Atom) (a : Atom),
      HProvN familyHorn Atom matSrcOf n P a → a ∈ closureAt familyHorn :=
  hprovN_mem_closure familyHorn Atom matSrcOf

/-- R01 前提皆初始事实（显式推导树的叶检查）。 -/
theorem premiseInitEnt (p : Atom) (hp : p ∈ ruleLoanEntitlement.horn.premises) :
    p ∈ familyHorn.initialFacts := by
  rcases Finset.mem_insert.mp hp with rfl | hp
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩
  rcases Finset.mem_insert.mp hp with rfl | hp
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩
  rcases Finset.mem_singleton.mp hp with rfl
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩

/-- R01 的溯源集：结论的来源 = 三份在卷材料来源之并（由构造给出，不是标注）。 -/
def loanProvSet : Finset Atom :=
  ruleLoanEntitlement.horn.premises.biUnion matSrcOf

/-- 旗舰显式推导树：`loanEntitlement` 的高度 2 带来源推导
    （叶 = 三个 fact 案例，来源即各自的在卷材料编号）。 -/
theorem loanEntitlement_prov :
    HProvN familyHorn Atom matSrcOf 2 loanProvSet loanEntitlement :=
  HProvN.rule 1 ruleLoanEntitlement.horn
    (rule_horn_mem ruleLoanEntitlement (by simp [familyRuleList])) matSrcOf
    (fun p hp => HProvN.fact 1 p (premiseInitEnt p hp))

/-- 溯源集非空且含银行结算材料（防 prov_sound 空洞为真）。 -/
theorem loanProvSet_settlement_mem : matBankSettlementMatched ∈ loanProvSet := by
  refine Finset.mem_biUnion.mpr ⟨matBankSettlementMatched,
    (by simp [ruleLoanEntitlement]), ?_⟩
  rw [matSrcOf_self matBankSettlementMatched rfl]
  exact Finset.mem_singleton_self _

/-- **溯源健全的旗舰实例化**：R01 推导引用的每个来源都追到已声明在卷材料
    （消费 UnifiedHornIT.hprovN_prov_sound 于具体推导树）。 -/
theorem loan_sources_trace (s : Atom) (hs : s ∈ loanProvSet) :
    ∃ b : Atom, b ∈ familyHorn.initialFacts ∧ s ∈ matSrcOf b :=
  hprovN_prov_sound familyHorn Atom matSrcOf 2 loanProvSet loanEntitlement
    loanEntitlement_prov s hs

/-- 法律规则来源树（镜像 UnifiedHornIT.HProvN 的模式）：fact 案例引用该在卷材料；
    rule 案例引用**该规则自己的具名法源**并并上各前提的引用集。 -/
inductive LTagN : ℕ → Finset SrcId → Atom → Prop
  | fact (n : ℕ) (a : Atom) (h : a ∈ familyHorn.initialFacts) :
      LTagN n {SrcId.mat a} a
  | rule (n : ℕ) (r : LawRule) (hr : r ∈ familyRuleList)
      (C : Atom → Finset SrcId)
      (hch : ∀ p ∈ r.horn.premises, LTagN n (C p) p) :
      LTagN (n + 1) (insert (SrcId.statute r.src) (r.horn.premises.biUnion C)) r.horn.conclusion

/-- **法源侧溯源健全**：来源树推导引用的每个来源，要么是某已声明在卷材料、
    要么是规则表内某条规则的具名法源——推导不能发明来源（材料与法源双侧）。 -/
theorem ltagN_declared :
    ∀ (n : ℕ) (C : Finset SrcId) (a : Atom), LTagN n C a → ∀ s ∈ C,
      (∃ b : Atom, b ∈ familyHorn.initialFacts ∧ s = SrcId.mat b) ∨
      (∃ r : LawRule, r ∈ familyRuleList ∧ s = SrcId.statute r.src) := by
  intro n
  induction n with
  | zero =>
      intro C a h s hs
      cases h with
      | fact _ _ ha =>
          exact Or.inl ⟨a, ha, Finset.mem_singleton.mp hs⟩
  | succ k ih =>
      intro C a h s hs
      cases h with
      | fact _ _ ha =>
          exact Or.inl ⟨a, ha, Finset.mem_singleton.mp hs⟩
      | rule _ r hr C' hch =>
          rcases Finset.mem_insert.mp hs with rfl | hmem
          · exact Or.inr ⟨r, hr, rfl⟩
          · rcases Finset.mem_biUnion.mp hmem with ⟨p, hp, hCp⟩
            exact ih (C' p) p (hch p hp) s hCp

/-- **来源树桥回闭包**：有来源树的推导必在 Horn 闭包内
    （镜像 hprovN_mem_closure，为针 08"法律 Horn 实例化"预留的健全方向）。 -/
theorem ltagN_mem_closure :
    ∀ (n : ℕ) (C : Finset SrcId) (a : Atom), LTagN n C a → a ∈ closureAt familyHorn := by
  intro n
  induction n with
  | zero =>
      intro C a h
      cases h with
      | fact _ _ ha => exact (SourceNorms.closure_is_model familyHorn).1 ha
  | succ k ih =>
      intro C a h
      cases h with
      | fact _ _ ha => exact (SourceNorms.closure_is_model familyHorn).1 ha
      | rule _ r hr C' hch =>
          refine (SourceNorms.closure_is_model familyHorn).2 r.horn (rule_horn_mem r hr) ?_
          intro p hp
          exact ih (C' p) p (hch p hp)

/-- R01 的引用集：一条法源 + 三份材料来源（来源树的确切形状）。 -/
def loanCited : Finset SrcId :=
  insert (SrcId.statute LawSource.civilCode490_626)
    (ruleLoanEntitlement.horn.premises.biUnion (fun p => {SrcId.mat p}))

/-- 旗舰来源树：R01 的引用集恰为 `loanCited`。 -/
theorem loanEntitlement_ltag : LTagN 1 loanCited loanEntitlement :=
  LTagN.rule 0 ruleLoanEntitlement (by simp [familyRuleList]) (fun p => {SrcId.mat p})
    (fun p hp => LTagN.fact 0 p (premiseInitEnt p hp))

/-- R01 引用集的每个成员都被声明（消费 ltagN_declared 于具体来源树）。 -/
theorem loan_cited_declared (s : SrcId) (hs : s ∈ loanCited) :
    (∃ b : Atom, b ∈ familyHorn.initialFacts ∧ s = SrcId.mat b) ∨
      (∃ r : LawRule, r ∈ familyRuleList ∧ s = SrcId.statute r.src) :=
  ltagN_declared 1 loanCited loanEntitlement loanEntitlement_ltag s hs

/-- 引用集非空且两侧各有实员：一份银行结算材料 + 一条具名法源
    （防 declared 谓词空洞为真）。 -/
theorem loan_cited_nonempty :
    SrcId.mat Atom.matBankSettlementMatched ∈ loanCited ∧
      SrcId.statute LawSource.civilCode490_626 ∈ loanCited := by
  refine ⟨?_, Finset.mem_insert_self _ _⟩
  exact Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr ⟨matBankSettlementMatched,
    (by simp [ruleLoanEntitlement]), Finset.mem_singleton.mpr rfl⟩)

/-! ## 十二、四态联合输出与见证案完整求值 -/

/-- 合同 :692 的四态：明确成立 / 未成立 / 依法暂未决 / 过程效力与不足清偿
    （第四态的过程侧为程序处分原子，量侧为 `unmetBalance`）。 -/
inductive JointState where
  | established
  | notEstablished
  | pendingByLaw
  | procedural
deriving DecidableEq

/-- 依法暂未决的 hold 原子读出：终局争点位 → 使其中止的程序原子。 -/
def holdOf : Atom → Atom
  | .loanFinalDecree => .holdOnLoanFinal
  | .dependentClaimFinalDecree => .holdOnDependentClaim
  | a => a

/-- 见证案联合输出结构：四态清单 + 净未偿额。 -/
structure WitnessJointOutput where
  established : List Atom
  notEstablished : List Atom
  pendingByLaw : List Atom
  procedural : List Atom
  unmetBalance : ℚ

/-- 四态清单（每族结论经对应规则链推导；未成立项无支持材料亦无规则结论；
    未决项各由中止原子托住）。 -/
def witnessEstablished : List Atom :=
  [Atom.loanEntitlement, Atom.guarantorStanding, Atom.gEnforcementAfterExhaustion,
    Atom.mortgageSecuredPriority, Atom.carDamageLiability, Atom.medicalFaultPresumed,
    Atom.ecoViolationEstablished, Atom.publicInterestStanding, Atom.fishPrivateCompensation,
    Atom.ecoRemediationCosts, Atom.wageDueEstablished, Atom.wageBankruptcyPriority,
    Atom.noComminglingProven, Atom.bankruptcyAccepted, Atom.ipOrdinaryInfringement,
    Atom.adminDefectsEstablished, Atom.xReturnDue, Atom.xDamageCompensation,
    Atom.retrialAdmitted, Atom.maritimeCarrierLiability, Atom.exemptionBurdenOnCarrier]

/-- 未成立清单（证明不足侧；每项由 `witness_model` 给出语义见证）。 -/
def witnessNotEstablished : List Atom :=
  [Atom.overtimeClaimEstablished, Atom.medicalAddedDamageAward, Atom.spousalJointDebt,
    Atom.ipPunitiveDamages, Atom.fraudConviction, Atom.remoteProfitAward,
    Atom.corporateVeilPierced]

/-- 依法暂未决清单（终局原子不可推导 + 对应中止原子在闭包）。 -/
def witnessPending : List Atom :=
  [Atom.loanFinalDecree, Atom.dependentClaimFinalDecree]

/-- 过程效力清单（程序处分原子全部在闭包）。 -/
def witnessProcedural : List Atom :=
  [Atom.bankruptcyExecutionStay, Atom.bankruptcyCivilStay, Atom.arbitrationStayed,
    Atom.stayForSuccession, Atom.stayDecreeIssued, Atom.holdOnLoanFinal,
    Atom.holdOnDependentClaim, Atom.executoryEffectKept]

/-- 见证案联合输出（净未偿额 = P0+w-(a+b)，合同 §10.2.3 检查 1）。 -/
def witnessOutput : WitnessJointOutput where
  established := witnessEstablished
  notEstablished := witnessNotEstablished
  pendingByLaw := witnessPending
  procedural := witnessProcedural
  unmetBalance :=
    fullDocket.qty.loanPrincipal + fullDocket.qty.provenDueWage -
      (fullDocket.qty.collateralNet + fullDocket.qty.otherNetAssets)

/-- 明确成立支：清单内每一原子都由规则链推入闭包（21 项逐一）。 -/
theorem witness_established_ok :
    ∀ a ∈ witnessOutput.established, a ∈ closureAt familyHorn := by
  intro a ha
  simp only [witnessOutput, witnessEstablished, List.mem_cons, List.mem_nil_iff] at ha
  obtain rfl | ha := ha
  · exact loanEntitlement_mem
  obtain rfl | ha := ha
  · exact guarantorStanding_mem
  obtain rfl | ha := ha
  · exact gEnforcementAfterExhaustion_mem
  obtain rfl | ha := ha
  · exact mortgageSecuredPriority_mem
  obtain rfl | ha := ha
  · exact carDamageLiability_mem
  obtain rfl | ha := ha
  · exact medicalFaultPresumed_mem
  obtain rfl | ha := ha
  · exact ecoViolationEstablished_mem
  obtain rfl | ha := ha
  · exact publicInterestStanding_mem
  obtain rfl | ha := ha
  · exact fishPrivateCompensation_mem
  obtain rfl | ha := ha
  · exact ecoRemediationCosts_mem
  obtain rfl | ha := ha
  · exact wageDueEstablished_mem
  obtain rfl | ha := ha
  · exact wageBankruptcyPriority_mem
  obtain rfl | ha := ha
  · exact noComminglingProven_mem
  obtain rfl | ha := ha
  · exact bankruptcyAccepted_mem
  obtain rfl | ha := ha
  · exact ipOrdinaryInfringement_mem
  obtain rfl | ha := ha
  · exact adminDefectsEstablished_mem
  obtain rfl | ha := ha
  · exact xReturnDue_mem
  obtain rfl | ha := ha
  · exact xDamageCompensation_mem
  obtain rfl | ha := ha
  · exact retrialAdmitted_mem
  obtain rfl | ha := ha
  · exact maritimeCarrierLiability_mem
  obtain rfl | ha := ha
  · exact exemptionBurdenOnCarrier_mem
  exact absurd ha (by simp)

/-- 未成立支：清单内每一原子都不可推导（语义见证：见证模型避开全部失败原子）。 -/
theorem witness_not_established_ok :
    ∀ a ∈ witnessOutput.notEstablished, a ∉ closureAt familyHorn := by
  intro a ha
  simp only [witnessOutput, witnessNotEstablished, List.mem_cons, List.mem_nil_iff] at ha
  obtain rfl | ha := ha
  · exact overtimeClaim_not_closure
  obtain rfl | ha := ha
  · exact medicalAddedDamage_not_closure
  obtain rfl | ha := ha
  · exact spousalJointDebt_not_closure
  obtain rfl | ha := ha
  · exact ipPunitive_not_closure
  obtain rfl | ha := ha
  · exact fraudConviction_not_closure
  obtain rfl | ha := ha
  · exact remoteProfit_not_closure
  obtain rfl | ha := ha
  · exact corporateVeil_not_closure
  exact absurd ha (by simp)

/-- 依法暂未决支：每一终局原子——托住它的中止原子在闭包、它自己不在闭包
    （"有程序处分"≠"实体已决"，"暂未决"≠"证明不足"）。 -/
theorem witness_pending_ok :
    ∀ a ∈ witnessOutput.pendingByLaw,
      holdOf a ∈ closureAt familyHorn ∧ a ∉ closureAt familyHorn := by
  intro a ha
  simp only [witnessOutput, witnessPending, List.mem_cons, List.mem_nil_iff] at ha
  obtain rfl | ha := ha
  · exact ⟨holdOnLoanFinal_mem, loanFinalDecree_not_closure⟩
  obtain rfl | ha := ha
  · exact ⟨holdOnDependentClaim_mem, dependentClaimFinal_not_closure⟩
  exact absurd ha (by simp)

/-- 过程效力支：程序处分原子全部在闭包。 -/
theorem witness_procedural_ok :
    ∀ a ∈ witnessOutput.procedural, a ∈ closureAt familyHorn := by
  intro a ha
  simp only [witnessOutput, witnessProcedural, List.mem_cons, List.mem_nil_iff] at ha
  obtain rfl | ha := ha
  · exact bankruptcyExecutionStay_mem
  obtain rfl | ha := ha
  · exact bankruptcyCivilStay_mem
  obtain rfl | ha := ha
  · exact arbitrationStayed_mem
  obtain rfl | ha := ha
  · exact stayForSuccession_mem
  obtain rfl | ha := ha
  · exact stayDecreeIssued_mem
  obtain rfl | ha := ha
  · exact holdOnLoanFinal_mem
  obtain rfl | ha := ha
  · exact holdOnDependentClaim_mem
  obtain rfl | ha := ha
  · exact executoryEffectKept_mem
  exact absurd ha (by simp)

/-- **十四族完整性**（合同 ：692 实例化义务）：满料见证案上每族材料都非空——
    至少一个材料原子在卷、主体列表非空。不是编造十四个标签。 -/
theorem witness_completeness_ok :
    ∀ f : Fam,
      materialHolds (familyWitness f) fullDocket = true ∧
      familyParties fullDocket f ≠ [] := by
  intro f
  exact ⟨by cases f <;> rfl, by cases f <;> simp [familyParties, fullDocket]⟩

/-- 债权成立 ≠ 终局裁判（不把最终裁判外包成布尔输入：同一网络内 loan 债权在闭包、
    实体终局不在闭包且被中止原子托住）。 -/
theorem witness_entitlement_not_finality :
    loanEntitlement ∈ closureAt familyHorn ∧ loanFinalDecree ∉ closureAt familyHorn :=
  ⟨loanEntitlement_mem, loanFinalDecree_not_closure⟩

/-- 净未偿额为正（不足清偿；一般形见 `shortfall_positive`）。 -/
theorem witness_shortfall_ok : 0 < witnessOutput.unmetBalance :=
  shortfall_positive fullDocket.qty

/-- 行政终局处分分支开放（针 06 接口：当前不可推导，枚举留给后续波）。 -/
theorem witness_admin_branch_open : adminFinalDisposition ∉ closureAt familyHorn :=
  adminFinalDisposition_not_closure

/-- **见证案完整求值定理**（合同 :692）：同一满料见证案上，四态联合输出全部成立——
    明确成立（21 项入闭包）、未成立（7 项语义见证不可推导）、依法暂未决（2 项各被
    中止原子托住且终局不可推导）、过程效力（8 项程序原子入闭包）、不足清偿
    （净未偿额>0），并附十四族材料完整性、阶段/法域不共用、债权与终局分离、
    全部规则法源在效力窗口内、行政终局分支开放。 -/
theorem witness_joint_evaluation :
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
    (adminFinalDisposition ∉ closureAt familyHorn) :=
  ⟨witness_established_ok, witness_not_established_ok, witness_pending_ok,
    witness_procedural_ok, witness_completeness_ok, witness_stages_not_shared,
    witness_forums_separate, witness_entitlement_not_finality, witness_shortfall_ok,
    all_rules_sources_in_force, witness_admin_branch_open⟩

/-! ## 十三、同卷不同射程的共存条款（§10.2.3 检查 3 的可证片段） -/

/-- 同一交付、两个程序：民事债权成立与刑事定罪不成立在同一网络内共存
    （民事成立 ≠ 刑事有罪，不列共同不变量）。 -/
theorem civil_not_criminal :
    loanEntitlement ∈ closureAt familyHorn ∧ fraudConviction ∉ closureAt familyHorn :=
  ⟨loanEntitlement_mem, fraudConviction_not_closure⟩

/-- 同一诊疗记录：过错推定成立与新增损害请求不支持共存（推定不直接推定全部
    因果和损失）。 -/
theorem fault_presumed_not_all_awarded :
    medicalFaultPresumed ∈ closureAt familyHorn ∧
      medicalAddedDamageAward ∉ closureAt familyHorn :=
  ⟨medicalFaultPresumed_mem, medicalAddedDamage_not_closure⟩

/-- H 共同债务失败与 G 保证责任成立共存（1064 路径失败不消灭已签保证）。 -/
theorem joint_debt_fails_guarantee_stands :
    spousalJointDebt ∉ closureAt familyHorn ∧ guarantorStanding ∈ closureAt familyHorn :=
  ⟨spousalJointDebt_not_closure, guarantorStanding_mem⟩

/-- 中止处分与债权成立共存、实体终局暂不作成（合同 §10.2：确定中止处分与
    loan 尚未作实体终结共存；"有程序处分"不等于"实体已决"）。 -/
theorem stay_coexists_with_entitlement :
    stayForSuccession ∈ closureAt familyHorn ∧
    loanEntitlement ∈ closureAt familyHorn ∧
    loanFinalDecree ∉ closureAt familyHorn :=
  ⟨stayForSuccession_mem, loanEntitlement_mem, loanFinalDecree_not_closure⟩

/-- 错误裁判暂有执行效力与具名错误在卷共存（执行效力 ≠ 规范允许裁判集；
    裁判正确性从不作为输入出现）。 -/
theorem execution_effect_not_correctness :
    executoryEffectKept ∈ closureAt familyHorn ∧
    retrialAdmitted ∈ closureAt familyHorn ∧
    matNamedErrorAlleged ∈ closureAt familyHorn :=
  ⟨executoryEffectKept_mem, retrialAdmitted_mem, matCl Atom.matNamedErrorAlleged rfl⟩

end JurisLean.Seams.UnifiedFourteenFamilies
