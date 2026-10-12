import Mathlib.Tactic
import JurisLean.Seams.UnifiedFourteenFamilies

/-!
针 42 差额项（W15）：共同十四族网络上的实际非空轨迹见证。

出处：`docs/full-math/NEEDLE_STRENGTH_AUDIT.md` 针 42 行（判**差额**：
`UnifiedNeedlesS6S7.lean:186 nontrivial_legal_trace_exists` 的载体是 FullProcess demo
——模块自认"十四族网络总见证不在本件"；W1-3 已把十四族网络基础件
`UnifiedFourteenFamilies.lean`（57 材料/29 规则/跨族接线）入根，但 Gap05 只在其上
建了 Horn 闭包推导树，未建过程轨迹）。合同唯一权威：
`docs/spec/20261007-统一法律数学模型_附录I_Lean施工明细.md` §I.13 :796——
"`FullProcess.lean:1304 trace_performs_and_keeps_history` 可作局部见证；**拟共同
十四族网络上实际非空轨迹**"。差额闭合 G4 行："在 UnifiedFourteenFamilies 载体上建
FullProcess 形态非空轨迹见证"。

## 一、法律语义（人话）

旧针 42 见证住在 FullProcess 的 demo 载体上：那里的 State 是关系账本＋回执堆，
Trace 是抽象事件列表（给付/登记/涂改），与十四族的实际材料网络没有接线——所以
它只证"事件语言里存在非空轨迹"，不证"共同网络上存在实际轨迹"。本件把轨迹搬到
**共同十四族网络本体**上：状态 = 已确立原子集（初始 = 在卷材料），轨迹 = 按序的
规则触发步列表，每步记录时点、触发的规则（规则自身携带消费前提、产出结论与
具名法源）。一条轨迹"实际运行"，当且仅当每一步消费的前提都在触发时刻之前已经
确立（材料在卷、或由更早的步产出）——这就是 Horn 网络上的实际推导过程，而不是
闭包求值的快照。

交付的轨迹见证：
- **满料案**（`fullDocket`）：17 步全轨迹（R01→R04 跨族 L02←L01、R07→R08→R10
  跨族深度 3 生态链（复用 Gap05 的链形但以轨迹记录交付）、R09、R11+R13→R17、
  R14/R15/R16、R28→R29、R19→R20→R21），每步无重复触发（productive）。
- **部分料案一**（`partialEcoDocket`，L05 超限实测材料 matExceedance 缺失）：
  1 步轨迹（R07 公益资格仍触发），但 R08 被缺料挡住——生态违法链在该案卷上
  对任何轨迹都到不了。
- **部分料案二**（`partialBankDocket`，L08 受理决定材料 matAcceptanceDecided 缺失）：
  4 步轨迹（R11、R19→R20→R21 照常运行），但破产族链根 bankruptcyAccepted 对
  任何轨迹都到不了（R13 缺料 ⇒ R14/R15/R16/R17 全阻断）。

结构定理（轨迹语言自身）：单调（状态沿轨迹只增）、与 closureAt 一致（从初始
状态出发的轨迹终态 ⊆ Horn 闭包——轨迹结论都真实在闭包内，不是轨迹私造）、
产出性长度上界（每步新增原子的轨迹长度 ≤ 网络原子总数 96——终止单调的定量形）、
单步关系良基（剩余可加原子数为测度，对 ℕ 归纳）、拼接与起点放大。

## 二、数学对象

- 载体：`Step`（idx 时点＋rule 规则＋htab 表成员证明）、`NetState = Finset Atom`、
  `NetTrace = List Step`、`initState`（= `(hornOf d).initialFacts`）、
  `runNetTrace`（结构递归折叠）、`addAll`（按触发序左折叠插入门表，与
  `runNetTrace` 定义性一致）、`mem_addAll`。
- 良构谓词：`TraceOk d S T tr`（归纳谓词：每步前提 ⊆ 当前状态；htab 已内置于
  Step，轨迹不能发明规则表外的规则）。
- 结构定理：`traceOk_mono`、`traceOk_runNetTrace`、`traceOk_concl_mem`、
  `traceOk_split`（拼接）、`traceOk_start_mono`（起点放大）、`traceOk_closure`
  （一致性一般形）、`traceOk_init_closure`（初始状态版）。
- 良基/终止：`remainCard`（剩余测度）、`remain_insert_lt`、`Productive d S tr`
  （每步结论此前不在状态中）、`productive_card_bound`（长度＋初始基数 ≤ 96）、
  `prodStepRel`＋`prodStep_wf`（单步关系良基，纯 ℕ 归纳，不用 InvImage）。
- 见证：`stR…` 17 个具名步、`fullTraj`、`fullTrajConcls`、`ecoChain`
  （R07→R08→R10 深度 3 链）、`TimesInc`（时点严格递增谓词）＋各见证 ok／
  productive／times／sources 定理、`eco_chain_depth3`。
- 部分料案：`partialEcoDocket`/`partialBankDocket`、`badEco`/`badBank`、
  内核级阻断扫描（`by rfl`）、`isModel_avoiding_gen`（避开坏集模型，本件独立
  复证）、逐原子不可推导定理、`partial_*_no_traj_reaches`（任何轨迹到不了）、
  `partialEcoTraj`/`partialBankTraj` 及其 ok/productive/times 定理。
- 旗舰：`nontrivial_net_trajectory_exists`（合同句存在形：共同网络上的实际
  非空轨迹）、`full_net_trajectory_end_to_end`（17 步全读数）、
  `partial_net_trajectory_difference`（部分料案差异）。

## 三、Scope, honestly

**证**：上述全部定理，零 sorry/零自定义 axiom/零 True 逃避；`decide` 战术零使用
（闭式计算一律 `rfl` 内核归约，包括 29 条规则表×阻断表×17 步法源效力全查）。
**不证/开放**（如实列出）：
- 轨迹见证覆盖 29 条规则中的 17 条（含全部跨族接线 R04/R07/R10/R16/R17 与
  R20/R21；R02/R03 等 12 条单族短链的轨迹形是同构机械实例，其闭包成员性已由
  `UnifiedFourteenFamilies.witness_joint_evaluation` 全覆盖，本件不重复展开）。
- `TimesInc` 只约束时点严格递增，不把时点绑定为"等于列表位置"（位置即下标
  是本件见证的实现事实，不是谓词语义）。
- 两张部分料案阻断表是内核级 `rfl` 全查（与 Gap05 同模式）；"对任意缺料组合
  的通用阻断分类"不在本件（通用形已在 Gap05 `conclusion_blocked_of_missing_premise`）。
- 轨迹到闭包只有单侧一致（轨迹终态 ⊆ 闭包）；"闭包元素必被某条有限轨迹产出"
  的完备方向是闭包迭代子的另一件事，不在针 42 合同句内。
- 满料/部分案是合成网络内的具体案卷（合同 §10.2 合成边界照旧）；数量层
  （ℚ 不足清偿等）在 `UnifiedFourteenFamilies` 已有定理，本件不重复。
- 与 FullProcess demo 载体的关系：本件不 import FullProcess；旧 demo 见证保留
  不删（它证的是事件账本语言里的存在性）；差异说明见
  `.local/agent_W15_net_traj_report.md`。

## 四、档位

全部定理 [已证，认定待 CI]；本机镜像试编译（仓外 LEAN_PATH 指向 pinned
mathlib v4.30.0 预编译 olean）exit=0；CI 是唯一 Lean 权威，当前 CI_NOT_RUN
（fail-closed）。`omega` 仅用于 ℕ 上的线性算术；量层无涉（ℚ 不出现在本件）。
-/

namespace JurisLean.Seams.UnifiedNetTrajectory

open JurisLean.Seams.UnifiedFourteenFamilies
open JurisLean.Seams.SourceNorms

open Atom

/-! ## 〇、载体：步／状态／轨迹／折叠／良构谓词 -/

/-- 网络轨迹步：一次规则触发的完整记录。`idx` 是时点（见证中取触发序号），
    `rule` 是触发的规则——规则自身携带消费前提 `premises`、产出结论
    `conclusion`、具名法源 `src`（时点/来源随步记录）；`htab` 钉死该规则在
    29 条规则表内：轨迹不能发明规则。 -/
structure Step where
  idx : ℕ
  rule : LawRule
  htab : rule ∈ familyRuleList

/-- 网络状态：已确立原子集（从在卷材料出发，逐步并入各步结论）。 -/
abbrev NetState := Finset Atom

/-- 网络轨迹：按序排列的规则触发步列表。 -/
abbrev NetTrace := List Step

/-- 某案卷的初始状态：全部在卷材料（定义即该案卷 Horn 网络的初始事实）。 -/
def initState (d : CaseDocket) : NetState :=
  Finset.univ.filter (fun a => materialHolds a d)

/-- 初始状态就是 Horn 网络的初始事实（定义性）。 -/
theorem initState_eq (d : CaseDocket) : initState d = (hornOf d).initialFacts := rfl

/-- 轨迹折叠：从状态 `S` 起，逐位并入各步结论（结构递归，FullProcess 的
    `runTrace` 在网络载体上的对应物）。 -/
def runNetTrace (S : NetState) : NetTrace → NetState
  | [] => S
  | st :: rest => runNetTrace (insert st.rule.horn.conclusion S) rest

/-- 按触发序左折叠插入（`runNetTrace` 的纯原子表读出，用于给终态一个
    不含 Step 的书写形状）。 -/
def addAll (S : NetState) : List Atom → NetState
  | [] => S
  | c :: cs => addAll (insert c S) cs

/-- `addAll` 的成员刻画：属于折叠结果 ⇔ 属于插入表或初始状态。 -/
theorem mem_addAll (a : Atom) (S : NetState) (cs : List Atom) :
    a ∈ addAll S cs ↔ a ∈ cs ∨ a ∈ S := by
  induction cs generalizing S with
  | nil =>
      simp only [addAll, List.not_mem_nil, false_or]
  | cons c cs ih =>
      simp only [addAll, ih, Finset.mem_insert, List.mem_cons]
      tauto

/-- 良构轨迹（核心谓词）：从 `S` 到 `T` 实际运行 `tr`——每步消费的前提都
    ⊆ 触发时刻之前的状态。 -/
inductive TraceOk (d : CaseDocket) : NetState → NetState → NetTrace → Prop
  | nil (S : NetState) : TraceOk d S S []
  | cons (S T : NetState) (st : Step) (tr : NetTrace)
      (hen : st.rule.horn.premises ⊆ S)
      (hrest : TraceOk d (insert st.rule.horn.conclusion S) T tr) :
      TraceOk d S T (st :: tr)

/-! ## 一、结构定理（单调／折叠／结论留存／拼接／起点放大／闭包一致） -/

/-- 材料原子入初始状态（求值桥）。 -/
theorem matIn (d : CaseDocket) (a : Atom) (h : materialHolds a d = true) :
    a ∈ initState d :=
  Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩

/-- 推导/失败原子不是任何案卷的输入材料（`materialHolds` 兜底分支，定义性）。 -/
theorem notMem_init_of_derived (d : CaseDocket) (a : Atom)
    (h : materialHolds a d = false) : a ∉ initState d := by
  intro hmem
  rw [(Finset.mem_filter.mp hmem).2] at h
  exact Bool.noConfusion h

/-- 初始状态 ⊆ 闭包（闭包是含初始事实的最小模型，左半边）。 -/
theorem initState_subset_closure (d : CaseDocket) :
    initState d ⊆ closureAt (hornOf d) := by
  rw [initState_eq]
  exact (closure_is_model (hornOf d)).1

/-- 规则表内规则属于任一案卷的 Horn 网络（Gap05 `rule_horn_mem_general` 的
    本件独立复证：本件不 import Gap05，阻断/触发机器全部自持）。 -/
theorem rule_horn_mem_any (d : CaseDocket) (r : LawRule) (hr : r ∈ familyRuleList) :
    r.horn ∈ (hornOf d).rules :=
  Finset.mem_image.mpr ⟨r, List.mem_toFinset.mpr hr, rfl⟩

/-- **单调**：良构轨迹的状态沿轨迹只增不减。 -/
theorem traceOk_mono {d : CaseDocket} : ∀ {S T : NetState} {tr : NetTrace},
    TraceOk d S T tr → S ⊆ T := by
  intro S T tr h
  induction h with
  | nil => exact Finset.Subset.refl _
  | cons S T st tr _ hrest ih =>
      exact Finset.Subset.trans (Finset.subset_insert _ _) ih

/-- **折叠一致**：良构轨迹的终态就是 `runNetTrace` 的折叠结果。 -/
theorem traceOk_runNetTrace {d : CaseDocket} {S T : NetState} {tr : NetTrace}
    (h : TraceOk d S T tr) : runNetTrace S tr = T := by
  induction h with
  | nil => rfl
  | cons _ _ _ _ _ _ ih => exact ih

/-- **结论留存**：轨迹中任何一步的结论都留在终态里。 -/
theorem traceOk_concl_mem {d : CaseDocket} {S T : NetState} {tr : NetTrace}
    (h : TraceOk d S T tr) : ∀ {st : Step}, st ∈ tr → st.rule.horn.conclusion ∈ T := by
  induction h with
  | nil => intro st hmem; cases hmem
  | cons S T st' tr _ hrest ih =>
      intro st hmem
      rcases List.mem_cons.mp hmem with h | hmem
      · rw [h]
        exact traceOk_mono hrest (Finset.mem_insert_self st'.rule.horn.conclusion S)
      · exact ih hmem

/-- **拼接**：前段到中点、后段从中点，则整段良构。 -/
theorem traceOk_split {d : CaseDocket} {S M T : NetState} {tr₁ tr₂ : NetTrace}
    (h₁ : TraceOk d S M tr₁) : TraceOk d M T tr₂ → TraceOk d S T (tr₁ ++ tr₂) := by
  induction h₁ with
  | nil => exact fun h₂ => h₂
  | cons S M st tr hen hrest ih =>
      exact fun h₂ => TraceOk.cons S T st (tr ++ tr₂) hen (ih h₂)

/-- **起点放大**：良构轨迹可以从更大的起点重跑（前提更多只更易满足），
    终态随之放大。 -/
theorem traceOk_start_mono {d : CaseDocket} {S T : NetState} {tr : NetTrace}
    (h : TraceOk d S T tr) : ∀ (S' : NetState), S ⊆ S' →
      ∃ T', TraceOk d S' T' tr ∧ T ⊆ T' := by
  induction h with
  | nil S => intro S' hsub; exact ⟨S', TraceOk.nil S', hsub⟩
  | cons S T st tr hen hrest ih =>
      intro S' hsub
      obtain ⟨T', hT', hle⟩ := ih (insert st.rule.horn.conclusion S')
        (Finset.insert_subset_insert _ hsub)
      exact ⟨T', TraceOk.cons S' T' st tr (Finset.Subset.trans hen hsub) hT', hle⟩

/-- **与 closureAt 一致（一般形）**：起点 ⊆ 闭包 ⇒ 终态 ⊆ 闭包——轨迹结论
    都真实落在该案卷 Horn 网络的闭包内，轨迹不能私造可推导性。 -/
theorem traceOk_closure {d : CaseDocket} {S T : NetState} {tr : NetTrace}
    (h : TraceOk d S T tr) (hsub : S ⊆ closureAt (hornOf d)) :
    T ⊆ closureAt (hornOf d) := by
  induction h with
  | nil => exact hsub
  | cons S T st tr hen hrest ih =>
      have hconcl : st.rule.horn.conclusion ∈ closureAt (hornOf d) :=
        (closure_is_model (hornOf d)).2 st.rule.horn
          (rule_horn_mem_any d st.rule st.htab) (Finset.Subset.trans hen hsub)
      exact ih (Finset.insert_subset hconcl hsub)

/-- 一致性的初始状态版：从在卷材料出发的实际轨迹，终态全部在闭包内。 -/
theorem traceOk_init_closure {d : CaseDocket} {T : NetState} {tr : NetTrace}
    (h : TraceOk d (initState d) T tr) : ∀ ⦃a : Atom⦄, a ∈ T → a ∈ closureAt (hornOf d) :=
  fun _ ha => traceOk_closure h (initState_subset_closure d) ha

/-- 轨迹终态成员 ⇒ 闭包成员（点读形式，差异定理的桥）。 -/
theorem trace_reaches_mem_closure {d : CaseDocket} {T : NetState} {tr : NetTrace}
    {a : Atom} (h : TraceOk d (initState d) T tr) (ha : a ∈ T) :
    a ∈ closureAt (hornOf d) :=
  traceOk_init_closure h ha

/-! ## 二、良基与终止单调 -/

/-- 剩余可加原子数（良基测度）：全域去掉已确立部分的大小。 -/
def remainCard (S : NetState) : ℕ := (Finset.univ \ S).card

/-- **测度递减**：新增一个此前不在状态中的原子，剩余数严格减少。 -/
theorem remain_insert_lt (S : NetState) (c : Atom) (hnew : c ∉ S) :
    remainCard (insert c S) < remainCard S := by
  have hsub : ({c} : Finset Atom) ⊆ Finset.univ \ S :=
    Finset.singleton_subset_iff.mpr (Finset.mem_sdiff.mpr ⟨Finset.mem_univ c, hnew⟩)
  have h1 : Finset.univ \ insert c S = (Finset.univ \ S) \ {c} := by
    ext a
    simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, Finset.mem_univ]
    tauto
  have h2 : (1 : ℕ) ≤ (Finset.univ \ S).card := Finset.card_le_card hsub
  simp only [remainCard]
  rw [h1, Finset.card_sdiff_of_subset hsub, Finset.card_singleton]
  omega

/-- **产出性轨迹**：每步的结论都是触发时刻之前状态中没有的新原子
    （无重复触发、无空转）。 -/
inductive Productive (d : CaseDocket) : NetState → NetTrace → Prop
  | nil (S : NetState) : Productive d S []
  | cons (S : NetState) (st : Step) (tr : NetTrace)
      (hnew : st.rule.horn.conclusion ∉ S)
      (hrest : Productive d (insert st.rule.horn.conclusion S) tr) :
      Productive d S (st :: tr)

/-- **终止单调的定量形**：产出性轨迹的长度＋初始基数 ≤ 网络原子总数——
    有限网络上没有无限产出轨迹。 -/
theorem productive_card_bound {d : CaseDocket} {S : NetState} {tr : NetTrace}
    (h : Productive d S tr) : tr.length + S.card ≤ Fintype.card Atom := by
  induction h with
  | nil S =>
      have h1 := Finset.card_le_card (Finset.subset_univ S)
      rw [Finset.card_univ] at h1
      simp only [List.length_nil]
      omega
  | cons S st tr hnew hrest ih =>
      have hcard : (insert st.rule.horn.conclusion S).card = S.card + 1 :=
        Finset.card_insert_of_notMem hnew
      simp only [List.length_cons]
      omega

/-- **单步关系**：`prodStepRel S T` ＝ T 由 S 一次产出性触发得到。 -/
def prodStepRel (S T : NetState) : Prop :=
  ∃ st : Step, st.rule.horn.conclusion ∉ S ∧ T = insert st.rule.horn.conclusion S

/-- 单步关系下剩余测度严格递减。 -/
theorem prodStep_remain_lt {S T : NetState} (h : prodStepRel S T) :
    remainCard T < remainCard S := by
  obtain ⟨st, hnew, rfl⟩ := h
  exact remain_insert_lt S st.rule.horn.conclusion hnew

/-- **良基**：产出性单步关系良基——以"亏额"（原子总数−剩余数）做强归纳：
    前驱的剩余数更大 ⇒ 亏额严格更小；纯 ℕ 强归纳，不用 InvImage。 -/
theorem prodStep_wf : WellFounded prodStepRel := by
  have hbound (S : NetState) : remainCard S ≤ Fintype.card Atom := by
    have h1 := Finset.card_le_card (Finset.sdiff_subset (s := Finset.univ) (t := S))
    rw [Finset.card_univ] at h1
    exact h1
  have key : ∀ (m : ℕ) (S : NetState),
      Fintype.card Atom - remainCard S = m → Acc prodStepRel S := by
    intro m
    induction m using Nat.strongRecOn with
    | ind m ih =>
        intro S hS
        refine Acc.intro S (fun T hT => ?_)
        have hlt : remainCard S < remainCard T := prodStep_remain_lt hT
        have hTb := hbound T
        exact ih (Fintype.card Atom - remainCard T) (by omega) T rfl
  exact ⟨fun S => key (Fintype.card Atom - remainCard S) S rfl⟩

/-! ## 三、时点谓词与见证轨迹 -/

/-- 时点严格递增谓词（每步记录时点；见证轨迹全部满足）。 -/
inductive TimesInc : NetTrace → Prop
  | nil : TimesInc []
  | one (s : Step) : TimesInc [s]
  | cons (s₁ s₂ : Step) (rest : NetTrace) (h : s₁.idx < s₂.idx)
      (hrest : TimesInc (s₂ :: rest)) : TimesInc (s₁ :: s₂ :: rest)

/-- 时点构造子引理：时点为 k 与 k+1 的两步相连。 -/
theorem incCons2 (k : ℕ) (s₁ s₂ : Step) (rest : NetTrace)
    (h₁ : s₁.idx = k) (h₂ : s₂.idx = k + 1) (hrest : TimesInc (s₂ :: rest)) :
    TimesInc (s₁ :: s₂ :: rest) :=
  TimesInc.cons s₁ s₂ rest (by rw [h₁, h₂]; exact Nat.lt_succ_self k) hrest

/-- 满料案 17 步轨迹的具名步（idx=触发序）。 -/
def stR01 : Step := ⟨0, ruleLoanEntitlement, by simp [familyRuleList]⟩
def stR04 : Step := ⟨1, ruleMortgagePriority, by simp [familyRuleList]⟩
def stR07 : Step := ⟨2, rulePublicStanding, by simp [familyRuleList]⟩
def stR08 : Step := ⟨3, ruleEcoViolation, by simp [familyRuleList]⟩
def stR09 : Step := ⟨4, ruleFishPrivate, by simp [familyRuleList]⟩
def stR10 : Step := ⟨5, ruleEcoRemediation, by simp [familyRuleList]⟩
def stR11 : Step := ⟨6, ruleWageDue, by simp [familyRuleList]⟩
def stR13 : Step := ⟨7, ruleBankruptcyAccepted, by simp [familyRuleList]⟩
def stR17 : Step := ⟨8, ruleWagePriority, by simp [familyRuleList]⟩
def stR14 : Step := ⟨9, ruleExecStay, by simp [familyRuleList]⟩
def stR15 : Step := ⟨10, ruleCivilStay, by simp [familyRuleList]⟩
def stR16 : Step := ⟨11, ruleArbStay, by simp [familyRuleList]⟩
def stR28 : Step := ⟨12, ruleMaritime, by simp [familyRuleList]⟩
def stR29 : Step := ⟨13, ruleExemptionBurden, by simp [familyRuleList]⟩
def stR19 : Step := ⟨14, ruleStaySuccession, by simp [familyRuleList]⟩
def stR20 : Step := ⟨15, ruleStayDecree, by simp [familyRuleList]⟩
def stR21 : Step := ⟨16, ruleHoldLoan, by simp [familyRuleList]⟩

/-- 满料案全轨迹：17 步（L01→L02 跨族、L05 生态链＋L14 接线、L07+L08→优先权、
    L08→执行/民事/仲裁中止、L14 海商、L06 继承中止→处分→loan 暂不作成）。 -/
def fullTraj : NetTrace :=
  [stR01, stR04, stR07, stR08, stR09, stR10, stR11, stR13, stR17, stR14, stR15,
    stR16, stR28, stR29, stR19, stR20, stR21]

/-- 满料案全轨迹的结论表（`addAll` 的插入表）。 -/
def fullTrajConcls : List Atom :=
  [loanEntitlement, mortgageSecuredPriority, publicInterestStanding,
    ecoViolationEstablished, fishPrivateCompensation, ecoRemediationCosts,
    wageDueEstablished, bankruptcyAccepted, wageBankruptcyPriority,
    bankruptcyExecutionStay, bankruptcyCivilStay, arbitrationStayed,
    maritimeCarrierLiability, exemptionBurdenOnCarrier, stayForSuccession,
    stayDecreeIssued, holdOnLoanFinal]

/-- 深度 3 生态链的三步（时点重起 0/1/2；复用 Gap05 的 R07→R08→R10 链形）。 -/
def stE0 : Step := ⟨0, rulePublicStanding, by simp [familyRuleList]⟩
def stE1 : Step := ⟨1, ruleEcoViolation, by simp [familyRuleList]⟩
def stE2 : Step := ⟨2, ruleEcoRemediation, by simp [familyRuleList]⟩

/-- 深度 3 生态链轨迹（R07→R08→R10）。 -/
def ecoChain : NetTrace := [stE0, stE1, stE2]

/-- 前提成员构造引理：材料前提（任意折叠前缀状态）。 -/
theorem premMat (d : CaseDocket) (p : Atom) (h : materialHolds p d = true)
    (cs : List Atom) : p ∈ addAll (initState d) cs :=
  (mem_addAll p (initState d) cs).mpr (Or.inr (matIn d p h))

/-- 前提成员构造引理：此前某步的结论（任意折叠前缀状态）。 -/
theorem premConcl (d : CaseDocket) (c : Atom) (cs : List Atom) (h : c ∈ cs) :
    c ∈ addAll (initState d) cs :=
  (mem_addAll c (initState d) cs).mpr (Or.inl h)

/-- 新原子构造引理：推导结论此前既不在结论表也不在材料状态。 -/
theorem hnew_of (d : CaseDocket) (a : Atom) (cs : List Atom)
    (hmat : materialHolds a d = false) (hcs : a ∉ cs) :
    a ∉ addAll (initState d) cs := by
  intro hmem
  rcases (mem_addAll a (initState d) cs).mp hmem with h | h
  · exact hcs h
  · exact notMem_init_of_derived d a hmat h

/-- 单步良构构造引理。 -/
theorem tstep {d : CaseDocket} {S T : NetState} {st : Step} {tr : NetTrace}
    (hen : st.rule.horn.premises ⊆ S)
    (hrest : TraceOk d (insert st.rule.horn.conclusion S) T tr) :
    TraceOk d S T (st :: tr) :=
  TraceOk.cons S T st tr hen hrest

/-- 单步产出构造引理。 -/
theorem pstep {d : CaseDocket} {S : NetState} {st : Step} {tr : NetTrace}
    (hnew : st.rule.horn.conclusion ∉ S)
    (hrest : Productive d (insert st.rule.horn.conclusion S) tr) :
    Productive d S (st :: tr) :=
  Productive.cons S st tr hnew hrest

/-- 深度 3 生态链良构（R07/R08 只用材料；R10 消费 R07 结论＋R08 结论＋材料）。 -/
theorem ecoChain_ok : TraceOk fullDocket (initState fullDocket)
    (addAll (initState fullDocket)
      [publicInterestStanding, ecoViolationEstablished, ecoRemediationCosts]) ecoChain := by
  have h0 : rulePublicStanding.horn.premises ⊆ addAll (initState fullDocket) ([] : List Atom) := by
    intro p hp
    rcases Finset.mem_singleton.mp hp with rfl
    exact premMat fullDocket matNQualified rfl []
  have h1 : ruleEcoViolation.horn.premises ⊆
      addAll (initState fullDocket) [publicInterestStanding] := by
    intro p hp
    rcases Finset.mem_insert.mp hp with rfl | hp
    · exact premMat fullDocket matSamplingMatch rfl _
    rcases Finset.mem_insert.mp hp with rfl | hp
    · exact premMat fullDocket matExceedance rfl _
    rcases Finset.mem_insert.mp hp with rfl | hp
    · exact premMat fullDocket matNoExculpation rfl _
    rcases Finset.mem_singleton.mp hp with rfl
    exact premMat fullDocket matInNewLawPeriod rfl _
  have h2 : ruleEcoRemediation.horn.premises ⊆
      addAll (initState fullDocket) [publicInterestStanding, ecoViolationEstablished] := by
    intro p hp
    rcases Finset.mem_insert.mp hp with rfl | hp
    · exact premMat fullDocket matEcoCostDocs rfl _
    rcases Finset.mem_insert.mp hp with rfl | hp
    · exact premConcl fullDocket publicInterestStanding _ (by simp)
    rcases Finset.mem_singleton.mp hp with rfl
    exact premConcl fullDocket ecoViolationEstablished _ (by simp)
  exact tstep h0 (tstep h1 (tstep h2 (TraceOk.nil _)))

/-- 深度 3 生态链产出性（三步结论互异且皆非材料）。 -/
theorem ecoChain_productive : Productive fullDocket (initState fullDocket) ecoChain := by
  refine pstep (hnew_of fullDocket publicInterestStanding [] rfl (by simp)) ?_
  refine pstep (hnew_of fullDocket ecoViolationEstablished [publicInterestStanding] rfl
    (by simp)) ?_
  exact pstep (hnew_of fullDocket ecoRemediationCosts
    [publicInterestStanding, ecoViolationEstablished] rfl (by simp))
    (Productive.nil _)

/-- 深度 3 生态链时点严格递增。 -/
theorem ecoChain_times : TimesInc ecoChain :=
  incCons2 0 stE0 stE1 [stE2] rfl rfl
    (incCons2 1 stE1 stE2 [] rfl rfl (TimesInc.one stE2))

/-- **链式触发见证（Gap05 R07→R08→R10 链形的轨迹交付）**：R07 与 R08 的前提
    全部是在卷材料；R10 的前提同时消费 R07 的结论（公益资格）与 R08 的结论
    （违法性认定）——初始材料→规则→结论→作为下游前提的汇聚触发，共 3 次发射。
    深度计数与 Gap05 旗舰一致（HProvN 高度 3 ＝ 材料层＋两级规则；网络内
    结论→结论的最深规则链为 2，无更深的发射链）。 -/
theorem eco_chain_depth3 :
    (∀ p ∈ rulePublicStanding.horn.premises, materialHolds p fullDocket = true) ∧
      (∀ p ∈ ruleEcoViolation.horn.premises, materialHolds p fullDocket = true) ∧
      publicInterestStanding ∈ ruleEcoRemediation.horn.premises ∧
      ecoViolationEstablished ∈ ruleEcoRemediation.horn.premises ∧
      (rulePublicStanding ∈ familyRuleList ∧ ruleEcoViolation ∈ familyRuleList ∧
        ruleEcoRemediation ∈ familyRuleList) ∧
      ecoRemediationCosts ∈ addAll (initState fullDocket)
        [publicInterestStanding, ecoViolationEstablished, ecoRemediationCosts] ∧
      3 ≤ ecoChain.length := by
  refine ⟨?_, ?_, ?_, ?_, ⟨by simp [familyRuleList], by simp [familyRuleList],
    by simp [familyRuleList]⟩, ?_, by rfl⟩
  · intro p hp
    rcases Finset.mem_singleton.mp hp with rfl
    rfl
  · intro p hp
    rcases Finset.mem_insert.mp hp with rfl | hp
    · rfl
    rcases Finset.mem_insert.mp hp with rfl | hp
    · rfl
    rcases Finset.mem_insert.mp hp with rfl | hp
    · rfl
    rcases Finset.mem_singleton.mp hp with rfl
    rfl
  · exact by simp [ruleEcoRemediation, LawRule.horn]
  · exact by simp [ruleEcoRemediation, LawRule.horn]
  · exact premConcl fullDocket ecoRemediationCosts _ (by simp)

/-- 满料案 17 步全轨迹良构（每步前提逐一检查：材料在卷或为此前步结论）。 -/
theorem fullTraj_ok : TraceOk fullDocket (initState fullDocket)
    (addAll (initState fullDocket) fullTrajConcls) fullTraj := by
  have h01 : ruleLoanEntitlement.horn.premises ⊆ addAll (initState fullDocket) ([] : List Atom) := by
    intro p hp
    rcases Finset.mem_insert.mp hp with rfl | hp
    · exact premMat fullDocket matContractSigned rfl _
    rcases Finset.mem_insert.mp hp with rfl | hp
    · exact premMat fullDocket matBankSettlementMatched rfl _
    rcases Finset.mem_singleton.mp hp with rfl
    exact premMat fullDocket matReconciliationUnpaid rfl _
  have h04 : ruleMortgagePriority.horn.premises ⊆
      addAll (initState fullDocket) [loanEntitlement] := by
    intro p hp
    rcases Finset.mem_insert.mp hp with rfl | hp
    · exact premMat fullDocket matMortgageRegistered rfl _
    rcases Finset.mem_insert.mp hp with rfl | hp
    · exact premMat fullDocket matRealizationRecord rfl _
    rcases Finset.mem_singleton.mp hp with rfl
    exact premConcl fullDocket loanEntitlement _ (by simp)
  have h07 : rulePublicStanding.horn.premises ⊆
      addAll (initState fullDocket) [loanEntitlement, mortgageSecuredPriority] := by
    intro p hp
    rcases Finset.mem_singleton.mp hp with rfl
    exact premMat fullDocket matNQualified rfl _
  have h08 : ruleEcoViolation.horn.premises ⊆
      addAll (initState fullDocket)
        [loanEntitlement, mortgageSecuredPriority, publicInterestStanding] := by
    intro p hp
    rcases Finset.mem_insert.mp hp with rfl | hp
    · exact premMat fullDocket matSamplingMatch rfl _
    rcases Finset.mem_insert.mp hp with rfl | hp
    · exact premMat fullDocket matExceedance rfl _
    rcases Finset.mem_insert.mp hp with rfl | hp
    · exact premMat fullDocket matNoExculpation rfl _
    rcases Finset.mem_singleton.mp hp with rfl
    exact premMat fullDocket matInNewLawPeriod rfl _
  have h09 : ruleFishPrivate.horn.premises ⊆
      addAll (initState fullDocket)
        [loanEntitlement, mortgageSecuredPriority, publicInterestStanding,
          ecoViolationEstablished] := by
    intro p hp
    rcases Finset.mem_insert.mp hp with rfl | hp
    · exact premMat fullDocket matPondTesting rfl _
    rcases Finset.mem_singleton.mp hp with rfl
    exact premConcl fullDocket ecoViolationEstablished _ (by simp)
  have h10 : ruleEcoRemediation.horn.premises ⊆
      addAll (initState fullDocket)
        [loanEntitlement, mortgageSecuredPriority, publicInterestStanding,
          ecoViolationEstablished, fishPrivateCompensation] := by
    intro p hp
    rcases Finset.mem_insert.mp hp with rfl | hp
    · exact premMat fullDocket matEcoCostDocs rfl _
    rcases Finset.mem_insert.mp hp with rfl | hp
    · exact premConcl fullDocket publicInterestStanding _ (by simp)
    rcases Finset.mem_singleton.mp hp with rfl
    exact premConcl fullDocket ecoViolationEstablished _ (by simp)
  have h11 : ruleWageDue.horn.premises ⊆
      addAll (initState fullDocket)
        [loanEntitlement, mortgageSecuredPriority, publicInterestStanding,
          ecoViolationEstablished, fishPrivateCompensation, ecoRemediationCosts] := by
    intro p hp
    rcases Finset.mem_singleton.mp hp with rfl
    exact premMat fullDocket matWageBasisOnFile rfl _
  have h13 : ruleBankruptcyAccepted.horn.premises ⊆
      addAll (initState fullDocket)
        [loanEntitlement, mortgageSecuredPriority, publicInterestStanding,
          ecoViolationEstablished, fishPrivateCompensation, ecoRemediationCosts,
          wageDueEstablished] := by
    intro p hp
    rcases Finset.mem_insert.mp hp with rfl | hp
    · exact premMat fullDocket matInsolvencyShown rfl _
    rcases Finset.mem_singleton.mp hp with rfl
    exact premMat fullDocket matAcceptanceDecided rfl _
  have h17 : ruleWagePriority.horn.premises ⊆
      addAll (initState fullDocket)
        [loanEntitlement, mortgageSecuredPriority, publicInterestStanding,
          ecoViolationEstablished, fishPrivateCompensation, ecoRemediationCosts,
          wageDueEstablished, bankruptcyAccepted] := by
    intro p hp
    rcases Finset.mem_insert.mp hp with rfl | hp
    · exact premConcl fullDocket wageDueEstablished _ (by simp)
    rcases Finset.mem_singleton.mp hp with rfl
    exact premConcl fullDocket bankruptcyAccepted _ (by simp)
  have h14 : ruleExecStay.horn.premises ⊆
      addAll (initState fullDocket)
        [loanEntitlement, mortgageSecuredPriority, publicInterestStanding,
          ecoViolationEstablished, fishPrivateCompensation, ecoRemediationCosts,
          wageDueEstablished, bankruptcyAccepted, wageBankruptcyPriority] := by
    intro p hp
    rcases Finset.mem_singleton.mp hp with rfl
    exact premConcl fullDocket bankruptcyAccepted _ (by simp)
  have h15 : ruleCivilStay.horn.premises ⊆
      addAll (initState fullDocket)
        [loanEntitlement, mortgageSecuredPriority, publicInterestStanding,
          ecoViolationEstablished, fishPrivateCompensation, ecoRemediationCosts,
          wageDueEstablished, bankruptcyAccepted, wageBankruptcyPriority,
          bankruptcyExecutionStay] := by
    intro p hp
    rcases Finset.mem_singleton.mp hp with rfl
    exact premConcl fullDocket bankruptcyAccepted _ (by simp)
  have h16 : ruleArbStay.horn.premises ⊆
      addAll (initState fullDocket)
        [loanEntitlement, mortgageSecuredPriority, publicInterestStanding,
          ecoViolationEstablished, fishPrivateCompensation, ecoRemediationCosts,
          wageDueEstablished, bankruptcyAccepted, wageBankruptcyPriority,
          bankruptcyExecutionStay, bankruptcyCivilStay] := by
    intro p hp
    rcases Finset.mem_singleton.mp hp with rfl
    exact premConcl fullDocket bankruptcyAccepted _ (by simp)
  have h28 : ruleMaritime.horn.premises ⊆
      addAll (initState fullDocket)
        [loanEntitlement, mortgageSecuredPriority, publicInterestStanding,
          ecoViolationEstablished, fishPrivateCompensation, ecoRemediationCosts,
          wageDueEstablished, bankruptcyAccepted, wageBankruptcyPriority,
          bankruptcyExecutionStay, bankruptcyCivilStay, arbitrationStayed] := by
    intro p hp
    rcases Finset.mem_insert.mp hp with rfl | hp
    · exact premMat fullDocket matCarrierCustody rfl _
    rcases Finset.mem_singleton.mp hp with rfl
    exact premMat fullDocket matCargoDamage rfl _
  have h29 : ruleExemptionBurden.horn.premises ⊆
      addAll (initState fullDocket)
        [loanEntitlement, mortgageSecuredPriority, publicInterestStanding,
          ecoViolationEstablished, fishPrivateCompensation, ecoRemediationCosts,
          wageDueEstablished, bankruptcyAccepted, wageBankruptcyPriority,
          bankruptcyExecutionStay, bankruptcyCivilStay, arbitrationStayed,
          maritimeCarrierLiability] := by
    intro p hp
    rcases Finset.mem_insert.mp hp with rfl | hp
    · exact premConcl fullDocket maritimeCarrierLiability _ (by simp)
    rcases Finset.mem_singleton.mp hp with rfl
    exact premMat fullDocket matExemptionMaterials rfl _
  have h19 : ruleStaySuccession.horn.premises ⊆
      addAll (initState fullDocket)
        [loanEntitlement, mortgageSecuredPriority, publicInterestStanding,
          ecoViolationEstablished, fishPrivateCompensation, ecoRemediationCosts,
          wageDueEstablished, bankruptcyAccepted, wageBankruptcyPriority,
          bankruptcyExecutionStay, bankruptcyCivilStay, arbitrationStayed,
          maritimeCarrierLiability, exemptionBurdenOnCarrier] := by
    intro p hp
    rcases Finset.mem_insert.mp hp with rfl | hp
    · exact premMat fullDocket matCDeathRecord rfl _
    rcases Finset.mem_singleton.mp hp with rfl
    exact premMat fullDocket matHeirsNotYetJoined rfl _
  have h20 : ruleStayDecree.horn.premises ⊆
      addAll (initState fullDocket)
        [loanEntitlement, mortgageSecuredPriority, publicInterestStanding,
          ecoViolationEstablished, fishPrivateCompensation, ecoRemediationCosts,
          wageDueEstablished, bankruptcyAccepted, wageBankruptcyPriority,
          bankruptcyExecutionStay, bankruptcyCivilStay, arbitrationStayed,
          maritimeCarrierLiability, exemptionBurdenOnCarrier, stayForSuccession] := by
    intro p hp
    rcases Finset.mem_insert.mp hp with rfl | hp
    · exact premConcl fullDocket stayForSuccession _ (by simp)
    rcases Finset.mem_singleton.mp hp with rfl
    exact premMat fullDocket matStayEventsKept rfl _
  have h21 : ruleHoldLoan.horn.premises ⊆
      addAll (initState fullDocket)
        [loanEntitlement, mortgageSecuredPriority, publicInterestStanding,
          ecoViolationEstablished, fishPrivateCompensation, ecoRemediationCosts,
          wageDueEstablished, bankruptcyAccepted, wageBankruptcyPriority,
          bankruptcyExecutionStay, bankruptcyCivilStay, arbitrationStayed,
          maritimeCarrierLiability, exemptionBurdenOnCarrier, stayForSuccession,
          stayDecreeIssued] := by
    intro p hp
    rcases Finset.mem_singleton.mp hp with rfl
    exact premConcl fullDocket stayForSuccession _ (by simp)
  exact tstep h01 (tstep h04 (tstep h07 (tstep h08 (tstep h09 (tstep h10
    (tstep h11 (tstep h13 (tstep h17 (tstep h14 (tstep h15 (tstep h16
    (tstep h28 (tstep h29 (tstep h19 (tstep h20 (tstep h21
    (TraceOk.nil _)))))))))))))))))

/-- 满料案 17 步全轨迹产出性（每步结论互异且皆非材料）。 -/
theorem fullTraj_productive : Productive fullDocket (initState fullDocket) fullTraj := by
  refine pstep (hnew_of fullDocket loanEntitlement [] rfl (by simp)) ?_
  refine pstep (hnew_of fullDocket mortgageSecuredPriority [loanEntitlement] rfl
    (by simp)) ?_
  refine pstep (hnew_of fullDocket publicInterestStanding
    [loanEntitlement, mortgageSecuredPriority] rfl (by simp)) ?_
  refine pstep (hnew_of fullDocket ecoViolationEstablished
    [loanEntitlement, mortgageSecuredPriority, publicInterestStanding] rfl
    (by simp)) ?_
  refine pstep (hnew_of fullDocket fishPrivateCompensation
    [loanEntitlement, mortgageSecuredPriority, publicInterestStanding,
      ecoViolationEstablished] rfl (by simp)) ?_
  refine pstep (hnew_of fullDocket ecoRemediationCosts
    [loanEntitlement, mortgageSecuredPriority, publicInterestStanding,
      ecoViolationEstablished, fishPrivateCompensation] rfl (by simp)) ?_
  refine pstep (hnew_of fullDocket wageDueEstablished
    [loanEntitlement, mortgageSecuredPriority, publicInterestStanding,
      ecoViolationEstablished, fishPrivateCompensation, ecoRemediationCosts] rfl
    (by simp)) ?_
  refine pstep (hnew_of fullDocket bankruptcyAccepted
    [loanEntitlement, mortgageSecuredPriority, publicInterestStanding,
      ecoViolationEstablished, fishPrivateCompensation, ecoRemediationCosts,
      wageDueEstablished] rfl (by simp)) ?_
  refine pstep (hnew_of fullDocket wageBankruptcyPriority
    [loanEntitlement, mortgageSecuredPriority, publicInterestStanding,
      ecoViolationEstablished, fishPrivateCompensation, ecoRemediationCosts,
      wageDueEstablished, bankruptcyAccepted] rfl (by simp)) ?_
  refine pstep (hnew_of fullDocket bankruptcyExecutionStay
    [loanEntitlement, mortgageSecuredPriority, publicInterestStanding,
      ecoViolationEstablished, fishPrivateCompensation, ecoRemediationCosts,
      wageDueEstablished, bankruptcyAccepted, wageBankruptcyPriority] rfl
    (by simp)) ?_
  refine pstep (hnew_of fullDocket bankruptcyCivilStay
    [loanEntitlement, mortgageSecuredPriority, publicInterestStanding,
      ecoViolationEstablished, fishPrivateCompensation, ecoRemediationCosts,
      wageDueEstablished, bankruptcyAccepted, wageBankruptcyPriority,
      bankruptcyExecutionStay] rfl (by simp)) ?_
  refine pstep (hnew_of fullDocket arbitrationStayed
    [loanEntitlement, mortgageSecuredPriority, publicInterestStanding,
      ecoViolationEstablished, fishPrivateCompensation, ecoRemediationCosts,
      wageDueEstablished, bankruptcyAccepted, wageBankruptcyPriority,
      bankruptcyExecutionStay, bankruptcyCivilStay] rfl (by simp)) ?_
  refine pstep (hnew_of fullDocket maritimeCarrierLiability
    [loanEntitlement, mortgageSecuredPriority, publicInterestStanding,
      ecoViolationEstablished, fishPrivateCompensation, ecoRemediationCosts,
      wageDueEstablished, bankruptcyAccepted, wageBankruptcyPriority,
      bankruptcyExecutionStay, bankruptcyCivilStay, arbitrationStayed] rfl
    (by simp)) ?_
  refine pstep (hnew_of fullDocket exemptionBurdenOnCarrier
    [loanEntitlement, mortgageSecuredPriority, publicInterestStanding,
      ecoViolationEstablished, fishPrivateCompensation, ecoRemediationCosts,
      wageDueEstablished, bankruptcyAccepted, wageBankruptcyPriority,
      bankruptcyExecutionStay, bankruptcyCivilStay, arbitrationStayed,
      maritimeCarrierLiability] rfl (by simp)) ?_
  refine pstep (hnew_of fullDocket stayForSuccession
    [loanEntitlement, mortgageSecuredPriority, publicInterestStanding,
      ecoViolationEstablished, fishPrivateCompensation, ecoRemediationCosts,
      wageDueEstablished, bankruptcyAccepted, wageBankruptcyPriority,
      bankruptcyExecutionStay, bankruptcyCivilStay, arbitrationStayed,
      maritimeCarrierLiability, exemptionBurdenOnCarrier] rfl (by simp)) ?_
  refine pstep (hnew_of fullDocket stayDecreeIssued
    [loanEntitlement, mortgageSecuredPriority, publicInterestStanding,
      ecoViolationEstablished, fishPrivateCompensation, ecoRemediationCosts,
      wageDueEstablished, bankruptcyAccepted, wageBankruptcyPriority,
      bankruptcyExecutionStay, bankruptcyCivilStay, arbitrationStayed,
      maritimeCarrierLiability, exemptionBurdenOnCarrier, stayForSuccession] rfl
    (by simp)) ?_
  exact pstep (hnew_of fullDocket holdOnLoanFinal
    [loanEntitlement, mortgageSecuredPriority, publicInterestStanding,
      ecoViolationEstablished, fishPrivateCompensation, ecoRemediationCosts,
      wageDueEstablished, bankruptcyAccepted, wageBankruptcyPriority,
      bankruptcyExecutionStay, bankruptcyCivilStay, arbitrationStayed,
      maritimeCarrierLiability, exemptionBurdenOnCarrier, stayForSuccession,
      stayDecreeIssued] rfl (by simp))
    (Productive.nil _)

/-- 满料案 17 步全轨迹时点严格递增。 -/
theorem fullTraj_times : TimesInc fullTraj :=
  show TimesInc [stR01, stR04, stR07, stR08, stR09, stR10, stR11, stR13, stR17, stR14,
    stR15, stR16, stR28, stR29, stR19, stR20, stR21] from
  incCons2 0 stR01 stR04 [stR07, stR08, stR09, stR10, stR11, stR13, stR17, stR14,
    stR15, stR16, stR28, stR29, stR19, stR20, stR21] rfl rfl
  (incCons2 1 stR04 stR07 [stR08, stR09, stR10, stR11, stR13, stR17, stR14,
    stR15, stR16, stR28, stR29, stR19, stR20, stR21] rfl rfl
  (incCons2 2 stR07 stR08 [stR09, stR10, stR11, stR13, stR17, stR14,
    stR15, stR16, stR28, stR29, stR19, stR20, stR21] rfl rfl
  (incCons2 3 stR08 stR09 [stR10, stR11, stR13, stR17, stR14,
    stR15, stR16, stR28, stR29, stR19, stR20, stR21] rfl rfl
  (incCons2 4 stR09 stR10 [stR11, stR13, stR17, stR14,
    stR15, stR16, stR28, stR29, stR19, stR20, stR21] rfl rfl
  (incCons2 5 stR10 stR11 [stR13, stR17, stR14,
    stR15, stR16, stR28, stR29, stR19, stR20, stR21] rfl rfl
  (incCons2 6 stR11 stR13 [stR17, stR14,
    stR15, stR16, stR28, stR29, stR19, stR20, stR21] rfl rfl
  (incCons2 7 stR13 stR17 [stR14,
    stR15, stR16, stR28, stR29, stR19, stR20, stR21] rfl rfl
  (incCons2 8 stR17 stR14 [stR15, stR16, stR28, stR29, stR19, stR20, stR21] rfl rfl
  (incCons2 9 stR14 stR15 [stR16, stR28, stR29, stR19, stR20, stR21] rfl rfl
  (incCons2 10 stR15 stR16 [stR28, stR29, stR19, stR20, stR21] rfl rfl
  (incCons2 11 stR16 stR28 [stR29, stR19, stR20, stR21] rfl rfl
  (incCons2 12 stR28 stR29 [stR19, stR20, stR21] rfl rfl
  (incCons2 13 stR29 stR19 [stR20, stR21] rfl rfl
  (incCons2 14 stR19 stR20 [stR21] rfl rfl
  (incCons2 15 stR20 stR21 [] rfl rfl
  (TimesInc.one stR21))))))))))))))))

/-- 满料案全轨迹长度读数。 -/
theorem fullTraj_length : fullTraj.length = 17 := by rfl

/-- 折叠读数：良构终态即 `runNetTrace` 结果（`addAll` 与 `runNetTrace` 定义性一致）。 -/
theorem fullTraj_run : runNetTrace (initState fullDocket) fullTraj =
    addAll (initState fullDocket) fullTrajConcls :=
  traceOk_runNetTrace fullTraj_ok

/-- 内核级全查：17 步触发的规则法源全部在效力窗口内。 -/
theorem fullTraj_sources_scan :
    fullTraj.all (fun st => srcInForce st.rule.src) = true := by rfl

/-- 17 步触发的规则法源全部在效力窗口内（读出形）。 -/
theorem fullTraj_sources : ∀ st ∈ fullTraj, srcInForce st.rule.src = true :=
  List.all_eq_true.mp fullTraj_sources_scan

/-- 内核级全查：深度 3 生态链三步的法源全部在效力窗口内。 -/
theorem ecoChain_sources_scan :
    ecoChain.all (fun st => srcInForce st.rule.src) = true := by rfl

/-- 深度 3 生态链三步的法源全部在效力窗口内（读出形）。 -/
theorem ecoChain_sources : ∀ st ∈ ecoChain, srcInForce st.rule.src = true :=
  List.all_eq_true.mp ecoChain_sources_scan

/-- 网络原子总数读数（57 材料＋29 推导＋10 失败）。 -/
theorem net_atom_card : Fintype.card Atom = 96 := by rfl

/-! ## 四、部分料案：缺料阻断与轨迹差异 -/

/-- 部分料案一：L05 超限实测材料缺失（其余逐字段照满料案）。 -/
def partialEcoDocket : CaseDocket :=
  { fullDocket with
    m05 := ⟨fullDocket.m05.parties, fullDocket.m05.samplingMatch, false,
      fullDocket.m05.pondTesting, fullDocket.m05.ecoCostDocs,
      fullDocket.m05.noExculpation, fullDocket.m05.inNewLawPeriod⟩ }

/-- 部分料案一的坏集：缺失材料＋只能经它推出的生态链结论。 -/
def badEco : Finset Atom :=
  {matExceedance, ecoViolationEstablished, fishPrivateCompensation, ecoRemediationCosts}

/-- 内核级全查：结论落坏集的规则，其前提都撞坏集（阻断表）。 -/
theorem eco_block_scan : familyRuleList.all (fun r =>
    (!decide (r.horn.conclusion ∈ badEco)) ||
      (!decide ((r.horn.premises ∩ badEco) = ∅))) = true := by rfl

/-- **避开坏集模型**（一般形；本件独立复证 Gap05 同名引理）：初始事实避开坏集、
    且每条"结论落坏集"的规则其前提都撞坏集 ⇒ 全域去坏集是模型。 -/
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

/-- 阻断表从内核 Bool 检查读成规则级命题。 -/
theorem eco_block (r : LawRule) (hr : r ∈ familyRuleList)
    (hcon : r.horn.conclusion ∈ badEco) : r.horn.premises ∩ badEco ≠ ∅ := by
  have hchk := List.all_eq_true.mp eco_block_scan r hr
  simp only [Bool.or_eq_true, not_decide_eq_true] at hchk
  rcases hchk with h9 | h9
  · exact absurd hcon h9
  · exact h9

/-- 部分料案一初始状态与坏集不相交。 -/
theorem eco_initial_disjoint : Disjoint (initState partialEcoDocket) badEco := by
  rw [Finset.disjoint_left]
  intro x hx hb
  have h1 : materialHolds x partialEcoDocket = true := (Finset.mem_filter.mp hx).2
  rcases Finset.mem_insert.mp hb with rfl | hb
  · rw [show materialHolds matExceedance partialEcoDocket = false from rfl] at h1
    exact Bool.noConfusion h1
  rcases Finset.mem_insert.mp hb with rfl | hb
  · rw [show materialHolds ecoViolationEstablished partialEcoDocket = false from rfl] at h1
    exact Bool.noConfusion h1
  rcases Finset.mem_insert.mp hb with rfl | hb
  · rw [show materialHolds fishPrivateCompensation partialEcoDocket = false from rfl] at h1
    exact Bool.noConfusion h1
  rcases Finset.mem_singleton.mp hb with rfl
  · rw [show materialHolds ecoRemediationCosts partialEcoDocket = false from rfl] at h1
    exact Bool.noConfusion h1

/-- 部分料案一的避开坏集模型。 -/
theorem eco_model : isModel (hornOf partialEcoDocket) (Finset.univ \ badEco) := by
  refine isModel_avoiding_gen (hornOf partialEcoDocket) badEco eco_initial_disjoint ?_
  intro rh hrh hcon
  obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hrh
  exact eco_block r (List.mem_toFinset.mp hr) hcon

/-- 坏集原子不可推导（部分料案一）。 -/
theorem not_in_closure_partialEco (f : Atom) (hf : f ∈ badEco) :
    f ∉ closureAt (hornOf partialEcoDocket) := by
  intro hmem
  obtain ⟨_, hnot⟩ := Finset.mem_sdiff.mp
    (closure_only_entailed (hornOf partialEcoDocket) hmem
      (Finset.univ \ badEco) eco_model)
  exact hnot hf

/-- 生态违法认定在满料闭包内、在部分料案一闭包外。 -/
theorem ecoViolation_partial_diff :
    ecoViolationEstablished ∈ closureAt familyHorn ∧
      ecoViolationEstablished ∉ closureAt (hornOf partialEcoDocket) :=
  ⟨ecoViolationEstablished_mem,
    not_in_closure_partialEco ecoViolationEstablished (by simp [badEco])⟩

/-- 部分料案一：任何从材料出发的实际轨迹都到不了生态链三结论。 -/
theorem partial_eco_no_traj_reaches : ∀ (T : NetState) (tr : NetTrace) (a : Atom),
    TraceOk partialEcoDocket (initState partialEcoDocket) T tr → a ∈ badEco → a ∉ T :=
  fun _ _ a h ha hmem =>
    not_in_closure_partialEco a ha (trace_reaches_mem_closure h hmem)

/-- 部分料案一的实际轨迹（1 步：R07 公益资格仍触发——缺的是 L05 材料，
    L14 的资格材料未动）。 -/
def stP0 : Step := ⟨0, rulePublicStanding, by simp [familyRuleList]⟩

def partialEcoTraj : NetTrace := [stP0]

theorem partialEcoTraj_ok : TraceOk partialEcoDocket (initState partialEcoDocket)
    (addAll (initState partialEcoDocket) [publicInterestStanding]) partialEcoTraj := by
  have h0 : rulePublicStanding.horn.premises ⊆
      addAll (initState partialEcoDocket) ([] : List Atom) := by
    intro p hp
    rcases Finset.mem_singleton.mp hp with rfl
    exact premMat partialEcoDocket matNQualified rfl []
  exact tstep h0 (TraceOk.nil _)

theorem partialEcoTraj_productive : Productive partialEcoDocket (initState partialEcoDocket)
    partialEcoTraj :=
  pstep (hnew_of partialEcoDocket publicInterestStanding [] rfl (by simp))
    (Productive.nil _)

theorem partialEcoTraj_times : TimesInc partialEcoTraj := TimesInc.one stP0

/-- 部分料案二：L08 受理决定材料缺失（其余逐字段照满料案）。 -/
def partialBankDocket : CaseDocket :=
  { fullDocket with
    m08 := ⟨fullDocket.m08.parties, fullDocket.m08.separateAccounts,
      fullDocket.m08.insolvencyShown, false⟩ }

/-- 部分料案二的坏集：缺失材料＋破产族链根＋只能经它推出的五结论。 -/
def badBank : Finset Atom :=
  {matAcceptanceDecided, bankruptcyAccepted, bankruptcyExecutionStay,
    bankruptcyCivilStay, arbitrationStayed, wageBankruptcyPriority}

/-- 内核级全查（部分料案二阻断表）。 -/
theorem bank_block_scan : familyRuleList.all (fun r =>
    (!decide (r.horn.conclusion ∈ badBank)) ||
      (!decide ((r.horn.premises ∩ badBank) = ∅))) = true := by rfl

theorem bank_block (r : LawRule) (hr : r ∈ familyRuleList)
    (hcon : r.horn.conclusion ∈ badBank) : r.horn.premises ∩ badBank ≠ ∅ := by
  have hchk := List.all_eq_true.mp bank_block_scan r hr
  simp only [Bool.or_eq_true, not_decide_eq_true] at hchk
  rcases hchk with h9 | h9
  · exact absurd hcon h9
  · exact h9

theorem bank_initial_disjoint : Disjoint (initState partialBankDocket) badBank := by
  rw [Finset.disjoint_left]
  intro x hx hb
  have h1 : materialHolds x partialBankDocket = true := (Finset.mem_filter.mp hx).2
  rcases Finset.mem_insert.mp hb with rfl | hb
  · rw [show materialHolds matAcceptanceDecided partialBankDocket = false from rfl] at h1
    exact Bool.noConfusion h1
  rcases Finset.mem_insert.mp hb with rfl | hb
  · rw [show materialHolds bankruptcyAccepted partialBankDocket = false from rfl] at h1
    exact Bool.noConfusion h1
  rcases Finset.mem_insert.mp hb with rfl | hb
  · rw [show materialHolds bankruptcyExecutionStay partialBankDocket = false from rfl] at h1
    exact Bool.noConfusion h1
  rcases Finset.mem_insert.mp hb with rfl | hb
  · rw [show materialHolds bankruptcyCivilStay partialBankDocket = false from rfl] at h1
    exact Bool.noConfusion h1
  rcases Finset.mem_insert.mp hb with rfl | hb
  · rw [show materialHolds arbitrationStayed partialBankDocket = false from rfl] at h1
    exact Bool.noConfusion h1
  rcases Finset.mem_singleton.mp hb with rfl
  · rw [show materialHolds wageBankruptcyPriority partialBankDocket = false from rfl] at h1
    exact Bool.noConfusion h1

theorem bank_model : isModel (hornOf partialBankDocket) (Finset.univ \ badBank) := by
  refine isModel_avoiding_gen (hornOf partialBankDocket) badBank bank_initial_disjoint ?_
  intro rh hrh hcon
  obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hrh
  exact bank_block r (List.mem_toFinset.mp hr) hcon

theorem not_in_closure_partialBank (f : Atom) (hf : f ∈ badBank) :
    f ∉ closureAt (hornOf partialBankDocket) := by
  intro hmem
  obtain ⟨_, hnot⟩ := Finset.mem_sdiff.mp
    (closure_only_entailed (hornOf partialBankDocket) hmem
      (Finset.univ \ badBank) bank_model)
  exact hnot hf

/-- 破产族链根与工资优先权：满料闭包内、部分料案二闭包外。 -/
theorem bankruptcy_partial_diff :
    bankruptcyAccepted ∈ closureAt familyHorn ∧
      wageBankruptcyPriority ∈ closureAt familyHorn ∧
      bankruptcyAccepted ∉ closureAt (hornOf partialBankDocket) ∧
      wageBankruptcyPriority ∉ closureAt (hornOf partialBankDocket) :=
  ⟨bankruptcyAccepted_mem, wageBankruptcyPriority_mem,
    not_in_closure_partialBank bankruptcyAccepted (by simp [badBank]),
    not_in_closure_partialBank wageBankruptcyPriority (by simp [badBank])⟩

/-- 部分料案二：任何从材料出发的实际轨迹都到不了坏集原子。 -/
theorem partial_bank_no_traj_reaches : ∀ (T : NetState) (tr : NetTrace) (a : Atom),
    TraceOk partialBankDocket (initState partialBankDocket) T tr → a ∈ badBank → a ∉ T :=
  fun _ _ a h ha hmem =>
    not_in_closure_partialBank a ha (trace_reaches_mem_closure h hmem)

/-- 部分料案二的实际轨迹（4 步：工资债权与继承中止链照常运行——缺的是
    L08 受理决定，L07/L06/L13 材料未动）。 -/
def stQ0 : Step := ⟨0, ruleWageDue, by simp [familyRuleList]⟩
def stQ1 : Step := ⟨1, ruleStaySuccession, by simp [familyRuleList]⟩
def stQ2 : Step := ⟨2, ruleStayDecree, by simp [familyRuleList]⟩
def stQ3 : Step := ⟨3, ruleHoldLoan, by simp [familyRuleList]⟩

def partialBankTraj : NetTrace := [stQ0, stQ1, stQ2, stQ3]

theorem partialBankTraj_ok : TraceOk partialBankDocket (initState partialBankDocket)
    (addAll (initState partialBankDocket)
      [wageDueEstablished, stayForSuccession, stayDecreeIssued, holdOnLoanFinal])
    partialBankTraj := by
  have h0 : ruleWageDue.horn.premises ⊆
      addAll (initState partialBankDocket) ([] : List Atom) := by
    intro p hp
    rcases Finset.mem_singleton.mp hp with rfl
    exact premMat partialBankDocket matWageBasisOnFile rfl []
  have h1 : ruleStaySuccession.horn.premises ⊆
      addAll (initState partialBankDocket) [wageDueEstablished] := by
    intro p hp
    rcases Finset.mem_insert.mp hp with rfl | hp
    · exact premMat partialBankDocket matCDeathRecord rfl _
    rcases Finset.mem_singleton.mp hp with rfl
    exact premMat partialBankDocket matHeirsNotYetJoined rfl _
  have h2 : ruleStayDecree.horn.premises ⊆
      addAll (initState partialBankDocket) [wageDueEstablished, stayForSuccession] := by
    intro p hp
    rcases Finset.mem_insert.mp hp with rfl | hp
    · exact premConcl partialBankDocket stayForSuccession _ (by simp)
    rcases Finset.mem_singleton.mp hp with rfl
    exact premMat partialBankDocket matStayEventsKept rfl _
  have h3 : ruleHoldLoan.horn.premises ⊆
      addAll (initState partialBankDocket)
        [wageDueEstablished, stayForSuccession, stayDecreeIssued] := by
    intro p hp
    rcases Finset.mem_singleton.mp hp with rfl
    exact premConcl partialBankDocket stayForSuccession _ (by simp)
  exact tstep h0 (tstep h1 (tstep h2 (tstep h3 (TraceOk.nil _))))

theorem partialBankTraj_productive : Productive partialBankDocket
    (initState partialBankDocket) partialBankTraj := by
  refine pstep (hnew_of partialBankDocket wageDueEstablished [] rfl (by simp)) ?_
  refine pstep (hnew_of partialBankDocket stayForSuccession [wageDueEstablished] rfl
    (by simp)) ?_
  refine pstep (hnew_of partialBankDocket stayDecreeIssued
    [wageDueEstablished, stayForSuccession] rfl (by simp)) ?_
  exact pstep (hnew_of partialBankDocket holdOnLoanFinal
    [wageDueEstablished, stayForSuccession, stayDecreeIssued] rfl (by simp))
    (Productive.nil _)

theorem partialBankTraj_times : TimesInc partialBankTraj :=
  incCons2 0 stQ0 stQ1 [stQ2, stQ3] rfl rfl
    (incCons2 1 stQ1 stQ2 [stQ3] rfl rfl
      (incCons2 2 stQ2 stQ3 [] rfl rfl (TimesInc.one stQ3)))

/-! ## 五、旗舰定理（针 42 合同句） -/

/-- **针 42（网络载体存在形）**：共同十四族网络上存在实际非空轨迹——
    非空、3 次发射的链式触发（R07/R08 从材料、R10 汇聚消费两前置结论——
    Gap05 HProvN 高度 3 的同一链形）、时点递增、从在卷材料出发良构运行、
    产出性（终止单调上界适用）、R10 结论确实留在终态、每步法源在效力窗口内、
    终态全部落在该网络 Horn 闭包内（与 closureAt 一致）。 -/
theorem nontrivial_net_trajectory_exists :
    ∃ (d : CaseDocket) (tr : NetTrace) (T : NetState),
      tr ≠ [] ∧
      3 ≤ tr.length ∧
      TimesInc tr ∧
      TraceOk d (initState d) T tr ∧
      Productive d (initState d) tr ∧
      ecoRemediationCosts ∈ T ∧
      (∀ st ∈ tr, srcInForce st.rule.src = true) ∧
      (∀ a ∈ T, a ∈ closureAt (hornOf d)) ∧
      (∀ p ∈ rulePublicStanding.horn.premises, materialHolds p fullDocket = true) ∧
      (∀ p ∈ ruleEcoViolation.horn.premises, materialHolds p fullDocket = true) ∧
      publicInterestStanding ∈ ruleEcoRemediation.horn.premises ∧
      ecoViolationEstablished ∈ ruleEcoRemediation.horn.premises :=
  ⟨fullDocket, ecoChain,
    addAll (initState fullDocket)
      [publicInterestStanding, ecoViolationEstablished, ecoRemediationCosts],
    List.cons_ne_nil _ _, by rfl, ecoChain_times, ecoChain_ok, ecoChain_productive,
    premConcl fullDocket ecoRemediationCosts _ (by simp),
    ecoChain_sources,
    fun _ ha => traceOk_init_closure ecoChain_ok ha,
    eco_chain_depth3.1, eco_chain_depth3.2.1, eco_chain_depth3.2.2.1,
    eco_chain_depth3.2.2.2.1⟩

/-- **满料案端到端**：17 步全轨迹的全部读数——良构、产出、时点递增、长度 17、
    与闭包一致（终态 ⊆ familyHorn 闭包）、每步法源在窗口内、含深度 3 生态链
    （作为 ecoChain 的同构链在 fullTraj 内重触发：见 ecoChain_ok）、终止单调
    上界 17＋初始基数 ≤ 96。 -/
theorem full_net_trajectory_end_to_end :
    TraceOk fullDocket (initState fullDocket)
      (addAll (initState fullDocket) fullTrajConcls) fullTraj ∧
    Productive fullDocket (initState fullDocket) fullTraj ∧
    TimesInc fullTraj ∧
    fullTraj.length = 17 ∧
    fullTraj ≠ [] ∧
    (runNetTrace (initState fullDocket) fullTraj =
      addAll (initState fullDocket) fullTrajConcls) ∧
    (∀ a ∈ addAll (initState fullDocket) fullTrajConcls, a ∈ closureAt familyHorn) ∧
    (∀ st ∈ fullTraj, srcInForce st.rule.src = true) ∧
    (fullTraj.length + (initState fullDocket).card ≤ Fintype.card Atom) ∧
    (Fintype.card Atom = 96) :=
  ⟨fullTraj_ok, fullTraj_productive, fullTraj_times, fullTraj_length,
    List.cons_ne_nil _ _, fullTraj_run,
    fun _ ha => traceOk_init_closure fullTraj_ok ha,
    fullTraj_sources,
    productive_card_bound fullTraj_productive, net_atom_card⟩

/-- **部分料案差异**：同一规则网络，材料不同 ⇒ 实际轨迹不同——部分案仍有
    非空良构产出轨迹（一/四步），但被缺料挡住的结论对任何轨迹都到不了
    （满料案上同一结论在闭包内且被 fullTraj 实际产出）。 -/
theorem partial_net_trajectory_difference :
    -- 部分料案一：1 步轨迹运行、生态链三结论任何轨迹到不了
    (partialEcoTraj ≠ [] ∧ TimesInc partialEcoTraj ∧
      TraceOk partialEcoDocket (initState partialEcoDocket)
        (addAll (initState partialEcoDocket) [publicInterestStanding]) partialEcoTraj ∧
      Productive partialEcoDocket (initState partialEcoDocket) partialEcoTraj ∧
      (∀ (T : NetState) (tr : NetTrace),
        TraceOk partialEcoDocket (initState partialEcoDocket) T tr →
          ecoViolationEstablished ∉ T ∧ fishPrivateCompensation ∉ T ∧
            ecoRemediationCosts ∉ T) ∧
      (ecoViolationEstablished ∈ closureAt familyHorn)) ∧
    -- 部分料案二：4 步轨迹运行、破产链五结论任何轨迹到不了
    (partialBankTraj ≠ [] ∧ TimesInc partialBankTraj ∧
      TraceOk partialBankDocket (initState partialBankDocket)
        (addAll (initState partialBankDocket)
          [wageDueEstablished, stayForSuccession, stayDecreeIssued, holdOnLoanFinal])
        partialBankTraj ∧
      Productive partialBankDocket (initState partialBankDocket) partialBankTraj ∧
      (∀ (T : NetState) (tr : NetTrace),
        TraceOk partialBankDocket (initState partialBankDocket) T tr →
          bankruptcyAccepted ∉ T ∧ bankruptcyExecutionStay ∉ T ∧
            bankruptcyCivilStay ∉ T ∧ arbitrationStayed ∉ T ∧
            wageBankruptcyPriority ∉ T) ∧
      (bankruptcyAccepted ∈ closureAt familyHorn ∧
        wageBankruptcyPriority ∈ closureAt familyHorn)) :=
  ⟨⟨List.cons_ne_nil _ _, partialEcoTraj_times, partialEcoTraj_ok,
      partialEcoTraj_productive,
      fun T tr h =>
        ⟨partial_eco_no_traj_reaches T tr ecoViolationEstablished h (by simp [badEco]),
          partial_eco_no_traj_reaches T tr fishPrivateCompensation h (by simp [badEco]),
          partial_eco_no_traj_reaches T tr ecoRemediationCosts h (by simp [badEco])⟩,
      ecoViolation_partial_diff.1⟩,
    ⟨List.cons_ne_nil _ _, partialBankTraj_times, partialBankTraj_ok,
      partialBankTraj_productive,
      fun T tr h =>
        ⟨partial_bank_no_traj_reaches T tr bankruptcyAccepted h (by simp [badBank]),
          partial_bank_no_traj_reaches T tr bankruptcyExecutionStay h (by simp [badBank]),
          partial_bank_no_traj_reaches T tr bankruptcyCivilStay h (by simp [badBank]),
          partial_bank_no_traj_reaches T tr arbitrationStayed h (by simp [badBank]),
          partial_bank_no_traj_reaches T tr wageBankruptcyPriority h (by simp [badBank])⟩,
      bankruptcy_partial_diff.1, bankruptcy_partial_diff.2.1⟩⟩

end JurisLean.Seams.UnifiedNetTrajectory
