import Mathlib.Data.Finset.Basic
import Mathlib.Data.List.Basic
import Mathlib.Tactic
import JurisLean.KernelV3
import JurisLean.Seams.Representation
import JurisLean.Seams.PrecedentFlow
import JurisLean.Seams.SourceNorms

/-!
S0/S1 针位承接件（附录 I.13 第 01–09 针）—— 以原验收名命名的九条真定理。

出处：`docs/spec/20261007-统一法律数学模型_附录I_Lean施工明细.md` §I.13 第 755–763 行
（S0=5 针、S1=4 针）；绑定现状见 `docs/full-math/BINDING_217_and_60.md` 第 252–260 行。

## 一、法律语义（人话）

附录 I.13 把旧 60 针的历史验收句逐名重立为"拟合同"：不得用同名弱式冒充，也不得把
前提外填。本件把第 01–09 针落成可命名的真定理，统一策略是**由实际构造实例化锚定理**：
先在本件内构造具体载体（小 Finset/List 载荷、具体编码函数、具体制度事件表），
把锚定理的前提真实证出，再套锚引理得出结论。逐针如下：

- 01 `representation_observations_preserved`（I.13:755）：锚 `Representation.lean:162`
  只在给定 `FaithfulRep` 下搬运观察。本件构造具体案卷片段（身份键 + 请求额档 + 登记位），
  **从实际编码证出** `RoundTrip` 与 `Coverage`，再实例化锚定理。
- 02 `representable_roundtrip`（I.13:756）：锚 `Representation.lean:153 obsModel_roundTrip`
  可消费往返。本件写具体身份编解码（作用域↔位），`identity_roundtrip` 由构造逐 case 证明，
  不以外填 `hrt` 代替；再经 `identityFragment` 交给锚引理消费。
- 03 `ontic_epistemic_separation_witness`（I.13:757）：锚
  `AdjudicationBridge.lean:746 proof_failure_not_ontic_negation` 是两个不同来源对象的
  乘积见证。本件改为**同一生成输入**（同一在卷材料）下的两个运行：本体状态 R 不同、
  认识状态 E 相同、认识层无法建立清偿判断（证明失败），并复用 `KernelV3` 的
  "真值为真而判断不成立"记录。
- 04 `power_obligation_occurrence_independent`（I.13:758）：本原名全树未见声明。本件在
  **同一制度**（价款债务清偿与消灭制度）的事件表内交出三个具名法律事件，其
  （权力位, 义务位, 实际发生）标志恰为单位向量 (1,0,0)/(0,1,0)/(0,0,1)，并附
  三事件互异、三维两两可分、三维各自两值可取的独立性条款；不是三个任意 Bool。
- 05 `joint_legal_model_exists`（I.13:759）：锚 `Representation.lean:366` 是 `Fin 2`
  两投影见证（该旧引理保留不动）。本件以**十四族（L01–L14）共同材料网络**为第一层
  片段、常值登记层为第二层，在同一法律对象层上经锚 `joint_model_is_not_collapsed`
  交出非退化联合见证，并附"十四族每族材料非空"的完整性条款。
- 06 `applicability_matches_source_semantics`（I.13:760）：锚
  `PrecedentFlow.lean:490 applicableAtBool_true_iff` 只是布尔查询的时点记录。本件给出
  `selected_iff_applicable`（选中 ⟺ 目录内且按声明语义可适用，对全部记录成立）与
  规范选择的全域布尔反射，并在两个时点上给出非退化实例（同一目录的选择确实随
  声明语义变化）。
- 07 `finite_priority_maximal_elements_exist`（I.13:761）：复用
  `SourceNorms.lean:308 exists_maximal_acyclic`（有限无环 ⇒ 极大元存在），并同一定理内
  附"极大元不等于唯一适用规范"的 P-015 平位阶见证（两个不同极大元）。
- 08 `horn_closure_semantic_iff`（I.13:762）：`SourceNorms.lean:171` 的同 basename 定理
  在纯正 Horn 原域上**语句不变地**承接为本针名定理（引用重述，不改动语句）；
  法律规则实例化与来源树接线按 I.13 明示另接，不在本件。
- 09 `incomparable_norms_not_forced_unique`（I.13:763）：锚
  `SourceNorms.lean:521 p015_some_not_unique_maximal` 的反例保留。本件把它升格为
  完整合同：存在两条**不可比**（位阶互不压过）规范，两条在冲突组内**都是极大元**
  （位阶不淘汰任何一条，分支完整保留），政策择一（判给新特别规定）仍然存在，
  但"组内唯一极大元/唯一适用规范"被显式否定。

## 二、数学对象

- 身份层：`IdScope`（作用域枚举）、`ScopedIdentity`（五字段键：案件/主体/争点/阶段/作用域）、
  `IdentityCode`（模型侧码字：四 Fin 分量 + 作用域位）、`encodeKey`/`decodeKey`、
  `identity_roundtrip`（decode∘encode = id，双向 `encode_decode`）。
- 表示片段：`caseFragment`（01 针载体）、`identityFragment`（02 针载体），
  复用 `JurisLean.Seams.Representation.Fragment/RoundTrip/Coverage/FaithfulRep/obsModel`。
- 分离见证：`GenInput`（生成输入）、`OnticR`（本体）、`EpistemicE`（认识）、
  `epistemicOf`（E 只由生成输入决定）、`SepRun`（输入 + 本体）、`docket`（在卷材料）。
- 制度事件：`DischargeEvent` 三构造子 + `powerArisen/obligationStanding/actuallyOccurred`
  三标志函数 + `dischargeInstitution`（同一制度事件表）。
- 联合网络：`MaterialPayload`（缺/已声明/有分歧）、`CaseMaterials`（身份键 + 十四族载荷）、
  `familyNet`（ι = `Fin 14` 的片段）、`registerLayer`（常值登记层）、`uniformCase`。
- 法源选择：`selectAt`（目录 × 时点 → 可适用子表，谓词即 `PrecedentFlow.applicableAtBool`）。
- 位阶：复用 `JurisLean.Seams.SourceNorms.provisionRank/maximal_left_of_rank_tie/
  maximal_right_of_rank_tie/p015_some_not_unique_maximal` 与
  `JurisLean.Genealogy.Part1.P015`。

## 三、本件证什么、不证什么

**证**：上述九针各一条定理，全部由本件内构造或既有锚定理合成；每针前提（如
`FaithfulRep`、`RoundTrip`、`hsep`）都在本件内对具体载体真实证出，无一外填为假设。
**不证**（逐针边界，另见各定理 doc 注）：
- 01/02 只覆盖所声明的观察族与五字段身份键，不证全 U01 观察族；显示名归一只做键级
  投影，不含字符串运算。
- 03 只在单一在卷材料形态上作见证，"证明失败"以收款凭证在卷为必要条件，不是完整
  证明负担演算。
- 04 的独立性是"单位向量实现 + 两两可分 + 各自两值 + 事件互异"，不主张也不可能主张
  一般布尔函数意义下的维间函数独立（单位向量族本就被 (¬p∧¬o) 型函数预测）。
- 05 的每族载荷是三值状态（缺/已声明/有分歧），**不是**各族完整材料内容；L01–L14
  完整材料网络是全工程量级的工作，本件只以状态级载荷替代 `Fin 2` 两投影总入口见证。
- 06 不建 `VersionEnv`/`KnowledgeView` 桥，不做 I.4.2 的具名冲突排除枚举（A/B 互斥
  分支全枚举合同仍开放）；缺版本与真实规范冲突的分别报告不在本件。
- 07 的非唯一性见证只在二元冲突组上。
- 08 语句与锚完全一致，纯 Horn 原域；法律规则实例化与来源树另接。
- 09 的政策择一是 P-015 台账政策（特别法/新法优先），不构成对任何真实条文位阶或
  效力冲突的认定。

## 四、档位

九针均为[已证，认定待 CI]。本件不含占位证明、不引入未证公理、不用 `native_decide`、
无 `: True :=` 逃避式；`decide` 只用于 `Nat`/`Bool`/枚举与短字符串字面量的闭式归约，
`rfl` 只用于本件内可定义展开的闭式计算。按仓库边界约定，Lean 权威认定在 CI；
本机不运行 Lean，当前状态 CI_NOT_RUN（fail-closed），本地静态自检仅为 provisional。
-/

namespace JurisLean.Seams.UnifiedNeedlesS0S1

open JurisLean.Seams.Representation
open JurisLean.Genealogy.Part1

/-! ## 第 01–02 针公共底座：实际身份编码 -/

/-- 法律作用域标签：规范作用域与分析作用域（I.4.1：键含作用域，显示名另存）。 -/
inductive IdScope where
  /-- 规范作用域。 -/
  | normScope
  /-- 分析作用域。 -/
  | analysisScope

/-- 归一后的法律身份键：案件、主体、争点、阶段、作用域五字段；显示名不进键。 -/
structure ScopedIdentity where
  caseNo : Fin 4
  party : Fin 4
  issue : Fin 3
  stage : Fin 2
  scope : IdScope

/-- 作用域压成模型侧一位 Bool。 -/
def scopeBit : IdScope → Bool
  | .normScope => false
  | .analysisScope => true

/-- 作用域位读回作用域。 -/
def scopeOfBit : Bool → IdScope
  | false => .normScope
  | true => .analysisScope

/-- 模型侧码字：四个键分量的原样槽位 + 作用域位。 -/
structure IdentityCode where
  codeCase : Fin 4
  codeParty : Fin 4
  codeIssue : Fin 3
  codeStage : Fin 2
  codeScope : Bool

/-- 实际编码：法律身份键 → 模型侧码字。 -/
def encodeKey (s : ScopedIdentity) : IdentityCode :=
  ⟨s.caseNo, s.party, s.issue, s.stage, scopeBit s.scope⟩

/-- 实际解码：模型侧码字 → 法律身份键。 -/
def decodeKey (c : IdentityCode) : ScopedIdentity :=
  ⟨c.codeCase, c.codeParty, c.codeIssue, c.codeStage, scopeOfBit c.codeScope⟩

/-- **identity_roundtrip（I.4.1 拟合同）**：实际编码的往返一致，从本案编码构造证明，
    不是外填假设。按作用域构造子逐 case 归约。 -/
theorem identity_roundtrip (s : ScopedIdentity) : decodeKey (encodeKey s) = s := by
  obtain ⟨c, p, i, st, sc⟩ := s
  cases sc <;> rfl

/-- 反向：每个码字都是某个身份键的像（02 针覆盖性、01 针覆盖性共用）。 -/
theorem encode_decode (c : IdentityCode) : encodeKey (decodeKey c) = c := by
  obtain ⟨a, b, d, e, g⟩ := c
  cases g <;> rfl

/-! ## 第 01 针：representation_observations_preserved -/

/-- 法律对象层（本案的案卷记录）：身份键 + 请求额档位 + 是否已入登记簿。 -/
structure CaseRecord where
  key : ScopedIdentity
  claimedAmount : Fin 5
  registered : Bool

/-- 模型侧载体（01 针）：码字 + 请求额槽 + 登记位。 -/
structure CaseRecordCode where
  idCode : IdentityCode
  amount : Fin 5
  reg : Bool

/-- 01 针的观察指标：请求额观察与登记观察。 -/
inductive CaseObsTag where
  | amountObs
  | registerObs

/-- 01 针的实际表示片段：观测族、编码、回读全部由本件构造给出。 -/
def caseFragment : Fragment CaseRecord where
  β := CaseRecordCode
  ι := CaseObsTag
  γ := Sum (Fin 5) Bool
  obs := fun i a =>
    match i with
    | CaseObsTag.amountObs => Sum.inl a.claimedAmount
    | CaseObsTag.registerObs => Sum.inr a.registered
  enc := fun a => ⟨encodeKey a.key, a.claimedAmount, a.registered⟩
  dec := fun c => ⟨decodeKey c.idCode, c.amount, c.reg⟩

/-- 01 针前提之一（往返性）：由 `identity_roundtrip` 对实际编码成立。 -/
theorem caseFragment_roundTrip : RoundTrip caseFragment := by
  intro a
  show (⟨decodeKey (encodeKey a.key), a.claimedAmount, a.registered⟩ : CaseRecord) = a
  rw [identity_roundtrip a.key]
  rfl

/-- 01 针前提之二（覆盖性）：模型侧每个状态都有法律原像。 -/
theorem caseFragment_coverage : Coverage caseFragment := by
  intro c
  refine ⟨⟨decodeKey c.idCode, c.amount, c.reg⟩, ?_⟩
  show (⟨encodeKey (decodeKey c.idCode), c.amount, c.reg⟩ : CaseRecordCode) = c
  rw [encode_decode c.idCode]
  rfl

/-- 01 针的忠实前提：往返 ∧ 覆盖，两者都在本件内对具体载体证出。 -/
theorem caseFragment_faithful : FaithfulRep caseFragment :=
  ⟨caseFragment_roundTrip, caseFragment_coverage⟩

/-- **第 01 针（S0，I.13:755；BINDING 行 01）**：表示保持声明观测。
    旧锚 `JurisLean.Seams.Representation.representation_observations_preserved`
    （`Representation.lean:162`）只把观察在给定 `FaithfulRep` 下搬运；本针把该前提
    由本案实际编码（`caseFragment_faithful`）真实证出后实例化锚定理，观测搬运因此
    落在具体案卷片段上，而不是悬空假设下的重言。
    边界：只覆盖两个已声明观察（请求额档、登记位），不覆盖全 U01 观察族。 -/
theorem representation_observations_preserved :
    ∀ (a : CaseRecord) (i : CaseObsTag),
      obsModel caseFragment i (caseFragment.enc a) = caseFragment.obs i a :=
  JurisLean.Seams.Representation.representation_observations_preserved caseFragment
    caseFragment_faithful

/-! ## 第 02 针：representable_roundtrip -/

/-- 02 针载体片段：法律身份键层，观察即身份键本身（可分辨观测）。 -/
def identityFragment : Fragment ScopedIdentity where
  β := IdentityCode
  ι := Unit
  γ := ScopedIdentity
  obs := fun _ s => s
  enc := encodeKey
  dec := decodeKey

/-- 02 针的往返前提：`identity_roundtrip` 在片段上的读法，仍由实际编码证明。 -/
theorem identityFragment_roundTrip : RoundTrip identityFragment :=
  fun s => identity_roundtrip s

/-- **第 02 针（S0，I.13:756；BINDING 行 02）**：可表示编码往返一致。
    三支合成：(1) `identity_roundtrip` 本体（从本案编码构造证明，不以外填 hrt 代替）；
    (2) 它使 `identityFragment` 满足锚 `RoundTrip`；(3) 锚
    `obsModel_roundTrip`（`Representation.lean:153`）消费该往返，得到模型侧观测在
    原像处与声明观测相等。第三支正是锚定理的消费面。
    边界：显示名归一只做键级投影（显示名不进键），不含字符串运算。 -/
theorem representable_roundtrip :
    (∀ s : ScopedIdentity, decodeKey (encodeKey s) = s) ∧
    RoundTrip identityFragment ∧
    ∀ (i : identityFragment.ι) (s : ScopedIdentity),
      obsModel identityFragment i (identityFragment.enc s) = identityFragment.obs i s :=
  ⟨identity_roundtrip, identityFragment_roundTrip,
    fun i s => obsModel_roundTrip identityFragment identityFragment_roundTrip s i⟩

/-! ## 第 03 针：ontic_epistemic_separation_witness -/

/-- 生成输入：在卷材料形态（借据是否在卷、收款凭证是否在卷）。 -/
structure GenInput where
  iouOnFile : Bool
  receiptOnFile : Bool

/-- 本体状态 R：债务实际上是否已清偿。 -/
structure OnticR where
  debtDischarged : Bool

/-- 认识状态 E：从在卷材料得到的证据画像。 -/
structure EpistemicE where
  iouSeen : Bool
  receiptSeen : Bool

/-- 认识状态只由生成输入决定（"同一生成输入 ⇒ E 相同"的载体）。 -/
def epistemicOf (g : GenInput) : EpistemicE := ⟨g.iouOnFile, g.receiptOnFile⟩

/-- 认识层能否建立"已清偿"判断：以收款凭证在卷为必要材料。 -/
def epistemicEstablishes (e : EpistemicE) : Bool := e.receiptSeen

/-- 见证生成输入：借据在卷、收款凭证不在卷。 -/
def docket : GenInput := ⟨true, false⟩

/-- 运行：一次生成输入与一个本体状态的配对（R 随运行而变，E 随输入而定）。 -/
structure SepRun where
  input : GenInput
  ontic : OnticR

/-- **第 03 针（S0，I.13:757；BINDING 行 03）**：本体/认识分离见证。
    旧锚 `AdjudicationBridge.lean:746 proof_failure_not_ontic_negation` 是两个不同来源
    对象（KernelV3 记录 × cycle2 论证）的乘积见证，仅作参考；本针改为**同一生成输入**
    `docket` 的两个运行：R 不同（已清偿 / 未清偿）、E 相同（`epistemicOf` 相等）、
    认识层证明失败（收款凭证不在卷，`epistemicEstablishes = false`）；并复用
    `KernelV3.judgment_notEstablished_does_not_force_truth_false` 的记录
    （真值为真而判断不成立），说明证明失败不是本体否定。
    边界：单一在卷材料形态上的见证；"证明失败"以凭证在卷为必要条件，非完整负担演算。 -/
theorem ontic_epistemic_separation_witness :
    ∃ (w₁ w₂ : SepRun) (x : KernelV3.TruthJudgment),
      w₁.input = w₂.input ∧
      epistemicOf w₁.input = epistemicOf w₂.input ∧
      w₁.ontic ≠ w₂.ontic ∧
      epistemicEstablishes (epistemicOf w₁.input) = false ∧
      x.truth = true ∧
      x.judgment = KernelV3.Judgment.notEstablished ∧
      w₁.ontic.debtDischarged = true ∧
      w₂.ontic.debtDischarged = false := by
  obtain ⟨x, hx, hj⟩ := KernelV3.judgment_notEstablished_does_not_force_truth_false
  refine ⟨⟨docket, ⟨true⟩⟩, ⟨docket, ⟨false⟩⟩, x, rfl, rfl, ?_, rfl, hx, hj, rfl, rfl⟩
  intro h
  have hb : (true : Bool) = false := congrArg OnticR.debtDischarged h
  exact absurd hb (by decide)

/-! ## 第 04 针：power_obligation_occurrence_independent -/

/-- 同一制度（价款债务的清偿与消灭制度）内的法律事件。 -/
inductive DischargeEvent where
  /-- 解除权已产生但未行使：权力位已立，行使事件未发生。 -/
  | rescissionRightArisen
  /-- 价金义务已届期但未清偿：义务位已立，清偿事件未发生。 -/
  | priceDueUnperformed
  /-- 洪水实际毁损标的物：自然事实已发生，既非权力位亦非义务位。 -/
  | floodDestroysGoods
deriving DecidableEq

/-- 权力位标志：该事件是否使一项（形成性）权力得以产生。 -/
def powerArisen : DischargeEvent → Bool
  | .rescissionRightArisen => true
  | .priceDueUnperformed => false
  | .floodDestroysGoods => false

/-- 义务位标志：该事件是否承载一项届期义务内容。 -/
def obligationStanding : DischargeEvent → Bool
  | .rescissionRightArisen => false
  | .priceDueUnperformed => true
  | .floodDestroysGoods => false

/-- 实际发生标志：该事件描述的事实是否已发生。 -/
def actuallyOccurred : DischargeEvent → Bool
  | .rescissionRightArisen => false
  | .priceDueUnperformed => false
  | .floodDestroysGoods => true

/-- 同一制度的事件全表（04 针的"同一制度"载体）。 -/
def dischargeInstitution : List DischargeEvent :=
  [DischargeEvent.rescissionRightArisen, DischargeEvent.priceDueUnperformed,
    DischargeEvent.floodDestroysGoods]

/-- **第 04 针（S0，I.13:758；BINDING 行 04，原 UNBOUND）**：权力/义务/事件三独立见证。
    同一制度事件表内交出三个**具名法律事件**，其（权力位, 义务位, 实际发生）标志恰为
    单位向量 (1,0,0)/(0,1,0)/(0,0,1)；并证三事件互不相同（不是同一 Bool 的三次改写）、
    三维在制度表内两两可分、三维各自两值都可取。
    边界：单位向量族本就可被 (¬p∧¬o) 型布尔函数预测，故本针不主张一般函数独立性，
    只主张上述可实现性与两两可分性。 -/
theorem power_obligation_occurrence_independent :
    DischargeEvent.rescissionRightArisen ∈ dischargeInstitution ∧
    DischargeEvent.priceDueUnperformed ∈ dischargeInstitution ∧
    DischargeEvent.floodDestroysGoods ∈ dischargeInstitution ∧
    (powerArisen DischargeEvent.rescissionRightArisen,
        obligationStanding DischargeEvent.rescissionRightArisen,
        actuallyOccurred DischargeEvent.rescissionRightArisen) = (true, false, false) ∧
    (powerArisen DischargeEvent.priceDueUnperformed,
        obligationStanding DischargeEvent.priceDueUnperformed,
        actuallyOccurred DischargeEvent.priceDueUnperformed) = (false, true, false) ∧
    (powerArisen DischargeEvent.floodDestroysGoods,
        obligationStanding DischargeEvent.floodDestroysGoods,
        actuallyOccurred DischargeEvent.floodDestroysGoods) = (false, false, true) ∧
    DischargeEvent.rescissionRightArisen ≠ DischargeEvent.priceDueUnperformed ∧
    DischargeEvent.priceDueUnperformed ≠ DischargeEvent.floodDestroysGoods ∧
    DischargeEvent.rescissionRightArisen ≠ DischargeEvent.floodDestroysGoods ∧
    (∃ e ∈ dischargeInstitution, powerArisen e ≠ obligationStanding e) ∧
    (∃ e ∈ dischargeInstitution, obligationStanding e ≠ actuallyOccurred e) ∧
    (∃ e ∈ dischargeInstitution, powerArisen e ≠ actuallyOccurred e) ∧
    (∃ e ∈ dischargeInstitution, powerArisen e = true) ∧
    (∃ e ∈ dischargeInstitution, powerArisen e = false) ∧
    (∃ e ∈ dischargeInstitution, obligationStanding e = true) ∧
    (∃ e ∈ dischargeInstitution, obligationStanding e = false) ∧
    (∃ e ∈ dischargeInstitution, actuallyOccurred e = true) ∧
    (∃ e ∈ dischargeInstitution, actuallyOccurred e = false) :=
  ⟨by simp [dischargeInstitution], by simp [dischargeInstitution],
    by simp [dischargeInstitution], rfl, rfl, rfl, by decide, by decide, by decide,
    ⟨DischargeEvent.rescissionRightArisen, by simp [dischargeInstitution], by decide⟩,
    ⟨DischargeEvent.priceDueUnperformed, by simp [dischargeInstitution], by decide⟩,
    ⟨DischargeEvent.rescissionRightArisen, by simp [dischargeInstitution], by decide⟩,
    ⟨DischargeEvent.rescissionRightArisen, by simp [dischargeInstitution], rfl⟩,
    ⟨DischargeEvent.priceDueUnperformed, by simp [dischargeInstitution], rfl⟩,
    ⟨DischargeEvent.priceDueUnperformed, by simp [dischargeInstitution], rfl⟩,
    ⟨DischargeEvent.floodDestroysGoods, by simp [dischargeInstitution], rfl⟩,
    ⟨DischargeEvent.floodDestroysGoods, by simp [dischargeInstitution], rfl⟩,
    ⟨DischargeEvent.rescissionRightArisen, by simp [dischargeInstitution], rfl⟩⟩

/-! ## 第 05 针：joint_legal_model_exists -/

/-- 十四族（L01–L14）每族格内共同材料的状态（状态级载荷，非完整材料内容）。 -/
inductive MaterialPayload where
  /-- 该族材料在本案缺。 -/
  | absent
  /-- 该族材料已声明且内容一致。 -/
  | declared
  /-- 该族存在合法分支分歧。 -/
  | divergent
deriving DecidableEq

/-- 法律对象层（05 针）：案件材料 = 身份键 + 十四族材料载荷。 -/
structure CaseMaterials where
  key : ScopedIdentity
  fam : Fin 14 → MaterialPayload

/-- 见证身份键（第一案、第一主体、第一争点、第一阶段、规范作用域）。 -/
def defaultKey : ScopedIdentity :=
  ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨0, by decide⟩, ⟨0, by decide⟩, .normScope⟩

/-- 见证案件材料：全族缺料的默认案。 -/
def defaultCase : CaseMaterials := ⟨defaultKey, fun _ => MaterialPayload.absent⟩

/-- **十四族共同材料网络**：第一层片段。观测指标类型就是 `Fin 14`（十四族逐族可观测），
    载体为（身份键 × 十四族载荷），编码/回读为配对与投影。 -/
def familyNet : Fragment CaseMaterials where
  β := ScopedIdentity × (Fin 14 → MaterialPayload)
  ι := Fin 14
  γ := MaterialPayload
  obs := fun i a => a.fam i
  enc := fun a => (a.key, a.fam)
  dec := fun c => ⟨c.1, c.2⟩

/-- 网络层往返性（配对/投影，结构 eta 级）。 -/
theorem familyNet_roundTrip : RoundTrip familyNet := fun a => rfl

/-- 第二层：常值登记层（只记"已入簿"一件事，同 `Representation.layerRegister` 之意）。 -/
def registerLayer : Fragment CaseMaterials where
  β := Bool
  ι := Fin 1
  γ := Bool
  obs := fun _ _ => true
  enc := fun _ => true
  dec := fun _ => defaultCase

/-- 均匀案件材料：十四族载荷同为 `p`。 -/
def uniformCase (p : MaterialPayload) : CaseMaterials := ⟨defaultKey, fun _ => p⟩

/-- 均匀载荷在任何族指标上可分：`divergent` 与 `declared` 的观测不同。 -/
theorem uniformCase_separates (i : Fin 14) :
    familyNet.obs i (uniformCase MaterialPayload.divergent) ≠
      familyNet.obs i (uniformCase MaterialPayload.declared) := by
  intro h
  exact absurd h (by decide)

/-- **第 05 针（S0，I.13:759；BINDING 行 05）**：联合法律模型存在性（总入口见证）。
    旧锚 `Representation.lean:366` 是 `Fin 2` 两投影见证（该旧引理保留不动）；本针以
    完整十四族共同材料网络 `familyNet` 为第一层、常值登记层为第二层，经锚
    `joint_model_is_not_collapsed` 交出非退化联合见证（两个不同联合元素 + 一个把它们
    分开的声明观测），并附完整性条款：十四族每族材料在满料案上都非空（均为
    `declared`）。
    边界：每族载荷是三值状态，不是各族完整材料内容；L01–L14 完整材料网络是全工程
    量级的工作，本针替换的是总入口见证的载体，不是那些内容。 -/
theorem joint_legal_model_exists :
    (∀ i : Fin 14,
        familyNet.obs i (uniformCase MaterialPayload.declared) = MaterialPayload.declared) ∧
    ∃ (p q : Joint familyNet registerLayer), p ≠ q ∧ ∃ i : Fin 14,
      jointObs₁ familyNet registerLayer i p ≠ jointObs₁ familyNet registerLayer i q := by
  have i13 : Fin 14 := ⟨13, by decide⟩
  exact ⟨fun i => rfl,
    joint_model_is_not_collapsed familyNet registerLayer
      (uniformCase MaterialPayload.divergent) (uniformCase MaterialPayload.declared)
      familyNet_roundTrip ⟨i13, uniformCase_separates i13⟩⟩

/-! ## 第 06 针：applicability_matches_source_semantics -/

/-- 规范选择算子：目录在时点 `t` 的可适用子表，过滤谓词即 `PrecedentFlow.applicableAtBool`。 -/
def selectAt (dir : List SourceVersionRecord) (t : Int) : List SourceVersionRecord :=
  dir.filter (fun v => PrecedentFlow.applicableAtBool v t)

/-- **selected_iff_applicable（I.4.2/U03 拟合同）**：某版本被选中 ⟺ 它在目录内且按
    声明侧语义（`versionApplicableAt`）可适用。锚 `PrecedentFlow.applicableAtBool_true_iff`
    （`PrecedentFlow.lean:490`）在此被实例化为成员级双向等值。 -/
theorem selected_iff_applicable (dir : List SourceVersionRecord) (t : Int)
    (v : SourceVersionRecord) :
    v ∈ selectAt dir t ↔ (v ∈ dir ∧ versionApplicableAt v t) := by
  simp only [selectAt, List.mem_filter]
  exact and_congr Iff.rfl (PrecedentFlow.applicableAtBool_true_iff v t)

/-- **第 06 针（S1，I.13:760；BINDING 行 06）**：规范适用与来源语义一致。
    三支合成：(1) `selected_iff_applicable`（成员级，对全部记录成立）；
    (2) 规范选择的全域布尔反射——目录内每条记录的布尔判据恰反映声明语义（锚定理对
    全体 `v` 的实例化）；(3) 非退化实例——同一目录 `[oldV, newV]` 在 `t = 30` 与
    `t = 60` 的选择确实随声明语义变化（`rfl` 级闭式归约，与 `PrecedentFlow` 见证
    同一计算）。
    边界：不建 `VersionEnv`/`KnowledgeView` 桥；I.4.2 的具名冲突排除枚举（A/B 互斥
    分支）与缺版本/真实冲突的分别报告不在本针。 -/
theorem applicability_matches_source_semantics (dir : List SourceVersionRecord) (t : Int) :
    (∀ v, v ∈ selectAt dir t ↔ (v ∈ dir ∧ versionApplicableAt v t)) ∧
    (∀ v, PrecedentFlow.applicableAtBool v t = true ↔ versionApplicableAt v t) ∧
    (selectAt [PrecedentFlow.oldV, PrecedentFlow.newV] 30 = [PrecedentFlow.oldV] ∧
      selectAt [PrecedentFlow.oldV, PrecedentFlow.newV] 60 =
        [PrecedentFlow.oldV, PrecedentFlow.newV]) :=
  ⟨selected_iff_applicable dir t,
    fun v => PrecedentFlow.applicableAtBool_true_iff v t,
    rfl, rfl⟩

/-! ## 第 07 针：finite_priority_maximal_elements_exist -/

/-- P-015 平位阶见证对的互异性（经公布日 10 ≠ 20 的闭式比较，避免字符串判定）。 -/
theorem oldGeneral_ne_newSpecial : SourceNorms.oldGeneral ≠ SourceNorms.newSpecial := by
  intro h
  have hv : (10 : Nat) = 20 := congrArg P015.NormProvision.enactedDay h
  exact absurd hv (by decide)

/-- 见证对左端的极大性：`oldGeneral` 在 `{oldGeneral, newSpecial}` 内不被组内成员压过。 -/
theorem oldGeneral_maximal_in_pair :
    ∀ x ∈ ({SourceNorms.oldGeneral, SourceNorms.newSpecial} : Finset P015.NormProvision),
      ¬ SourceNorms.provisionRank SourceNorms.oldGeneral < SourceNorms.provisionRank x :=
  (SourceNorms.maximal_left_of_rank_tie SourceNorms.oldGeneral SourceNorms.newSpecial
    (by decide)).2

/-- 见证对右端的极大性：`newSpecial` 同样极大。 -/
theorem newSpecial_maximal_in_pair :
    ∀ x ∈ ({SourceNorms.oldGeneral, SourceNorms.newSpecial} : Finset P015.NormProvision),
      ¬ SourceNorms.provisionRank SourceNorms.newSpecial < SourceNorms.provisionRank x :=
  (SourceNorms.maximal_right_of_rank_tie SourceNorms.oldGeneral SourceNorms.newSpecial
    (by decide)).2

/-- **第 07 针（S1，I.13:761；BINDING 行 07）**：有限优先序极大元存在。
    一般支逐字复用锚 `SourceNorms.exists_maximal_acyclic`（`SourceNorms.lean:308`，
    只要求优先关系不自反且传递）；同一定理内附"极大元不等于唯一适用规范"的见证：
    同一冲突组内存在两条互异规范**同时**极大，故极大元不唯一。
    边界：非唯一性见证只在二元冲突组上；本针不认定任何真实条文的位阶归属。 -/
theorem finite_priority_maximal_elements_exist {β : Type} [DecidableEq β]
    (r : β → β → Prop)
    (h_irrefl : ∀ x, ¬ r x x)
    (h_trans : ∀ {x y z}, r x y → r y z → r x z) :
    (∀ (s : Finset β), s.Nonempty → ∃ m, m ∈ s ∧ ∀ x, x ∈ s → ¬ r m x) ∧
    (∃ (a b : P015.NormProvision), a ≠ b ∧
      (∀ x ∈ ({a, b} : Finset P015.NormProvision),
          ¬ SourceNorms.provisionRank a < SourceNorms.provisionRank x) ∧
      (∀ x ∈ ({a, b} : Finset P015.NormProvision),
          ¬ SourceNorms.provisionRank b < SourceNorms.provisionRank x)) :=
  ⟨SourceNorms.exists_maximal_acyclic r h_irrefl h_trans,
    SourceNorms.oldGeneral, SourceNorms.newSpecial, oldGeneral_ne_newSpecial,
    oldGeneral_maximal_in_pair, newSpecial_maximal_in_pair⟩

/-! ## 第 08 针：horn_closure_semantic_iff -/

/-- **第 08 针（S1，I.13:762；BINDING 行 08）**：Horn 闭包与语义等价。
    `SourceNorms.lean:171` 的同 basename 定理按纯正 Horn 原域直接承接：语句与锚定理
    完全一致（`a` 在 |univ| 步迭代闭包里 ⟺ `a` 是语义后承），本针名定理是它的
    引用重述，未改一字、未弱化。法律规则实例化与来源树接线按 I.13 明示另接，
    不在本件。 -/
theorem horn_closure_semantic_iff {α : Type} [DecidableEq α]
    (sys : HornSystem α) (a : α) :
    a ∈ SourceNorms.closureAt sys ↔ SourceNorms.entailed sys a :=
  SourceNorms.horn_closure_semantic_iff sys a

/-! ## 第 09 针：incomparable_norms_not_forced_unique -/

/-- **第 09 针（S1，I.13:763；BINDING 行 09）**：不可比规范不强制唯一适用。
    见证对 `oldGeneral / newSpecial`（锚 `SourceNorms.lean:521` 的反例族保留）：
    (1) 两条不可比（位阶互不压过）；(2) 分支完整保留——两条在冲突组 `{a, b}` 内都是
    极大元，位阶不淘汰任何一条；(3) 依法允许的择一仍在——P-015 政策判给新特别规定
    （`resolveConflict = some`），这是政策择一而非序淘汰；(4) "组内唯一极大元/唯一
    适用规范"被显式否定（`oldGeneral` 极大却 ≠ `newSpecial`）。
    边界：政策择一是 P-015 台账政策（特别法/新法优先），不构成对任何真实条文位阶
    或效力冲突的认定。 -/
theorem incomparable_norms_not_forced_unique :
    ∃ (a b : P015.NormProvision),
      a ≠ b ∧
      ¬ SourceNorms.provisionRank a < SourceNorms.provisionRank b ∧
      ¬ SourceNorms.provisionRank b < SourceNorms.provisionRank a ∧
      (∀ x ∈ ({a, b} : Finset P015.NormProvision),
          ¬ SourceNorms.provisionRank a < SourceNorms.provisionRank x) ∧
      (∀ x ∈ ({a, b} : Finset P015.NormProvision),
          ¬ SourceNorms.provisionRank b < SourceNorms.provisionRank x) ∧
      P015.resolveConflict a b = some b.provisionId ∧
      ¬ ∀ m ∈ ({a, b} : Finset P015.NormProvision),
        (∀ x ∈ ({a, b} : Finset P015.NormProvision),
            ¬ SourceNorms.provisionRank m < SourceNorms.provisionRank x) → m = b := by
  refine ⟨SourceNorms.oldGeneral, SourceNorms.newSpecial, oldGeneral_ne_newSpecial,
    by decide, by decide, oldGeneral_maximal_in_pair, newSpecial_maximal_in_pair, ?_, ?_⟩
  · exact SourceNorms.p015_some_not_unique_maximal.1
  · intro hall
    exact oldGeneral_ne_newSpecial
      (hall SourceNorms.oldGeneral (Finset.mem_insert.mpr (Or.inl rfl))
        oldGeneral_maximal_in_pair)

end JurisLean.Seams.UnifiedNeedlesS0S1
