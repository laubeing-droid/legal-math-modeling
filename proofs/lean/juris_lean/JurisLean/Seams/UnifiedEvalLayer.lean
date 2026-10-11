import JurisLean.KernelV3
import Mathlib.Tactic

/-!
# 评价层五针组（W1-12）：针 10/11/12/13/14 差额清算（UnifiedEvalLayer）

本件承接 Z1 审计（`docs/full-math/NEEDLE_STRENGTH_AUDIT.md` §一 针 10–14 五行，全部判差额）
钉出的同一根因：主文 §5 完整终结片段（分阶段评价构造＋Exhaustion 加 Need 分量＋实际
Pos/Neg 前提）未落载体，旧交付停在 `Seams/AdjudicationBridge.lean` 三族规则锚
（`mem_rounds_fst_fires`/`two_valued_exclusion`/`exhaustionOf`/cycle2 乘积见证）的重述。

## 施工合同（唯一权威：`docs/spec/20261007-统一法律数学模型_附录I_Lean施工明细.md` §I.13 原句）

- **针 10（I:764）`eval_has_licensed_derivation`**："拟逐卡片、攻击、标准和终结构造的独立
  LegalDerives 健全"——四阶段构造（卡片 §5.3.1／攻击 §5.3.6／标准 §5.3.3／终局 §5.4）
  各自进入语句的独立健全性定理＋端到端许可追溯（终局的每张标准证书都落在已准入材料
  生成的卡片上）＋同快照攻击封闭（终局后框架内攻击不能翻案，框架外攻击只能另算快照）。
- **针 11（I:765）`final_binary_decisions_exclusive`**："拟由强理由同身份反证及实际
  Pos/Neg 前提证明排斥"——`posOutcome ∧ negOutcome → False` **不依赖 baseConflictFree**：
  第一负支与 Pos 的 ¬B 直接 Bool 矛盾，第二负支与 E 所含每要件 Established 矛盾；
  另一侧 `civilHigh ∧ civilHighNeg → False` 只用扩展冲突自由＋准确相反角色桥
  （Strong(¬q,s) 即 MaterialCounter(q,s)，§5.3.6 同一身份第二角色）＋实际 defeat。
- **针 12（I:766）`final_undetermined_iff_exhausted`**："按主文公开更正加入 Need，完整
  终结片段才导出原简式"——Need 作为**显式结构分量**（`NeedItem`：先决未定/尚未取得＋
  无法定替代位）进 `ExhaustionRec` 记录（不是 missing premise 的 Bool）；主 iff 为
  `undetermined ⇔ Exhausted4 ∧ Need ∧ ¬Pos ∧ ¬Neg`；旧简式（穷尽∧无二值 ⇔ 未决）
  **被反例否证**（无 Need 时是规范处置缺口，不得扩张未决定义吞掉）；在完整终结片段
  （覆盖由实际表读出）旧简式作为推论重建。
- **针 13（I:767）`proof_failure_not_ontic_negation`**："拟在同输入真实推导且 R 为真的
  族内重建"——同一 `GenInput` 同时生成真值记录侧（R 真）与评价框架侧（真实推导失败：
  材料在场、内容相符、但未准入 ⇒ 卡片被拒 ⇒ 标准不可得 ⇒ 负担产生不成立）；
  评价对 onticTruth 盲（翻真值分量不改变判断分量）。
- **针 14（I:768）`argument_undec_not_final_undetermined`**："拟新法定负担输入产生
  grounded 未接受而最终不成立"——负担变化是**独立显式输入通道**（`BurdenInput`：具名
  法定依据＋作用争点＋举证终结位），`applyBurdenInput` 只写程序/负担位、**不触碰论证层**
  （materials/cards/reasons/attacks/accepted 全 rfl 不变）；见证：输入前无二值终局
  （举证未终结，负担不发动——材料缺证据不自动产生负担终结），输入后同快照重评价为
  notEstablished（非 undetermined），而该争点的论证层理由始终未进入接受集。

## 与旧锚（AdjudicationBridge/UnifiedNeedlesS2）的差异

旧锚的三族规则采纳（rounds/FinalDerivable）、`exhaustionOf` 宣告读法、cycle2 见证全部
保留不动；本件**不重述**它们，而是在主文 §5 的分阶段评价载体上重建五针：卡片/攻击/
标准/终局四构造、Exhaustion5 记录（四族条目表＋Need 结构分量）、Pos/Neg 独立终结表、
FinalCall 四路分类（Pos/Neg/依法未决/规范处置缺口）。旧 `baseConflictFree`（整框架
无冲突假设）在针 11 被实际前提排斥取代；扩展冲突自由仅用于 CivilHigh 正反排斥那一侧
（主文 §5.3.6 原话："这只使用扩展的冲突自由、准确相反角色桥和实际defeat"）。

## 载体与开放点（诚实声明）

- 理由节点接受状态取 §5.3.6 完整扩展 E 的 In_E（`fr.accepted`，最终层实际消费的读法）；
  "grounded 算子"的 Dung 语义留在旧锚件（DungFixedPoint/cycle2），本件不建平行语义。
- `ExhaustionRec` 的完整性（规则身份集合与候选生成定理对应）在结构层由逐条目
  "适用推导或至少一项法定败因见证"承载；对十四族真实规则表的逐表覆盖证明不在本件
  （依赖 W1-3 网络作实例层，如实留开放）。
- 法定替代依据（自认/免证/妨碍，§5.2 构造子）未在本载体实例化——本件承载普通本证
  标准路径（CivilHigh）与负担/程序位；E(q) 的"法定替代依据"分量以标准证书承载，
  特殊路径留 §5.2 构造子层，如实声明。
- 终结性是**同快照**封闭：框架外攻击不得在原快照派生（`attack` 构造要求证书在
  `fr.attacks` 内），新证据/新许可是新快照事件（§5.3.6"不在同一静态图内倒流"）。

## 档位

零 `sorry`、零 `admit`、零自定义 `axiom`、零 `True` 逃避；`CI_NOT_RUN`（本机不编译仓内
Lean，fail-closed），以 GitHub Actions 模块轮为唯一编译权威。语句位只写闭命题；
if/decide 只出现在定义位；合取证明逐分量 `⟨_, _⟩`；`∀` 型 Iff 投影全参
（`(... fr q).mp/.mpr`）。证明只用 core 战术与引理（cases/intro/exact/rw/simp/decide/
Classical），引名已对 v4.30.0 core 逐一核名。
-/

namespace JurisLean.Seams.UnifiedEvalLayer

/-! ## 一、评价层载体（主文 §5.3.1–§5.4 的有限呈现） -/

/-- 评价材料段（§5.3.1：e=(artifact,origin,eventId,author,time,use,contentSpan)的截取）：
实际来源身份独立，复制文档不增加新观察；`admitted`＝已准入且已质证/依法可直接采用。 -/
structure EvidenceItem where
  evidenceId : Nat
  sourceId : Nat
  contentClaim : Nat
  admitted : Bool
deriving DecidableEq, Repr

/-- 局部事实卡（§5.3.1：Card(e,k,v,reason,source)）：k 只允许单证或特定证据对的性质；
卡片命题不是当前实体争点的最终成立/败诉状态——由四阶段构造分离承载。 -/
structure FactCard where
  cardId : Nat
  fromEvidence : Nat
  propKey : Nat
  value : Bool
  reason : Nat
deriving DecidableEq, Repr

/-- 理由节点（§5.3.2：r=(claim,polarity,kind,leaves,warrant,conditions)的截取）：
`strong`＝由具名充分性许可模板（W-STRONG/S1–S6）生成的 StrongBasis 位；
`leaves`＝卡片叶（许可的局部前提）。 -/
structure ReasonNode where
  reasonId : Nat
  claim : Nat
  polarity : Bool
  strong : Bool
  leaves : List Nat
  warrant : Nat
deriving DecidableEq, Repr

/-- 攻击证书（§5.3.6 第 3/4 条：AnswerCert/CompareCert 须携带具名局部材料锚点与
实际 Defeat 见证；仅"未采信"不是攻击的前提——锚点为 0 的证书不发放、不派生）。 -/
structure AttackCert where
  attackId : Nat
  attacker : Nat
  target : Nat
  materialAnchor : Nat
deriving DecidableEq, Repr

/-- Need 分量的种类（主文 §5.4：尚未取得／先决未定）。 -/
inductive PendingKind where
  | notYetObtained
  | priorPending
deriving DecidableEq, Repr

/-- Need 分量（主文公开更正）：本阶段必要前提中依法记录为尚未取得/先决未定、
且确认没有其法定替代的项——显式结构记录，不是 missing premise 的 Bool。 -/
structure NeedItem where
  itemId : Nat
  kind : PendingKind
  noAlternative : Bool
deriving DecidableEq, Repr

/-- 法定规则族条目（§5.4 Exhausted4 分量）：每条有适用推导（applied）或至少一项
法定败因见证（defeatWitness）——不是一个外填布尔。 -/
structure RuleEntry where
  ruleId : Nat
  applied : Bool
  defeatWitness : Option Nat
deriving DecidableEq, Repr

/-- 穷尽记录（含 Need 分量）：负担/推定免证/妨碍/程序终结四族条目表＋Need 结构分量
（Z1 差额清算点：Need 进 Exhaustion 记录）。 -/
structure ExhaustionRec where
  burden : List RuleEntry
  presumption : List RuleEntry
  obstruction : List RuleEntry
  terminal : List RuleEntry
  need : List NeedItem
deriving DecidableEq, Repr

/-- 空穷尽记录：四族均无已实例化条目、无 Need 项。 -/
def emptyExh : ExhaustionRec :=
  { burden := [], presumption := [], obstruction := [], terminal := [], need := [] }

/-- 评价快照（Frame）：材料/卡片/理由/攻击证书的有限呈现＋完整扩展 E 的接受集
＋程序与负担位（Ready/F/B/要件表/负担指派/穷尽记录）。 -/
structure Frame where
  materials : List EvidenceItem
  cards : List FactCard
  reasons : List ReasonNode
  attacks : List AttackCert
  accepted : List Nat
  ready : Nat → Bool
  proofClosed : Nat → Bool
  barred : Nat → Bool
  elements : Nat → List Nat
  burdenOnClaimant : Nat → Bool
  exhaustion : Nat → ExhaustionRec

/-- 框架内理由节点 id 表。 -/
def reasonIds (fr : Frame) : List Nat := fr.reasons.map fun r => r.reasonId

/-! ## 二、四阶段构造（LegalDerives）与扩展语义 -/

/- 四阶段构造的推导关系（§5.2 的分阶段评价读法）。各构造独立定义、独立健全；
标准/终局两个构造在扩展语义与独立终结表定义之后补入本命名空间（依赖序）。 -/
namespace LegalDerives

/-- 卡片构造（§5.3.1）：卡在框架卡片表内，由**已准入**材料生成、理由具名；
只能由框架内材料生成，不从输入自由改值，不读标准/终局位。 -/
def card (fr : Frame) (c : FactCard) : Prop :=
  c ∈ fr.cards ∧ ∃ e ∈ fr.materials,
    e.admitted = true ∧ e.evidenceId = c.fromEvidence ∧ c.reason ≠ 0

/-- 攻击构造（§5.3.6）：证书在框架攻击表内、两端为框架内理由节点、携带具名材料锚点
（实际 Defeat 见证）；框架外攻击不得在本快照派生。 -/
def attack (fr : Frame) (a : AttackCert) : Prop :=
  a ∈ fr.attacks ∧ a.attacker ∈ reasonIds fr ∧ a.target ∈ reasonIds fr ∧
    a.materialAnchor ≠ 0

end LegalDerives

/-- 强理由的许可（§5.3.2）：strong 位由具名充分性许可生成，且每片叶都是可派生卡片
（许可的局部前提落在材料上）。 -/
def reasonLicensed (fr : Frame) (rn : ReasonNode) : Prop :=
  rn.strong = true ∧ ∀ l ∈ rn.leaves, ∃ c ∈ fr.cards, c.cardId = l ∧ LegalDerives.card fr c

/-- 对原子 (q,pol) 的强理由（StrongBasis）。 -/
def strongFor (fr : Frame) (q : Nat) (pol : Bool) (r : Nat) : Prop :=
  ∃ rn ∈ fr.reasons, rn.reasonId = r ∧ reasonLicensed fr rn ∧ rn.claim = q ∧ rn.polarity = pol

/-- 实质反证（§5.3.6 同一身份角色桥）：q 的实质反证恰是 ¬q 侧的强理由——
"对同争点/用途的准确相反原子 p、¬p，同时赋予 MaterialCounter(¬p,r) 角色"的定义化承载。 -/
def materialCounter (fr : Frame) (q : Nat) (r : Nat) : Prop := strongFor fr q false r

/-- In_E：理由在完整扩展接受集内。 -/
def inExt (fr : Frame) (r : Nat) : Prop := r ∈ fr.accepted

/-- Out_E：存在带锚攻击证书、其攻击者在接受集内（实际 Defeat，§5.3.6 Live/Out）。 -/
def outExt (fr : Frame) (r : Nat) : Prop :=
  ∃ a ∈ fr.attacks, a.target = r ∧ a.materialAnchor ≠ 0 ∧ a.attacker ∈ fr.accepted

/-- Undec：既不在接受集也未被实际击败（不得由"未进入 In"推成 Out）。 -/
def undecExt (fr : Frame) (r : Nat) : Prop := ¬ inExt fr r ∧ ¬ outExt fr r

/-- Live：In 或 Undec（未退出本分支待回答域）。 -/
def liveExt (fr : Frame) (r : Nat) : Prop := inExt fr r ∨ undecExt fr r

/-- 扩展冲突自由：接受集内的理由不被实际击败（§5.3.6 正反排斥证明的唯一扩展假设）。 -/
def conflictFree (fr : Frame) : Prop := ∀ r ∈ fr.accepted, ¬ outExt fr r

/-- CivilHigh（正原子侧，§5.3.3）：存在 In 的已许可强理由，且每个 Live 实质反证均已 Out。 -/
def civilHigh (fr : Frame) (q : Nat) : Prop :=
  ∃ r, strongFor fr q true r ∧ inExt fr r ∧
    ∀ s, materialCounter fr q s → liveExt fr s → outExt fr s

/-- CivilHigh（负原子侧）：同一标准对 ¬q 的实例化。 -/
def civilHighNeg (fr : Frame) (q : Nat) : Prop :=
  ∃ r, strongFor fr q false r ∧ inExt fr r ∧
    ∀ s, strongFor fr q true s → liveExt fr s → outExt fr s

/-- E(q)：全部必要要件已有标准证书（要件级 Established）。 -/
def allElementsEstablished (fr : Frame) (q : Nat) : Prop :=
  ∀ e ∈ fr.elements q, civilHigh fr e

/-- Pos(q)（§5.4 独立终结表）：Ready ∧ E ∧ ¬B。 -/
def posOutcome (fr : Frame) (q : Nat) : Prop :=
  fr.ready q = true ∧ allElementsEstablished fr q ∧ fr.barred q = false

/-- Neg(q)（§5.4 独立终结表）：Ready ∧ [B ∨ (F ∧ ∃必要要件：本方负担 ∧ 未成立)]。 -/
def negOutcome (fr : Frame) (q : Nat) : Prop :=
  fr.ready q = true ∧
    (fr.barred q = true ∨
      (fr.proofClosed q = true ∧
        ∃ e ∈ fr.elements q, fr.burdenOnClaimant e = true ∧ ¬ civilHigh fr e))

namespace LegalDerives

/-- 标准构造（§5.3.3 CivilHigh）：存在 In 的已许可强理由，且每个 Live 的实质反证均已被
实际击败（Out）——"没有尚存 Live 的实质反证"的派生定义，不是调用者可填的字段。 -/
def standard (fr : Frame) (q : Nat) : Prop := civilHigh fr q

/-- 终局构造（§5.4 独立终结表）：由实际程序/负担前提派生的 Pos/Neg。 -/
def final (fr : Frame) (q : Nat) : Prop :=
  posOutcome fr q ∨ negOutcome fr q

end LegalDerives

/-- 条目已解决：有适用推导或至少一项法定败因见证。 -/
def entryResolved (e : RuleEntry) : Prop := e.applied = true ∨ e.defeatWitness ≠ none

/-- 规则族已穷尽：族内逐条目已解决。 -/
def familyResolved (l : List RuleEntry) : Prop := ∀ e ∈ l, entryResolved e

/-- Exhausted4(q)：四族规则条目逐条已解决（穷尽判据的四族分量）。 -/
def exhausted4 (fr : Frame) (q : Nat) : Prop :=
  familyResolved (fr.exhaustion q).burden ∧ familyResolved (fr.exhaustion q).presumption ∧
    familyResolved (fr.exhaustion q).obstruction ∧ familyResolved (fr.exhaustion q).terminal

/-- Need(q)（主文公开更正的第五分量）：穷尽记录的 Need 结构分量中存在
"尚未取得/先决未定且无法定替代"的项。 -/
def needHolds (fr : Frame) (q : Nat) : Prop :=
  ∃ it ∈ (fr.exhaustion q).need, it.noAlternative = true

/-- 终局分类（§5.4＋§5.5）：Pos／Neg／依法未决／规范处置缺口四路。
缺口不是 Judgment 值——不能扩张未决定义吞掉它（NONE 不充当单一桶）。 -/
inductive FinalCall (fr : Frame) (q : Nat) : Type where
  | finalPos (h : posOutcome fr q)
  | finalNeg (h : negOutcome fr q)
  | finalUndet (hexh : exhausted4 fr q) (hneed : needHolds fr q)
      (hnp : ¬ posOutcome fr q) (hnn : ¬ negOutcome fr q)
  | finalGap (hnp : ¬ posOutcome fr q) (hnn : ¬ negOutcome fr q)
      (hn : ¬ (exhausted4 fr q ∧ needHolds fr q))

/-- 分类到判断值（缺口读 none）。 -/
def judgmentOf {fr : Frame} {q : Nat} : FinalCall fr q → Option KernelV3.Judgment
  | .finalPos _ => some KernelV3.Judgment.established
  | .finalNeg _ => some KernelV3.Judgment.notEstablished
  | .finalUndet _ _ _ _ => some KernelV3.Judgment.undetermined
  | .finalGap _ _ _ => none

/-- 完整终结片段的覆盖条件（§5.4：有限要件每项均由本证/负担覆盖——覆盖由实际
程序/负担表读出，不是外填"覆盖正确"位）。 -/
def coveredFragment (fr : Frame) (q : Nat) : Prop :=
  fr.ready q = true ∧ fr.proofClosed q = true ∧ ∀ e ∈ fr.elements q, fr.burdenOnClaimant e = true

/-- 法定负担输入（针 14：独立显式输入通道——具名输入身份＋法定依据＋作用争点＋
举证终结位；不是论证层改读）。 -/
structure BurdenInput where
  inputId : Nat
  statutoryBasis : Nat
  onQuestion : Nat
  closesProof : Bool
deriving DecidableEq, Repr

/-- 负担输入通道：只写程序/负担位（F），不触碰论证层与标准层。 -/
def applyBurdenInput (fr : Frame) (bi : BurdenInput) : Frame :=
  { fr with proofClosed := fun q => if q = bi.onQuestion then bi.closesProof else fr.proofClosed q }

open Classical in
/-- 终局分类函数（经典情形分析；非计算定义）。 -/
noncomputable def classify (fr : Frame) (q : Nat) : FinalCall fr q :=
  if h : posOutcome fr q then FinalCall.finalPos h
  else if h2 : negOutcome fr q then FinalCall.finalNeg h2
  else if h3 : exhausted4 fr q ∧ needHolds fr q
    then FinalCall.finalUndet h3.1 h3.2 h h2
    else FinalCall.finalGap h h2 h3

/-- 快照终局判断值：none＝规范处置缺口（无二值终局且未决判据不满足）。 -/
noncomputable def finalJudgment (fr : Frame) (q : Nat) : Option KernelV3.Judgment :=
  judgmentOf (classify fr q)

/-- 判断值的展开引理（rw 穿不透 def 应用，统一走本式）。 -/
theorem finalJudgment_eq (fr : Frame) (q : Nat) :
    finalJudgment fr q = judgmentOf (classify fr q) :=
  rfl

/-- 生成输入（针 03 形态；针 13 同源绑定）：一次生成输入同时生成评价框架侧与
真值记录侧（R 分量独立于评价——评价不读它）。 -/
structure GenInput where
  frame : Frame
  focus : Nat
  onticTruth : Bool

/-- 生成输入的真值记录侧：truth＝R 分量，judgment＝评价框架的分类结果。 -/
noncomputable def genTruthJudgment (g : GenInput) : Option KernelV3.TruthJudgment :=
  match finalJudgment g.frame g.focus with
  | some j => some { truth := g.onticTruth, judgment := j }
  | none => none

/-! ## 三、针 10：eval_has_licensed_derivation（逐构造独立健全＋许可追溯＋终局封闭） -/

/-- 卡片构造健全（§5.3.1）：卡片推导 ⇒ 卡在表内、材料在场且已准入、理由具名
（具名理由≠0）。 -/
theorem legalDerives_card_sound (fr : Frame) (c : FactCard) (h : LegalDerives.card fr c) :
    c ∈ fr.cards ∧ ∃ e ∈ fr.materials,
      e.admitted = true ∧ e.evidenceId = c.fromEvidence ∧ c.reason ≠ 0 :=
  h

/-- 攻击构造健全（§5.3.6）：攻击推导 ⇒ 证书在框架攻击表内、两端为框架理由、
携带非零材料锚点（实际 Defeat 见证）。 -/
theorem legalDerives_attack_sound (fr : Frame) (a : AttackCert) (h : LegalDerives.attack fr a) :
    a ∈ fr.attacks ∧ a.attacker ∈ reasonIds fr ∧ a.target ∈ reasonIds fr ∧
      a.materialAnchor ≠ 0 :=
  h

/-- 无锚攻击永不派生：锚点为 0 的"未采信"伪证书不发放（仅"未采信s"不是攻击的前提）。 -/
theorem anchorless_attack_rejected (fr : Frame) (a : AttackCert)
    (ha : a.materialAnchor = 0) : ¬ LegalDerives.attack fr a :=
  fun h => h.2.2.2 ha

/-- 针 10 反例见证：框架攻击表内确实摆着一张无锚证书，它不派生——
攻击构造的锚点要求不是空转。 -/
def n10Anchorless : AttackCert :=
  { attackId := 1, attacker := 30, target := 31, materialAnchor := 0 }

def n10Frame : Frame :=
  { materials := [], cards := [], reasons := [], attacks := [n10Anchorless], accepted := [],
    ready := fun _ => false, proofClosed := fun _ => false, barred := fun _ => false,
    elements := fun _ => [], burdenOnClaimant := fun _ => false,
    exhaustion := fun _ => emptyExh }

theorem anchorless_attack_witness :
    ∃ (fr : Frame) (a : AttackCert),
      a ∈ fr.attacks ∧ a.materialAnchor = 0 ∧ ¬ LegalDerives.attack fr a :=
  ⟨n10Frame, n10Anchorless, by decide, rfl, anchorless_attack_rejected n10Frame n10Anchorless rfl⟩

/-- 标准构造健全（§5.3.3）：标准推导 ⇒ 见证强理由在表内、已许可、claim/polarity 相符、
In 扩展，且全部 Live 实质反证均已 Out。 -/
theorem legalDerives_standard_sound (fr : Frame) (q : Nat) (h : LegalDerives.standard fr q) :
    ∃ (r : Nat) (rn : ReasonNode),
      rn ∈ fr.reasons ∧ rn.reasonId = r ∧ reasonLicensed fr rn ∧ rn.claim = q ∧
        rn.polarity = true ∧ r ∈ fr.accepted ∧
        ∀ s, materialCounter fr q s → liveExt fr s → outExt fr s := by
  cases h with
  | intro r hr =>
    cases hr with
    | intro hstrong hrest =>
      cases hstrong with
      | intro rn hrn =>
        cases hrn with
        | intro hmem hfields =>
          exact ⟨r, rn, hmem, hfields.1, hfields.2.1, hfields.2.2.1, hfields.2.2.2,
            hrest.1, hrest.2⟩

/-- 标准被 Live 反证阻断：存在未回答（未 Out）的 Live 实质反证时标准不可得
（实质反证尚有未解决定性部分时不得径行越过）。 -/
theorem standard_blocked_by_live_counter (fr : Frame) (q : Nat) (s : Nat)
    (hmc : materialCounter fr q s) (hlive : liveExt fr s) (hnotout : ¬ outExt fr s) :
    ¬ LegalDerives.standard fr q := by
  intro h
  cases h with
  | intro r hr =>
    have hout := hr.2.2 s hmc hlive
    exact hnotout hout

/-- 同一身份角色桥（§5.3.6 第 1 条）：¬q 侧的强理由恰是 q 的实质反证
（r 的第二个观察角色，不另造辅助论证）。 -/
theorem strong_counter_same_identity (fr : Frame) (q : Nat) (r : Nat) :
    strongFor fr q false r ↔ materialCounter fr q r :=
  Iff.rfl

/-- 终局构造健全（§5.4 独立终结表）：终局推导 ⇒ 前提恰为实际程序/负担位
（Ready/E/¬B 或 Ready/B 或 Ready/F/负担/未成立）——Pos/Neg 不是卡片输入。 -/
theorem legalDerives_final_sound (fr : Frame) (q : Nat) (h : LegalDerives.final fr q) :
    (fr.ready q = true ∧ (∀ e ∈ fr.elements q, LegalDerives.standard fr e) ∧
        fr.barred q = false) ∨
      (fr.ready q = true ∧ (fr.barred q = true ∨
        (fr.proofClosed q = true ∧
          ∃ e ∈ fr.elements q, fr.burdenOnClaimant e = true ∧ ¬ LegalDerives.standard fr e))) := by
  cases h with
  | inl hpos => exact Or.inl hpos
  | inr hneg => exact Or.inr hneg

/-- 终结性（同快照攻击封闭）：Pos 成立时，(i) 每个必要要件的每个 Live 实质反证均已被
实际击败——框架内攻击不能翻案；(ii) 框架外攻击证书在本快照不派生——新攻击只能作为
新快照事件进入（不在同一静态图内倒流）。 -/
theorem finalization_closed (fr : Frame) (q : Nat) (hpos : posOutcome fr q) :
    (∀ e ∈ fr.elements q, ∀ s, materialCounter fr e s → liveExt fr s → outExt fr s) ∧
      ∀ a, ¬ (a ∈ fr.attacks) → ¬ LegalDerives.attack fr a := by
  refine ⟨fun e he => by
      cases hpos.2.1 e he with
      | intro r hr => exact hr.2.2
    , ?_⟩
  intro a hnotin hderiv
  exact hnotin hderiv.1

/-- 负担通道与证据/标准层分离：负担输入后卡片/攻击/标准构造的推导性不变
（负担输出不得反馈成为自己所要求的证据——卡/攻击/标准层根本不读程序/负担位）。 -/
theorem burden_channel_leaves_evidence_layer (fr : Frame) (bi : BurdenInput)
    (c : FactCard) (a : AttackCert) (q : Nat) :
    (LegalDerives.card fr c ↔ LegalDerives.card (applyBurdenInput fr bi) c) ∧
      (a.materialAnchor ≠ 0 →
        (LegalDerives.attack fr a ↔ LegalDerives.attack (applyBurdenInput fr bi) a)) ∧
      (LegalDerives.standard fr q ↔ LegalDerives.standard (applyBurdenInput fr bi) q) :=
  ⟨Iff.rfl, fun _ => Iff.rfl, Iff.rfl⟩

/-- **针 10（S2，I:764）**：评价有许可推导——终局 Pos 的每张标准证书都落在已许可强理由上，
强理由的每片叶都是已准入材料生成的卡片，卡片可追溯到在场已准入材料与具名理由
（卡片→攻击→标准→终局的端到端许可追溯；健全性逐构造独立给出，本条收口 Pos 侧链条）。 -/
theorem eval_has_licensed_derivation (fr : Frame) (q : Nat) (hpos : posOutcome fr q) :
    ∀ e ∈ fr.elements q,
      ∃ rn ∈ fr.reasons,
        rn.claim = e ∧ rn.polarity = true ∧ rn.reasonId ∈ fr.accepted ∧
          reasonLicensed fr rn ∧
          ∀ l ∈ rn.leaves,
            ∃ c ∈ fr.cards, c.cardId = l ∧ LegalDerives.card fr c ∧
              ∃ m ∈ fr.materials,
                m.admitted = true ∧ m.evidenceId = c.fromEvidence ∧ c.reason ≠ 0 := by
  intro e he
  cases hpos.2.1 e he with
  | intro r hr =>
    cases hr with
    | intro hstrong hrest =>
      cases hstrong with
      | intro rn hrn =>
        cases hrn with
        | intro hmem hfields =>
          refine ⟨rn, hmem, hfields.2.2.1, hfields.2.2.2,
            by rw [hfields.1]; exact hrest.1, hfields.2.1, ?_⟩
          intro l hl
          cases hfields.2.1.2 l hl with
          | intro c hc =>
            cases hc with
            | intro hcmem hcrest =>
              refine ⟨c, hcmem, hcrest.1, hcrest.2, ?_⟩
              have hcard : ∃ m ∈ fr.materials,
                  m.admitted = true ∧ m.evidenceId = c.fromEvidence ∧ c.reason ≠ 0 :=
                hcrest.2.2
              cases hcard with
              | intro m hm =>
                cases hm with
                | intro hmmem hmrest =>
                  exact ⟨m, hmmem, hmrest.1, hmrest.2.1, hmrest.2.2⟩

/-! ## 四、针 11：final_binary_decisions_exclusive（实际前提排斥＋强理由同身份反证） -/

/-- **针 11（S2，I:765）主式**：终局二值互斥——由实际 Pos/Neg 前提直接反证，
**不依赖 baseConflictFree**：第一负支（B）与 Pos 的 ¬B 直接矛盾；第二负支
（∃要件未成立）与 E 所含每一要件成立矛盾。 -/
theorem final_binary_decisions_exclusive (fr : Frame) (q : Nat)
    (h1 : posOutcome fr q) (h2 : negOutcome fr q) : False := by
  cases h2.2 with
  | inl hb =>
    rw [h1.2.2] at hb
    exact Bool.noConfusion hb
  | inr hF =>
    cases hF.2 with
    | intro e he =>
      cases he with
      | intro heMem heRest =>
        exact heRest.2 (h1.2.1 e heMem)

/-- **针 11（S2，I:765）副式**：CivilHigh 正反排斥——由强理由同一身份反证：
¬q 侧的 StrongBasis 即 q 的实质反证；扩展冲突自由下 ¬q 标准的 In 强理由被 q 标准的
全称检查击败，与冲突自由矛盾（§5.3.6 一般证明，只用扩展冲突自由＋角色桥＋实际
defeat，不用 ASPIC 子论证闭合、不选全局证据赢家）。 -/
theorem civil_high_same_identity_exclusive (fr : Frame) (q : Nat)
    (hcf : conflictFree fr) (hpos : civilHigh fr q) (hneg : civilHighNeg fr q) : False := by
  cases hneg with
  | intro s hs =>
    cases hs with
    | intro hsStrong hsRest =>
      cases hpos with
      | intro r hr =>
        cases hr with
        | intro _ hrRest =>
          have hout := hrRest.2 s hsStrong (Or.inl hsRest.1)
          exact hcf s hsRest.1 hout

/-! 针 11 非空洞见证：完整正链（已准入材料→可派生卡片→已许可强理由 In→无反证→
CivilHigh→Pos），Neg 不成立，判断=成立；扩展冲突自由成立、¬q 侧标准不成立。 -/

def n11Material : EvidenceItem :=
  { evidenceId := 5, sourceId := 1, contentClaim := 2, admitted := true }

def n11Card : FactCard :=
  { cardId := 25, fromEvidence := 5, propKey := 1, value := true, reason := 6 }

def n11Reason : ReasonNode :=
  { reasonId := 35, claim := 2, polarity := true, strong := true, leaves := [25], warrant := 7 }

def n11Frame : Frame :=
  { materials := [n11Material], cards := [n11Card], reasons := [n11Reason], attacks := [],
    accepted := [35],
    ready := fun q => q == 1, proofClosed := fun _ => true, barred := fun _ => false,
    elements := fun q => if q = 1 then [2] else [],
    burdenOnClaimant := fun e => e == 2,
    exhaustion := fun _ => emptyExh }

theorem n11_card_derives : LegalDerives.card n11Frame n11Card :=
  ⟨by decide, n11Material, by decide, rfl, rfl, by decide⟩

theorem n11_reason_licensed : reasonLicensed n11Frame n11Reason :=
  ⟨rfl, fun l hl => by
    cases List.mem_cons.mp hl with
    | inl heq =>
      exact ⟨n11Card, by decide, by rw [heq]; exact rfl, n11_card_derives⟩
    | inr hnil => exact absurd hnil (by simp)⟩

theorem n11_in_ext : inExt n11Frame 35 := by
  show (35 : Nat) ∈ n11Frame.accepted
  decide

theorem n11_civil_high : civilHigh n11Frame 2 := by
  refine ⟨35, ⟨n11Reason, by decide, rfl, n11_reason_licensed, rfl, rfl⟩,
    n11_in_ext, ?_⟩
  intro s hs _
  cases hs with
  | intro rn hrn =>
    cases hrn with
    | intro hmem hfields =>
      cases List.mem_cons.mp hmem with
      | inl heq =>
        subst heq
        exact Bool.noConfusion hfields.2.2.2
      | inr hnil => exact absurd hnil (by simp)

theorem n11_all_elements : ∀ e ∈ n11Frame.elements 1, civilHigh n11Frame e := by
  intro e he
  cases List.mem_cons.mp he with
  | inl heq => rw [heq]; exact n11_civil_high
  | inr hnil => exact absurd hnil (by simp)

theorem n11_pos : posOutcome n11Frame 1 :=
  ⟨rfl, n11_all_elements, rfl⟩

theorem n11_not_neg : ¬ negOutcome n11Frame 1 := by
  intro h
  cases h.2 with
  | inl hb =>
    have hbar : n11Frame.barred 1 = false := rfl
    rw [hbar] at hb
    exact Bool.noConfusion hb
  | inr hF =>
    cases hF.2 with
    | intro e he =>
      cases he with
      | intro heMem heRest =>
        exact heRest.2 (n11_pos.2.1 e heMem)

theorem n11_conflict_free : conflictFree n11Frame := by
  intro r _ hout
  cases hout with
  | intro a ha =>
    cases ha with
    | intro hmem _ =>
      exact List.not_mem_nil hmem

theorem n11_not_civil_high_neg : ¬ civilHighNeg n11Frame 2 := by
  intro h
  cases h with
  | intro r hr =>
    cases hr with
    | intro hstrong _ =>
      cases hstrong with
      | intro rn hrn =>
        cases hrn with
        | intro hmem hfields =>
          cases List.mem_cons.mp hmem with
          | inl heq =>
            subst heq
            exact Bool.noConfusion hfields.2.2.2
          | inr hnil => exact absurd hnil (by simp)

theorem n11_final_established :
    finalJudgment n11Frame 1 = some KernelV3.Judgment.established := by
  have hcls : classify n11Frame 1 = FinalCall.finalPos n11_pos := by
    rw [classify, dif_pos n11_pos]
  rw [finalJudgment_eq, hcls]
  rfl

/-- 针 11 非空洞见证：Pos 实际成立（排斥的两前提可同时可得——不因定理而空转），
Neg 不成立，判断=成立；¬q 侧标准亦不成立（同身份排斥两侧都非空洞）。 -/
theorem final_binary_decisions_witness :
    posOutcome n11Frame 1 ∧ ¬ negOutcome n11Frame 1 ∧ conflictFree n11Frame ∧
      civilHigh n11Frame 2 ∧ ¬ civilHighNeg n11Frame 2 ∧
        finalJudgment n11Frame 1 = some KernelV3.Judgment.established :=
  ⟨n11_pos, n11_not_neg, n11_conflict_free, n11_civil_high, n11_not_civil_high_neg,
    n11_final_established⟩

/-! ## 五、针 12：final_undetermined_iff_exhausted（含 Need 的更正 iff＋旧简式否证与片段重建） -/

/-- **针 12（S2，I:766）主式**：终局未定 ⇔ Exhausted4 ∧ Need ∧ ¬Pos ∧ ¬Neg
（主文公开更正版：Need 是必要合取分量；无 Need 时无二值终局读规范处置缺口 none，
不是未决）。 -/
theorem final_undetermined_iff_exhausted (fr : Frame) (q : Nat) :
    finalJudgment fr q = some KernelV3.Judgment.undetermined ↔
      (exhausted4 fr q ∧ needHolds fr q ∧ ¬ posOutcome fr q ∧ ¬ negOutcome fr q) := by
  constructor
  · intro h
    cases hc : classify fr q with
    | finalPos hpos =>
        rw [finalJudgment_eq] at h
        rw [hc] at h
        simp [judgmentOf] at h
    | finalNeg hneg =>
        rw [finalJudgment_eq] at h
        rw [hc] at h
        simp [judgmentOf] at h
    | finalUndet hexh hneed hnp hnn =>
        exact ⟨hexh, hneed, hnp, hnn⟩
    | finalGap hnp hnn hn =>
        rw [finalJudgment_eq] at h
        rw [hc] at h
        simp [judgmentOf] at h
  · intro h4
    have hexh := h4.1
    have hneed := h4.2.1
    have hnp := h4.2.2.1
    have hnn := h4.2.2.2
    have hcls : classify fr q = FinalCall.finalUndet hexh hneed hnp hnn := by
      rw [classify, dif_neg hnp, dif_neg hnn, dif_pos ⟨hexh, hneed⟩]
    rw [finalJudgment_eq, hcls]
    rfl

/-! 无理由框架的通用引理：框架理由表为空 ⇒ 任何原子都无标准证书。 -/
theorem no_reasons_no_standard (fr : Frame) (q : Nat) (hn : fr.reasons = []) :
    ¬ civilHigh fr q := by
  intro h
  cases h with
  | intro r hr =>
    cases hr with
    | intro hstrong _ =>
      cases hstrong with
      | intro rn hrn =>
        cases hrn with
        | intro hmem _ =>
          rw [hn] at hmem
          exact absurd hmem (by simp)

/-! 针 12 见证组一：规范处置缺口（旧简式否证）。要件说服负担在**对方**：本方不成立
不产生 Neg 第二支，对方也没证明——两值皆无、规则穷尽、无 Need：这是规范处置缺口
（none），不是未决（若规则/材料完整却两类证明皆无且没有 Need，返回规范处置缺口，
不能扩张未决定义吞掉它）。 -/

def n12BaseFrame : Frame :=
  { materials := [], cards := [], reasons := [], attacks := [], accepted := [],
    ready := fun q => q == 1,
    proofClosed := fun _ => true,
    barred := fun _ => false,
    elements := fun q => if q = 1 then [2] else [],
    burdenOnClaimant := fun _ => false,
    exhaustion := fun _ => emptyExh }

theorem n12_gap_exhausted : exhausted4 n12BaseFrame 1 :=
  ⟨fun _ he => (List.not_mem_nil he).elim, fun _ he => (List.not_mem_nil he).elim,
    fun _ he => (List.not_mem_nil he).elim, fun _ he => (List.not_mem_nil he).elim⟩

theorem n12_gap_not_need : ¬ needHolds n12BaseFrame 1 := by
  intro h
  cases h with
  | intro it hit =>
    cases hit with
    | intro hmem _ =>
      exact List.not_mem_nil hmem

theorem n12_gap_not_pos : ¬ posOutcome n12BaseFrame 1 := by
  intro h
  exact no_reasons_no_standard n12BaseFrame 2 rfl (h.2.1 2 (by decide))

theorem n12_gap_not_neg : ¬ negOutcome n12BaseFrame 1 := by
  intro h
  cases h.2 with
  | inl hb =>
    have hbar : n12BaseFrame.barred 1 = false := rfl
    rw [hbar] at hb
    exact Bool.noConfusion hb
  | inr hF =>
    cases hF.2 with
    | intro e he =>
      cases he with
      | intro _ heRest =>
        have hb : n12BaseFrame.burdenOnClaimant e = false := rfl
        rw [hb] at heRest
        exact Bool.noConfusion heRest.1

/-- **针 12 反例（主文公开更正）**：旧简式（穷尽且无二值 ⇔ 未决）不成立——
穷尽且无二值且**无 Need** 时读数是规范处置缺口（none），不是未决。 -/
theorem old_simple_form_refuted :
    ∃ (fr : Frame) (q : Nat),
      exhausted4 fr q ∧ ¬ posOutcome fr q ∧ ¬ negOutcome fr q ∧
        finalJudgment fr q ≠ some KernelV3.Judgment.undetermined := by
  refine ⟨n12BaseFrame, 1, n12_gap_exhausted, n12_gap_not_pos, n12_gap_not_neg, ?_⟩
  intro h
  have hcls : classify n12BaseFrame 1
      = FinalCall.finalGap n12_gap_not_pos n12_gap_not_neg
        (fun hp => n12_gap_not_need hp.2) := by
    rw [classify, dif_neg n12_gap_not_pos, dif_neg n12_gap_not_neg,
      dif_neg (fun hp => n12_gap_not_need hp.2)]
  rw [finalJudgment_eq] at h
  rw [hcls] at h
  simp [judgmentOf] at h

/-! 针 12 见证组二：完整终结片段的覆盖定理与旧简式的片段重建。 -/

/-- 覆盖定理（§5.4）：完整终结片段（必须评价 Ready+F、全部要件负担在本方——每项
要件均由本证/负担覆盖，覆盖从实际程序/负担表读出）中，无二值终局推出 Need；
等价地，片段内无 Need 则必有二值终局。 -/
theorem covered_fragment_binary_or_need (fr : Frame) (q : Nat)
    (hcov : coveredFragment fr q)
    (hnp : ¬ posOutcome fr q) (hnn : ¬ negOutcome fr q) : needHolds fr q := by
  by_cases hall : ∀ e ∈ fr.elements q, civilHigh fr e
  · cases hb : fr.barred q with
    | false =>
        exact absurd ⟨hcov.1, hall, hb⟩ hnp
    | true =>
        exact absurd ⟨hcov.1, Or.inl hb⟩ hnn
  · have hex : ∃ e ∈ fr.elements q, ¬ civilHigh fr e :=
      Classical.byContradiction fun hc =>
        hall (fun e he => Classical.byContradiction fun hce => hc ⟨e, he, hce⟩)
    cases hex with
    | intro e he =>
      cases he with
      | intro heMem hne =>
        exact absurd ⟨hcov.1, Or.inr ⟨hcov.2.1, e, heMem, hcov.2.2 e heMem, hne⟩⟩ hnn

/-- **针 12 片段重建**：在明确绑定的完整终结片段，旧简式（穷尽 ∧ 无二值 ⇔ 未决）
作为推论成立——Need 分量由覆盖定理补出，无 Need 的缺口情形被排除在片段之外。 -/
theorem old_simple_form_in_fragment (fr : Frame) (q : Nat)
    (hcov : coveredFragment fr q) (hexh : exhausted4 fr q) :
    finalJudgment fr q = some KernelV3.Judgment.undetermined ↔
      (exhausted4 fr q ∧ ¬ posOutcome fr q ∧ ¬ negOutcome fr q) := by
  constructor
  · intro h
    have h4 := (final_undetermined_iff_exhausted fr q).mp h
    exact ⟨h4.1, h4.2.2.1, h4.2.2.2⟩
  · intro hcond
    exact (final_undetermined_iff_exhausted fr q).mpr
      ⟨hexh, covered_fragment_binary_or_need fr q hcov hcond.2.1 hcond.2.2,
        hcond.2.1, hcond.2.2⟩

/-! 针 12 见证组三：更正 iff 的非空洞正例（真未决见证：先决未定且无法定替代）。 -/

def n12NeedItem : NeedItem :=
  { itemId := 9, kind := PendingKind.priorPending, noAlternative := true }

def n12UndetExh : ExhaustionRec :=
  { burden := [], presumption := [], obstruction := [], terminal := [], need := [n12NeedItem] }

def n12UndetFrame : Frame :=
  { n12BaseFrame with exhaustion := fun _ => n12UndetExh }

theorem n12_undet_exhausted : exhausted4 n12UndetFrame 1 :=
  ⟨fun _ he => (List.not_mem_nil he).elim, fun _ he => (List.not_mem_nil he).elim,
    fun _ he => (List.not_mem_nil he).elim, fun _ he => (List.not_mem_nil he).elim⟩

theorem n12_undet_need : needHolds n12UndetFrame 1 :=
  ⟨n12NeedItem, by decide, rfl⟩

theorem n12_undet_not_pos : ¬ posOutcome n12UndetFrame 1 := by
  intro h
  exact no_reasons_no_standard n12UndetFrame 2 rfl (h.2.1 2 (by decide))

theorem n12_undet_not_neg : ¬ negOutcome n12UndetFrame 1 := by
  intro h
  cases h.2 with
  | inl hb =>
    have hbar : n12UndetFrame.barred 1 = false := rfl
    rw [hbar] at hb
    exact Bool.noConfusion hb
  | inr hF =>
    cases hF.2 with
    | intro e he =>
      cases he with
      | intro _ heRest =>
        have hb : n12UndetFrame.burdenOnClaimant e = false := rfl
        rw [hb] at heRest
        exact Bool.noConfusion heRest.1

/-- 更正 iff 的非空洞正例：穷尽＋Need（先决未定且无法定替代）＋无二值 ⇒ 未决。 -/
theorem undetermined_witness :
    ∃ (fr : Frame) (q : Nat),
      exhausted4 fr q ∧ needHolds fr q ∧ ¬ posOutcome fr q ∧ ¬ negOutcome fr q ∧
        finalJudgment fr q = some KernelV3.Judgment.undetermined :=
  ⟨n12UndetFrame, 1, n12_undet_exhausted, n12_undet_need, n12_undet_not_pos,
    n12_undet_not_neg,
    (final_undetermined_iff_exhausted n12UndetFrame 1).mpr
      ⟨n12_undet_exhausted, n12_undet_need, n12_undet_not_pos, n12_undet_not_neg⟩⟩

/-! ## 六、针 13：proof_failure_not_ontic_negation（同一生成输入：R 真＋真实推导失败） -/

/-! 见证材料（§5.3.4 的改写例）：交付确实发生过（R 真、材料内容指向要件 2），但材料
**未准入**（如尚未最终结算的转账指令/无法确认作者身份的文书——必要局部条件不再成立）。 -/

def n13Material : EvidenceItem :=
  { evidenceId := 7, sourceId := 1, contentClaim := 2, admitted := false }

def n13Card : FactCard :=
  { cardId := 20, fromEvidence := 7, propKey := 1, value := true, reason := 3 }

def n13Reason : ReasonNode :=
  { reasonId := 30, claim := 2, polarity := true, strong := true, leaves := [20], warrant := 4 }

def n13Frame : Frame :=
  { materials := [n13Material], cards := [n13Card], reasons := [n13Reason], attacks := [],
    accepted := [],
    ready := fun q => q == 1,
    proofClosed := fun q => q == 1,
    barred := fun _ => false,
    elements := fun q => if q = 1 then [2] else [],
    burdenOnClaimant := fun e => e == 2,
    exhaustion := fun _ => emptyExh }

/-- 真实推导失败有因（一）：卡片被拒——唯一材料未准入，卡片构造的许可条件不满足。 -/
theorem n13_no_card : ¬ LegalDerives.card n13Frame n13Card := by
  intro h
  cases h.2 with
  | intro m hm =>
    cases hm with
    | intro hmem hmrest =>
      cases List.mem_cons.mp hmem with
      | inl heq =>
        subst heq
        exact absurd hmrest.1 (by decide)
      | inr hnil => exact absurd hnil (by simp)

/-- 真实推导失败有因（二）：标准不可得——唯一强理由的叶指向被拒卡片，许可不成立。 -/
theorem n13_no_standard : ¬ LegalDerives.standard n13Frame 2 := by
  intro h
  cases h with
  | intro r hr =>
    cases hr with
    | intro hstrong _ =>
      cases hstrong with
      | intro rn hrn =>
        cases hrn with
        | intro hmem hfields =>
          cases List.mem_cons.mp hmem with
          | inl heq =>
            subst heq
            have hlic := hfields.2.1
            have hleaf := hlic.2 20 (by decide)
            cases hleaf with
            | intro c hc =>
              cases hc with
              | intro _ hcrest =>
                have hcard : ∃ m ∈ n13Frame.materials,
                    m.admitted = true ∧ m.evidenceId = c.fromEvidence ∧ c.reason ≠ 0 :=
                  hcrest.2.2
                cases hcard with
                | intro m hm =>
                  cases hm with
                  | intro hmem2 hmrest2 =>
                    cases List.mem_cons.mp hmem2 with
                    | inl heq2 =>
                      subst heq2
                      exact absurd hmrest2.1 (by decide)
                    | inr hnil2 => exact absurd hnil2 (by simp)
          | inr hnil => exact absurd hnil (by simp)

theorem n13_not_pos : ¬ posOutcome n13Frame 1 := by
  intro h
  exact n13_no_standard (h.2.1 2 (by decide))

/-- 程序就绪＋举证终结＋本方负担＋要件未成立：负担规则产生不成立（§5.3.4：
若无其他充分许可且程序已就绪，负担规则产生不成立）。 -/
theorem n13_neg : negOutcome n13Frame 1 :=
  ⟨rfl, Or.inr ⟨rfl, 2, by decide, rfl, n13_no_standard⟩⟩

theorem n13_final : finalJudgment n13Frame 1 = some KernelV3.Judgment.notEstablished := by
  have hcls : classify n13Frame 1 = FinalCall.finalNeg n13_neg := by
    rw [classify, dif_neg n13_not_pos, dif_pos n13_neg]
  rw [finalJudgment_eq, hcls]
  rfl

/-- 完整终结片段覆盖见证（针 12 覆盖定理的非空洞正例）：n13Frame 覆盖、无 Need、
有二值终局（Neg）。 -/
theorem n13_covered : coveredFragment n13Frame 1 := by
  refine ⟨rfl, rfl, ?_⟩
  intro e he
  cases List.mem_cons.mp he with
  | inl heq => rw [heq]; exact rfl
  | inr hnil => exact absurd hnil (by simp)

theorem n13_no_need : ¬ needHolds n13Frame 1 := by
  intro h
  cases h with
  | intro it hit =>
    cases hit with
    | intro hmem _ =>
      exact List.not_mem_nil hmem

theorem covered_fragment_witness :
    coveredFragment n13Frame 1 ∧ ¬ needHolds n13Frame 1 ∧
      (posOutcome n13Frame 1 ∨ negOutcome n13Frame 1) :=
  ⟨n13_covered, n13_no_need, Or.inr n13_neg⟩

/-- 生成输入：同一输入承载评价框架侧与真值记录侧（R 分量=true）。 -/
def n13Gen : GenInput := { frame := n13Frame, focus := 1, onticTruth := true }

theorem n13_gen_truth :
    genTruthJudgment n13Gen =
      some { truth := true, judgment := KernelV3.Judgment.notEstablished } := by
  show (match finalJudgment n13Frame 1 with
        | some j => some ({ truth := true, judgment := j } : KernelV3.TruthJudgment)
        | none => none) =
    some { truth := true, judgment := KernelV3.Judgment.notEstablished }
  rw [n13_final]

/-- 评价对真值分量盲：翻转生成输入的 onticTruth 不改变判断分量
（仅在事后获知真实 R 发生过，不改变当前法庭输出——评价不读 R 通道）。 -/
theorem eval_blind_to_ontic_truth (g : GenInput) (b : Bool) :
    (genTruthJudgment { g with onticTruth := b }).map (fun r => r.judgment) =
      (genTruthJudgment g).map (fun r => r.judgment) := by
  show Option.map (fun r => r.judgment)
      (match finalJudgment g.frame g.focus with
        | some j => some ({ truth := b, judgment := j } : KernelV3.TruthJudgment)
        | none => none) =
    Option.map (fun r => r.judgment)
      (match finalJudgment g.frame g.focus with
        | some j => some ({ truth := g.onticTruth, judgment := j } : KernelV3.TruthJudgment)
        | none => none)
  cases finalJudgment g.frame g.focus with
  | some j => rfl
  | none => rfl

/-- **针 13（S2，I:767）**：求证失败不是本体否定——**同一生成输入**上：
R 侧记录真（材料在场、内容指向要件）＋推导侧真实失败（材料未准入 ⇒ 卡片被拒 ⇒
标准不可得）＋判断侧由负担规则产生不成立（非未决）；三侧读数同源（同一个 g）。 -/
theorem proof_failure_not_ontic_negation :
    ∃ (g : GenInput) (e : Nat),
      e ∈ (g.frame.elements g.focus) ∧
        g.onticTruth = true ∧
        (∃ m ∈ g.frame.materials, m.contentClaim = e ∧ m.admitted = false) ∧
        (∀ c ∈ g.frame.cards, ¬ LegalDerives.card g.frame c) ∧
        ¬ LegalDerives.standard g.frame e ∧
        genTruthJudgment g = some { truth := true, judgment := KernelV3.Judgment.notEstablished } := by
  refine ⟨n13Gen, 2, by decide, rfl,
    ⟨n13Material, by decide, rfl, rfl⟩, ?_, n13_no_standard, n13_gen_truth⟩
  intro c hc
  cases List.mem_cons.mp hc with
  | inl heq =>
    subst heq
    exact n13_no_card
  | inr hnil => exact absurd hnil (by simp)

/-! ## 七、针 14：argument_undec_not_final_undetermined（新法定负担输入通道） -/

/-- 负担输入不触碰论证层：材料/卡片/理由/攻击证书/接受集全部 rfl 不变
（负担输出不得反馈成为自己所要求的证据——负担通道根本不写这些字段）。 -/
theorem burden_input_leaves_argument_layer (fr : Frame) (bi : BurdenInput) :
    (applyBurdenInput fr bi).materials = fr.materials ∧
      (applyBurdenInput fr bi).cards = fr.cards ∧
      (applyBurdenInput fr bi).reasons = fr.reasons ∧
      (applyBurdenInput fr bi).attacks = fr.attacks ∧
      (applyBurdenInput fr bi).accepted = fr.accepted :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- 接受集/标准构造对负担输入不变（论证层与标准层读不到程序/负担位）。 -/
theorem in_ext_burden_invariant (fr : Frame) (bi : BurdenInput) (r : Nat) :
    inExt (applyBurdenInput fr bi) r ↔ inExt fr r :=
  Iff.rfl

theorem civil_high_burden_invariant (fr : Frame) (bi : BurdenInput) (e : Nat) :
    civilHigh (applyBurdenInput fr bi) e ↔ civilHigh fr e :=
  Iff.rfl

/-- Pos 终局对负担输入不变（负担输入永不翻转已成立的 Pos）。 -/
theorem pos_outcome_burden_invariant (fr : Frame) (bi : BurdenInput) (q : Nat) :
    posOutcome (applyBurdenInput fr bi) q ↔ posOutcome fr q :=
  Iff.rfl

theorem burden_input_never_flips_pos (fr : Frame) (bi : BurdenInput) (q : Nat)
    (hpos : posOutcome fr q) :
    finalJudgment (applyBurdenInput fr bi) q = some KernelV3.Judgment.established := by
  have hpos' : posOutcome (applyBurdenInput fr bi) q := hpos
  have hcls : classify (applyBurdenInput fr bi) q
      = FinalCall.finalPos hpos' := by
    rw [classify, dif_pos hpos']
  rw [finalJudgment_eq, hcls]
  rfl

/-- **针 14 一般式（新输入触发重评价）**：新法定负担输入（具名、作用于该争点、
终结举证）在 Neg 前提其余分量齐备时，把该快照的终局变为不成立——负担规则经
显式输入通道发动，材料缺证据不再自动产生负担终结（§5.2：阶段未到必须保留）。 -/
theorem burden_input_triggers_reevaluation (fr : Frame) (bi : BurdenInput) (q : Nat)
    (hq : bi.onQuestion = q) (hclose : bi.closesProof = true)
    (hr : fr.ready q = true)
    (he : ∃ e ∈ fr.elements q, fr.burdenOnClaimant e = true ∧ ¬ civilHigh fr e)
    (hpos : ¬ posOutcome fr q) :
    finalJudgment (applyBurdenInput fr bi) q = some KernelV3.Judgment.notEstablished := by
  subst hq
  have hF : (applyBurdenInput fr bi).proofClosed bi.onQuestion = true := by
    show (if bi.onQuestion = bi.onQuestion then bi.closesProof
        else fr.proofClosed bi.onQuestion) = true
    rw [if_pos rfl]
    exact hclose
  have hneg : negOutcome (applyBurdenInput fr bi) bi.onQuestion :=
    ⟨hr, Or.inr ⟨hF, he⟩⟩
  have hnp : ¬ posOutcome (applyBurdenInput fr bi) bi.onQuestion := fun hp => hpos hp
  have hcls : classify (applyBurdenInput fr bi) bi.onQuestion
      = FinalCall.finalNeg hneg := by
    rw [classify, dif_neg hnp, dif_pos hneg]
  rw [finalJudgment_eq, hcls]
  rfl

/-! 针 14 见证：输入前举证未终结（无二值终局——负担不发动），新负担输入后同快照
重评价为不成立；论证层理由 30 始终未进入接受集（未接受），且负担输入前后论证层
逐字段不变。 -/

def n14Frame : Frame := { n13Frame with proofClosed := fun _ => false }

def n14BurdenInput : BurdenInput :=
  { inputId := 100, statutoryBasis := 55, onQuestion := 1, closesProof := true }

theorem n14_not_pos : ¬ posOutcome n14Frame 1 := fun hp => n13_not_pos hp

theorem n14_not_neg_before : ¬ negOutcome n14Frame 1 := by
  intro h
  cases h.2 with
  | inl hb =>
    have hbar : n14Frame.barred 1 = false := rfl
    rw [hbar] at hb
    exact Bool.noConfusion hb
  | inr hF =>
    have hpc : n14Frame.proofClosed 1 = false := rfl
    rw [hpc] at hF
    exact Bool.noConfusion hF.1

theorem n14_no_need : ¬ needHolds n14Frame 1 := n13_no_need

/-- 输入前：举证未终结 ⇒ 两值皆无且无 Need ⇒ 规范处置缺口（none），**不是未决**，
也不是不成立（阶段未到必须保留，材料缺证据不自动产生负担终结）。 -/
theorem n14_before_none : finalJudgment n14Frame 1 = none := by
  have hcls : classify n14Frame 1
      = FinalCall.finalGap n14_not_pos n14_not_neg_before
        (fun hp => n14_no_need hp.2) := by
    rw [classify, dif_neg n14_not_pos, dif_neg n14_not_neg_before,
      dif_neg (fun hp => n14_no_need hp.2)]
  rw [finalJudgment_eq, hcls]
  rfl

theorem n14_not_in_ext_30 : ¬ inExt n14Frame 30 := fun h => List.not_mem_nil h

theorem n14_not_in_ext_30_after :
    ¬ inExt (applyBurdenInput n14Frame n14BurdenInput) 30 := fun h => List.not_mem_nil h

/-- 输入后：举证终结经负担通道写入，Neg 第二支发动——要件 2 本方负担、未成立。 -/
theorem n14_after_neg : negOutcome (applyBurdenInput n14Frame n14BurdenInput) 1 :=
  ⟨rfl, Or.inr ⟨by decide, 2, by decide, rfl, n13_no_standard⟩⟩

theorem n14_after_notEstablished :
    finalJudgment (applyBurdenInput n14Frame n14BurdenInput) 1
      = some KernelV3.Judgment.notEstablished := by
  have hnp : ¬ posOutcome (applyBurdenInput n14Frame n14BurdenInput) 1 :=
    fun hp => n13_not_pos hp
  have hcls : classify (applyBurdenInput n14Frame n14BurdenInput) 1
      = FinalCall.finalNeg n14_after_neg := by
    rw [classify, dif_neg hnp, dif_pos n14_after_neg]
  rw [finalJudgment_eq, hcls]
  rfl

theorem n14_after_not_undetermined :
    finalJudgment (applyBurdenInput n14Frame n14BurdenInput) 1
      ≠ some KernelV3.Judgment.undetermined := by
  intro h
  rw [n14_after_notEstablished] at h
  simp at h

/-- **针 14（S2，I:768）**：论证层未决不等于终局未定——**新法定负担输入**（具名身份
100、法定依据 55、独立通道，非论证层改读）产生"未接受而最终不成立"：输入前该争点
无二值终局（举证未终结，负担不发动），输入后重评价为不成立（且不是未决）；论证层
理由 30 输入前后都未进入接受集，论证层五字段逐字段不变。 -/
theorem argument_undec_not_final_undetermined :
    ∃ (fr : Frame) (bi : BurdenInput) (c : Nat),
      bi.inputId ≠ 0 ∧ bi.statutoryBasis ≠ 0 ∧
        (¬ inExt fr c ∧ ¬ inExt (applyBurdenInput fr bi) c) ∧
        (applyBurdenInput fr bi).reasons = fr.reasons ∧
        (applyBurdenInput fr bi).attacks = fr.attacks ∧
        (applyBurdenInput fr bi).accepted = fr.accepted ∧
        finalJudgment fr bi.onQuestion = none ∧
        finalJudgment (applyBurdenInput fr bi) bi.onQuestion
          = some KernelV3.Judgment.notEstablished ∧
        finalJudgment (applyBurdenInput fr bi) bi.onQuestion
          ≠ some KernelV3.Judgment.undetermined :=
  ⟨n14Frame, n14BurdenInput, 30, by decide, by decide,
    ⟨n14_not_in_ext_30, n14_not_in_ext_30_after⟩, rfl, rfl, rfl,
    n14_before_none, n14_after_notEstablished, n14_after_not_undetermined⟩

/-! ## 八、旗舰：评价层五针收口 -/

/-- **旗舰**：任一快照上，Pos 终局 ⇒ ①每要件标准证书的端到端许可追溯（卡片→材料→
准入）②Pos/Neg 互斥（实际前提排斥）③终局判断=成立 ④未决判读严格走含 Need 的更正
iff——针 10/11/12 的普遍层收口（针 13/14 为构造性见证定理，不入本合取）。 -/
theorem unified_eval_layer_flagship (fr : Frame) (q : Nat) (hpos : posOutcome fr q) :
    (∀ e ∈ fr.elements q,
      ∃ rn ∈ fr.reasons,
        rn.claim = e ∧ rn.polarity = true ∧ rn.reasonId ∈ fr.accepted ∧
          reasonLicensed fr rn ∧
          ∀ l ∈ rn.leaves,
            ∃ c ∈ fr.cards, c.cardId = l ∧ LegalDerives.card fr c ∧
              ∃ m ∈ fr.materials,
                m.admitted = true ∧ m.evidenceId = c.fromEvidence ∧ c.reason ≠ 0) ∧
      ¬ negOutcome fr q ∧
      finalJudgment fr q = some KernelV3.Judgment.established ∧
      (finalJudgment fr q = some KernelV3.Judgment.undetermined ↔
        (exhausted4 fr q ∧ needHolds fr q ∧ ¬ posOutcome fr q ∧ ¬ negOutcome fr q)) := by
  refine ⟨eval_has_licensed_derivation fr q hpos,
    fun hn => final_binary_decisions_exclusive fr q hpos hn, ?_,
    final_undetermined_iff_exhausted fr q⟩
  have hcls : classify fr q = FinalCall.finalPos hpos := by
    rw [classify, dif_pos hpos]
  rw [finalJudgment_eq, hcls]
  rfl

end JurisLean.Seams.UnifiedEvalLayer
