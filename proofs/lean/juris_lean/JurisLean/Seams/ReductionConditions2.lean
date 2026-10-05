import Mathlib.Tactic
import JurisLean.Seams.Probability

open JurisLean.Seams.Probability

/-!
## S3 条文批第二件（W4 批1／G3）：法释〔2023〕13号第 63—66 条进条件记录

**写者边界**：本件只新建这一份文件，不改动 `Seams/Probability.lean` 与任何既有件。
既有主契约 `ReductionData`、闸门 `reductionGate`、准许关系 `Allow`、下界 `reductionFloor`
一律原样引用，本件把它们放进新记录的 `base` 字段。于是"现有模型对某一法律位无感"
不再是注释里的客气话，而是**可检验的等式**与**可判定的准入式**。

### 一、法源与核验层级（法律侧 fail-closed）
一手源：《最高人民法院关于适用〈中华人民共和国民法典〉合同编通则若干问题的解释》，
法释〔2023〕13 号（2023-05-23 审委会第 1889 次会议通过，2023-12-05 施行，全文 69 条），
最高法官网权威发布页 `https://www.court.gov.cn/fabu/xiangqing/419382.html`（层级 A2 一手）。
本件第 63、64、65、66 条的引句按该页逐字照录，逐句挂在字段旁的注释上。

《民法典》第 584、585 条：**转载级**。人大一手文本本次未取得（`flk.npc.gov.cn` 不可达、
`npc.gov.cn` 目录页 403），本件引的是政府域名转载全文（湖南省审计厅 `sjt.hunan.gov.cn`），
双源字句逐字一致、标点从本件排版。**禁止把这两条读成"已对全国人大标准文本核验"**——
11 卷 §W4 批2 已把该表述封死。

第 66 条的分款读数存疑：一手页把该条排成三段（释明义务／一审未释明的二审处理／被告
一审未到庭的二审处理），本施工令记作"两款"。本件的字段只挂"第66条第1款（释明义务）"，
后两段登记为未覆盖片段；**款号差异登记为待复核项，不冒充定论**。

引句的核验强度不齐（照 07 卷 §四·一 的登记口径写）：**第64条三款与第65条三款**已由 07 卷
记为对该官方页逐句机检命中；**第63条与第66条**本件的引句取自同一页的本轮抽取、与 07 卷 §三
的要旨一致，但**未逐句机检**。故第63、66条引号内的文字若与公报页有出入，以公报页为准，
且这一出入不构成任何定理的前提（本件的定理只依赖位与 Bool/ℤ 的算法，不依赖引句文本）。

### 二、既有件与本件的分工（实测）
`Seams/Probability.lean` 的 `ReductionCondition` 有六个条件名，`reductionGate` 读其中五个
（只把 `balancing_factors` 留在闸门外，见该文件对第65条第1款"刻意不建定理"的立场），
`TwoSidedBurden` 另立一个守约方举证位做对照。实测（本件写入之前，`proofs/lean/juris_lean/JurisLean`
全树，`grep` 计行）：`可预见` **0 命中**；`释明` 只有 1 处命中，且在
`Seams/Transitions.lean:42` 的**限制注**里（"本件尚不含……释明义务（第66条第1款）"），
不是模型位；`Seams/Probability.lean` 内两者皆 **0 命中**。
即第66条第1款与第63条第1款（连同《民法典》第584条的可预见性封顶）**从未被模型表达**。
本件先把它做成盲区定理，再补出可判定的位。
（注：`Probability.lean` 此刻由另一写者并行修改，上面该行读数取自本会话开始时的工作树快照。）

另记一处款号引用漂移（**不在本件修改范围**）：既有件把"恶意违约……一般不予支持"引作
第65条第**2**款共五处，一手页该句是第65条第**3**款（第2款只是百分之三十门槛）。
本件一律按第65条第3款引用；纠错归 W1 与另一写者。

### 三、本件产出什么
1. `ConditionRecord F`：可判定条件记录（`base` + 六个 `Bool` 位 + 一个 `Amount` 位），
   每位旁挂条号、款号与逐字关键句；建模选择一律标 `[代拟稿]`，取不到一手的一律标 `转载级`。
2. `recordGate`／`recordFloor`／`AllowC`／`recordChoose`：**对照物**口径，形状照旧件，
   闸门以旧闸门为前提。
3. 已证定理三类（形状参照 `TwoSidedBurden`）：
   ① 盲区——`allow_blind_to_programme_bits`（第64条第1款＋第66条第1款）、
     `allow_blind_to_foreseeable_cap`（第63条第1款＋《民法典》第584条）、
     `allow_blind_to_malicious_register`（第65条第3款）、
     `allowC_blind_to_noAdjustmentClause`（第64条第3款，"不予支持"读成零效力）；
   ② 夹具改变外延——`clarification_changes_extension`、`foreseeable_cap_changes_extension`、
     `malicious_register_changes_extension`（三条都是**准许集**层面：同一个具体数额在一位取
     真/取假时归属相反），另加 `one_sided_burden_is_not_enough`（闸门面：第64条第2款单向不够）；
   ③ 不过度主张——`new_bits_never_open_base_closed_gate`、`recordGate_true_implies_oldGate_true`、
     `all_new_bits_open_still_cannot_pass_malicious_base`、
     `compliant_proof_alone_does_not_open_gate`、`recordFloor_le_reductionFloor`。
   另交可判定性：`allowC_iff_decidable`、`decidable_AllowC`、`recordGate_decidable`。
   全部零 `sorry`，全部走 `Bool`/`ℤ` 的闭式计算，不用浮点，不用 `native_decide`。

### 四、本件不做什么
- **不认定任何真实案件的违约金数额**，不认定任何真实案件的"过分高于"、恶意违约、
  可预见损失，也不作任何裁判结论。
- **不主张已实现全部 63—66 条**：63条第2款（额外费用）、第3款（扣除项）、66条后两段
  本件**没有**表达，见第五节。
- `recordGate`／`AllowC` 是本件构造的**对照物**，不是"现行法的酌减关系"。它们只把
  "旧模型少了哪一格、补上之后外延怎么变"量化成定理。
- 不声称 `recordChoose`（或旧件的 `choose`）最优、唯一，或与任何运行时实现相 refinement。
- 不把第65条第1款的衡量因素写成定理：因素面 `F` 经 `base.factors` 始终是未解释的自由输入。
- 不声称本件已入根、已编译、已过 CI；不做任何经验或校准主张。

### 五、未覆盖片段（承认没表达的法律内容，以及缺什么）
1. **第63条第2款**："除合同履行后可以获得的利益外，非违约方主张还有其向第三人承担违约责任
   应当支出的额外费用等其他因违约所造成的损失，并请求违约方赔偿，经审理认为该损失系违约一方
   订立合同时预见到或者应当预见到的，人民法院应予支持。"——未建模。缺：一个"额外费用"的
   数额位与它自己的可预见检验式；本件只有一个总封顶 `foreseeableLoss`，分不出"哪一部分
   损失因何被计入"。
2. **第63条第3款**："在确定违约损失赔偿额时，违约方主张扣除非违约方未采取适当措施导致的
   扩大损失、非违约方也有过错造成的相应损失、非违约方因违约获得的额外利益或者减少的必要
   支出的，人民法院依法予以支持。"——未建模。缺：四类扣除项各自的数额位与"主张扣除"的
   启动位；本件的下界只做可预见封顶，不做扣除。
3. **第66条后两段**（一审认为抗辩成立且未释明时二审可直接释明并组织举证、质证、辩论后判减；
   被告因客观原因一审未到庭、二审到庭并请求减少的处理）——未建模。缺：审级位与"到庭"位；
   本件的 `clarified` 只有一个不分审级的总位。
4. **第65条第3款的"一般"**：与旧件同样的降级——本件把恶意违约建成硬关闸，
   法院在恶意违约下仍予酌减的例外面未建模。
5. **第64条第1款的正面效力**："……人民法院依法予以支持"是**支持**该主张进入审理；
   本件只把它建成闸门的必要前提（关闸方向），"依法予以支持"的正面义务未建模。
6. **第64条第2款的证明标准**：条文只分配举证与举证必要，本件压成两个 `Bool`，
   与民诉法解释第 108、109 条的证明标准之间**无桥**（那是 W4 批3 的工作）。
7. **第65条第1款的衡量因素面**：仍是自由输入 `F`，无定理。
8. **记录层的 `DecidableEq`**：`F` 无判定，故本件不给记录整体的相等判定；
   可判定性只覆盖位面与闸门、下界、准入式。
9. **款号事实**：第66条分款读数未定谳；既有件第65条的五处款号未改（本件无权限改）。

### 六、档位
`LANDED_AND_ATTESTED`：**本件已入根并已认定**，此前此节写作"本件未编译／CI_NOT_RUN"是
**过期档位**（2026-10-05 验收轮更正）。现状：本件由根文件 `JurisLean.lean:180` 导入，
其 35 条定理逐条列在公理审计面 `AxiomAudit.lean:1484-1518`；最近一次整树 clean build
认定是 run 37227626074（subject 5aa3863，八作业 success，sorryAx 0）。
**该认定只属于那个 subject**：本文件之后的任何提交都不继承它，读数一律以源码与 CI 工件为准。
-/

namespace JurisLean.Seams.ReductionConditions2

section Record

/-- **条件记录**（W4 批1）：把法释〔2023〕13号第 63—66 条与《民法典》第 584 条的可预见性封顶
    拆成**可判定字段**。新增位全是 `Bool`，唯一的数额位是 `Amount`（=ℤ，最小货币单位），
    每一位都可闭式取值；唯一仍自由的输入是底数据里的因素面 `F`（第65条第1款）。

    法律侧的诚实线：字段旁的中文是**条文挂靠**，不是把自造要件冒充法条；
    凡属本件的建模选择一律标 `[代拟稿]`，一手取不到的一律标 `转载级`。 -/
structure ConditionRecord (F : Type) where
  /-- 底数据＝既有主契约 `ReductionData`，原样取回：`agreed`（约定违约金）、`loss`
      （第65条第1款"以民法典第五百八十四条规定的损失为基础"的那个损失）、
      `requested`（《民法典》第585条第2款"可以根据当事人的请求予以适当减少"，**转载级**）、
      `badFaith`（第65条第3款恶意违约的**既有**登记位，旧闸门已读它）、
      `proved`（第64条第2款**违约方**一侧的举证位）、`overFound`（第65条第2款
      "一般可以认定为过分高于造成的损失"的裁定位）、`factors`（第65条第1款因素面）。 -/
  base : ReductionData F
  /-- 第66条第1款（释明义务；A2 一手逐字）："当事人一方请求对方支付违约金，对方以合同不成立、
      无效、被撤销、确定不发生效力、不构成违约或者非违约方不存在损失等为由抗辩，未主张调整
      过高的违约金的，人民法院**应当**就若不支持该抗辩，当事人是否请求调整违约金进行**释明**。"
      本位读作"法院已就调整违约金问题作过释明"。
      `[代拟稿]`：条文给的是法院义务，本件把它压成一个不分审级的位（分审级缺位，
      见未覆盖片段第3项）。 -/
  clarified : Bool
  /-- 第64条第1款（A2 一手逐字）："当事人一方通过**反诉或者抗辩**的方式，请求调整违约金的，
      人民法院依法予以支持。"本位读作"调整主张已以反诉或抗辩的方式进入诉讼"。
      正面效力（"依法予以支持"）未建模，见未覆盖片段第5项。 -/
  viaCounterOrDefense : Bool
  /-- 第64条第2款**后段**（A2 一手逐字）："非违约方主张约定的违约金合理的，也应当提供相应的证据。"
      同条第2款**前段**是违约方一侧："违约方主张约定的违约金过分高于违约造成的损失，请求予以
      适当减少的，应当承担举证责任"——那一侧在底数据的 `proved` 位。两位合起来才是"双向举证"。 -/
  nonBreacherProved : Bool
  /-- 第64条第3款（A2 一手逐字）："当事人**仅以**合同约定不得对违约金进行调整为由主张不予调整
      违约金的，人民法院**不予支持**。"本位登记该抗辩是否被提出。
      按第3款它不产生"不予调整"的效果，故本件**故意不把它写进闸门、下界与准入式**
      （可检验形式见 `allowC_blind_to_noAdjustmentClause`）。 -/
  onlyNoAdjustmentClause : Bool
  /-- 第63条第1款（A2 一手逐字）："在认定民法典第五百八十四条规定的'违约一方订立合同时预见到
      或者应当预见到的因违约可能造成的损失'时，人民法院应当根据当事人订立合同的目的，综合考虑
      合同主体、合同内容、交易类型、交易习惯、磋商过程等因素，**按照与违约方处于相同或者类似
      情况的民事主体在订立合同时预见到或者应当预见到的损失予以确定**。"
      配《民法典》第584条末句（**转载级**）："……但是，**不得超过违约一方订立合同时预见到
      或者应当预见到的因违约可能造成的损失**。"本位是按该口径确定的可预见损失额（封顶）。 -/
  foreseeableLoss : Amount
  /-- 第63条第1款的比较基准是否按"与违约方处于**相同或者类似情况的民事主体**"这一客观口径确定。
      `[代拟稿]`：条文给的是认定方法（应当如何确定），本件把它建成一个可判定的口径位。 -/
  likeSubjectStandard : Bool
  /-- 第65条第3款（A2 一手逐字）："恶意违约的当事人一方请求减少违约金的，人民法院一般不予支持。"
      同一法律要件在旧件里由 `base.badFaith` 登记（旧闸门读它）；本件另立第二本登记，
      闸门按新位再关一次。款号按一手页记为第**3**款（旧件记作第2款，漂移未在本件修）。
      `[代拟稿]`："一般"留出的例外面未建模。 -/
  maliciousBreach : Bool

/-- 程序入口面（第64条第1款 + 第66条第1款）：调整主张或者已由反诉/抗辩提出，或者法院已就
    调整违约金释明、当事人据此提出。
    `[代拟稿]` 这个**析取**是本件的建模选择：两条文分别规定"反诉或者抗辩的方式"与"应当释明"，
    没有把它们写成一条析取式。请求之存在仍由底数据的 `requested`（第585条第2款）把关。 -/
def procedurePath {F : Type} (r : ConditionRecord F) : Bool :=
  r.viaCounterOrDefense || r.clarified

/-- 新闸门在旧闸门之外的合取面：程序入口 ∧ 非恶意违约（第65条第3款的第二本登记）∧
    守约方一侧已举证（第64条第2款后段）∧ 可预见口径按客观基准确定（第63条第1款）。
    第64条第3款的抗辩位**不在其中**（该款"不予支持"）。 -/
def extraGate {F : Type} (r : ConditionRecord F) : Bool :=
  procedurePath r && !r.maliciousBreach && r.nonBreacherProved && r.likeSubjectStandard

/-- **新闸门**：旧闸门是**前提**，新位只在旧闸门已开时继续筛选。
    写成 `if` 而非再套一层 `&&`，是为了让"新位不能替旧闸门开门"（③类定理）只用
    `if_pos`/`if_neg` 就能证，而不必拆解布尔合取。 -/
def recordGate {F : Type} (r : ConditionRecord F) : Bool :=
  if reductionGate r.base = true then extraGate r else false

/-- 可预见封顶后的损失基础（第63条第1款 + 《民法典》第584条末句，**转载级**）：
    酌减基准是第584条的损失，而该损失"不得超过违约一方订立合同时预见到或者应当预见到的
    因违约可能造成的损失"。 -/
def cappedBasis {F : Type} (r : ConditionRecord F) : Amount :=
  min r.base.loss r.foreseeableLoss

/-- 新口径的准许下界：形状与旧件 `reductionFloor`（`min 约定额 (max 损失 0)`）一致，
    只是把"损失"换成封顶后的损失基础。 -/
def recordFloor {F : Type} (r : ConditionRecord F) : Amount :=
  min r.base.agreed (max (cappedBasis r) 0)

/-- **对照物口径的准许关系** `AllowC`：与旧件 `Allow` 同形，闸门换成 `recordGate`、
    下界换成 `recordFloor`。本件不声称它是现行法的关系（见头部第四节）。 -/
def AllowC {F : Type} (r : ConditionRecord F) (x : Amount) : Prop :=
  (recordGate r = true → recordFloor r ≤ x ∧ x ≤ r.base.agreed) ∧
    (recordGate r = true ∨ x = r.base.agreed)

/-- 对照物口径的选择函数（镜像旧件 `choose` 的契约形状；不声称最优或唯一）。 -/
def recordChoose {F : Type} (r : ConditionRecord F) : Amount :=
  if recordGate r = true then recordFloor r else r.base.agreed

end Record

section Decidability

/-- 可判定（闸门面）：闸门是 `Bool` 值函数，"闸门开"这一命题由 `Bool` 等式的判定实例决定，
    也不要求 `F` 有任何判定性。本件不写 `Classical`/`by_contra`；公理维度以 CI 的
    `#print axioms` 为准，本件不自称干净。
    工程说明（**声明种类，非陈述强度**）：`Decidable p` 在本 pin 是
    `structure Decidable (p : Prop) : Type`，即**类型不是命题**，故 Lean 语法上**不许**写成
    `theorem`（实测报错 `type of theorem ... is not a proposition`）。
    这里改用 `def` 交出同一个判定项：待判命题、结论类型与证明项（`inferInstance`）
    与本轮之前**逐字相同**，没有加宽也没有收窄。 -/
def recordGate_decidable {F : Type} (r : ConditionRecord F) :
    Decidable (recordGate r = true) := inferInstance

/-- 可判定（数额面）：下界与约定额都是 `ℤ`，带的成员关系可判。
    声明种类同上——`Decidable p : Type`，不能是 `theorem`；类型与证明项一字未改。 -/
def band_membership_decidable {F : Type} (r : ConditionRecord F) (x : Amount) :
    Decidable (recordFloor r ≤ x) := inferInstance

/-- **准入的可判定形式**：`AllowC` 等价于一段只用 `Bool` 等式与整数序判定式的析取式——
    闸门开就要落在带内，闸门关就只能是约定额。法律读法：新口径下"这个数额准不准"是算出来的，
    不是悬着的。 -/
theorem allowC_iff_decidable {F : Type} (r : ConditionRecord F) (x : Amount) :
    AllowC r x ↔ (recordGate r = true ∧ recordFloor r ≤ x ∧ x ≤ r.base.agreed) ∨
      (¬ (recordGate r = true) ∧ x = r.base.agreed) := by
  constructor
  · intro h
    obtain ⟨himp, hor⟩ := h
    by_cases hg : recordGate r = true
    · exact Or.inl ⟨hg, himp hg⟩
    · cases hor with
      | inl hg2 => exact absurd hg2 hg
      | inr he => exact Or.inr ⟨hg, he⟩
  · rintro (⟨hg, hband⟩ | ⟨hnt, he⟩)
    · exact ⟨fun _ => hband, Or.inl hg⟩
    · exact ⟨fun h => absurd h hnt, Or.inr he⟩

/-- 下界不退化：准许带永不因可预见封顶而变成空带。 -/
theorem recordFloor_le_agreed {F : Type} (r : ConditionRecord F) :
    recordFloor r ≤ r.base.agreed := by
  unfold recordFloor
  exact min_le_left _ _

/-- **封顶单调（第63条第1款 + 《民法典》第584条"不得超过"的方向）**：
    加了可预见封顶之后，新下界**不高于**旧下界。法律读法：可预见性对酌减基准只起封顶作用，
    绝不会把基准抬高；封顶位本身也就不是开门的凭据（见③类定理）。 -/
theorem recordFloor_le_reductionFloor {F : Type} (r : ConditionRecord F) :
    recordFloor r ≤ reductionFloor r.base := by
  have h2 : max (min r.base.loss r.foreseeableLoss) 0 ≤ max r.base.loss 0 := by
    refine max_le ?_ (le_max_right _ _)
    exact le_trans (min_le_left _ _) (le_max_left _ _)
  unfold recordFloor reductionFloor cappedBasis
  refine le_min (min_le_left _ _) ?_
  exact le_trans (min_le_right _ _) h2

end Decidability

section Helpers

/-- 闸门开、额落在带内 ⇒ 准入（旧件 `allow_of_gate_open` 的同形判据）。 -/
theorem allowC_of_gate_open_band {F : Type} (r : ConditionRecord F) (x : Amount)
    (hg : recordGate r = true) (hband : recordFloor r ≤ x ∧ x ≤ r.base.agreed) :
    AllowC r x := ⟨fun _ => hband, Or.inl hg⟩

/-- 闸门关 ⇒ 唯一可准入的是维持约定额（旧件 `allow_of_gate_closed` 的同形判据）。 -/
theorem allowC_of_gate_closed {F : Type} (r : ConditionRecord F) (x : Amount)
    (hg : ¬ (recordGate r = true)) (hx : x = r.base.agreed) : AllowC r x :=
  ⟨fun h => absurd h hg, Or.inr hx⟩

/-- 闸门关且额不等于约定额 ⇒ 不准入（②类定理的反向判据）。 -/
theorem not_allowC_of_gate_closed {F : Type} (r : ConditionRecord F) (x : Amount)
    (hg : ¬ (recordGate r = true)) (hx : ¬ (x = r.base.agreed)) : ¬ AllowC r x := by
  intro h
  obtain ⟨_, hor⟩ := h
  cases hor with
  | inl hg2 => exact absurd hg2 hg
  | inr he => exact hx he

/-- 旧关系 `Allow` 一侧的判据：旧闸门开而额低于**旧**下界 ⇒ 旧关系不准入。
    ②类定理用它把"旧口径算不出新口径的结论"钉成事实。 -/
theorem not_Allow_of_gate_open_and_lt_floor {F : Type} (c : ReductionData F) (x : Amount)
    (hg : reductionGate c = true) (hx : ¬ (reductionFloor c ≤ x)) : ¬ Allow c x := by
  intro h
  obtain ⟨himp, _⟩ := h
  exact hx ((himp hg).1)

/-- `AllowC` 的判定程序：先判闸门，再判带。三个分情况都落在 `Bool` 等式与整数序的判定实例上
    （判定实例缺失就会编译红，不会被排中律悄悄兜底）——这就是本件对"可判定"的兑现方式。
    声明种类同上：`Decidable (AllowC r x)` 是 `Type` 不是 `Prop`，故写成 `def`；
    待判命题与判定项构造一字未改。 -/
def decidable_AllowC {F : Type} (r : ConditionRecord F) (x : Amount) :
    Decidable (AllowC r x) := by
  by_cases hg : recordGate r = true
  · by_cases h1 : recordFloor r ≤ x
    · by_cases h2 : x ≤ r.base.agreed
      · exact isTrue (allowC_of_gate_open_band r x hg ⟨h1, h2⟩)
      · refine isFalse ?_
        intro h
        obtain ⟨himp, _⟩ := h
        exact h2 ((himp hg).2)
    · refine isFalse ?_
      intro h
      obtain ⟨himp, _⟩ := h
      exact h1 ((himp hg).1)
  · by_cases h3 : x = r.base.agreed
    · exact isTrue (allowC_of_gate_closed r x hg h3)
    · exact isFalse (not_allowC_of_gate_closed r x hg h3)

end Helpers

section Fixtures

/-- 夹具底数据甲：约定 300、损失 100，有请求、非恶意、违约方一侧已举证，但未另行认定
    "过分高于"（`overFound := false`）——旧闸门只因第65条第2款的百分之三十门槛而开
    （`13 * 100 = 1300 < 10 * 300 = 3000`）。 -/
def openBaseA : ReductionData Unit :=
  { agreed := 300, loss := 100, requested := true, badFaith := false, proved := true,
    overFound := false, factors := () }

/-- 夹具底数据乙：约定 300、损失 200，其余同甲，`overFound := true`
    （第65条第2款"一般可以认定"的裁定位取真）。 -/
def openBaseB : ReductionData Unit :=
  { agreed := 300, loss := 200, requested := true, badFaith := false, proved := true,
    overFound := true, factors := () }

/-- 甲的旧闸门开（闭式 `Bool`/`ℤ` 计算，不用浮点）。 -/
theorem openBaseA_oldGate : reductionGate openBaseA = true := by
  simp [reductionGate, conditionHolds, overThirtyTest, openBaseA]

/-- 乙的旧闸门开。 -/
theorem openBaseB_oldGate : reductionGate openBaseB = true := by
  simp [reductionGate, conditionHolds, overThirtyTest, openBaseB]

/-- 甲的旧下界是损失 100；乙的旧下界是损失 200（`reductionFloor` 不含可预见封顶）。 -/
theorem oldFloor_openBaseA : reductionFloor openBaseA = (100 : Amount) := by
  simp [reductionFloor, openBaseA]

theorem oldFloor_openBaseB : reductionFloor openBaseB = (200 : Amount) := by
  simp [reductionFloor, openBaseB]

/-- **中立记录**：`base` 原样放好，受检位取"放行且不设更紧的界"的值（程序入口以反诉/抗辩为真、
    守约方已举证、口径按客观基准、非恶意、无"约定不得调整"抗辩、可预见额取约定额），
    只有释明位由参数给。盲区与③类定理用它，为使前提里不夹带任何别的差异。 -/
def neutral {F : Type} (d : ReductionData F) (clar : Bool) : ConditionRecord F :=
  { base := d, clarified := clar, viaCounterOrDefense := true, nonBreacherProved := true,
    onlyNoAdjustmentClause := false, foreseeableLoss := d.agreed,
    likeSubjectStandard := true, maliciousBreach := false }

/-- 变**程序入口位**（第64条第1款／第66条第1款）的夹具记录：`viaCounterOrDefense := false`，
    于是入口面只由释明位决定；其余位与 `neutral` 相同。 -/
def programmeRecord {F : Type} (d : ReductionData F) (clar : Bool) : ConditionRecord F :=
  { base := d, clarified := clar, viaCounterOrDefense := false, nonBreacherProved := true,
    onlyNoAdjustmentClause := false, foreseeableLoss := d.agreed,
    likeSubjectStandard := true, maliciousBreach := false }

/-- 变**可预见损失额**（第63条第1款 + 《民法典》第584条末句，**转载级**）的夹具记录。 -/
def capRecord {F : Type} (d : ReductionData F) (cap : Amount) : ConditionRecord F :=
  { base := d, clarified := true, viaCounterOrDefense := true, nonBreacherProved := true,
    onlyNoAdjustmentClause := false, foreseeableLoss := cap,
    likeSubjectStandard := true, maliciousBreach := false }

/-- 变**恶意违约第二本登记位**（第65条第3款）的夹具记录。 -/
def malRecord {F : Type} (d : ReductionData F) (mal : Bool) : ConditionRecord F :=
  { base := d, clarified := true, viaCounterOrDefense := true, nonBreacherProved := true,
    onlyNoAdjustmentClause := false, foreseeableLoss := d.agreed,
    likeSubjectStandard := true, maliciousBreach := mal }

/-- 变**"约定不得调整"抗辩位**（第64条第3款）的夹具记录：本件按该款不给它任何效力。 -/
def clauseRecord {F : Type} (d : ReductionData F) (v : Bool) : ConditionRecord F :=
  { base := d, clarified := true, viaCounterOrDefense := true, nonBreacherProved := true,
    onlyNoAdjustmentClause := v, foreseeableLoss := d.agreed,
    likeSubjectStandard := true, maliciousBreach := false }

/-- 变**守约方一侧举证位**（第64条第2款后段）的夹具记录。 -/
def burdenRecord {F : Type} (d : ReductionData F) (v : Bool) : ConditionRecord F :=
  { base := d, clarified := true, viaCounterOrDefense := true, nonBreacherProved := v,
    onlyNoAdjustmentClause := false, foreseeableLoss := d.agreed,
    likeSubjectStandard := true, maliciousBreach := false }

/-- 变**客观基准口径位**（第63条第1款"相同或者类似情况的民事主体"）的夹具记录。 -/
def likeRecord {F : Type} (d : ReductionData F) (v : Bool) : ConditionRecord F :=
  { base := d, clarified := true, viaCounterOrDefense := true, nonBreacherProved := true,
    onlyNoAdjustmentClause := false, foreseeableLoss := d.agreed,
    likeSubjectStandard := v, maliciousBreach := false }

/-- 中立记录不替旧闸门加戏：旧闸门开 ⇒ 新闸门开（`[代拟稿]` 口径下的保守性）。
    投影归约交给 `simp`（`show` 在本 pin 里不做结构投影的 iota 归约，已实测）。 -/
theorem recordGate_neutral_of_oldGate_true {F : Type} (d : ReductionData F) (clar : Bool)
    (h : reductionGate d = true) : recordGate (neutral d clar) = true := by
  simp [recordGate, extraGate, procedurePath, neutral, h]

/-- 程序入口两面皆假（既未以反诉/抗辩提出，法院也未释明）⇒ 新闸门关，
    与旧闸门是否已开无关。第64条第1款 + 第66条第1款的合取读法。 -/
theorem recordGate_false_of_no_programme_entry {F : Type} (d : ReductionData F)
    (h : reductionGate d = true) : recordGate (programmeRecord d false) = false := by
  simp [recordGate, extraGate, procedurePath, programmeRecord, h]

/-- 客观基准口径位为假 ⇒ 新闸门关（第63条第1款"按照与违约方处于相同或者类似情况的民事主体
    ……予以确定"在本件被建成要件之一，`[代拟稿]`）。 -/
theorem like_standard_off_closes_gate {F : Type} (d : ReductionData F)
    (h : reductionGate d = true) : recordGate (likeRecord d false) = false := by
  simp [recordGate, extraGate, procedurePath, likeRecord, h]

end Fixtures

section Blindness

/-- **①盲区（第64条第1款 + 第66条第1款）**：旧准许关系 `Allow` 只读底数据，
    因此对"是否经反诉/抗辩提出"与"法院是否已释明"**完全无感**——两个取值给出同一个准许集。
    这不是"法律如此"，而是"本仓当前模型未表达该条文"的可检验形式
    （写入本件之前，`释明` 在全树只有 `Seams/Transitions.lean:42` 限制注里的 1 次提及，
    没有任何模型位读它）。 -/
theorem allow_blind_to_programme_bits {F : Type} (d : ReductionData F) (v w : Bool)
    (x : Amount) :
    Allow (programmeRecord d v).base x ↔ Allow (programmeRecord d w).base x :=
  ⟨fun h => h, fun h => h⟩

/-- **①盲区（第63条第1款 + 《民法典》第584条末句，转载级）**：旧关系看不到可预见封顶额——
    把封顶额改成任何值，旧的准许集一字不变。`可预见` 在本件写入前也是 0 命中。 -/
theorem allow_blind_to_foreseeable_cap {F : Type} (d : ReductionData F) (v w : Amount)
    (x : Amount) :
    Allow (capRecord d v).base x ↔ Allow (capRecord d w).base x :=
  ⟨fun h => h, fun h => h⟩

/-- **①盲区（第65条第3款）**：旧关系只有 `base.badFaith` 一本恶意登记；
    本件新增的第二本登记对旧关系毫无影响。 -/
theorem allow_blind_to_malicious_register {F : Type} (d : ReductionData F) (v w : Bool)
    (x : Amount) :
    Allow (malRecord d v).base x ↔ Allow (malRecord d w).base x :=
  ⟨fun h => h, fun h => h⟩

/-- **①盲区（第64条第3款，方向相反）**："当事人仅以合同约定不得对违约金进行调整为由主张不予
    调整违约金的，人民法院不予支持"——本件把"不予支持"实现成**该位不进入闸门、下界与准入式**，
    于是它对新口径的准许集也毫无影响。这是"零效力"的可检验读法，
    **不是**对第3款全部法律效果的宣称。 -/
theorem allowC_blind_to_noAdjustmentClause {F : Type} (d : ReductionData F) (x : Amount) :
    AllowC (clauseRecord d true) x ↔ AllowC (clauseRecord d false) x :=
  ⟨fun h => h, fun h => h⟩

/-- 同上一条的闸门形式：新闸门对第64条第3款的抗辩位无感。 -/
theorem recordGate_blind_to_noAdjustmentClause {F : Type} (d : ReductionData F) :
    recordGate (clauseRecord d true) = recordGate (clauseRecord d false) := by
  simp [recordGate, extraGate, procedurePath, clauseRecord]

/-- 旧闸门的读取面只有一本：底数据。上面三条盲区定理的共同原因写成等式。 -/
theorem reductionGate_reads_only_base {F : Type} (d : ReductionData F) (clar : Bool) :
    reductionGate (neutral d clar).base = reductionGate d := by
  simp [neutral]

end Blindness

section Extension

/-- 释明位为真时新闸门开（夹具甲：旧闸门开，入口面只剩释明这一条路）。 -/
theorem gate_programmeRecord_on : recordGate (programmeRecord openBaseA true) = true := by
  simp [recordGate, extraGate, procedurePath, reductionGate, conditionHolds, overThirtyTest,
    programmeRecord, openBaseA]

/-- 恶意位为真时新闸门关（第65条第3款的第二本登记）。 -/
theorem gate_malRecord_on : recordGate (malRecord openBaseB true) = false := by
  simp [recordGate, extraGate, procedurePath, reductionGate, conditionHolds, overThirtyTest,
    malRecord, openBaseB]

/-- 封顶前后的下界取值：乙式（约定 300、损失 200）封顶额 100 时下界 100，
    封顶额 300（封顶不咬）时下界 200＝旧下界。这两颗算珠支撑②类定理。 -/
theorem floor_capRecord_openBaseB_100 :
    recordFloor (capRecord openBaseB 100) = (100 : Amount) := by
  simp [recordFloor, cappedBasis, capRecord, openBaseB]

theorem floor_capRecord_openBaseB_300 :
    recordFloor (capRecord openBaseB 300) = (200 : Amount) := by
  simp [recordFloor, cappedBasis, capRecord, openBaseB]

/-- 甲式（约定 300、损失 100）的下界：封顶取约定额时不咬，下界 100。 -/
theorem floor_programmeRecord_openBaseA :
    recordFloor (programmeRecord openBaseA true) = (100 : Amount) := by
  simp [recordFloor, cappedBasis, programmeRecord, openBaseA]

/-- 乙式的下界：封顶取约定额时不咬，下界 200。 -/
theorem floor_malRecord_openBaseB_off :
    recordFloor (malRecord openBaseB false) = (200 : Amount) := by
  simp [recordFloor, cappedBasis, malRecord, openBaseB]

/-- **②外延改变（第66条第1款 释明 + 第64条第1款 反诉/抗辩）**：交出具体夹具——
    同一份底数据（甲）、同一个数额 100，**释明过**就被新口径准许，**未释明**就不被准许。
    故"释明"这一位不是装饰：它改变外延。
    对照：旧关系 `Allow` 对这两次取值给出**相同**准许集（`allow_blind_to_programme_bits`）。 -/
theorem clarification_changes_extension :
    AllowC (programmeRecord openBaseA true) (100 : Amount) ∧
      ¬ AllowC (programmeRecord openBaseA false) (100 : Amount) := by
  have hon : recordGate (programmeRecord openBaseA true) = true := gate_programmeRecord_on
  have hclosed : recordGate (programmeRecord openBaseA false) = false :=
    recordGate_false_of_no_programme_entry openBaseA openBaseA_oldGate
  constructor
  · refine allowC_of_gate_open_band _ _ hon ?_
    rw [floor_programmeRecord_openBaseA]
    exact ⟨le_refl _, by simp [programmeRecord, openBaseA]⟩
  · refine not_allowC_of_gate_closed _ _ ?_ ?_
    · simp [hclosed]
    · intro he
      have h3 : (programmeRecord openBaseA false).base.agreed = (300 : Amount) := by
        simp [programmeRecord, openBaseA]
      rw [h3] at he
      exact absurd he (by decide)

/-- **②外延改变（第63条第1款 + 《民法典》第584条末句，转载级）**：同一份底数据（乙：约定 300、
    损失 200），可预见额取 100 时数额 150 被新口径准许；封顶额取 300（封顶不咬）时同一个 150
    不被准许——而它在**旧**关系里一律不被准许（`capRecord openBaseB 100 |>.base` 就是
    `openBaseB`，读取面见 `allow_blind_to_foreseeable_cap`）。
    三件事合起来：该位改变新口径的外延，且旧口径表达不出这个差别。 -/
theorem foreseeable_cap_changes_extension :
    AllowC (capRecord openBaseB 100) (150 : Amount) ∧
      ¬ AllowC (capRecord openBaseB 300) (150 : Amount) ∧
      ¬ Allow openBaseB (150 : Amount) := by
  have hb1 : recordGate (capRecord openBaseB 100) = true := by
    simp [recordGate, extraGate, procedurePath, reductionGate, conditionHolds, overThirtyTest,
      capRecord, openBaseB]
  have hb2 : recordGate (capRecord openBaseB 300) = true := by
    simp [recordGate, extraGate, procedurePath, reductionGate, conditionHolds, overThirtyTest,
      capRecord, openBaseB]
  refine ⟨?_, ?_, ?_⟩
  · refine allowC_of_gate_open_band (capRecord openBaseB 100) 150 hb1 ?_
    rw [floor_capRecord_openBaseB_100]
    exact ⟨by decide, by simp [capRecord, openBaseB]⟩
  · intro h
    obtain ⟨himp, _⟩ := h
    have hband := himp hb2
    rw [floor_capRecord_openBaseB_300] at hband
    exact absurd hband.1 (by decide)
  · refine not_Allow_of_gate_open_and_lt_floor openBaseB 150 openBaseB_oldGate ?_
    rw [oldFloor_openBaseB]
    decide

/-- **②外延改变（第65条第3款）**：恶意位为假时 200 被新口径准许、为真时 200 不被准许，
    而旧关系在同一份底数据（`malRecord openBaseB true |>.base` 就是 `openBaseB`，
    读取面见 `allow_blind_to_malicious_register`）上仍准许 200。
    故第二本恶意登记确实改变外延，旧口径看不出这个差别。 -/
theorem malicious_register_changes_extension :
    AllowC (malRecord openBaseB false) (200 : Amount) ∧
      Allow openBaseB (200 : Amount) ∧
      ¬ AllowC (malRecord openBaseB true) (200 : Amount) := by
  have hg : recordGate (malRecord openBaseB false) = true := by
    simp [recordGate, extraGate, procedurePath, reductionGate, conditionHolds, overThirtyTest,
      malRecord, openBaseB]
  refine ⟨?_, ?_, ?_⟩
  · refine allowC_of_gate_open_band (malRecord openBaseB false) 200 hg ?_
    rw [floor_malRecord_openBaseB_off]
    exact ⟨le_refl _, by simp [malRecord, openBaseB]⟩
  · refine allow_of_gate_open openBaseB 200 openBaseB_oldGate ?_
    rw [oldFloor_openBaseB]
    exact ⟨le_refl _, by simp [openBaseB]⟩
  · refine not_allowC_of_gate_closed _ _ ?_ ?_
    · simp [gate_malRecord_on]
    · intro he
      have h3 : (malRecord openBaseB true).base.agreed = (300 : Amount) := by
        simp [malRecord, openBaseB]
      rw [h3] at he
      exact absurd he (by decide)

/-- **②外延改变（第64条第2款 双向举证）**：底数据那一侧（前段，违约方举证）已足使旧闸门开，
    但守约方位（后段）为假时新闸门关、为真时开——单向不够。
    本件只把它写成闸门上的合取，不涉及证明标准（见未覆盖片段第6项）。 -/
theorem one_sided_burden_is_not_enough :
    recordGate (burdenRecord openBaseA true) = true ∧
      recordGate (burdenRecord openBaseA false) = false := by
  refine ⟨?_, ?_⟩
  · simp [recordGate, extraGate, procedurePath, reductionGate, conditionHolds, overThirtyTest,
      burdenRecord, openBaseA]
  · simp [recordGate, extraGate, procedurePath, reductionGate, conditionHolds, overThirtyTest,
      burdenRecord, openBaseA]

/-- 新口径的选择函数总被自己的准入关系接受（镜像旧件 `reduction_admits_declared_conditions`
    的契约形状；不声称最优或唯一）。 -/
theorem allowC_admits_recordChoose {F : Type} (r : ConditionRecord F) :
    AllowC r (recordChoose r) := by
  refine ⟨?_, ?_⟩
  · intro hg
    rw [recordChoose, if_pos hg]
    exact ⟨le_refl _, recordFloor_le_agreed r⟩
  · by_cases hg : recordGate r = true
    · rw [recordChoose, if_pos hg]
      exact Or.inl hg
    · rw [recordChoose, if_neg hg]
      exact Or.inr rfl

end Extension

section NonOverclaim

/-- **③不过度主张（一般式）**：新位**不能**替旧闸门开门——旧闸门关时，
    无论释明、反诉/抗辩、守约方举证、客观口径、恶意、封顶、"约定不得调整"这些位取什么值，
    新闸门一律关。法律读法：本件没有把任何新位说成独立的酌减依据。 -/
theorem new_bits_never_open_base_closed_gate {F : Type} (r : ConditionRecord F)
    (h : reductionGate r.base = false) : recordGate r = false := by
  have hnt : ¬ (reductionGate r.base = true) := by simp [h]
  rw [recordGate, if_neg hnt]

/-- **③不过度主张（读取面）**：新闸门开 ⇒ 旧闸门开。上一条的逆否读法，
    挡住"新口径比旧口径更容易酌减"的误读。 -/
theorem recordGate_true_implies_oldGate_true {F : Type} (r : ConditionRecord F)
    (h : recordGate r = true) : reductionGate r.base = true := by
  by_cases hb : reductionGate r.base = true
  · exact hb
  · rw [recordGate, if_neg hb] at h
    exact absurd h Bool.false_ne_true

/-- 新位全部取"放行"值的具体记录：底数据用旧件的 `maliciousData`（恶意违约，第65条第3款），
    释明已作、经反诉/抗辩提出、守约方已举证、口径按客观基准、恶意位为假、封顶取约定额。 -/
def onMaliciousAllNewOpen : ConditionRecord Unit :=
  { base := maliciousData, clarified := true, viaCounterOrDefense := true,
    nonBreacherProved := true, onlyNoAdjustmentClause := false, foreseeableLoss := 200,
    likeSubjectStandard := true, maliciousBreach := false }

/-- **③不过度主张（具体夹具）**：新位全放行仍过不了旧件的恶意违约底数据——
    旧闸门已经关着（旧件已证 `maliciousData_gate`）。这条把"新位不是后门"钉在具体数据上。 -/
theorem all_new_bits_open_still_cannot_pass_malicious_base :
    recordGate onMaliciousAllNewOpen = false := by
  have hb : reductionGate onMaliciousAllNewOpen.base = false := by
    simp [onMaliciousAllNewOpen, maliciousData_gate]
  exact new_bits_never_open_base_closed_gate onMaliciousAllNewOpen hb

/-- **③不过度主张（第64条第2款）**：守约方一侧举证完成并不使新闸门开——底数据那一侧的闸门
    关着时，两侧合取仍然关。挡住"双向举证＝酌减依据"的过度读法。 -/
theorem compliant_proof_alone_does_not_open_gate :
    recordGate (burdenRecord maliciousData true) = false := by
  have hb : reductionGate (burdenRecord maliciousData true).base = false := by
    simp [burdenRecord, maliciousData_gate]
  exact new_bits_never_open_base_closed_gate (burdenRecord maliciousData true) hb

end NonOverclaim

/- 本件的法律侧边界（与 07 卷 §四、11 卷 §W4 对照）：
   上面的盲区定理与外延定理断言的**全是模型事实**——某个位在旧关系里没被读到、
   补上之后某个具体数额的归属发生变化——不是裁判规则。`AllowC` 是本件构造的对照物，
   把它说成"现行法的酌减关系"即越界；用它做任何案件结论即越界。
   条文核验状态：第63—66条为最高法官网权威发布页 A2 一手逐字；《民法典》第584、585条
   封顶为**转载级**，未取得人大一手文本，不得写"已对全国人大标准文本核验"。
   第66条的分款读数（两款抑或三段）与既有件第65条的五处款号漂移均登记在头部第五节，
   本件未修，也无权修。 -/

end JurisLean.Seams.ReductionConditions2
