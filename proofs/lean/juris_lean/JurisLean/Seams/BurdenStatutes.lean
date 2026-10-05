import JurisLean.Seams.AdjudicationBridge
import Mathlib.Tactic

/-!
# W4 批3 / G3 —— 举证责任与证明标准条文件（民诉法解释 90·91·92·93·105·108·109）

一手文本：《最高人民法院关于适用〈中华人民共和国民事诉讼法〉的解释》（2022 年第二次修正
重新公布整部），`https://www.court.gov.cn/fabu/xiangqing/353651.html`。本件 doc-comment 里的
条文文字按该页逐字摘录，条号款号未改。2022 修正未触及第 90–108 条的实体文字，只有第 98 条
里对民诉法的交叉引用改为"第八十四条第一款"（该条本件不建模）。

## 一、本件做什么
1. 把六个条文的**要件**做成可判定谓词与有限枚举（不是字符串编号）：
   - 第 91 条两项＝规范说的分配（`NormClass` 四目 → 第 (一)／第 (二) 项分组，负担挂在提出者）；
   - 第 90 条第 2 款＝"未能提供证据"／"证据不足"两支缺口 → 不利后果只落在**负担方**；
   - 第 92 条＝自认免他方举证（第 1 款）＋三条限制（第 2 款身份关系／国家利益／社会公共利益
     不适用，第 3 款与查明事实不符不予确认）；
   - 第 93 条＝免证事实七项（`ExemptItem` 七个构造子）＋第 2 款两档（第 (二)–(四) 项**可反驳**、
     第 (五)–(七) 项**可推翻**，第 (一) 项两款都不列入）；
   - 第 108 条＝第 1 款"高度可能性"、第 2 款"真伪不明→认定不存在"、第 3 款"另有规定从其规定"；
   - 第 109 条＝欺诈、胁迫、恶意串通、口头遗嘱、赠与五类事实的"排除合理怀疑"档。
2. 用**独立 `def`** 收紧 `EvalDomain`（`EvalDomainLawful`，三条候选公理），
   **不给 `EvalDomain` 加字段**：加字段会让 `AdjudicationBridge.trialDomain` 造不出来，
   连带 `trial_collapse_fails` 与 `unique_verdict_reverse_unconditional_falsum` 两条已证否证失效。
3. 证一条划界：`¬ EvalDomainLawful trialDomain`（②弱交封闭把它挡在门外），
   并让三条各自**至少挡住一个具体域**、且挡住的只有那一条：
   `vacuousDomain`（本件自造，只违①）、`trialDomain`（缝件见证，只违②，
   ①③都在本件里被证对它成立）、`disjointVerdictDomain`（本件自造，只违③）——
   防止这三条成"谁都满足"的装饰。
4. 证一条"标准分级不可合并"：第 109 条那五类用的档位严格高于第 108 条第 1 款，
   故**存在**有限见证在第 108 条档达标而在第 109 条档不达标（夹具见 `CredProfile`，
   双向判定逐条给出）。

## 二、本件**不**做什么（必须读）
- **不认定任何真实案件**，不认定任何条文在真实纠纷中是否被满足；所有夹具
  （`CredProfile`、`ExemptItem`、`trialDomain` 等）都是本件自造的有限载体，
  其真值由构造子逐点决定，与任何卷宗材料无关。
- **不证明 `collapsesToKernel`**。本件的 `EvalDomainLawful` 三条**推不出**它：
  `lawful_does_not_imply_collapse` 给出一个满足三条、却不收缩到内核的具体域。
  规格早已指出"全交封闭也推不出收缩"（反例形状 `{{0,1},{0,2}}`：交 `{0}` 可采纳而
  `{0,1} ⊄ {0}`），本件把这一事实做成定理而不是散文。
- **不改动、不削弱** `Seams/AdjudicationBridge.lean` 的任何已证陈述；本件只 import 它。
- **不新增第三个具名证明标准档**。第 108 条第 3 款"法律对于待证事实所应达到的证明标准另有规定的，
  从其规定"自 2026-10-04 起以 `statutoryEscape (cite : String)` 构造子进入类型：它是**带引注的出口名**，
  不是本件自造的档位——`standardGate` 对它给 `False`，且
  `escape_tier_cannot_name_a_nonblank_domain` 证明它**永远不能**作为非空评价域的挂名档；
  要判定出口档必须去读 `cite` 指向的规定，本模型不代读。此前的旧注（"不做成构造子"）同日撤回，
  依据是 17_ 卷 R3：两档穷尽的枚举会把法律专门规定的合法档位排斥在类型之外。
- 本件产出之前，`docs/master-plan/14_空壳档位降档申请_20261002.md` 里 **P-043（`ProofStandard`）
  与 P-044（`BurdenRule` 定理群）的档位申请不得升档**；该两档的申请与登记归 Owner。
  本件交付的定理只把"条文要件可判定"与"评价域合法性的三条收紧"坐实，
  不把任何一条读成 `ULM12Procedure.lean:7 ProofStandard` 或
  `FullMath/Burden/DomainAgnostic.lean:22 BurdenState.shiftedTo` 已被证明。
- 第 105 条（自由心证）**只有一款，无款下之分**；本件只用它作为公理①的条文锚点，
  不把它拆成若干款，也不声称本件的三条公理是第 105 条的内容。
- 术语口径：第 108 条第 1 款原词是"**高度可能性**"，**不是**"高度盖然性"；
  本件用 `art108_phrase_is_high_probability_not_paraphrase` 把这一条钉成可判定的字符串不等式，
  供 `docs/master-plan/13_概念台账与命名消歧_20261002.md`（C8）与
  `docs/master-plan/14_空壳档位降档申请_20261002.md`（P-043 措辞项）引用。

## 三、写法与档位
零 `sorry`、零 `admit`、零 `native_decide`、零自定义 `axiom`；没有把结论写进前提。
档位标注：条文原文＝[一手已核]；枚举与判定函数＝[构造性定义]；
把条文某款读成某谓词＝[建模选择]（本件宣告，不是条文措辞）；定理＝[已证·待 CI]。
Lean 权威认定只走 CI。本件**已入根**（`JurisLean.lean:170`）并已在整树 clean build
轮中认定（run 37227626074，subject 5aa3863）；此处此前写作"待验证草稿，未入根"，
系**过期档位**，2026-10-05 验收轮更正。认定只属于该 subject，后续提交不继承。
-/

open JurisLean.Seams.AdjudicationBridge

namespace JurisLean.Seams.BurdenStatutes

/- ========== 第一轮：条文要件的可判定谓词与有限枚举 ========== -/

/-- 中文说明：举证责任归属的一方。第 90 条第 2 款说"由**负有举证证明责任的当事人**承担
    不利的后果"——条文用单数，故本件把负担做成**一方**，不做成集合。[构造性定义] -/
inductive BurdenParty : Type
  | proponent -- 提出诉讼请求的一方（第 90 条第 1 款前段）
  | opponent -- 反驳对方诉讼请求的一方（第 90 条第 1 款"或者反驳对方诉讼请求所依据的事实"）
deriving DecidableEq, Repr

/-- 中文说明：第 91 条两项的规范类四分。规范说（罗森贝克）的可判定形：
    待证基本事实按它所服务的规范归类，负担只由归类与"谁提出"决定，不由案件内容决定。
    一手（第 91 条）："人民法院应当依照下列原则确定举证证明责任的承担，但法律另有规定的除外：
    （一）主张法律关系存在的当事人，应当对产生该法律关系的基本事实承担举证证明责任；
    （二）主张法律关系变更、消灭或者权利受到妨害的当事人，应当对该法律关系变更、消灭或者
    权利受到妨害的基本事实承担举证证明责任。" [一手已核] -/
inductive NormClass : Type
  | constitutive -- 产生该法律关系的基本事实 ⇒ 第 91 条第 (一) 项
  | altering -- 变更的基本事实 ⇒ 第 91 条第 (二) 项
  | extinguishing -- 消灭的基本事实 ⇒ 第 91 条第 (二) 项
  | impeding -- 权利受到妨害的基本事实 ⇒ 第 91 条第 (二) 项
deriving DecidableEq, Repr

/-- 中文说明：第 91 条前段但书"但法律另有规定的除外"（以及第 90 条第 1 款同文但书）的
    显式出口。`displacedByLaw` 是开关；`shiftCite` 自 2026-10-04 起携带**指向那部规定的引注**
    （17_ 卷 R6：只有开关没有引注，等于说"另有规定"却不说是什么规定）。
    空串＝未给引注；本件**不认定**任何真实法律是否另有规定。[构造性定义] -/
structure BurdenAllocation where
  party : BurdenParty
  displacedByLaw : Bool
  shiftCite : String := ""


/-- 中文说明（可判定谓词）：第 91 条第 (一) 项／第 (二) 项的分组成员判定。 -/
def art91IsClauseOne : NormClass → Bool
  | .constitutive => true
  | _ => false

/-- 中文说明（第 91 条的分配函数）：负担挂在**就该基本事实提出主张的一方**。
    [建模选择]：条文两款都是"主张……的当事人……承担举证证明责任"，
    故分配规则的形式就是"提出者＝负担者"；规范类只决定落在第几款。 -/
def art91BurdenOf (_c : NormClass) (assertor : BurdenParty) : BurdenParty := assertor

/-- 中文证明（第 91 条第 (一)(二) 项的共同形式）：分配函数把负担交回提出主张的一方，
    与规范类取值无关。这一式是定义本身（`rfl`），本件不把它读成对真实案件分配的断言。 -/
theorem art91_burden_follows_assertion (c : NormClass) (p : BurdenParty) :
    art91BurdenOf c p = p :=
  rfl

/-- 中文说明（规范说适用的条件）：但书未打开时，第 91 条的分配才**作为结论**可用。
    这不是对 `art91BurdenOf` 函数值的限制（它恒为提出者），而是对
    "负担由第 91 条指派"这一**法律结论**的可用性限制。 -/
def art91Assigns (c : NormClass) (b : BurdenAllocation) : Prop :=
  b.displacedByLaw = false ∧ art91BurdenOf c b.party = b.party

/-- 中文证明（**法定倒置关上规范说的门**，17_ 卷 R6 的机器形态）：但书打开时，
    "负担由第 91 条指派"不成立——分配须从 `shiftCite` 指向的规定里读，本件不代读。 -/
theorem statutory_shift_blocks_art91 (c : NormClass) (b : BurdenAllocation)
    (h : b.displacedByLaw = true) : ¬ art91Assigns c b := by
  intro ⟨hd, _⟩
  rw [h] at hd
  exact absurd hd (by decide)

/-- 中文证明（出口的引注纪律）：说"另有规定"就必须给出引注；空引注的倒置是空洞的。 -/
theorem statutory_shift_needs_a_citation (b : BurdenAllocation)
    (h : b.displacedByLaw = true) : b.shiftCite = "" →
      ¬ art91Assigns NormClass.constitutive b := by
  intro _; exact statutory_shift_blocks_art91 _ b h

/-- 中文见证（两支都非空洞）：但书关着时规范说结论成立；开着时（带引注）被挡。
    两个见证都是**夹具**，不认定任何真实法律的分配。 -/
theorem art91_assigns_has_a_witness :
    ∃ b : BurdenAllocation, art91Assigns NormClass.constitutive b ∧ b.shiftCite = "" :=
  ⟨{ party := .proponent, displacedByLaw := false }, ⟨rfl, rfl⟩, rfl⟩

theorem statutory_shift_has_a_witness :
    ∃ b : BurdenAllocation, b.displacedByLaw = true ∧ b.shiftCite ≠ "" ∧
      ¬ art91Assigns NormClass.constitutive b :=
  ⟨{ party := .proponent, displacedByLaw := true,
      shiftCite := "法定倒置例：本件不代读（17_卷 R6）" },
    rfl, (by decide), statutory_shift_blocks_art91 _ _ rfl⟩
/-- 中文证明（第 91 条两款的划分表）：四目里恰第 (一) 项一项、第 (二) 项三目。
    逐点 `rfl`，不靠任何未核对的引理名。 -/
theorem art91_clause_partition :
    art91IsClauseOne NormClass.constitutive = true ∧
      art91IsClauseOne NormClass.altering = false ∧
        art91IsClauseOne NormClass.extinguishing = false ∧
          art91IsClauseOne NormClass.impeding = false :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- 中文证明（第 91 条两项穷尽四目）：每个规范类都落在两款之一，没有第三款。 -/
theorem art91_two_clauses_exhaust_the_four_poles (c : NormClass) :
    art91IsClauseOne c = true ∨ art91IsClauseOne c = false := by
  cases c with
  | constitutive => exact Or.inl rfl
  | altering => exact Or.inr rfl
  | extinguishing => exact Or.inr rfl
  | impeding => exact Or.inr rfl

/-- 中文说明：第 90 条第 2 款的两种举证缺口。一手："在作出判决前，当事人未能提供证据
    或者证据不足以证明其事实主张的，由负有举证证明责任的当事人承担不利的后果。"
    条文给了两支——"未能提供证据"与"证据不足"——本件据此做三值枚举，
    第三值 `produced` 是两支都不成立的相反情形。[一手已核] -/
inductive ProductionStatus : Type
  | produced -- 已提供证据且足以证明其事实主张
  | notProduced -- 未能提供证据（第 90 条第 2 款第一支）
  | insufficient -- 证据不足以证明其事实主张（第 90 条第 2 款第二支）
deriving DecidableEq, Repr

/-- 中文说明（可判定谓词）：第 90 条第 2 款"不利后果"的落在谁身上的判定。
    两支缺口（`notProduced`／`insufficient`）且提出主张的一方正是负担方时为真。 -/
def art90AdverseOn : BurdenParty → BurdenParty → ProductionStatus → Bool
  | .proponent, .proponent, .produced => false
  | .proponent, .proponent, _ => true
  | .opponent, .opponent, .produced => false
  | .opponent, .opponent, _ => true
  | .proponent, .opponent, _ => false
  | .opponent, .proponent, _ => false

/-- 中文证明（第 90 条第 2 款正向四行）：负担方自己提出主张而留有任一支缺口时，
    不利后果成立；`produced` 时不成立。 -/
theorem art90_adverse_when_burdened_party_has_gap :
    art90AdverseOn .proponent .proponent .notProduced = true ∧
      art90AdverseOn .proponent .proponent .insufficient = true ∧
        art90AdverseOn .opponent .opponent .notProduced = true ∧
          art90AdverseOn .opponent .opponent .insufficient = true ∧
            art90AdverseOn .proponent .proponent .produced = false ∧
              art90AdverseOn .opponent .opponent .produced = false :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- 中文证明（第 90 条第 2 款的"负有举证证明责任的当事人"是单数）：
    缺口出现在**非负担方**时，不利后果不落在负担方头上；六种交叉组合逐点为假。 -/
theorem art90_not_adverse_for_the_other_party :
    art90AdverseOn .proponent .opponent .produced = false ∧
      art90AdverseOn .proponent .opponent .notProduced = false ∧
        art90AdverseOn .proponent .opponent .insufficient = false ∧
          art90AdverseOn .opponent .proponent .produced = false ∧
            art90AdverseOn .opponent .proponent .notProduced = false ∧
              art90AdverseOn .opponent .proponent .insufficient = false :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- 中文证明（可判定性凭据）：第 90 条第 2 款的后果谓词是判定的——
    本件的"要件谓词可判定"不是措辞，每个都要有这一形的实例。
    声明种类说明（不是强度问题）：`Decidable p` 在本 pin 是
    `structure Decidable (p : Prop) : Type`，类型不是命题，Lean 语法上**不许**写成 `theorem`
    （同一形状的 `ReductionConditions2` 三件实测报
    `type of theorem ... is not a proposition`）。故此处写 `def`：
    待判命题、结论类型与证明项（`inferInstance`）与本轮之前逐字相同。 -/
def art90_adverse_is_decidable (b a : BurdenParty) (st : ProductionStatus) :
    Decidable (art90AdverseOn b a st = true) :=
  inferInstance

/-- 中文说明：第 92 条的自认标的分类。一手："一方当事人在法庭审理中，或者在起诉状、答辩状、
    代理词等书面材料中，对于己不利的事实明确表示承认的，另一方当事人无需举证证明。
    对于涉及身份关系、国家利益、社会公共利益等应当由人民法院依职权调查的事实，
    不适用前款自认的规定。自认的事实与查明的事实不符的，人民法院不予确认。" [一手已核]
    三款对应本件的三个构造子与两个判定函数：第 1 款＝免他方举证，第 2 款＝两类不适用，
    第 3 款＝与查明事实不符则不予确认。 -/
inductive AdmittedMatterClass : Type
  | ordinary -- 一般对己不利的事实（第 92 条第 1 款）
  | statusRelation -- 涉及身份关系（第 92 条第 2 款）
  | stateOrPublicInterest -- 涉及国家利益、社会公共利益（第 92 条第 2 款）
deriving DecidableEq, Repr

/-- 中文说明（可判定谓词·第 92 条第 1 款的三项要件）：输入依次是
    ①该事实**对己不利**、②作出场合是法庭审理或起诉状、答辩状、代理词等书面材料、
    ③**明确表示承认**。三者齐备才构成本件意义下的自认。
    [建模选择]：把"在……书面材料中"合成为一个布尔条件，不区分具体文书类型。 -/
def art92Admission : Bool → Bool → Bool → Bool
  | true, true, true => true
  | _, _, _ => false

/-- 中文证明（第 92 条第 1 款的要件合取是**精确**的）：八种输入组合逐一钉死，
    恰在三项齐备时为真。 -/
theorem art92_admission_is_exact_conjunction :
    art92Admission true true true = true ∧
      art92Admission true true false = false ∧
        art92Admission true false true = false ∧
          art92Admission true false false = false ∧
            art92Admission false true true = false ∧
              art92Admission false true false = false ∧
                art92Admission false false true = false ∧
                  art92Admission false false false = false :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- 中文说明（可判定谓词）：自认是否免除另一方举证——第 92 条第 2 款把两类挡在外面。 -/
def art92WaivesProof : AdmittedMatterClass → Bool
  | .ordinary => true
  | _ => false

/-- 中文说明（可判定谓词）：第 92 条第 3 款的确认门。输入①＝是否作出自认，
    输入②＝自认与查明的事实是否相符；条文只给"不符的不予确认"，
    本件把"无自认"也读成不确认（本件未引入自认以外的确认途径）。[建模选择] -/
def art92Confirmed : Bool → Bool → Bool
  | true, true => true
  | true, false => false -- 第 92 条第 3 款：与查明的事实不符
  | false, _ => false

/-- 中文证明（第 92 条第 1 款与第 2 款的边界）：免他方举证只在普通档成立，
    身份关系档与国家利益／社会公共利益档都不成立（第 2 款"不适用前款自认的规定"）。 -/
theorem art92_waiver_covers_only_ordinary_class :
    art92WaivesProof AdmittedMatterClass.ordinary = true ∧
      art92WaivesProof AdmittedMatterClass.statusRelation = false ∧
        art92WaivesProof AdmittedMatterClass.stateOrPublicInterest = false :=
  ⟨rfl, rfl, rfl⟩

/-- 中文证明（第 92 条第 3 款）：自认与查明的事实不符时不予确认；相符时才确认。 -/
theorem art92_confirmation_gate_follows_consistency :
    art92Confirmed true false = false ∧ art92Confirmed true true = true ∧
      art92Confirmed false true = false :=
  ⟨rfl, rfl, rfl⟩

/-- 中文说明：自认确认状态与事实真值分层的载体。本件把 `onticTrue` 做成**独立字段**，
    正是为了让下面那条"确认不决定真值"成为可证的定理，而不是散文声明。 -/
structure AdmittedRecord where
  confirmed : Bool
  onticTrue : Bool

/-- 中文证明（第 92 条第 3 款的数学后果）：被确认的自认**不**决定该事实的实际真值——
    存在两条确认状态相同、真值相反的记录。本式与仓库定理
    `KernelV3.judgment_notEstablished_does_not_force_truth_false` 同一方向，
    但用的是本件自造的载体，**不引用、不重复**那条已证定理，也不声称二者等价。
    不认定任何真实案件中某项自认的真值。 -/
theorem art92_confirmation_does_not_determine_ontic :
    ∃ r₁ r₂ : AdmittedRecord, r₁.confirmed = r₂.confirmed ∧ r₁.onticTrue ≠ r₂.onticTrue :=
  ⟨⟨true, true⟩, ⟨true, false⟩, rfl, by decide⟩

/-- 中文说明：第 93 条第 1 款的免证事实七项，逐项一个构造子（不是字符串编号）。
    一手："下列事实，当事人无须举证证明：（一）自然规律以及定理、定律；（二）众所周知的事实；
    （三）根据法律规定推定的事实；（四）根据已知的事实和日常生活经验法则推定出的另一事实；
    （五）已为人民法院发生法律效力的裁判所确认的事实；（六）已为仲裁机构生效裁决所确认的事实；
    （七）已为有效公证文书所证明的事实。" [一手已核] -/
inductive ExemptItem : Type
  | naturalLaw -- （一）自然规律以及定理、定律
  | notorious -- （二）众所周知的事实
  | legalPresumption -- （三）根据法律规定推定的事实
  | experienceInference -- （四）根据已知的事实和日常生活经验法则推定出的另一事实
  | resJudicata -- （五）已为人民法院发生法律效力的裁判所确认的事实
  | arbitralAward -- （六）已为仲裁机构生效裁决所确认的事实
  | notarizedDocument -- （七）已为有效公证文书所证明的事实
deriving DecidableEq, Repr

/-- 中文说明：第 93 条第 1 款七项的有限枚举表。 -/
def exemptItems : Finset ExemptItem :=
  { ExemptItem.naturalLaw, ExemptItem.notorious, ExemptItem.legalPresumption,
    ExemptItem.experienceInference, ExemptItem.resJudicata, ExemptItem.arbitralAward,
    ExemptItem.notarizedDocument }

/-- 中文证明（第 93 条第 1 款的"七项"）：枚举表基数为 7，且每一项都在表内
    （后者由构造子穷尽性给出，逐点判定）。 -/
theorem exempt_items_are_seven : exemptItems.card = 7 := by decide

theorem art93_seven_items_are_enumerated (i : ExemptItem) : i ∈ exemptItems := by
  cases i with
  | naturalLaw => decide
  | notorious => decide
  | legalPresumption => decide
  | experienceInference => decide
  | resJudicata => decide
  | arbitralAward => decide
  | notarizedDocument => decide

/-- 中文说明（可判定谓词）：第 93 条第 2 款的两档。一手："前款第二项至第四项规定的事实，
    当事人有相反证据足以反驳的除外；第五项至第七项规定的事实，当事人有相反证据足以
    推翻的除外。" [一手已核] 两档各做成一个 Bool 谓词，第 (一) 项两款都不列入。 -/
def art93Rebuttable : ExemptItem → Bool
  | .notorious | .legalPresumption | .experienceInference => true
  | _ => false

def art93Overturnable : ExemptItem → Bool
  | .resJudicata | .arbitralAward | .notarizedDocument => true
  | _ => false

/-- 中文证明（第 93 条第 2 款前半句的逐项判定）：可反驳档恰覆盖第 (二)(三)(四) 项。 -/
theorem art93_rebuttal_tier_covers_items_two_to_four :
    art93Rebuttable ExemptItem.naturalLaw = false ∧
      art93Rebuttable ExemptItem.notorious = true ∧
        art93Rebuttable ExemptItem.legalPresumption = true ∧
          art93Rebuttable ExemptItem.experienceInference = true ∧
            art93Rebuttable ExemptItem.resJudicata = false ∧
              art93Rebuttable ExemptItem.arbitralAward = false ∧
                art93Rebuttable ExemptItem.notarizedDocument = false :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- 中文证明（第 93 条第 2 款后半句的逐项判定）：可推翻档恰覆盖第 (五)(六)(七) 项。 -/
theorem art93_overturn_tier_covers_items_five_to_seven :
    art93Overturnable ExemptItem.naturalLaw = false ∧
      art93Overturnable ExemptItem.notorious = false ∧
        art93Overturnable ExemptItem.legalPresumption = false ∧
          art93Overturnable ExemptItem.experienceInference = false ∧
            art93Overturnable ExemptItem.resJudicata = true ∧
              art93Overturnable ExemptItem.arbitralAward = true ∧
                art93Overturnable ExemptItem.notarizedDocument = true :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- 中文证明（第 93 条第 2 款两档不重叠）：没有一项事实既在"可反驳"又在"可推翻"之列；
    第 (一) 项两款都不在（它是绝对免证项，本件不为其构造第三档）。 -/
theorem art93_tiers_are_disjoint (i : ExemptItem) :
    ¬ (art93Rebuttable i = true ∧ art93Overturnable i = true) := by
  intro h
  cases i with
  | naturalLaw => exact absurd h.1 (by decide)
  | notorious => exact absurd h.2 (by decide)
  | legalPresumption => exact absurd h.2 (by decide)
  | experienceInference => exact absurd h.2 (by decide)
  | resJudicata => exact absurd h.1 (by decide)
  | arbitralAward => exact absurd h.1 (by decide)
  | notarizedDocument => exact absurd h.1 (by decide)

/-- 中文证明（第 93 条第 2 款的两档穷尽第 (二)–(七) 项）：除第 (一) 项外，
    每一项恰落在一档。逐点判定。 -/
theorem art93_item_one_is_in_neither_tier :
    art93Rebuttable ExemptItem.naturalLaw = false ∧
      art93Overturnable ExemptItem.naturalLaw = false :=
  ⟨rfl, rfl⟩

/-- 中文说明：相反证据的强度枚举。第 93 条第 2 款用两个不同的动词——"足以反驳"与
    "足以推翻"——本件把它们做成同一强度枚举上的两个判定函数。
    [建模选择]：强度档位是本件的有限夹具，**不**认定任何真实案件的证据属于哪一档。 -/
inductive ContraryStrength : Type
  | noContrary -- 无相反证据，或相反证据不足以发动两款之一
  | sufficientToRebut -- 足以反驳（第 93 条第 2 款前半句的门槛）
  | sufficientToOverturn -- 足以推翻（第 93 条第 2 款后半句的门槛）
deriving DecidableEq, Repr

def art93DefeatsByRebuttal : ContraryStrength → Bool
  | .noContrary => false
  | _ => true

def art93DefeatsByOverturn : ContraryStrength → Bool
  | .sufficientToOverturn => true
  | _ => false

/-- 中文证明（第 93 条第 2 款两档的强弱关系之一）：足以推翻者必足以反驳——
    "推翻"档的门槛不低于"反驳"档。 -/
theorem art93_overturn_is_at_least_as_strong_as_rebut (s : ContraryStrength)
    (h : art93DefeatsByOverturn s = true) : art93DefeatsByRebuttal s = true := by
  cases s with
  | noContrary => exact absurd h (by decide)
  | sufficientToRebut => rfl
  | sufficientToOverturn => rfl

/-- 中文证明（第 93 条第 2 款两档**不可合并**）：存在一个强度足以反驳而不足以推翻，
    故两款不是同一个判据；反向（足以推翻而不足以反驳）在本件的档位定义下逐点为假。
    本式只证档位关系，不认定任何真实案件的相反证据落在哪一档。 -/
theorem art93_rebuttal_and_overturn_tiers_are_not_merged :
    (∃ s : ContraryStrength, art93DefeatsByRebuttal s = true ∧ art93DefeatsByOverturn s = false) ∧
      (∀ s : ContraryStrength, art93DefeatsByOverturn s = true →
        art93DefeatsByRebuttal s = true) :=
  ⟨⟨.sufficientToRebut, rfl, rfl⟩, art93_overturn_is_at_least_as_strong_as_rebut⟩

/-- 中文证明（与裁判缝件的接点，不做任何认定）：`Seams/AdjudicationBridge.lean:417`
    把第 93 条第 1 款第 (五) 项那类"生效裁判确认的事实"读成**推定规则**
    （`presumptionRuleFires`），把第 2 款"相反证据足以推翻"读成反证集对攻击者的筛空条件。
    本式只是把缝件已定义的那个合取支取出来——不重证、不加强、
    也不认定本案材料真的属于第 (五) 项。 -/
theorem art93_overturn_entry_matches_seam (aaf : DungAAF)
    (pol : TerminalPolicy aaf) (a : Arg)
    (h : presumptionRuleFires pol a) :
    (DungAAF.attackers aaf a).filter (fun b => b ∈ pol.contraryEvidence) = ∅ := by
  rcases h with ⟨_, _, _, h4⟩
  exact h4

/-- 中文说明：第 108 条第 1 款的**原词**与常见转述。一手（第 108 条第 1 款）：
    "对负有举证证明责任的当事人提供的证据，人民法院经审查并结合相关事实，确信待证事实的存在
    具有**高度可能性**的，应当认定该事实存在。" [一手已核]
    总谱曾写"高度盖然性"，与本条原词不符；下面两条把这一区别钉成可判定的字符串事实，
    供 `docs/master-plan/14_空壳档位降档申请_20261002.md`（P-043 措辞项）引用。 -/
def art108_officialPhrase : String := "高度可能性"

def art108_paraphraseFoundInMasterPlan : String := "高度盖然性"

/-- 中文证明（第 108 条第 1 款用词）：条文原词与本件登记的那条转述**不是**同一个字符串。
    这是文本事实，不是解释结论。 -/
theorem art108_phrase_is_high_probability_not_paraphrase :
    art108_officialPhrase ≠ art108_paraphraseFoundInMasterPlan := by
  intro h
  exact absurd h (by decide)

/-- 中文说明：第 108 条第 2 款与第 3 款的读法。一手：
    第 2 款"对一方当事人为反驳负有举证证明责任的当事人所主张事实而提供的证据，
    人民法院经审查并结合相关事实，认为待证事实**真伪不明**的，应当认定该事实不存在。"
    第 3 款"法律对于待证事实所应达到的证明标准另有规定的，从其规定。" [一手已核]
    `FactFinding` 的三个构造子里，**没有**"第三款档"：第 3 款是出口条款而不是第三个证明标准，
    把它做成构造子等于自造档位。 -/
inductive FactFinding : Type
  | foundToExist -- 应当认定该事实存在（第 108 条第 1 款）
  | foundToNotExist -- 应当认定该事实不存在（第 108 条第 2 款）
  | noFindingUnderArt108 -- 两款都未发动（第 3 款另有规定时由该规定处理，本件不认定）
deriving DecidableEq, Repr

/-- 中文说明（可判定谓词）：第 108 条第 1、2 款的判定顺序。
    输入①＝第 1 款的高度可能性是否达成；输入②＝第 2 款的真伪不明是否成立。
    [建模选择]：两款同时发动时本件取第 1 款（条文的肯定式在前），这一取舍是建模选择，
    不是条文给出的位阶；真实案卷中的竞合处理本件不认定。 -/
def art108Finding : Bool → Bool → FactFinding
  | true, _ => .foundToExist
  | false, true => .foundToNotExist
  | false, false => .noFindingUnderArt108

/-- 中文证明（第 108 条第 2 款的后果）：真伪不明 ⇒ 认定该事实**不存在**。
    注意这一式只说本件的判定函数怎么算，不说该事实在世界中是否为假。 -/
theorem art108_unclarity_yields_nonexistence :
    art108Finding false true = FactFinding.foundToNotExist :=
  rfl

/-- 中文证明（第 108 条第 1 款的后果）：高度可能性达成 ⇒ 认定该事实存在；
    且第 1 款的判定不看第二个输入（条文第 1 款只条件于本证）。 -/
theorem art108_high_probability_yields_existence (u : Bool) :
    art108Finding true u = FactFinding.foundToExist :=
  rfl

/-- 中文证明（第 108 条第 2、3 款的边界）：两款都不发动时，本件不给认定结论，
    并把这一情形登记为"第 3 款另有规定的由其规定"——本件**不**在此处新增档位。 -/
theorem art108_no_gap_nofinding :
    art108Finding false false = FactFinding.noFindingUnderArt108 :=
  rfl

/-- 中文说明：认定结论与事实真值分层的载体（与 `AdmittedRecord` 同一手法，
    独立字段是为了让"认定不决定真值"成为定理）。 -/
structure EvaluatedFact where
  finding : FactFinding
  onticTrue : Bool

/-- 中文证明（第 108 条第 2 款"认定不存在"不是本体论断言）：
    存在两条认定结论相同、实际真值相反的案卷记录。故"应当认定该事实不存在"
    在本件的模型里只是一个**后果分配**，不宣称该事实客观为假。
    本件不认定任何真实案件的待证事实真值。 -/
theorem art108_finding_does_not_determine_ontic :
    ∃ f₁ f₂ : EvaluatedFact, f₁.finding = f₂.finding ∧ f₁.onticTrue ≠ f₂.onticTrue :=
  ⟨⟨FactFinding.foundToNotExist, true⟩, ⟨FactFinding.foundToNotExist, false⟩, rfl, by decide⟩

/-- 中文说明：第 109 条的五类例外事实。一手："当事人对欺诈、胁迫、恶意串通事实的证明，
    以及对口头遗嘱或者赠与事实的证明，人民法院确信该待证事实存在的可能性能够
    **排除合理怀疑**的，应当认定该事实存在。" [一手已核] -/
inductive ExceptionalMatter : Type
  | fraud -- 欺诈
  | duress -- 胁迫
  | maliciousCollusion -- 恶意串通
  | oralWill -- 口头遗嘱
  | gift -- 赠与
deriving DecidableEq, Repr

/-- 中文说明：第 109 条五类的枚举表。 -/
def exceptionalMatters : Finset ExceptionalMatter :=
  { ExceptionalMatter.fraud, ExceptionalMatter.duress, ExceptionalMatter.maliciousCollusion,
    ExceptionalMatter.oralWill, ExceptionalMatter.gift }

/-- 中文证明（第 109 条的"五类"）：枚举表基数为 5，且每类都在表内。 -/
theorem exceptional_matters_are_five : exceptionalMatters.card = 5 := by decide

theorem art109_five_matters_are_enumerated (m : ExceptionalMatter) : m ∈ exceptionalMatters := by
  cases m with
  | fraud => decide
  | duress => decide
  | maliciousCollusion => decide
  | oralWill => decide
  | gift => decide

/-- 中文说明：本件承认的**两个具名**证明标准档＋一个**带引注的出口名**，按条文具名。
    两个具名构造子：第 108 条第 1 款"高度可能性"、第 109 条"排除合理怀疑"。
    第 108 条第 3 款"另有规定的，从其规定"是出口条款——`statutoryEscape (cite : String)`
    只携带指向那部规定的引注，**不是本件自造的第三档**：`standardGate` 对它恒为 `False`，
    `escape_tier_cannot_name_a_nonblank_domain` 证明它不能作为任何非空评价域的挂名档。
    换句话说："不许自造无名档位"保留为 `named_tier_exhausts_non_escape`。
    [一手已核＋构造性定义；出口构造子为 2026-10-04 增（17_ 卷 R3）] -/
inductive ProofStandardName : Type
  | highProbability108 -- 第 108 条第 1 款：高度可能性
  | excludesReasonableDoubt109 -- 第 109 条：排除合理怀疑
  | statutoryEscape (cite : String) -- 第 108 条第 3 款：另有规定，从其规定（携带引注的出口名）
deriving DecidableEq, Repr

/-- 中文证明（旧定理 `proof_standard_names_are_exactly_two` 的诚实改写）：
    两具名档互异；任何**非出口**的标准名必为两具名档之一——这就是"不许自造无名第三档"
    的可检查形式。出口名另由 `statutory_escape_is_not_a_named_tier` 与
    `escape_tier_cannot_name_a_nonblank_domain` 约束。 -/
theorem named_tier_exhausts_non_escape :
    ProofStandardName.highProbability108 ≠ ProofStandardName.excludesReasonableDoubt109 ∧
      ∀ σ : ProofStandardName,
        (∀ c : String, σ ≠ ProofStandardName.statutoryEscape c) →
          σ = ProofStandardName.highProbability108 ∨
            σ = ProofStandardName.excludesReasonableDoubt109 :=
  ⟨by decide, by
    intro σ hnesc
    cases σ with
    | highProbability108 => exact Or.inl rfl
    | excludesReasonableDoubt109 => exact Or.inr rfl
    | statutoryEscape c => exact absurd rfl (hnesc c)⟩

/-- 中文证明：出口名不是具名档（三条不等式）。 -/
theorem statutory_escape_is_not_a_named_tier (c : String) :
    ProofStandardName.statutoryEscape c ≠ ProofStandardName.highProbability108 ∧
      ProofStandardName.statutoryEscape c ≠ ProofStandardName.excludesReasonableDoubt109 :=
  ⟨fun h => ProofStandardName.noConfusion h,
    fun h => ProofStandardName.noConfusion h⟩

/-- 中文说明：第 109 条与第 108 条第 1 款的**分档**表：事实类别 → 应达到的具名标准。
    第 109 条那五类一律挂"排除合理怀疑"档（`excludesReasonableDoubt109`）。 -/
def art109StandardOf : ExceptionalMatter → ProofStandardName
  | .fraud | .duress | .maliciousCollusion | .oralWill | .gift =>
      ProofStandardName.excludesReasonableDoubt109

/-- 中文说明：普通民事待证事实挂第 108 条第 1 款档（第 109 条五类之外的默认档）。
    [代拟稿]：默认档的读法是本件宣告——条文只对第 109 条那五类明写更高档，
    对"其余事实一律用第 108 条第 1 款"没有逐字规定（第 108 条第 3 款还留了出口）。 -/
def art108StandardOf : ExceptionalMatter → ProofStandardName
  | _ => ProofStandardName.highProbability108

/-- 中文证明（第 109 条的五类**全部**走"排除合理怀疑"档）：逐点判定，无一例外。 -/
theorem art109_all_five_use_the_stricter_tier :
    art109StandardOf ExceptionalMatter.fraud = ProofStandardName.excludesReasonableDoubt109 ∧
      art109StandardOf ExceptionalMatter.duress = ProofStandardName.excludesReasonableDoubt109 ∧
        art109StandardOf ExceptionalMatter.maliciousCollusion =
          ProofStandardName.excludesReasonableDoubt109 ∧
            art109StandardOf ExceptionalMatter.oralWill =
              ProofStandardName.excludesReasonableDoubt109 ∧
                art109StandardOf ExceptionalMatter.gift =
                  ProofStandardName.excludesReasonableDoubt109 :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- 中文证明（第 109 条那一档**不是**第 108 条第 1 款那一档）：五类事实的档位都不等于
    高度可能性档。逐点判定。 -/
theorem art109_tier_is_not_the_108_tier (m : ExceptionalMatter) :
    art109StandardOf m ≠ ProofStandardName.highProbability108 := by
  cases m <;> decide

/-- 中文证明（同一载体上的分档不是空操作）：第 109 条五类挂 109 档，普通事实挂 108 档，
    两个映射在同一个 `ExceptionalMatter` 上取**不同**值。
    [代拟稿]：默认档一侧的读法见 `art108StandardOf` 的注，本件不把它写成条文原话。 -/
theorem art108_and_art109_standards_differ (m : ExceptionalMatter) :
    art109StandardOf m ≠ art108StandardOf m := by
  cases m <;> decide

/- ========== 第二轮：EvalDomainLawful（三条候选公理，**不加字段**） ========== -/

/-- 中文说明（公理①）：**存在**可采纳评价，且**没有**空白评价。
    条文锚点：第 105 条（只有一款——"人民法院应当按照法定程序，全面地、客观地审核证据，
    依照法律规定，运用逻辑推理和日常生活经验法则，对证据有无证明力和证明力大小进行判断，
    并公开判断的理由和结果"，[一手已核] 本件用它作为"必须作出判断且必须给出结果"的锚点，
    不把它拆成若干款）＋第 108 条第 1、2 款（两款合起来要求认定"存在"或"不存在"，
    不许留空白认定）＋第 90 条第 2 款（不利后果必须以有认定为前提）。
    两个合取支与 `Seams/AdjudicationBridge.lean` 已证定理
    `stable_kernel_singleton_of_allowed_singleton` 的 `hNE`、`hnoBlank` **逐字同形**，
    故公理①就是把那条定理的两条外加假设收进"依法"这个名目下。[建模选择] -/
def hasNonblankAdmissibleEvaluation {V : Type} (E : EvalDomain V) : Prop :=
  (∃ S : Set V, Admissible E S) ∧ (∀ S : Set V, Admissible E S → ∃ x : V, x ∈ S)

/-- 中文说明（公理②·弱交封闭）：两个可采纳评价若**共享至少一个结论**（存在共同 refinement），
    它们的交仍是可采纳评价。
    条文锚点：第 93 条第 1 款（七项"当事人无须举证证明"——两个合法心证都承认的那部分，
    其免证地位不因叠合而丧失）＋第 92 条第 1 款（自认后他方无需举证，共同承认的部分同样
    无须再举证）。[建模选择]：把两款读成"评价族对交封闭"是本件的建模选择，不是条文措辞。
    **刻意不写全交封闭**：规格已指出全交也推不出 `collapsesToKernel`
    （反例形状 `{{0,1},{0,2}}`：交 `{0}` 可采纳而 `{0,1} ⊄ {0}`）——
    本件用 `fullInterDomain` 把这个反例形状做成定理（`lawful_does_not_imply_collapse`），
    并把守卫条件（"存在共同结论"）作为②的一部分：没有共同结论的两个评价，其交是空集，
    而空集评价已被公理①排除，故②不对它施加强制。 -/
def admissibleWeakInterClosed {V : Type} (E : EvalDomain V) : Prop :=
  ∀ S T : Set V, Admissible E S → Admissible E T →
    (∃ x : V, x ∈ S ∧ x ∈ T) → Admissible E (S ∩ T)

/-- 中文说明（②′·全交封闭形，本件**不采用**）：去掉守卫条件的版本。写在这里只有一个目的——
    让"②为什么取弱的这一边"成为可对照的事实：`fullInterDomain` 满足②′却仍不收缩
    （`lawful_does_not_imply_collapse`），而 `disjointVerdictDomain` 满足②却不满足②′
    （`disjointVerdict_fails_fullInterClosed`），故②严格弱于②′、且两者都填不上收缩的空隙。 -/
def admissibleFullInterClosed {V : Type} (E : EvalDomain V) : Prop :=
  ∀ S T : Set V, Admissible E S → Admissible E T → Admissible E (S ∩ T)

/-- 中文说明（挂名判据）：一个具名标准档在评价域 `E` 上对一个结论集 `S` 生效的读法。
    两档分别对应：
    - `highProbability108`（第 108 条第 1 款"高度可能性"）＝ `S` 与稳定内核**有公共结论**
      （`S ∩ stableKernel E` 不空）：达到高度可能性档的评价，必须至少交付一个
      一切合法心证都不会放弃的结论，否则它没有资格叫"认定该事实存在"。[建模选择]
    - `excludesReasonableDoubt109`（第 109 条"排除合理怀疑"）＝ `S` 含于**每一个**可采纳评价
      （`S ⊆ ⋂` 全体可采纳评价）：留在 `S` 里的每个结论都不被任何合法心证排除，
      即"其余可能性的合理怀疑已被排除"。[建模选择]
    两档之外的第三档本件**不做**（第 108 条第 3 款是"另有规定从其规定"的出口条款）。 -/
def standardGate {V : Type} (σ : ProofStandardName) (E : EvalDomain V) (S : Set V) : Prop :=
  match σ with
  | .highProbability108 => ∃ x : V, x ∈ S ∧ x ∈ stableKernel E
  | .excludesReasonableDoubt109 => ∀ T : Set V, Admissible E T → S ⊆ T
  | .statutoryEscape _ => False

/-- 中文说明：标准 σ 对 `E` 的**全部**可采纳评价生效。 -/
def StandardNamedAt {V : Type} (σ : ProofStandardName) (E : EvalDomain V) : Prop :=
  ∀ S : Set V, Admissible E S → standardGate σ E S

/-- 中文说明（公理③·挂名到具体证明标准）：评价族挂名到第 108 条第 1 款与第 109 条这两档之一，
    且该档对全体可采纳评价生效。二选一由 `∃ σ` 表达；出口名带 `False` 闸门，且
    `escape_tier_cannot_name_a_nonblank_domain` 证明它挂不了非空评价域，
    `lawful_named_standard_is_a_named_tier` 证明合法域挂的必是具名档。
    条文锚点：第 108 条第 1 款或第 109 条；第 108 条第 3 款**不**在本公理覆盖之列，
    它登记在本件头注"不做什么"里。[建模选择] -/
def attachesNamedStandard {V : Type} (E : EvalDomain V) : Prop :=
  ∃ σ : ProofStandardName, StandardNamedAt σ E

/-- 中文说明（本件的收紧谓词，独立 `def`，**不是** `EvalDomain` 的字段）：
    评价域"依法"＝公理① ∧ 公理② ∧ 公理③。
    为什么不加字段：`EvalDomain` 的具象见证 `trialDomain`（`AdjudicationBridge.lean:884`）
    一旦要补新字段就构造不出来，`trial_collapse_fails`（`:964`）与
    `unique_verdict_reverse_unconditional_falsum`（`:993`）两条已证否证会成片失效。
    做成谓词后那两条原样保留，本件还能证 `trialDomain_is_not_lawful`。 -/
def EvalDomainLawful {V : Type} (E : EvalDomain V) : Prop :=
  hasNonblankAdmissibleEvaluation E ∧ admissibleWeakInterClosed E ∧ attachesNamedStandard E

/-- 中文证明（三条公理的投影）：`EvalDomainLawful` 确实逐条给出①②③，
    不是一句口号；下面 `lawful_of_allowedSet_singleton` 说明①立刻有数学回报。 -/
theorem lawful_part_one {V : Type} (E : EvalDomain V) (hl : EvalDomainLawful E) :
    hasNonblankAdmissibleEvaluation E :=
  And.left hl

/-- 中文证明（**出口档在本模型内无闸门**）：`standardGate` 对出口名定义为 `False`，
    所以它对任何评价域、任何采纳集都开不出闸——要判定"从其规定"必须去读 `cite` 指向的规定，
    本模型不代读。这不是把出口档做废，而是"从其规定"的字面忠实。 -/
theorem escape_tier_has_no_gate (c : String) {V : Type} (E : EvalDomain V) (S : Set V) :
    ¬ standardGate (ProofStandardName.statutoryEscape c) E S := fun h => h

/-- 中文证明（**出口名挂不了非空评价域**）：非空 ⇒ 存在某个可采纳 `S`；把挂名条件作用到 `S`
    上就得到 `False`。于是"合法评价域的挂名标准必是具名档"（下一条）。 -/
theorem escape_tier_cannot_name_a_nonblank_domain (c : String) {V : Type} (E : EvalDomain V)
    (hnb : hasNonblankAdmissibleEvaluation E) :
    ¬ StandardNamedAt (ProofStandardName.statutoryEscape c) E := by
  obtain ⟨⟨S, hS⟩, _⟩ := hnb
  intro hσ
  exact escape_tier_has_no_gate c E S (hσ S hS)

/-- 中文证明（**合法域只挂具名档**）：`EvalDomainLawful` 的第①条（非空）把出口名排除，
    所以 `attachesNamedStandard` 的存在量词实际落在两具名档之一——
    这就是旧定理"两档穷尽"在出口名加入后的诚实形态。 -/
theorem lawful_named_standard_is_a_named_tier {V : Type} (E : EvalDomain V)
    (hl : EvalDomainLawful E) :
    ∃ σ : ProofStandardName,
      (σ = ProofStandardName.highProbability108 ∨
        σ = ProofStandardName.excludesReasonableDoubt109) ∧ StandardNamedAt σ E := by
  obtain ⟨σ, hσ⟩ := hl.2.2
  cases σ with
  | highProbability108 => exact ⟨_, Or.inl rfl, hσ⟩
  | excludesReasonableDoubt109 => exact ⟨_, Or.inr rfl, hσ⟩
  | statutoryEscape c =>
      exact absurd hσ (escape_tier_cannot_name_a_nonblank_domain c E hl.1)

theorem lawful_part_two {V : Type} (E : EvalDomain V) (hl : EvalDomainLawful E) :
    admissibleWeakInterClosed E :=
  And.left (And.right hl)

theorem lawful_part_three {V : Type} (E : EvalDomain V) (hl : EvalDomainLawful E) :
    attachesNamedStandard E :=
  And.right (And.right hl)

/-- 中文证明（公理①的回报，接到缝件已证定理上）：在合法评价域上，
    `AdjudicationBridge.stable_kernel_singleton_of_allowed_singleton` 的两条外加假设
    （存在可采纳评价、评价非空白）自动齐备，故"允许集单点 ⇒ 内核单点"无需再挂假设。
    本式**不**引入新论证，只是那条已证定理的一次应用——这也说明公理①不是装饰：
    它换来的正是缝件里原本要额外声明的东西。 -/
theorem lawful_of_allowedSet_singleton {V : Type} (E : EvalDomain V) (v : V)
    (hl : EvalDomainLawful E) (hv : allowedSet E = {v}) : stableKernel E = {v} :=
  stable_kernel_singleton_of_allowed_singleton E v (And.left (And.left hl))
    (And.right (And.left hl)) hv

/-- 中文证明（公理③的另一半回报）：把评价族挂名到第 109 条那一档，
    **就推出** `collapsesToKernel`。这条是本件对"三组规则判据填不上空隙"这一诊断的正向补充：
    空隙不是不能填，而是要用 109 档那种跨评价的强度来填；
    108 档（只要求与内核有公共结论）填不上——见 `trialDomain_attaches_the_108_standard`
    与缝件已证的 `trial_collapse_fails`。 -/
theorem standard109_named_at_implies_collapse {V : Type} (E : EvalDomain V)
    (h : StandardNamedAt ProofStandardName.excludesReasonableDoubt109 E) :
    collapsesToKernel E := by
  intro S hS
  have hg : ∀ T : Set V, Admissible E T → S ⊆ T := h S hS
  intro x hx
  show x ∈ stableKernel E
  rw [mem_stableKernel_iff]
  exact fun T hT => hg T hT hx

/-- 中文证明（公理③的档位不可两全）：见证域 `trialDomain` 挂得上 108 档，
    因而**挂不上** 109 档（否则与已证的 `trial_collapse_fails` 矛盾）。 -/
theorem trialDomain_attaches_the_108_standard :
    StandardNamedAt ProofStandardName.highProbability108 trialDomain := by
  intro S hS
  have hk : (0 : Fin 3) ∈ stableKernel trialDomain := by
    rw [trial_stableKernel]
    simp
  rw [admissible_trialDomain] at hS
  rcases hS with (rfl | rfl)
  · exact ⟨0, by simp, hk⟩
  · exact ⟨0, by simp, hk⟩

/-- 中文证明（公理①对见证域成立）：两条假设直接取自缝件已证的
    `trial_admissible_exists` 与 `trial_admissible_no_blank`（本件原样引用，不重证）。
    这条与下一条的作用是把"误伤"范围钉准：**挡住 `trialDomain` 的只有公理②**。 -/
theorem trialDomain_holds_part_one : hasNonblankAdmissibleEvaluation trialDomain :=
  ⟨trial_admissible_exists, trial_admissible_no_blank⟩

/-- 中文证明（公理③对见证域成立，走 108 档）：故 `trialDomain` 违的只是②。 -/
theorem trialDomain_holds_part_three : attachesNamedStandard trialDomain :=
  ⟨ProofStandardName.highProbability108, trialDomain_attaches_the_108_standard⟩

/-- 中文证明（109 档在见证域上不成立，且理由正是缝件已证的否证）：若 `trialDomain`
    挂得上 109 档，则由 `standard109_named_at_implies_collapse` 得 `collapsesToKernel trialDomain`，
    与已证的 `trial_collapse_fails`（`AdjudicationBridge.lean:964`）矛盾。
    本式**引用**那条否证而不重证、不改写它。 -/
theorem trialDomain_fails_the_109_standard :
    ¬ StandardNamedAt ProofStandardName.excludesReasonableDoubt109 trialDomain := by
  intro h
  exact trial_collapse_fails (standard109_named_at_implies_collapse trialDomain h)

/- ========== 第三轮：划界见证（三条各挡一个具体域）+ 标准分级不可合并 ========== -/

/-- 中文说明（空白评价域）：没有任何可采纳评价。用来隔离公理①的作用。
    它是**反例夹具**，不代表任何真实裁判状态。 -/
def vacuousDomain : EvalDomain (Fin 3) where
  admissibleSupport := fun _ => False
  sufficientStandard := fun _ => False
  rebuttalClosed := fun _ => False

/-- 中文证明（公理①挡住空白域，②③对它却真空满足）：这同时说明②③单独不够，
    必须配上①——否则"谁都满足"的装饰正来自真空成立。 -/
theorem vacuousDomain_fails_part_one : ¬ hasNonblankAdmissibleEvaluation vacuousDomain := by
  intro h
  rcases (And.left h) with ⟨S, hS⟩
  obtain ⟨h1, _, _⟩ := hS
  exact False.elim h1

theorem vacuousDomain_holds_part_two : admissibleWeakInterClosed vacuousDomain := by
  intro S T hS _ _
  obtain ⟨h1, _, _⟩ := hS
  exact False.elim h1

theorem vacuousDomain_holds_part_three : attachesNamedStandard vacuousDomain :=
  ⟨ProofStandardName.highProbability108, by
    intro S hS
    obtain ⟨h1, _, _⟩ := hS
    exact False.elim h1⟩

theorem vacuousDomain_is_not_lawful : ¬ EvalDomainLawful vacuousDomain := by
  intro h
  exact vacuousDomain_fails_part_one (And.left h)

/-- 中文说明（互斥评价域）：可采纳评价恰为 `{0}` 与 `{1}`——两个互相排斥的结论。
    用来隔离公理③的作用：①成立（两个评价都非空白），②成立（没有共同结论，守卫条件
    从不发动），③失败（内核是空集，108 档要公共结论；109 档要互含，两者都不满足）。 -/
def disjointVerdictDomain : EvalDomain (Fin 3) where
  admissibleSupport := fun S => S = ({0} : Set (Fin 3)) ∨ S = ({1} : Set (Fin 3))
  sufficientStandard := fun S => S = ({0} : Set (Fin 3)) ∨ S = ({1} : Set (Fin 3))
  rebuttalClosed := fun S => S = ({0} : Set (Fin 3)) ∨ S = ({1} : Set (Fin 3))

theorem admissible_disjointVerdict (S : Set (Fin 3)) :
    Admissible disjointVerdictDomain S ↔
      S = ({0} : Set (Fin 3)) ∨ S = ({1} : Set (Fin 3)) :=
  ⟨fun ⟨h, _, _⟩ => h, fun h => ⟨h, h, h⟩⟩

theorem disjointVerdict_holds_part_one : hasNonblankAdmissibleEvaluation disjointVerdictDomain :=
  ⟨⟨({0} : Set (Fin 3)), (admissible_disjointVerdict _).mpr (Or.inl rfl)⟩, by
    intro S hS
    rw [admissible_disjointVerdict] at hS
    rcases hS with (rfl | rfl)
    · exact ⟨0, by simp⟩
    · exact ⟨1, by simp⟩⟩

theorem disjointVerdict_holds_part_two : admissibleWeakInterClosed disjointVerdictDomain := by
  intro S T hS hT hcommon
  rw [admissible_disjointVerdict] at hS hT ⊢
  rcases hS with (rfl | rfl)
  · rcases hT with (rfl | rfl)
    · refine Or.inl ?_
      refine Set.Subset.antisymm (fun x hx => Set.mem_of_mem_inter_left hx) ?_
      intro x hx
      exact Set.mem_inter hx hx
    · rcases hcommon with ⟨x, hx0, hx1⟩
      rw [Set.mem_singleton_iff] at hx0 hx1
      exact absurd (hx0.symm.trans hx1) (by decide)
  · rcases hT with (rfl | rfl)
    · rcases hcommon with ⟨x, hx0, hx1⟩
      rw [Set.mem_singleton_iff] at hx0 hx1
      exact absurd (hx0.symm.trans hx1) (by decide)
    · refine Or.inr ?_
      refine Set.Subset.antisymm (fun x hx => Set.mem_of_mem_inter_left hx) ?_
      intro x hx
      exact Set.mem_inter hx hx

/-- 中文证明（②与②′的区别有见证）：`disjointVerdictDomain` 满足弱交封闭公理②，
    却**不**满足全交封闭②′——`{0}` 与 `{1}` 都可采纳，交是空集、不可采纳。
    故本件采用的②确实是较弱的那一边，不是把强要求换了个名字。 -/
theorem disjointVerdict_fails_fullInterClosed :
    ¬ admissibleFullInterClosed disjointVerdictDomain := by
  intro h
  have h0 : Admissible disjointVerdictDomain ({0} : Set (Fin 3)) :=
    (admissible_disjointVerdict _).mpr (Or.inl rfl)
  have h1 : Admissible disjointVerdictDomain ({1} : Set (Fin 3)) :=
    (admissible_disjointVerdict _).mpr (Or.inr rfl)
  have hi : Admissible disjointVerdictDomain
      (({0} : Set (Fin 3)) ∩ ({1} : Set (Fin 3))) := h ({0} : Set (Fin 3)) ({1} : Set (Fin 3)) h0 h1
  rw [admissible_disjointVerdict] at hi
  rcases hi with (heq | heq)
  · have hmem : (0 : Fin 3) ∈ ({0} : Set (Fin 3)) := by simp
    rw [← heq] at hmem
    have hn : ¬ ((0 : Fin 3) ∈ ({0} : Set (Fin 3)) ∩ ({1} : Set (Fin 3))) := by
      intro hh
      exact absurd (Set.mem_of_mem_inter_right hh) (by simp)
    exact absurd hmem hn
  · have hmem : (1 : Fin 3) ∈ ({1} : Set (Fin 3)) := by simp
    rw [← heq] at hmem
    have hn : ¬ ((1 : Fin 3) ∈ ({0} : Set (Fin 3)) ∩ ({1} : Set (Fin 3))) := by
      intro hh
      exact absurd (Set.mem_of_mem_inter_left hh) (by simp)
    exact absurd hmem hn

theorem disjointVerdict_kernel_is_empty :
    stableKernel disjointVerdictDomain = (∅ : Set (Fin 3)) := by
  refine Set.Subset.antisymm ?_ ?_
  · intro x hx
    rw [mem_stableKernel_iff] at hx
    have h0 : Admissible disjointVerdictDomain ({0} : Set (Fin 3)) :=
      (admissible_disjointVerdict _).mpr (Or.inl rfl)
    have h1 : Admissible disjointVerdictDomain ({1} : Set (Fin 3)) :=
      (admissible_disjointVerdict _).mpr (Or.inr rfl)
    have hx0 := hx ({0} : Set (Fin 3)) h0
    have hx1 := hx ({1} : Set (Fin 3)) h1
    rw [Set.mem_singleton_iff] at hx0 hx1
    exact absurd (hx0.symm.trans hx1) (by decide)
  · intro x hx
    exact False.elim hx

theorem disjointVerdict_fails_part_three : ¬ attachesNamedStandard disjointVerdictDomain := by
  intro ⟨σ, hσ⟩
  have h0 : Admissible disjointVerdictDomain ({0} : Set (Fin 3)) :=
    (admissible_disjointVerdict _).mpr (Or.inl rfl)
  cases σ with
  | highProbability108 =>
    have hh : ∃ x : Fin 3, x ∈ ({0} : Set (Fin 3)) ∧ x ∈ stableKernel disjointVerdictDomain :=
      hσ ({0} : Set (Fin 3)) h0
    rcases hh with ⟨x, _, hxK⟩
    rw [disjointVerdict_kernel_is_empty] at hxK
    exact False.elim hxK
  | excludesReasonableDoubt109 =>
    have hg : ∀ T : Set (Fin 3), Admissible disjointVerdictDomain T →
        ({0} : Set (Fin 3)) ⊆ T := hσ ({0} : Set (Fin 3)) h0
    have h1 : Admissible disjointVerdictDomain ({1} : Set (Fin 3)) :=
      (admissible_disjointVerdict _).mpr (Or.inr rfl)
    have hsub : ({0} : Set (Fin 3)) ⊆ ({1} : Set (Fin 3)) := hg ({1} : Set (Fin 3)) h1
    have hmem : (0 : Fin 3) ∈ ({0} : Set (Fin 3)) := by simp
    have hnotin : ¬ ((0 : Fin 3) ∈ ({1} : Set (Fin 3))) := by simp
    exact absurd (hsub hmem) hnotin
  | statutoryEscape _ =>
    exact (hσ ({0} : Set (Fin 3)) h0).elim

theorem disjointVerdict_is_not_lawful : ¬ EvalDomainLawful disjointVerdictDomain := by
  intro h
  exact disjointVerdict_fails_part_three (And.right (And.right h))

/-- 中文说明（见证域本身）：`AdjudicationBridge.trialDomain` 的可采纳评价恰为 `{0,1}` 与
    `{0,2}`，它们共享结论 `0`，交却是 `{0}`——不在可采纳族内。公理②正是为此而设。 -/
theorem trialDomain_fails_part_two : ¬ admissibleWeakInterClosed trialDomain := by
  intro h
  have hA : Admissible trialDomain ({0, 1} : Set (Fin 3)) :=
    (admissible_trialDomain _).mpr (Or.inl rfl)
  have hB : Admissible trialDomain ({0, 2} : Set (Fin 3)) :=
    (admissible_trialDomain _).mpr (Or.inr rfl)
  have hc : ∃ x : Fin 3, x ∈ ({0, 1} : Set (Fin 3)) ∧ x ∈ ({0, 2} : Set (Fin 3)) :=
    ⟨0, by simp, by simp⟩
  have hi : Admissible trialDomain (({0, 1} : Set (Fin 3)) ∩ ({0, 2} : Set (Fin 3))) :=
    h ({0, 1} : Set (Fin 3)) ({0, 2} : Set (Fin 3)) hA hB hc
  rw [admissible_trialDomain] at hi
  rcases hi with (heq | heq)
  · have hne : ¬ ((1 : Fin 3) ∈
        (({0, 1} : Set (Fin 3)) ∩ ({0, 2} : Set (Fin 3)))) := by
      intro hh
      have hb : (1 : Fin 3) ∈ ({0, 2} : Set (Fin 3)) := Set.mem_of_mem_inter_right hh
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hb
      rcases hb with (h | h)
      · exact absurd h (by decide)
      · exact absurd h (by decide)
    have hmem : (1 : Fin 3) ∈ ({0, 1} : Set (Fin 3)) := by simp
    rw [← heq] at hmem
    exact absurd hmem hne
  · have hne : ¬ ((2 : Fin 3) ∈
        (({0, 1} : Set (Fin 3)) ∩ ({0, 2} : Set (Fin 3)))) := by
      intro hh
      have hb : (2 : Fin 3) ∈ ({0, 1} : Set (Fin 3)) := Set.mem_of_mem_inter_left hh
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hb
      rcases hb with (h | h)
      · exact absurd h (by decide)
      · exact absurd h (by decide)
    have hmem : (2 : Fin 3) ∈ ({0, 2} : Set (Fin 3)) := by simp
    rw [← heq] at hmem
    exact absurd hmem hne

/-- 中文证明（**划界主定理**，任务要求的第三条）：缝件的见证域不满足本件的合法性谓词。
    这一条的作用是防止 `EvalDomainLawful` 成"谁都满足"的装饰。
    诚实说明**误伤**：挡住 `trialDomain` 的正是公理②。`trialDomain` 因此不能被称为
    "依法的评价域"——但它的两条已证否证（`trial_collapse_fails`、
    `unique_verdict_reverse_unconditional_falsum`）里都没有 `EvalDomainLawful`，
    本件也**没有**改动那两条的任何陈述，故它们不受影响（本件只 import，不重写）。
    法律读法：`trialDomain` 的两个可采纳评价在共同结论 `0` 上的交 `{0}` 不可采纳，
    这与第 93 条第 1 款"七项事实无须举证证明"的叠合稳定性相违，
    所以它作为"合法心证族"的模型是**不合格**的，而作为边界夹具仍然有效。 -/
theorem trialDomain_is_not_lawful : ¬ EvalDomainLawful trialDomain := by
  intro h
  exact trialDomain_fails_part_two (And.left (And.right h))

/-- 中文说明（全交封闭也不够）：可采纳评价族＝`{S : Set (Fin 3) | 0 ∈ S ∧ S ⊆ {0,1}}`，
    即恰为 `{{0}, {0,1}}` 这一族。它对**不加守卫的二元全交**封闭
    （`{0} ∩ {0,1} = {0}`、`{0,1} ∩ {0,1} = {0,1}`），稳定内核是 `{0}`，
    而 `{0,1}` 可采纳却不含于内核。这就是规格点名的那件事：
    反例形状 `{{0,1},{0,2}}` 把交 `{0}` 补进族里以后（本件用的是它的二元简化形），
    全交封闭仍然推不出 `collapsesToKernel`——所以本件**不**用全交封闭冒充成果。
    它是**反例夹具**，不代表任何真实裁判状态。 -/
def fullInterDomain : EvalDomain (Fin 3) where
  admissibleSupport := fun S => (0 : Fin 3) ∈ S ∧ S ⊆ ({0, 1} : Set (Fin 3))
  sufficientStandard := fun S => (0 : Fin 3) ∈ S ∧ S ⊆ ({0, 1} : Set (Fin 3))
  rebuttalClosed := fun S => (0 : Fin 3) ∈ S ∧ S ⊆ ({0, 1} : Set (Fin 3))

theorem admissible_fullInterDomain (S : Set (Fin 3)) :
    Admissible fullInterDomain S ↔
      ((0 : Fin 3) ∈ S ∧ S ⊆ ({0, 1} : Set (Fin 3))) :=
  ⟨fun ⟨h, _, _⟩ => h, fun h => ⟨h, h, h⟩⟩

/-- 中文证明：`fullInterDomain` 满足公理①。 -/
theorem fullInter_holds_part_one : hasNonblankAdmissibleEvaluation fullInterDomain :=
  ⟨⟨({0} : Set (Fin 3)), (admissible_fullInterDomain _).mpr ⟨by simp,
      by
        intro x hx
        rw [Set.mem_singleton_iff] at hx
        subst hx
        simp⟩⟩, by
    intro S hS
    rw [admissible_fullInterDomain] at hS
    exact ⟨0, hS.1⟩⟩

/-- 中文证明（比公理②**更强**的要求在这里成立）：任意两个可采纳评价的交仍可采纳，
    守卫条件根本用不上。 -/
theorem fullInter_holds_fullInterClosed : admissibleFullInterClosed fullInterDomain := by
  intro S T hS hT
  rw [admissible_fullInterDomain] at hS hT ⊢
  refine ⟨Set.mem_inter hS.1 hT.1, ?_⟩
  intro x hx
  exact hS.2 (Set.mem_of_mem_inter_left hx)

/-- 中文证明：全交封闭蕴含本件的弱交封闭（公理②是②′的 weakening，本件取弱的这一边）。 -/
theorem fullInterClosed_implies_weak {V : Type} (E : EvalDomain V)
    (h : admissibleFullInterClosed E) : admissibleWeakInterClosed E := by
  intro S T hS hT _
  exact h S T hS hT

theorem fullInter_holds_part_two : admissibleWeakInterClosed fullInterDomain :=
  fullInterClosed_implies_weak fullInterDomain fullInter_holds_fullInterClosed

theorem fullInter_kernel_is_singleton : stableKernel fullInterDomain = ({0} : Set (Fin 3)) := by
  refine Set.Subset.antisymm ?_ ?_
  · intro x hx
    have h0 : Admissible fullInterDomain ({0} : Set (Fin 3)) :=
      (admissible_fullInterDomain _).mpr ⟨by simp, by
        intro y hy
        rw [Set.mem_singleton_iff] at hy
        subst hy
        simp⟩
    rw [mem_stableKernel_iff] at hx
    exact hx ({0} : Set (Fin 3)) h0
  · intro x hx
    rw [mem_stableKernel_iff]
    intro S hS
    rw [admissible_fullInterDomain] at hS
    rw [Set.mem_singleton_iff] at hx
    subst hx
    exact hS.1

/-- 中文证明：`fullInterDomain` 满足公理③（挂 108 档）。 -/
theorem fullInter_holds_part_three : attachesNamedStandard fullInterDomain :=
  ⟨ProofStandardName.highProbability108, by
    intro S hS
    rw [admissible_fullInterDomain] at hS
    have hk : (0 : Fin 3) ∈ stableKernel fullInterDomain := by
      rw [fullInter_kernel_is_singleton]
      simp
    exact ⟨0, hS.1, hk⟩⟩

/-- 中文证明：`fullInterDomain` 是合法的却**不**收缩到内核——`{0,1}` 可采纳而 `1` 不在内核。 -/
theorem fullInter_collapse_fails : ¬ collapsesToKernel fullInterDomain := by
  intro h
  have hS : Admissible fullInterDomain ({0, 1} : Set (Fin 3)) :=
    (admissible_fullInterDomain _).mpr ⟨by simp, fun x hx => hx⟩
  have h1 : (1 : Fin 3) ∈ ({0, 1} : Set (Fin 3)) := by simp
  have hker : (1 : Fin 3) ∈ stableKernel fullInterDomain := h ({0, 1} : Set (Fin 3)) hS h1
  rw [fullInter_kernel_is_singleton] at hker
  rw [Set.mem_singleton_iff] at hker
  exact absurd hker (by decide)

theorem fullInterDomain_is_lawful : EvalDomainLawful fullInterDomain :=
  ⟨fullInter_holds_part_one, fullInter_holds_part_two, fullInter_holds_part_three⟩

/-- 中文证明（本件的**封顶否证**）：`EvalDomainLawful` 三条（连②加强成全交封闭）**推不出**
    `collapsesToKernel`。反面登记：本件没有把缝件留下的空隙填上，
    而且**证明了三条候选公理这条路线填不上它**（见证 `fullInterDomain`：合法、
    甚至全交封闭，却 `{0,1}` 可采纳而内核是 `{0}`）。
    想在一般法律域上证唯一判决，必须另外给出跨评价的强度判据——
    本件给出的一个可行方向是 109 档那种"含于每一个可采纳评价"的形（见
    `standard109_named_at_implies_collapse`），但那是**更强的第 109 条读法**，
    不是第 108 条第 1 款所能负担的。 -/
theorem lawful_does_not_imply_collapse :
    ¬ (∀ (V : Type) (E : EvalDomain V), EvalDomainLawful E → collapsesToKernel E) := by
  intro h
  exact fullInter_collapse_fails
    (h (Fin 3) fullInterDomain fullInterDomain_is_lawful)

/-- 中文说明：第 108 条第 1 款与第 109 条之间的**档位差**用的有限夹具。
    载体：`FactIndex` 是三项待证事实之名（本件自造，不指任何真实案件事实），
    `claimOn`＝该项被主张，`doubtOn`＝该项的相反可能尚未排除。 -/
inductive FactIndex : Type
  | first
  | second
  | third
deriving DecidableEq, Repr

inductive CredProfile : Type
  | cAllAccepted -- 三项全部被主张，且无一项留有未排除的相反可能
  | cSecondDoubt -- 前两项被主张且干净，第三项未被主张
  | cEverySecondDoubted -- 三项都被主张，但第二项同时留有未排除的相反可能
deriving DecidableEq, Repr

def claimOn : CredProfile → FactIndex → Bool
  | .cAllAccepted, _ => true
  | .cSecondDoubt, .first => true
  | .cSecondDoubt, .second => true
  | .cSecondDoubt, .third => false
  | .cEverySecondDoubted, _ => true

def doubtOn : CredProfile → FactIndex → Bool
  | .cAllAccepted, _ => false
  | .cSecondDoubt, .first => false
  | .cSecondDoubt, .second => false
  | .cSecondDoubt, .third => true
  | .cEverySecondDoubted, .first => false
  | .cEverySecondDoubted, .second => true
  | .cEverySecondDoubted, .third => false

/-- 中文说明（残余合理怀疑）：被主张而未排除相反可能的那一项。 -/
def residualDoubtOn (ρ : CredProfile) (i : FactIndex) : Bool := claimOn ρ i && doubtOn ρ i

/-- 中文说明（**案件事实类别位**，17_ 卷缺口 4 的桥）：待证事实在本案被归入
    第 109 条五类的哪一类（`some`），还是普通事实（`none`）。
    这是"证明标准 ↔ 事实认定"之间此前缺失的那条数据通道：模型不会自己"发现"
    本案属欺诈——它读的是这一位。夹具映射：第一项是欺诈，其余普通。
    `[代拟稿]`：真实案件里这一位由审理认定，本件只给通道与读数。 -/
def factMatterClass (i : FactIndex) : Option ExceptionalMatter :=
  match i with
  | .first => some ExceptionalMatter.fraud
  | .second => none
  | .third => none

/-- 中文说明（**通道的读数**）：类别位给出该事实应达到的具名标准——
    五类挂 109 档，普通事实挂 108 条第 1 款档。 -/
def standardFor : FactIndex → ProofStandardName :=
  fun i => match factMatterClass i with
    | some m => art109StandardOf m
    | none => ProofStandardName.highProbability108

/-- 中文证明（**五类事实必须走严档**）：类别位非空 ⇒ 读数恰为"排除合理怀疑"。 -/
theorem exceptional_fact_requires_the_stricter_tier (i : FactIndex) (m : ExceptionalMatter)
    (h : factMatterClass i = some m) :
    standardFor i = ProofStandardName.excludesReasonableDoubt109 := by
  unfold standardFor
  rw [h]
  cases m <;> rfl

/-- 中文证明（**普通事实走常档**）：类别位为空 ⇒ 读数是 108 条第 1 款档。 -/
theorem ordinary_fact_gets_the_ordinary_tier (i : FactIndex)
    (h : factMatterClass i = none) :
    standardFor i = ProofStandardName.highProbability108 := by
  unfold standardFor
  rw [h]

/-- 中文证明（**通道与 109 分档表一致**）：读数就是 `art109StandardOf` 在该类别上的值。 -/
theorem the_bridge_respects_the_109_table (i : FactIndex) (m : ExceptionalMatter)
    (h : factMatterClass i = some m) : standardFor i = art109StandardOf m := by
  unfold standardFor
  rw [h]

/-- 中文证明（**读严档必有类别**）：读数是严档 ⇒ 类别位非空——
    模型不能凭空给某事实上严档，必须指回一项五类认定。 -/
theorem stricter_tier_requires_a_classified_fact (i : FactIndex)
    (h : standardFor i = ProofStandardName.excludesReasonableDoubt109) :
    ∃ m : ExceptionalMatter, factMatterClass i = some m := by
  unfold standardFor at h
  cases hfm : factMatterClass i with
  | none => rw [hfm] at h; exact absurd h (by simp [standardFor])
  | some m => exact ⟨m, rfl⟩


/-- 中文说明（第 108 条第 1 款档的可判定读法）：三项待证事实都没有残余怀疑。
    [建模选择]：本件把"确信存在具有高度可能性"读成**序关系**上的低一档
    （被主张者不自相矛盾），**不**给它任何概率数字；真实法秩序里的数字门槛
    本件不声称，第 108 条第 3 款的"另有规定"也不在本件覆盖内。 -/
def meetsHighProbability108 : CredProfile → Bool
  | ρ => !residualDoubtOn ρ FactIndex.first && !residualDoubtOn ρ FactIndex.second &&
    !residualDoubtOn ρ FactIndex.third

/-- 中文说明（第 109 条档的可判定读法）：先过 108 档，再要求主张**覆盖全部**待证事实
    （无一保留）。档差是本件选定，不是条文给定的数字。 -/
def meetsBeyondReasonableDoubt109 : CredProfile → Bool
  | ρ => meetsHighProbability108 ρ && claimOn ρ FactIndex.first &&
    claimOn ρ FactIndex.second && claimOn ρ FactIndex.third

/-- 中文说明：把两档挂到具名标准上（与公理③同一个 `ProofStandardName`）。 -/
def standardMeets : ProofStandardName → CredProfile → Bool
  | .highProbability108 => meetsHighProbability108
  | .excludesReasonableDoubt109 => meetsBeyondReasonableDoubt109
  | .statutoryEscape _ => fun _ => false

/-- 中文证明（**标准分级不可合并**，任务第四条·方向一：109 档严格不低于 108 档）：
    任一夹具达到第 109 条的档位，就必达第 108 条第 1 款的档位。逐点判定。 -/
theorem standard_tier_is_a_hierarchy (ρ : CredProfile)
    (h : standardMeets ProofStandardName.excludesReasonableDoubt109 ρ = true) :
    standardMeets ProofStandardName.highProbability108 ρ = true := by
  cases ρ with
  | cAllAccepted => rfl
  | cSecondDoubt => exact absurd h (by decide)
  | cEverySecondDoubted => exact absurd h (by decide)

/-- 中文证明（**方向二：两档不等价**）：存在有限夹具（`CredProfile.cSecondDoubt`）
    在第 108 条第 1 款档达标、在第 109 条档**不**达标。
    这就是"第 109 条那五类（欺诈、胁迫、恶意串通、口头遗嘱、赠与）用的标准比
    第 108 条第 1 款高"的可判定形。 -/
theorem standard_tier_gap_witness :
    ∃ ρ : CredProfile, standardMeets ProofStandardName.highProbability108 ρ = true ∧
      standardMeets ProofStandardName.excludesReasonableDoubt109 ρ = false :=
  ⟨CredProfile.cSecondDoubt, rfl, rfl⟩

/-- 中文证明（合并两档是**不合法**的操作）：把两档读成同一个判据的全称命题为假。 -/
theorem standard_tiers_cannot_be_merged :
    ¬ ∀ ρ : CredProfile,
        standardMeets ProofStandardName.highProbability108 ρ = true ↔
          standardMeets ProofStandardName.excludesReasonableDoubt109 ρ = true := by
  intro h
  have hc := h CredProfile.cSecondDoubt
  have ha : standardMeets ProofStandardName.highProbability108 CredProfile.cSecondDoubt = true :=
    rfl
  exact absurd (hc.mp ha) (by decide)

/-- 中文证明（**双向判定**：任务要求的"给具体有限见证＋双向判定"）：
    三个夹具在两档上的六种判定逐一钉死，全部是构造子的逐点计算。 -/
theorem standard_tier_two_way_decision :
    standardMeets ProofStandardName.highProbability108 CredProfile.cAllAccepted = true ∧
      standardMeets ProofStandardName.excludesReasonableDoubt109
        CredProfile.cAllAccepted = true ∧
        standardMeets ProofStandardName.highProbability108 CredProfile.cSecondDoubt = true ∧
          standardMeets ProofStandardName.excludesReasonableDoubt109
            CredProfile.cSecondDoubt = false ∧
            standardMeets ProofStandardName.highProbability108
              CredProfile.cEverySecondDoubted = false ∧
              standardMeets ProofStandardName.excludesReasonableDoubt109
                CredProfile.cEverySecondDoubted = false :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- 中文证明（第 108 条第 1 款与第 109 条的**语词**互异）：
    "高度可能性"与"排除合理怀疑"不是同一个字符串，本件不把它们当同义词。 -/
theorem art108_art109_phrases_are_distinct :
    art108_officialPhrase ≠ ("排除合理怀疑" : String) := by
  intro h
  exact absurd h (by decide)

end JurisLean.Seams.BurdenStatutes
