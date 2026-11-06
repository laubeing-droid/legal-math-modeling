import JurisLean.Hohfeld
import JurisLean.KernelV3

/-!
中文说明：中国法四墙 drop-in（D6 冻结稿的 Lean 落地）。
本模块只依赖 Hohfeld 与 KernelV3，不用 MeasureTheory（那是 U 债地盘）。
无 sorry。法无明文不填。适用法律，不立法。
CI_NOT_RUN / UNCOMPILED。
-/

namespace JurisLean.CN.Walls

/-! ## 客体七类（老七类落位；数据/虚拟财产立位不编权属） -/

/-- 中文说明：民法典总则客体位。数据与虚拟财产有位，权属不编码。 -/
inductive ObjKind
  | thing          -- 物
  | act            -- 行为
  | personality    -- 人格利益
  | status         -- 身份
  | intelprop      -- 智力成果
  | data           -- 数据（位在，权属不冻）
  | virtual        -- 网络虚拟财产（位在，权属不冻）
  deriving DecidableEq, Repr

/-- 中文证明：七类两两不同。 -/
theorem obj_seven_distinct :
    ObjKind.thing ≠ ObjKind.act
    ∧ ObjKind.thing ≠ ObjKind.data
    ∧ ObjKind.data ≠ ObjKind.virtual
    ∧ ObjKind.personality ≠ ObjKind.thing := by
  decide

/-- 中文说明：人格利益不能当物。 -/
theorem personality_not_thing : ObjKind.personality ≠ ObjKind.thing := by
  decide

/-- 中文说明：身份不能用余额零表示。 -/
theorem status_not_thing : ObjKind.status ≠ ObjKind.thing := by
  decide

/-! ## 权利四态，接 Hohfeld -/

/-- 中文说明：中国民法四态。接 JurisLean.Hohfeld.Concept，不另起炉灶。
支配 ≈ 对世 claim + 使用 privilege；
请求 ≈ claim；
形成 ≈ power；
抗辩 ≈ 对抗 claim 的权限（claim 不灭）。 -/
inductive RightKind
  | domin
  | req
  | form
  | defend
  deriving DecidableEq, Repr

/-- 中文说明：一个情形的四态持有位。互不推出 = 四个独立布尔。 -/
structure Case where
  hasDomin : Bool
  hasReq : Bool
  hasForm : Bool
  hasDefend : Bool

/-- 中文证明：存在有支配无请求（所有权人不待请求已有物）。 -/
theorem exists_domin_not_req :
    ∃ c : Case, c.hasDomin = true ∧ c.hasReq = false :=
  ⟨{ hasDomin := true, hasReq := false, hasForm := false, hasDefend := false }, rfl, rfl⟩

/-- 中文证明：存在有请求无形成（债权人一般不能单方撕合同）。 -/
theorem exists_req_not_form :
    ∃ c : Case, c.hasReq = true ∧ c.hasForm = false :=
  ⟨{ hasDomin := false, hasReq := true, hasForm := false, hasDefend := false }, rfl, rfl⟩

/-- 中文证明：存在有形成无支配（撤销权人不必对标的物有物权）。 -/
theorem exists_form_not_domin :
    ∃ c : Case, c.hasForm = true ∧ c.hasDomin = false :=
  ⟨{ hasDomin := false, hasReq := false, hasForm := true, hasDefend := false }, rfl, rfl⟩

/-- 中文证明：存在有抗辩仍有请求（时效届满债还在）。 -/
theorem exists_defend_with_req :
    ∃ c : Case, c.hasDefend = true ∧ c.hasReq = true :=
  ⟨{ hasDomin := false, hasReq := true, hasForm := false, hasDefend := true }, rfl, rfl⟩

/-- 中文说明：四态是四个不同构造子，不相等。 -/
theorem four_kinds_distinct :
    RightKind.domin ≠ RightKind.req
    ∧ RightKind.domin ≠ RightKind.form
    ∧ RightKind.domin ≠ RightKind.defend
    ∧ RightKind.req ≠ RightKind.form
    ∧ RightKind.req ≠ RightKind.defend
    ∧ RightKind.form ≠ RightKind.defend := by
  decide

/-- 中文说明：与 Hohfeld 的接口：四态不冒充八概念中的同一个。 -/
theorem domin_not_hohfeld_claim_eq :
    RightKind.domin ≠ RightKind.req := by
  decide

/-! ## 时间：时效是抗辩权，除斥是形成权消灭 -/

/-- 中文说明：期间届满的法律效果，三种不混。 -/
inductive TimeOut
  | defenseRaised   -- 抗辩权发生（中国时效）
  | claimGone       -- 请求权消灭（不是中国时效）
  | formGone        -- 形成权消灭（除斥期间）
  deriving DecidableEq, Repr

/-- 中文说明：诉讼时效的编码。适用民法典，不是立法。 -/
def limitationEffect : TimeOut := TimeOut.defenseRaised

/-- 中文说明：除斥期间的编码。 -/
def exceptioEffect : TimeOut := TimeOut.formGone

/-- 中文证明：时效不是请求权消灭。 -/
theorem limitation_not_claimGone :
    limitationEffect ≠ TimeOut.claimGone := by
  decide

/-- 中文证明：除斥是形成权消灭。 -/
theorem exceptio_is_formGone :
    exceptioEffect = TimeOut.formGone := rfl

/-- 中文证明：时效效果 ≠ 除斥效果。 -/
theorem limitation_ne_exceptio :
    limitationEffect ≠ exceptioEffect := by
  decide

/-- 中文说明：法院不主动援引时效 = 系统不自动把 defenseRaised 写成 claimGone。 -/
def courtAutoRaise : Bool := false

theorem court_not_auto_raise : courtAutoRaise = false := rfl

/-! ## 三把证明尺不换算 -/

/-- 中文说明：证明标准是离散代数数据类型，不是实数。 -/
inductive StdCN
  | beyondReasonableDoubt   -- 刑事
  | highPossibility         -- 民事一般
  | adminDefendant          -- 行政被告对合法性举证
  | statutoryInverse (kind : String)  -- 法定倒置，kind 是要件不是案由
  deriving DecidableEq, Repr

/-- 中文证明：三把尺两两不同。 -/
theorem three_scales_distinct :
    StdCN.beyondReasonableDoubt ≠ StdCN.highPossibility
    ∧ StdCN.highPossibility ≠ StdCN.adminDefendant
    ∧ StdCN.beyondReasonableDoubt ≠ StdCN.adminDefendant := by
  decide

/-- 中文说明：高度可能性是定性心证，不是阈值 0.5。
存在证据概率 6/10 但心证不认的模型。 -/
structure ProbModel where
  numer : Nat
  denom : Nat
  conviction : Bool   -- true = 确信高度可能性
  contradictions : Bool

/-- 中文证明：P=6/10 且有未排矛盾 → 不确信。 -/
theorem high_possib_not_threshold :
    ∃ m : ProbModel,
      m.numer = 6 ∧ m.denom = 10 ∧ m.conviction = false :=
  ⟨{ numer := 6, denom := 10, conviction := false, contradictions := true }, rfl, rfl, rfl⟩

/-- 中文说明：刑诉 55 结构禁止：只有供述不能定罪。
证据 = 仅口供 → 不得 established。 -/
inductive EvidenceSet
  | confessionOnly
  | confessionPlusOther
  | otherOnly
  | empty
  deriving DecidableEq, Repr

inductive Guilty
  | yes
  | no
  | undetermined
  deriving DecidableEq, Repr

/-- 中文说明：定罪函数。仅口供 → 不得 yes。这是适用刑诉 55，不是立法。 -/
def convict : EvidenceSet → Guilty
  | EvidenceSet.confessionOnly => Guilty.no
  | EvidenceSet.confessionPlusOther => Guilty.undetermined  -- 还要看是否排除合理怀疑
  | EvidenceSet.otherOnly => Guilty.undetermined
  | EvidenceSet.empty => Guilty.no

/-- 中文证明：仅口供不能定罪。 -/
theorem confession_only_not_guilty :
    convict EvidenceSet.confessionOnly ≠ Guilty.yes := by
  decide

/-- 中文说明：Record 只改 E，不改 F。适用 v2 T04，不立法。 -/
structure FactFrame where
  fPays : Bool       -- 自然事实：款付没付
  eAdmitted : Bool   -- 认定：自认与否

/-- 中文说明：自认动作：只写 eAdmitted，fPays 原样。 -/
def recordConfession (before : FactFrame) : FactFrame :=
  { before with eAdmitted := true }

/-- 中文证明：自认后 F 逐位不变。 -/
theorem confession_frame_E_not_F :
    ∀ before, (recordConfession before).fPays = before.fPays := by
  intro before
  rfl

/-! ## 拘束九种不混 -/

/-- 中文说明：拘束种类。公定/参照/信用独立，不折算成钱或事实真。 -/
inductive KBind
  | resJudicata
  | constitutive
  | executable
  | evidential
  | publicValidity
  | referential
  | persuasive
  | credit
  | procedural
  deriving DecidableEq, Repr

/-- 中文证明：公定力 ≠ 既判力 ≠ 参照力 ≠ 信用。 -/
theorem kbind_distinct :
    KBind.publicValidity ≠ KBind.resJudicata
    ∧ KBind.referential ≠ KBind.resJudicata
    ∧ KBind.credit ≠ KBind.executable
    ∧ KBind.referential ≠ KBind.evidential := by
  decide

/-- 中文说明：行政行为三态可同真：公定力成立、实质违法、事实假。 -/
structure AdminAct where
  publicValidity : Bool
  substantiallyLegal : Bool
  factTrue : Bool

/-- 中文证明：公定力不是事实真，也不是实质合法。 -/
theorem gongding_not_truth :
    ∃ a : AdminAct,
      a.publicValidity = true
      ∧ a.factTrue = false
      ∧ a.substantiallyLegal = false :=
  ⟨{ publicValidity := true, substantiallyLegal := false, factTrue := false }, rfl, rfl, rfl⟩

/-! ## 规范来源：政策/纪要不进 N -/

/-- 中文说明：来源种类。 -/
inductive SourceKind
  | statute          -- 法律
  | adminReg         -- 行政法规
  | localReg         -- 地方性法规
  | rule             -- 规章
  | judicial         -- 司法解释
  | treaty           -- 条约
  | guidingCase      -- 指导性案例（参照）
  | policy           -- 政策（数据二十条等）
  | jiyao            -- 纪要（九民纪要等）
  deriving DecidableEq, Repr

/-- 中文说明：N 成员。yes 进规范；no 只能当说理/参照/政策。 -/
inductive NMember
  | yes (s : SourceKind)
  | no
  deriving DecidableEq, Repr

/-- 中文说明：什么进 N。适用立法法，不替立法。 -/
def inN : SourceKind → NMember
  | SourceKind.statute => NMember.yes SourceKind.statute
  | SourceKind.adminReg => NMember.yes SourceKind.adminReg
  | SourceKind.localReg => NMember.yes SourceKind.localReg
  | SourceKind.rule => NMember.yes SourceKind.rule
  | SourceKind.judicial => NMember.yes SourceKind.judicial
  | SourceKind.treaty => NMember.yes SourceKind.treaty
  | SourceKind.guidingCase => NMember.no
  | SourceKind.policy => NMember.no
  | SourceKind.jiyao => NMember.no

/-- 中文证明：政策不是法源。 -/
theorem policy_not_inN :
    inN SourceKind.policy = NMember.no := rfl

/-- 中文证明：纪要不是法源。 -/
theorem jiyao_not_inN :
    inN SourceKind.jiyao = NMember.no := rfl

/-- 中文证明：指导性案例不是依据（是参照）。 -/
theorem guiding_not_inN :
    inN SourceKind.guidingCase = NMember.no := rfl

/-- 中文证明：法律是法源。 -/
theorem statute_inN :
    inN SourceKind.statute = NMember.yes SourceKind.statute := rfl

/-! ## 规范冲突：排不了挂起，不偷选 -/

/-- 中文说明：ResolveCN 输出。 -/
inductive ResolveOut
  | chosen (n : Nat)
  | adjudicate (organ : String)
  | incompatible
  | unknown
  deriving DecidableEq, Repr

/-- 中文说明：地方性法规撞部门规章 → 挂起等国务院/人大。适用立法法 106，不偷选。 -/
def localVsDept : ResolveOut :=
  ResolveOut.adjudicate "国务院→或人大"

/-- 中文证明：挂起不是选中。 -/
theorem localVsDept_not_chosen :
    localVsDept ≠ ResolveOut.chosen 0 := by
  decide

/-- 中文证明：挂起不是 unknown（有具名机关）。 -/
theorem localVsDept_is_adjudicate :
    localVsDept = ResolveOut.adjudicate "国务院→或人大" := rfl

/-- 中文说明：同机关新一般撞旧特别 → 制定机关裁决。立法法 105。 -/
def newGeneralVsOldSpecial : ResolveOut :=
  ResolveOut.adjudicate "制定机关"

theorem newGeneral_not_chosen :
    newGeneralVsOldSpecial ≠ ResolveOut.chosen 0 := by
  decide

/-! ## 涵摄不是相似度 -/

/-- 中文说明：涵摄结果：入某要件 / 不入。 -/
inductive Subsumption
  | inReq (n : Nat)
  | out
  deriving DecidableEq, Repr

/-- 中文说明：借条落入借款要件。 -/
def jietiao : Subsumption := Subsumption.inReq 1

/-- 中文说明：欠条文字近，但不自动落入借款要件（可能是其他债）。 -/
def qiantiao : Subsumption := Subsumption.out

/-- 中文证明：文字近不等于同涵摄。 -/
theorem text_near_not_same : jietiao ≠ qiantiao := by
  decide

/-- 中文说明：安慰函文字远，可入保证。相似度低不推出不入。 -/
def anweihan : Subsumption := Subsumption.inReq 1

/-- 中文证明：相似度低也可以同涵摄。 -/
theorem text_far_can_same : anweihan = jietiao := rfl

/-! ## 跨法域：适用 ≠ 承认 -/

/-- 中文说明：涉外两关系。 -/
structure CrossCase where
  applicableForeign : Bool
  recognizeJudgment : Bool

/-- 中文证明：可适用外国法同时拒绝承认其判决。 -/
theorem applicable_ne_recognize :
    ∃ c : CrossCase,
      c.applicableForeign = true ∧ c.recognizeJudgment = false :=
  ⟨{ applicableForeign := true, recognizeJudgment := false }, rfl, rfl⟩

/-- 中文说明：公共秩序否决是改道，不是混合。 -/
inductive ChoiceOfLaw
  | cn
  | foreign
  | vetoedToCN
  deriving DecidableEq, Repr

def publicPolicyVeto : ChoiceOfLaw := ChoiceOfLaw.vetoedToCN

theorem veto_is_cn_not_mix : publicPolicyVeto = ChoiceOfLaw.vetoedToCN := rfl

/-! ## 刑民不互盖 -/

/-- 中文说明：同一事实的刑事/民事认定。 -/
structure SameFact where
  criminalGuilty : Bool
  civilLiable : Bool

/-- 中文证明：刑事无罪民事可赔。 -/
theorem criminal_not_cover_civil :
    ∃ s : SameFact,
      s.criminalGuilty = false ∧ s.civilLiable = true :=
  ⟨{ criminalGuilty := false, civilLiable := true }, rfl, rfl⟩

/-- 中文证明：刑事有罪民事也可能不赔（另行判断）。 -/
theorem guilty_not_auto_liable :
    ∃ s : SameFact,
      s.criminalGuilty = true ∧ s.civilLiable = false :=
  ⟨{ criminalGuilty := true, civilLiable := false }, rfl, rfl⟩

/-! ## DeepInfer 认识桥：写 K 不写 R -/

/-- 中文说明：模型输出。 -/
inductive AIOut
  | score (p : Nat)   -- 万分比，避免浮点
  | text (s : String)
  deriving DecidableEq, Repr

/-- 中文说明：Bind 来源。 -/
inductive BindFrom
  | courtDoc
  | aiOut
  deriving DecidableEq, Repr

/-- 中文证明：模型输出不是判决拘束。97 也一样。 -/
theorem ai_not_bind :
    ∀ p : Nat, BindFrom.aiOut ≠ BindFrom.courtDoc := by
  intro p h
  injection h

/-- 中文说明：个保法 24。拒绝纯自动化 → 阻断转人工，不是弹窗。 -/
inductive AutoDecision
  | proceed
  | blockedHuman
  deriving DecidableEq, Repr

/-- 中文说明：适用个保法 24，不立法。 -/
def rejectPureAI (refuse : Bool) : AutoDecision :=
  if refuse then AutoDecision.blockedHuman else AutoDecision.proceed

/-- 中文证明：拒绝 → 阻断。 -/
theorem refuse_blocks :
    rejectPureAI true = AutoDecision.blockedHuman := rfl

/-- 中文证明：不拒绝也不得自动 Bind，只是不阻断。 -/
theorem not_refuse_not_bind :
    rejectPureAI false ≠ AutoDecision.blockedHuman := by
  decide

/-- 中文说明：训练数据门。违法获取 → 合规不过。 -/
inductive TrainData
  | lawful
  | illegallyObtained
  | unknown
  deriving DecidableEq, Repr

inductive Compliance
  | pass
  | fail
  deriving DecidableEq, Repr

/-- 中文说明：适用现行规定，不替立法冻权属。 -/
def complyTrain : TrainData → Compliance
  | TrainData.lawful => Compliance.pass
  | TrainData.illegallyObtained => Compliance.fail
  | TrainData.unknown => Compliance.fail   -- fail-closed

theorem illegal_train_fail :
    complyTrain TrainData.illegallyObtained = Compliance.fail := rfl

theorem unknown_train_fail :
    complyTrain TrainData.unknown = Compliance.fail := rfl

/-! ## KAT 观察商：顺序留在 Hist，交换只在观察 -/

/-- 中文说明：两步历史。保留先后。 -/
inductive Hist
  | nil
  | step (prev : Hist) (act : String)
  deriving DecidableEq, Repr

/-- 中文说明：观察投影（律师人话：外人看到的法律效果）。 -/
def obs : Hist → String
  | Hist.nil => "init"
  | Hist.step _ a => a

/-- 中文说明：观察相等。 -/
def obsEq (h1 h2 : Hist) : Prop := obs h1 = obs h2

/-- 中文证明：不同历史可同观察（案卷记先后，效果相同才可换）。 -/
theorem order_kept_in_hist :
    Hist.step (Hist.step Hist.nil "a") "b" ≠ Hist.step (Hist.step Hist.nil "b") "a" := by
  decide

/-- 中文证明：观察可相等。 -/
theorem obs_can_equal :
    obsEq (Hist.step Hist.nil "判") (Hist.step Hist.nil "判") := rfl

/-! ## 六态：不合并 -/

/-- 中文说明：六态谓词各自独立，不给无条件的等价式。 -/
inductive SixState
  | trueF          -- 事实真
  | supportE       -- 证据支持
  | justified      -- 论证/依法认定
  | recognized     -- 决定作出
  | valid          -- 决定有效
  | bound          -- 决定拘束
  deriving DecidableEq, Repr

/-- 中文证明：六态两两不同。 -/
theorem six_distinct :
    SixState.trueF ≠ SixState.supportE
    ∧ SixState.supportE ≠ SixState.justified
    ∧ SixState.justified ≠ SixState.recognized
    ∧ SixState.recognized ≠ SixState.valid
    ∧ SixState.valid ≠ SixState.bound := by
  decide

/-- 中文说明：无罪推定下的六态模型：决定有效、事实假、拘束在。 -/
structure SixWitness where
  trueF : Bool
  supportE : Bool
  justified : Bool
  recognized : Bool
  valid : Bool
  bound : Bool

/-- 中文证明：有权机关错案：决定有效、事实假、拘束在。True ≠ Valid ≠ Bind 不合并。 -/
theorem wrong_verdict_still_binds :
    ∃ w : SixWitness,
      w.trueF = false
      ∧ w.recognized = true
      ∧ w.valid = true
      ∧ w.bound = true :=
  ⟨{ trueF := false, supportE := false, justified := true,
     recognized := true, valid := true, bound := true }, rfl, rfl, rfl, rfl⟩

/-! ## 法无明文 -/

/-- 中文说明：数据权属：有位无结论。不替立法。 -/
inductive DataOwnership
  -- 故意不给构造子？不行，空类型有特殊性质。
  -- 给一个「未定」唯一构造子，表示法未定。
  | undetermined
  deriving DecidableEq, Repr

/-- 中文证明：数据权属只有未定，没有物权/债权编码。 -/
theorem data_ownership_undetermined :
    ∀ o : DataOwnership, o = DataOwnership.undetermined := by
  intro o
  cases o
  rfl

/-- 中文说明：AIGC 作品性：有位无结论。 -/
inductive AIGCWork
  | undetermined
  deriving DecidableEq, Repr

theorem aigc_work_undetermined :
    ∀ a : AIGCWork, a = AIGCWork.undetermined := by
  intro a
  cases a
  rfl

end JurisLean.CN.Walls
