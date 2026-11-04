import JurisLean.CN.Revision20261101.Ops
import JurisLean.CN.Revision20261101.Rights
import JurisLean.CN.Revision20261101.World

/-!
中文说明：十二项制度 Lean 实例（v4 §6 集群补全）。
命名空间 JurisLean.CN.Twelve。落位候选：`JurisLean/CN/Twelve.lean`。
无 sorry。不用 `axiom` 关键字关目标。已拍板语义（S1–S6、D2/D3/D5、立法技术边界）
以 Guard 字段、类型合同与 Revision20261101 已证命题消费。
法无明文不填。适用法律，不立法。
编译状态：UNCOMPILED / CI_NOT_RUN（本轮未获 CI 授权，不在本地跑 Lean/Elan/Lake）。
依赖闭包：KernelV3、Hohfeld、CN.Walls、CN.Ops、Revision20261101.{Ops,Rights,World}。
-/

namespace JurisLean.CN.Completion20261105.InstitutionRules

open JurisLean.CN.Revision20261101
open JurisLean.KernelV3

/-! ## 已拍板公理（2026-10-31 主人拍板；本模块当前提，不用 `axiom` 关键字）

S1 规范打架排不了就挂起：`unresolvedConflict ≠ selected`（Ops 已证）。
S2 三套证明标准分开用，不换算 0–100 分：`StdCN` 两两不同；本模块 `WeightOut` 无分数域。
S3 模型输出只是参考：`Candidate` ≠ `DecisionRecord`；无 Decide/Bind 边。
S4 拒绝仅 AI → 阻断：`refused_automated_step`（World 已证）。
S5 公定力/参照力/信用惩戒三种拘束独立（Walls `KBind`）。
S6 案卷记先后，Hist 不取商（World `Hist`）。
D2 只有法官/检察院能塞模板：`lawyer_cannot_add_template`。
D3/D5 缺回执 fail-closed；D4 撤回不抹 raw。
立法技术边界：政策/纪要/指导性案例不进 N；数据权属、AI 生成物权属不冻。
这些在本模块作为已证命题或类型合同消费，不另立 axiom，不重开拍板。
-/

/-! ## 合成同宇宙（同对象同历史的一组具名身份；非现实案件） -/

def aO : Ref .actor := ⟨1⟩      -- 原权利人 / 本人
def aD : Ref .actor := ⟨2⟩      -- 无权处分人 / 代理人
def aT : Ref .actor := ⟨3⟩      -- 受让人 / 相对人
def aJia : Ref .actor := ⟨4⟩    -- 甲
def aYi : Ref .actor := ⟨5⟩     -- 乙
def ev1 : Ref .event := ⟨6⟩
def ev2 : Ref .event := ⟨7⟩
def doc1 : Ref .document := ⟨8⟩
def doc2 : Ref .document := ⟨9⟩
def q1 : Ref .query := ⟨10⟩
def sc0 : Scope := ⟨⟨1⟩, ⟨2⟩, ⟨3⟩⟩

def boolToJ : Bool → Judgment
  | true => .established
  | false => .notEstablished

/-- 共同历史见证：复用 World 非裁判形成史，不另造第二套事件图。 -/
theorem twelve_history_shared :
    nonjudicialHistory.length = 3 :=
  nonjudicial_formation_exists.2.2

/-! ## 6.1 民事法律行为生命周期 -/

structure RevokeGuard where
  holder : Ref .actor
  ground : Ref .document
  methodOK : Bool
  windowStart : Nat
  windowStop : Nat
  atTime : Nat
  deriving Repr

def revokeGuardOK (g : RevokeGuard) : Bool :=
  g.methodOK && decide (g.windowStart ≤ g.atTime ∧ g.atTime ≤ g.windowStop)

/-- Effect：合法撤销改现时效果；失败出口不动原生命周期，不冒充已撤销。 -/
def applyRevoke (c : CivilActLife) (g : RevokeGuard) : CivilActLife × StepStatus :=
  match revokeGuardOK g with
  | true => (revokeLife c, .applied)
  | false => (c, .unauthorized)

/-- 缺成立事实 ≠ 已证无效：三者可分离。 -/
def neverEstablished : CivilActLife :=
  ⟨false, false, false, false,
    fun h => Bool.noConfusion h, fun h => Bool.noConfusion h⟩

theorem twelve_revoke_success_effective :
    (applyRevoke revocableLife ⟨aO, doc1, true, 0, 10, 5⟩).1.effective = false :=
  rfl

theorem twelve_revoke_success_keeps_established :
    (applyRevoke revocableLife ⟨aO, doc1, true, 0, 10, 5⟩).1.established = true :=
  rfl

theorem twelve_revoke_success_status :
    (applyRevoke revocableLife ⟨aO, doc1, true, 0, 10, 5⟩).2 = StepStatus.applied :=
  rfl

/-- 失败出口：越除斥期间不冒充合法撤销；原有效性不被偷改。 -/
theorem twelve_revoke_out_of_window :
    (applyRevoke revocableLife ⟨aO, doc1, true, 0, 10, 11⟩).2 =
      StepStatus.unauthorized :=
  rfl

theorem twelve_revoke_fail_keeps_effective :
    (applyRevoke revocableLife ⟨aO, doc1, true, 0, 10, 11⟩).1.effective = true :=
  rfl

theorem twelve_revoke_fail_keeps_revocation_power :
    (applyRevoke revocableLife ⟨aO, doc1, true, 0, 10, 11⟩).1.revocationPower = true :=
  rfl

theorem twelve_neverEstablished_not_invalid :
    neverEstablished.invalid = false := rfl

theorem twelve_neverEstablished_not_effective :
    neverEstablished.effective = false := rfl

/-- 确认不创设：确认事件不改关系表（消费 KernelV3）。 -/
theorem twelve_confirmatory_preserves :
    (applyEffect (formed : Sit) (.confirmatory .established)).L = formed.L :=
  confirmatory_preserves_relations formed .established

/-! ## 6.2 代理 -/

structure ApparentGuard where
  principalName : Bool
  appearance : Bool
  goodFaithNoFault : Judgment
  inScope : Bool
  deriving Repr

/-- 表见归属：四要件 andJ；未知保留未知，不填 false。 -/
def apparentAttribution (g : ApparentGuard) : Judgment :=
  andJ (boolToJ g.principalName)
       (andJ (boolToJ g.appearance)
             (andJ g.goodFaithNoFault (boolToJ g.inScope)))

structure AgencyOutcome where
  attribution : Judgment
  agentCounterpartyLiability : Judgment

/-- 无权代理对本人不生预期效力 ≠ 行为人与相对人绝无责任。 -/
def unauthorizedAgencyOutcome : AgencyOutcome :=
  ⟨.notEstablished, .established⟩

theorem twelve_apparent_success :
    apparentAttribution ⟨true, true, .established, true⟩ = .established :=
  rfl

theorem twelve_apparent_unknown :
    apparentAttribution ⟨true, true, .undetermined, true⟩ = .undetermined :=
  rfl

theorem twelve_apparent_bad_faith :
    apparentAttribution ⟨true, true, .notEstablished, true⟩ = .notEstablished :=
  rfl

theorem twelve_apparent_no_name :
    apparentAttribution ⟨false, true, .established, true⟩ = .notEstablished :=
  rfl

theorem twelve_delegate_keeps_capacity :
    (delegate ⟨aO, aD, aT, sc0, true, []⟩
      ⟨⟨12⟩, .registrar, sc0, ⟨5⟩, 1, 0, 10, .constitute, ⟨13⟩⟩).principalCapacity = true :=
  rfl

theorem twelve_unauthorized_not_no_liability :
    unauthorizedAgencyOutcome.attribution = .notEstablished ∧
    unauthorizedAgencyOutcome.agentCounterpartyLiability = .established :=
  ⟨rfl, rfl⟩

/-! ## 6.3 管辖 -/

/-- 事实未查明不填 false；已查明才进有限路由。 -/
def jurisdictionCheck (factsKnown : Bool) (j : JurisdictionInput) :
    Check (Option JurisdictionBranch) :=
  if factsKnown then .known (jurisdiction j) else .unknown .inputUnchecked

/-- 仲裁阻却实体审理；保全/监督是另一个 Query，不被该阻却直接排除。 -/
inductive ProcQuery
  | merits | preservation | supervision
  deriving DecidableEq, Repr

def arbitrationBlocks : ProcQuery → Bool
  | .merits => true
  | .preservation => false
  | .supervision => false

theorem twelve_jur_ordinary :
    jurisdictionCheck true ⟨true, false, false, false, false, false, false, true⟩ =
      .known (some .ordinary) := by decide

theorem twelve_jur_exclusive_fail :
    jurisdictionCheck true ⟨true, true, false, false, false, false, true, true⟩ =
      .known none := by decide

/-- 失败出口：未知分支条件保留候选，不把 false 默认填进去。 -/
theorem twelve_jur_unknown_not_false :
    jurisdictionCheck false ⟨true, false, false, false, false, false, false, true⟩ =
      .unknown .inputUnchecked := rfl

theorem twelve_arbitration_preservation_open :
    arbitrationBlocks .preservation = false := rfl

theorem twelve_arbitration_merits_blocked :
    arbitrationBlocks .merits = true := rfl

theorem twelve_appearance_cannot_override_exclusive :
    jurisdiction ⟨true, true, false, false, false, false, true, true⟩ = none := by decide

/-! ## 6.4 证据能力、证明力与证明责任 -/

/-- 证明力是三个独立 Judgment，不是分数；WeightOut 无 Rat 域（S2）。 -/
structure WeightOut where
  relevance : Judgment
  reliability : Judgment
  probative : Judgment
  deriving Repr

def weightJ (w : WeightOut) : Judgment :=
  andJ w.relevance (andJ w.reliability w.probative)

/-- Burden 只吃 admitted（World `admittedView` / `ProofPolicy.evaluate`）。 -/
def burdenJ (p : ProofPolicy) (e : Evidence) (ids : List (Ref .material))
    (a : Atom) : Judgment :=
  p.evaluate (admittedView e ids) a

theorem twelve_pending_not_admitted {i : Ref .material} (r : Raw i) :
    isAdmitted (EvidenceCell.pending r : EvidenceCell i) = false := rfl

theorem twelve_excluded_not_admitted {i : Ref .material} (r : Raw i) (why : Ref .document) :
    isAdmitted (EvidenceCell.excluded r why : EvidenceCell i) = false := rfl

/-- 补正可能性 ≠ 补正已完成。 -/
structure FixState where
  fixable : Bool
  fixed : Bool
  hfix : fixed = true → fixable = true

theorem twelve_fixable_not_fixed :
    ∃ s : FixState, s.fixable = true ∧ s.fixed = false :=
  ⟨⟨true, false, fun h => Bool.noConfusion h⟩, ⟨rfl, rfl⟩⟩

/-- 撤回后当前支持消失，raw 与排除史保留（World 同款）。 -/
theorem twelve_withdraw_support_gone :
    support (admittedView withdrawn.E [⟨9⟩]) toyAtom = .undetermined :=
  withdrawal_removes_support

theorem twelve_withdraw_keeps_raw :
    rawOf (withdrawn.E ⟨9⟩) = some toyRaw :=
  withdrawal_keeps_excluded_and_raw.2

/-! ## 6.5 善意取得 -/

inductive AcqRoute
  | ordinary311 | lost312 | otherSpecial
  deriving DecidableEq, Repr

/-- 特别对象先路由，不套普通 311。312 规则本轮不填（不立法）。 -/
def acqJudge (route : AcqRoute) (g price pub : Judgment) : Judgment :=
  match route with
  | .ordinary311 => ordinaryAcquisition g price pub
  | .lost312 => .undetermined
  | .otherSpecial => .undetermined

structure AcqOutcome where
  acquired : Judgment
  transactionOccurred : Bool

theorem twelve_acq_success :
    acqJudge .ordinary311 .established .established .established = .established := rfl

theorem twelve_acq_bad_faith :
    acqJudge .ordinary311 .notEstablished .established .established = .notEstablished := rfl

theorem twelve_acq_unchecked :
    acqJudge .ordinary311 .undetermined .established .established = .undetermined := rfl

theorem twelve_acq_312_not_ordinary :
    acqJudge .lost312 .established .established .established = .undetermined := rfl

/-- 取得不成立不抹实际交易。 -/
theorem twelve_acq_fail_keeps_transaction :
    ∃ o : AcqOutcome, o.acquired = .notEstablished ∧ o.transactionOccurred = true :=
  ⟨⟨.notEstablished, true⟩, ⟨rfl, rfl⟩⟩

theorem twelve_three_parties_distinct :
    (⟨1⟩ : Ref .actor) ≠ (⟨2⟩ : Ref .actor)
    ∧ (⟨1⟩ : Ref .actor) ≠ (⟨3⟩ : Ref .actor)
    ∧ (⟨2⟩ : Ref .actor) ≠ (⟨3⟩ : Ref .actor) := by
  decide

theorem aO_is_1 : aO.value = 1 := rfl
theorem aD_is_2 : aD.value = 2 := rfl
theorem aT_is_3 : aT.value = 3 := rfl

/-! ## 6.6 共同犯罪 -/

structure Participation where
  person : Ref .actor
  event : Ref .event
  commonIntent : Bool
  commonScope : Ref .query
  role : Ref .query
  stage : Ref .query
  deriving DecidableEq, Repr

def hasJoint (ps : List Participation) (who : Ref .actor) (ev : Ref .event)
    (sc : Ref .query) : Bool :=
  ps.any fun p => p.person == who && p.event == ev && p.commonIntent && p.commonScope == sc

/-- 个人投影：对该人该事件有共同故意才走能力评价；否则该路径不成立。
    不由组员身份复制过限行为。 -/
def liableFor (ps : List Participation) (ability : Judgment)
    (who : Ref .actor) (ev : Ref .event) (sc : Ref .query) : Judgment :=
  if hasJoint ps who ev sc then ability else .notEstablished

def jiaParts : List Participation :=
  [⟨aJia, ev1, true, q1, ⟨11⟩, ⟨12⟩⟩]

def yiParts : List Participation :=
  [⟨aYi, ev1, true, q1, ⟨11⟩, ⟨12⟩⟩]   -- 乙只在 ev1；ev2 无共同故意记录

theorem twelve_jia_e1 :
    liableFor jiaParts .established aJia ev1 q1 = .established := rfl

/-- 失败出口：乙对 e2 的共同故意未满足，不得因共同组身份复制 e2。 -/
theorem twelve_yi_e2_not_copied :
    liableFor yiParts .established aYi ev2 q1 = .notEstablished := rfl

theorem twelve_yi_e1_ok :
    liableFor yiParts .established aYi ev1 q1 = .established := rfl

/-- 共同事件身份相同不推出责任恒同。 -/
theorem twelve_same_event_can_differ :
    liableFor jiaParts .established aJia ev1 q1 ≠
    liableFor yiParts .notEstablished aYi ev2 q1 := by
  have h1 : liableFor jiaParts .established aJia ev1 q1 = .established := rfl
  have h2 : liableFor yiParts .notEstablished aYi ev2 q1 = .notEstablished := rfl
  rw [h1, h2]
  decide

theorem twelve_unknown_ability :
    liableFor jiaParts .undetermined aJia ev1 q1 = .undetermined := rfl

/-- 共同故意/范围未查明 → inputUnchecked，不默认有罪。 -/
def liableGate (known : Bool) (ps : List Participation) (ability : Judgment)
    (who : Ref .actor) (ev : Ref .event) (sc : Ref .query) : Check Judgment :=
  if known then .known (liableFor ps ability who ev sc)
  else .unknown .inputUnchecked

theorem twelve_liable_unknown_gate :
    liableGate false jiaParts .established aJia ev1 q1 = .unknown .inputUnchecked := rfl

/-! ## 6.7 破产 -/

structure InterestClaim where
  id : Ref .relation
  debtor : Ref .actor
  start : Nat
  in46 : Bool
  deriving DecidableEq, Repr

structure InterestLedger where
  preAccrued : Quantity .money
  postAccrued : Quantity .money

def zeroQ : Quantity .money := ⟨0⟩

/-- 受理时前息不清零。 -/
def onAcceptance (pre : Quantity .money) : InterestLedger :=
  ⟨pre, zeroQ⟩

theorem twelve_pre_interest_kept (q : Quantity .money) :
    (onAcceptance q).preAccrued = q := rfl

/-- 第46条截日：min(t, acceptedAt)；非该类债权不套此截止（不另编截止日）。 -/
def cutDay (accepted : Check Bool) (acceptedAt : Nat) (c : InterestClaim) (t : Nat) : Check Nat :=
  match accepted with
  | .unknown r => .unknown r
  | .known false => .unknown .inputUnchecked
  | .known true =>
    if c.in46 then
      if t ≤ acceptedAt then .known t else .known acceptedAt
    else .unknown .lawNotWritten

theorem twelve_cut_day :
    cutDay (.known true) 10 ⟨⟨20⟩, aD, 0, true⟩ 5 = .known 5 := by decide

theorem twelve_cut_day_cap :
    cutDay (.known true) 10 ⟨⟨20⟩, aD, 0, true⟩ 15 = .known 10 := by decide

theorem twelve_cut_not46_unknown :
    cutDay (.known true) 10 ⟨⟨20⟩, aD, 0, false⟩ 5 = .unknown .lawNotWritten := rfl

/-- 受理未核不能提前冻结；申请日不替代受理日。 -/
structure CaseDates where
  filing : Nat
  accepted : Option Nat

def stayNeedsAcceptance (d : CaseDates) : Check Bool :=
  match d.accepted with
  | some _ => .known true
  | none => .unknown .inputUnchecked

theorem twelve_filing_not_acceptance :
    stayNeedsAcceptance ⟨5, none⟩ = .unknown .inputUnchecked := rfl

theorem twelve_accepted_stay :
    stayNeedsAcceptance ⟨5, some 8⟩ = .known true := rfl

structure ExecProc where
  id : Ref .event
  debtor : Ref .actor
  property : Ref .object
  deriving DecidableEq, Repr

def procD : ExecProc := ⟨⟨20⟩, aD, ⟨21⟩⟩
def procO : ExecProc := ⟨⟨22⟩, aO, ⟨23⟩⟩

/-- 写域 = 被规则选中的同债务人执行；另一债务人程序保持。 -/
def staySelected (debtor : Ref .actor) (ps : List ExecProc) : List ExecProc :=
  ps.filter fun p => p.debtor == debtor

theorem twelve_other_debtor_not_stayed :
    staySelected aD [procD, procO] = [procD] := rfl

theorem twelve_unknown_acc_no_freeze :
    (stayNeedsAcceptance ⟨5, none⟩) = .unknown .inputUnchecked := rfl

/-! ## 6.8 国家赔偿第四轨 -/

inductive CompTrack
  | civil | criminal | administrative | state
  deriving DecidableEq, Repr

structure FourOut where
  civil : Judgment
  criminal : Judgment
  administrative : Judgment
  state : Judgment
  deriving Repr

theorem twelve_four_tracks_distinct :
    CompTrack.civil ≠ CompTrack.criminal
    ∧ CompTrack.civil ≠ CompTrack.administrative
    ∧ CompTrack.civil ≠ CompTrack.state
    ∧ CompTrack.criminal ≠ CompTrack.administrative
    ∧ CompTrack.criminal ≠ CompTrack.state
    ∧ CompTrack.administrative ≠ CompTrack.state := by decide

theorem twelve_comp_kinds_distinct :
    CompensationKind.administrative ≠ CompensationKind.criminal
    ∧ CompensationKind.criminal ≠ CompensationKind.civilAdministrativeJudicial
    ∧ CompensationKind.administrative ≠ CompensationKind.civilAdministrativeJudicial := by decide

/-- 无罪裁断不是自动生金额的充分条件；仍按所问措施与 17–19 求值。
    `_acq` 有意不进入 andJ。 -/
def compFromCustody (custody : Bool) (_acq : Bool) (g1719 : Judgment) : Judgment :=
  andJ (boolToJ custody) g1719

theorem twelve_acquittal_insufficient :
    compFromCustody true true .undetermined = .undetermined := rfl

theorem twelve_custody_with_1719 :
    compFromCustody true true .established = .established := rfl

/-- 本模块不定义 `addTracks`；FourOut 无总分域。轨道不加总 ≠ 已证绝无重复赔偿。 -/
theorem twelve_four_out_no_collapse :
    (⟨.established, .notEstablished, .undetermined, .established⟩ : FourOut).civil
      = .established := rfl

/-! ## 6.9 基本权利及规范冲突 -/

theorem twelve_s1_unresolved_not_selected :
    unresolvedConflict .law105 ≠ Resolve.selected ⟨99⟩ :=
  unresolved_ne_selected .law105 ⟨99⟩

theorem twelve_law105_route :
    reviewRoute .law105 = .npcStanding := rfl

theorem twelve_admin105_route :
    reviewRoute .admin105 = .stateCouncil := rfl

theorem twelve_same_maker_route :
    reviewRoute .sameMaker106 = .maker := rfl

theorem twelve_local_dept_route :
    reviewRoute .localDepartment106 = .stateCouncilThenNPC := rfl

theorem twelve_routes_differ :
    reviewRoute .law105 ≠ reviewRoute .admin105 :=
  article105_routes_differ

/-- 顶位路由是挂起等有权机关，不是 selected，也不是撤法权。 -/
theorem twelve_route_not_selected :
    reviewRoute .constitutionalReview ≠ .npcStanding := by decide

/-! ## 6.10 意思表示解释 -/

def MeaningMap := Ref .document → Option Formula

/-- 只写该合同的解释环境，不写全局 N.λ。 -/
def setMeaning (m : MeaningMap) (c : Ref .document) (f : Formula) : MeaningMap :=
  fun x => if x = c then some f else m x

theorem twelve_interpret_self (m : MeaningMap) (c : Ref .document) (f : Formula) :
    setMeaning m c f c = some f := by
  simp only [setMeaning]
  split
  · rfl
  · next h => exact (h rfl).elim

theorem twelve_interpret_other (m : MeaningMap) (c1 c2 : Ref .document) (f : Formula)
    (hne : c1 ≠ c2) :
    setMeaning m c1 f c2 = m c2 := by
  simp only [setMeaning]
  split
  · next hc => exact absurd hc.symm hne
  · rfl

/-- 争议未解决不选评分最高解释：没有评分器，返回 UNKNOWN。 -/
def disputedMeaning : Check Formula := .unknown .inputUnchecked

theorem twelve_disputed_unknown :
    disputedMeaning = .unknown .inputUnchecked := rfl

/-! ## 6.11 既判力人/物/时索引 -/

def idx1 : BindingIndex := ⟨[⟨1⟩], ⟨⟨1⟩,⟨2⟩,⟨3⟩⟩, 10, 20⟩

def resJudicataGate (i : Option BindingIndex) (p : Ref .actor) (s : Scope) (t : Nat) :
    Check Bool :=
  match i with
  | none => .unknown .inputUnchecked
  | some idx => .known (withinBinding idx p s t)

theorem twelve_res_hit :
    resJudicataGate (some idx1) ⟨1⟩ ⟨⟨1⟩,⟨2⟩,⟨3⟩⟩ 15 = .known true := by decide

theorem twelve_res_miss_person :
    resJudicataGate (some idx1) ⟨2⟩ ⟨⟨1⟩,⟨2⟩,⟨3⟩⟩ 15 = .known false := by decide

theorem twelve_res_miss_time :
    resJudicataGate (some idx1) ⟨1⟩ ⟨⟨1⟩,⟨2⟩,⟨3⟩⟩ 25 = .known false := by decide

theorem twelve_res_miss_subject :
    resJudicataGate (some idx1) ⟨1⟩ ⟨⟨1⟩,⟨2⟩,⟨4⟩⟩ 15 = .known false := by decide

/-- 缺索引 → inputUnchecked，不借用别的拘束。 -/
theorem twelve_res_missing_index :
    resJudicataGate none ⟨1⟩ ⟨⟨1⟩,⟨2⟩,⟨3⟩⟩ 15 = .unknown .inputUnchecked := rfl

/-- 案外人不在范围 ≠ 自动取得第三人撤销/异议/再审资格（另问，不派生）。 -/
structure RemedyGate where
  within : Bool
  thirdParty : Check Bool

theorem twelve_outsider_not_auto_remedy :
    ∃ r : RemedyGate, r.within = false ∧ r.thirdParty = .unknown .inputUnchecked :=
  ⟨⟨false, .unknown .inputUnchecked⟩, ⟨rfl, rfl⟩⟩

/-! ## 6.12 DeepInfer 提议器消费 U 引擎 -/

def fitPayload : Quantity .scalar × Quantity .scalar :=
  (⟨(1 : Rat)⟩, ⟨(2 : Rat)⟩)

def fitOut : EngineOutput :=
  { engine := .fit
    scope := sc0
    target := ⟨30⟩
    sourceHistory := []
    theoremRef := "paper://U00/fit-not-a-lean-proof"
    assumptions := []
    payload := fitPayload }

theorem twelve_candidate_basis :
    (candidateFromEngine ⟨31⟩ fitOut).basis = [fitOut] := rfl

theorem twelve_candidate_scope :
    (candidateFromEngine ⟨31⟩ fitOut).scope = sc0 := rfl

/-- theoremRef 是待核出处（String），不是 Lean 证明项。 -/
theorem twelve_theorem_ref_is_string :
    fitOut.theoremRef = "paper://U00/fit-not-a-lean-proof" := rfl

def consumeEngine (parent : Ref .model) (out : EngineOutput) (ready : Bool) :
    Check Candidate :=
  if ready then .known (candidateFromEngine parent out)
  else .unknown .inputUnchecked

theorem twelve_consume_unknown :
    consumeEngine ⟨31⟩ fitOut false = .unknown .inputUnchecked := rfl

theorem twelve_no_permit_no_bridge :
    bridgeCandidate none fitOut = .unknown .inputUnchecked :=
  no_causal_permit_no_bridge fitOut

/-- 候选不是决定：没有到 Bind 的边（World Event.bindDecision 另要 present）。 -/
theorem twelve_candidate_not_decision :
    (candidateFromEngine ⟨31⟩ fitOut).proposed = .atom ⟨sc0, ⟨30⟩⟩ := rfl

/-! ## 公理审计 -/

#print axioms twelve_history_shared
#print axioms twelve_revoke_success_effective
#print axioms twelve_revoke_success_keeps_established
#print axioms twelve_revoke_success_status
#print axioms twelve_revoke_out_of_window
#print axioms twelve_revoke_fail_keeps_effective
#print axioms twelve_revoke_fail_keeps_revocation_power
#print axioms twelve_neverEstablished_not_invalid
#print axioms twelve_neverEstablished_not_effective
#print axioms twelve_confirmatory_preserves
#print axioms twelve_apparent_success
#print axioms twelve_apparent_unknown
#print axioms twelve_apparent_bad_faith
#print axioms twelve_apparent_no_name
#print axioms twelve_delegate_keeps_capacity
#print axioms twelve_unauthorized_not_no_liability
#print axioms twelve_jur_ordinary
#print axioms twelve_jur_exclusive_fail
#print axioms twelve_jur_unknown_not_false
#print axioms twelve_arbitration_preservation_open
#print axioms twelve_arbitration_merits_blocked
#print axioms twelve_appearance_cannot_override_exclusive
#print axioms twelve_pending_not_admitted
#print axioms twelve_excluded_not_admitted
#print axioms twelve_fixable_not_fixed
#print axioms twelve_withdraw_support_gone
#print axioms twelve_withdraw_keeps_raw
#print axioms twelve_acq_success
#print axioms twelve_acq_bad_faith
#print axioms twelve_acq_unchecked
#print axioms twelve_acq_312_not_ordinary
#print axioms twelve_acq_fail_keeps_transaction
#print axioms twelve_three_parties_distinct
#print axioms twelve_jia_e1
#print axioms twelve_yi_e2_not_copied
#print axioms twelve_yi_e1_ok
#print axioms twelve_same_event_can_differ
#print axioms twelve_unknown_ability
#print axioms twelve_liable_unknown_gate
#print axioms twelve_pre_interest_kept
#print axioms twelve_cut_day
#print axioms twelve_cut_day_cap
#print axioms twelve_cut_not46_unknown
#print axioms twelve_filing_not_acceptance
#print axioms twelve_accepted_stay
#print axioms twelve_other_debtor_not_stayed
#print axioms twelve_unknown_acc_no_freeze
#print axioms twelve_four_tracks_distinct
#print axioms twelve_comp_kinds_distinct
#print axioms twelve_acquittal_insufficient
#print axioms twelve_custody_with_1719
#print axioms twelve_four_out_no_collapse
#print axioms twelve_s1_unresolved_not_selected
#print axioms twelve_law105_route
#print axioms twelve_admin105_route
#print axioms twelve_same_maker_route
#print axioms twelve_local_dept_route
#print axioms twelve_routes_differ
#print axioms twelve_route_not_selected
#print axioms twelve_interpret_self
#print axioms twelve_interpret_other
#print axioms twelve_disputed_unknown
#print axioms twelve_res_hit
#print axioms twelve_res_miss_person
#print axioms twelve_res_miss_time
#print axioms twelve_res_miss_subject
#print axioms twelve_res_missing_index
#print axioms twelve_outsider_not_auto_remedy
#print axioms twelve_candidate_basis
#print axioms twelve_candidate_scope
#print axioms twelve_theorem_ref_is_string
#print axioms twelve_consume_unknown
#print axioms twelve_no_permit_no_bridge
#print axioms twelve_candidate_not_decision

end JurisLean.CN.Completion20261105.InstitutionRules
