import JurisLean.Candidates.AuthorizationClosureAudit20261104
import JurisLean.Candidates.LegalActionDomainAudit20261027

/-!
本文件只补冻结10.2 L109/L111/L113的差额。直接复用既有刷新协议、Temporal选择与
源材料/准入fixture。验收以独立CI及权威原题台账绑定为准；本文件不自行改账。
新增证明的验收由实际声明和独立CI给出；经验标记、输出字符串和运行数量不代替读取链。
-/
namespace JurisLean.Candidates.FinalizeReadClosureAudit20261105

open JurisLean.Candidates.Final20261021
open JurisLean.Candidates.SourceCompilation20261027
open JurisLean.Candidates.FiniteLegalValidation20261027
open JurisLean.Candidates.LegalActionDomain20261027

/-- 阻断L109：在独立材料提取/准入前提和同一完整快照下，实际evaluator逐分支读取Select。
不把“实际输出已正确”当前提，也不另算理想Eval替代实际调用。 -/
theorem actual_eval_reads_snapshot_selection {W : Type} (current : Ledger.Handle)
    (input : LegalInput W) (branch : Nat) (view : ExtractedView) (bound : BoundData)
    (sameGamma : input.anchor.gamma = current.gamma)
    (sameHistory : input.history = current.state.normHistory)
    (fresh : current.state.env =
      Temporal.proposed_applicability current.gamma current.state.normHistory)
    (extracted : extractView input.anchor branch input.catalog = .known view)
    (admitted : bindAdditional view input.supplements input.policies = .known bound) :
    JurisLean.Candidates.U10_1RefreshRuleProtocol20261030.evaluateCurrentRules current input branch =
      (match selectedHorn bound.source
          (Temporal.proposed_applicability current.gamma current.state.normHistory)
          input.rules input.ruleGate (eligibleFacts bound) with
       | .known out => .known (bound, out)
       | .unknown e => .unknown e
       | .rejected e => .rejected e
       | .conflict left right => .conflict left right) := by
  cases hs : selectedHorn bound.source
      (Temporal.proposed_applicability current.gamma current.state.normHistory)
      input.rules input.ruleGate (eligibleFacts bound) <;>
    simp [JurisLean.Candidates.U10_1RefreshRuleProtocol20261030.evaluateCurrentRules,
      sameGamma, sameHistory, extracted, admitted, fresh, hs]

/-- 阻断L111：Gamma或history不属于本次同一快照的请求在真实入口拒绝。 -/
theorem mismatched_request_is_rejected {W : Type} (current : Ledger.Handle)
    (input : LegalInput W) (branch : Nat)
    (mismatch : input.anchor.gamma ≠ current.gamma ∨ input.history ≠ current.state.normHistory) :
    JurisLean.Candidates.U10_1RefreshRuleProtocol20261030.evaluateCurrentRules current input branch =
      .rejected .scopeMismatch := by
  have hn : ¬ (input.anchor.gamma = current.gamma ∧ input.history = current.state.normHistory) := by
    intro h
    rcases mismatch with hg | hh
    · exact hg h.1
    · exact hh h.2
  simp only [JurisLean.Candidates.U10_1RefreshRuleProtocol20261030.evaluateCurrentRules, if_neg hn]

/-- 阻断L109：原题明确区分的仅日志追加准备阶段；未声称它是合法Trace.Step。 -/
def appendOnly (h : Ledger.Handle) (event : Temporal.VersionRecord) : Ledger.Handle :=
  { h with state := { h.state with normHistory := h.state.normHistory ++ [event] } }

def minimalChange : Pipeline.RefreshInput :=
  ⟨AuthorizationClosureAudit20261104.baseGamma, Acceptance.version, ⟨1⟩⟩

def minimalDraft : AuthorizationClosureAudit20261104.Draft := ⟨minimalChange, true, true⟩

def minimalCatalog : List Authorization.Grant :=
  [AuthorizationClosureAudit20261104.grantFor
    (AuthorizationClosureAudit20261104.queryForRefresh
      AuthorizationClosureAudit20261104.phaseBefore minimalDraft)]

def minimalAfter : Ledger.Handle :=
  AuthorizationClosureAudit20261104.phasePost minimalDraft

/-- 一份已获准事件确已追加、Gamma保持同一个值、env仍旧，而实际Select已有known0。
同一个请求走真实refresh则把新history/env共同发布。 -/
theorem authorized_append_is_not_environment_refresh :
    AuthorizationClosureAudit20261104.Granted minimalCatalog
      AuthorizationClosureAudit20261104.phaseBefore minimalDraft ∧
    (appendOnly AuthorizationClosureAudit20261104.phaseBefore Acceptance.version).gamma =
      AuthorizationClosureAudit20261104.phaseBefore.gamma ∧
    (appendOnly AuthorizationClosureAudit20261104.phaseBefore Acceptance.version).state.env =
      AuthorizationClosureAudit20261104.phaseBefore.state.env ∧
    Temporal.proposed_applicability
      (appendOnly AuthorizationClosureAudit20261104.phaseBefore Acceptance.version).gamma
      (appendOnly AuthorizationClosureAudit20261104.phaseBefore Acceptance.version).state.normHistory =
        .known 0 ∧
    (appendOnly AuthorizationClosureAudit20261104.phaseBefore Acceptance.version).state.env ≠ .known 0 ∧
    Pipeline.refresh minimalCatalog AuthorizationClosureAudit20261104.phaseBefore minimalChange =
      .known minimalAfter := by
  unfold AuthorizationClosureAudit20261104.Granted
  decide +kernel

/-- 阻断L109/L111：把现有实际refresh后态直接实例化到上面的全分支读取等式。
成功刷新同时给出Gamma/history/env三个后置，外部调用者再对齐下次请求的同一快照。 -/
theorem actual_finalize_next_eval_reads_selection {W : Type}
    (catalog : List Authorization.Grant) (before after : Ledger.Handle)
    (d : AuthorizationClosureAudit20261104.Draft) (input : LegalInput W) (branch : Nat)
    (view : ExtractedView) (bound : BoundData)
    (refreshed : AuthorizationClosureAudit20261104.submitDraft catalog before d = .known after)
    (sameGamma : input.anchor.gamma = after.gamma)
    (sameHistory : input.history = after.state.normHistory)
    (extracted : extractView input.anchor branch input.catalog = .known view)
    (admitted : bindAdditional view input.supplements input.policies = .known bound) :
    after.gamma = d.change.gamma ∧
    after.state.normHistory = before.state.normHistory ++ [d.change.event] ∧
    JurisLean.Candidates.U10_1RefreshRuleProtocol20261030.evaluateCurrentRules after input branch =
      (match selectedHorn bound.source
          (Temporal.proposed_applicability after.gamma after.state.normHistory)
          input.rules input.ruleGate (eligibleFacts bound) with
       | .known out => .known (bound, out)
       | .unknown e => .unknown e
       | .rejected e => .rejected e
       | .conflict left right => .conflict left right) := by
  have hs := AuthorizationClosureAudit20261104.actual_refresh_requires_old_authority
    catalog before after d refreshed
  have hf : after.state.env = Temporal.proposed_applicability after.gamma after.state.normHistory := by
    rw [hs.2.1, hs.2.2.1]
    exact hs.2.2.2
  exact ⟨hs.2.1, hs.2.2.1,
    actual_eval_reads_snapshot_selection after input branch view bound sameGamma sameHistory hf extracted admitted⟩

/-- 后续L113有限例将复用已存LegalInput及其真实材料/准入门，而不新拼理想evaluator。 -/
def fixtureInput : LegalInput (List Nat) :=
  JurisLean.Candidates.LegalActionDomain20261027.Audit.legalInput

def fixtureGamma : Gamma := fixtureInput.anchor.gamma

def currentVersion : Temporal.VersionRecord :=
  ⟨⟨700⟩, 1, fixtureGamma.jurisdiction, fixtureGamma.question, ⟨0⟩, none, ⟨0⟩, ⟨0⟩⟩

def inputAt (h : Ledger.Handle) : LegalInput (List Nat) :=
  { fixtureInput with history := h.state.normHistory }

/-- 阻断L109/L113：使用已存真实LegalInput材料/准入fixture，构造一次真实授权刷新。 -/
def fixtureBefore : Ledger.Handle := Trace.initial fixtureGamma Acceptance.debt

def changeFor (event : Temporal.VersionRecord) : Pipeline.RefreshInput :=
  ⟨fixtureGamma, event, ⟨1⟩⟩

def catalogFor (event : Temporal.VersionRecord) : List Authorization.Grant :=
  [AuthorizationClosureAudit20261104.grantFor
    (AuthorizationClosureAudit20261104.queryForRefresh fixtureBefore
      ⟨changeFor event, false, false⟩)]

def publishedAfter (h : Ledger.Handle) (event : Temporal.VersionRecord) : Ledger.Handle :=
  ⟨fixtureGamma, h.revision + 1,
    { h.state with
      normHistory := h.state.normHistory ++ [event]
      env := Temporal.proposed_applicability fixtureGamma (h.state.normHistory ++ [event]) }⟩

def fixtureAfter : Ledger.Handle := publishedAfter fixtureBefore currentVersion

def actualEvaluation (h : Ledger.Handle) : Result (BoundData × HornReport) :=
  JurisLean.Candidates.U10_1RefreshRuleProtocol20261030.evaluateCurrentRules h (inputAt h) 0

def actualKnown (h : Ledger.Handle) : Bool :=
  match actualEvaluation h with
  | .known _ => true
  | _ => false

theorem actual_fixture_has_refresh_and_known_evaluation :
    Pipeline.refresh (catalogFor currentVersion) fixtureBefore (changeFor currentVersion) =
      .known fixtureAfter ∧
    ∃ bound out, actualEvaluation fixtureAfter = .known (bound, out) := by
  refine ⟨?_, ?_⟩
  · decide +kernel
  · have hk : actualKnown fixtureAfter = true := by decide +kernel
    have expose (r : Result (BoundData × HornReport))
        (h : (match r with | .known _ => true | _ => false) = true) :
        ∃ bound out, r = .known (bound, out) := by
      cases r with
      | known pair =>
          exact ⟨pair.1, pair.2, by cases pair; rfl⟩
      | unknown e => cases h
      | rejected e => cases h
      | conflict left right => cases h
    exact expose _ hk

/-- 阻断L111：三个指定时间分支使用实际授权refresh后态及真实evaluator。 -/
def dormantVersion : Temporal.VersionRecord :=
  { currentVersion with
    id := ⟨701⟩
    version := 2
    factFrom := ⟨fixtureGamma.lawDate.ordinal + 1⟩ }

def overlappingVersion : Temporal.VersionRecord :=
  { currentVersion with id := ⟨702⟩, version := 2 }

def lateRecordedVersion : Temporal.VersionRecord :=
  { currentVersion with
    id := ⟨703⟩
    version := 3
    recordedAt := ⟨fixtureGamma.recordCutoff.ticks + 1⟩
    knownAt := ⟨fixtureGamma.knowledgeCutoff.ticks + 1⟩ }

def dormantAfter : Ledger.Handle := publishedAfter fixtureAfter dormantVersion

def conflictAfter : Ledger.Handle := publishedAfter fixtureAfter overlappingVersion

def historicalAfter : Ledger.Handle := publishedAfter fixtureAfter lateRecordedVersion

theorem not_yet_effective_is_not_latest_evaluation :
    Pipeline.refresh (catalogFor dormantVersion) fixtureAfter (changeFor dormantVersion) =
      .known dormantAfter ∧
    dormantVersion.version > currentVersion.version ∧
    dormantAfter.state.env = .known 1 ∧
    actualEvaluation dormantAfter = actualEvaluation fixtureAfter := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · rfl

theorem unresolved_conflict_stays_in_actual_evaluation :
    Pipeline.refresh (catalogFor overlappingVersion) fixtureAfter (changeFor overlappingVersion) =
      .known conflictAfter ∧
    conflictAfter.state.env = .conflict 1 2 ∧
    actualEvaluation conflictAfter = .conflict 1 2 := by
  refine ⟨?_, ?_, ?_⟩
  · decide +kernel
  · decide +kernel
  · rfl

theorem historical_cutpoint_is_consumed_by_actual_evaluation :
    Pipeline.refresh (catalogFor lateRecordedVersion) fixtureAfter (changeFor lateRecordedVersion) =
      .known historicalAfter ∧
    Temporal.visible fixtureGamma lateRecordedVersion = false ∧
    historicalAfter.state.env =
      Temporal.proposed_applicability fixtureGamma fixtureAfter.state.normHistory ∧
    actualEvaluation historicalAfter = actualEvaluation fixtureAfter := by
  have later : ∀ e ∈ [lateRecordedVersion], Temporal.visible fixtureGamma e = false := by
    intro e he
    have heq : e = lateRecordedVersion := by simpa using he
    subst e
    decide +kernel
  have hs := Temporal.u08_1_selection_stable fixtureGamma
    fixtureAfter.state.normHistory [lateRecordedVersion] later
  refine ⟨?_, ?_, ?_, ?_⟩
  · decide +kernel
  · decide +kernel
  · exact hs
  · rfl

/-- 阻断L113：同一日志事件重复追加，一次与两次分别比较三种结果。
这三个谓词严格区分日志本体、Select结果、真实Eval完整Result，不以字符串替代Result。 -/
def AppendIdempotent (h : Ledger.Handle) (event : Temporal.VersionRecord) : Prop :=
  appendOnly (appendOnly h event) event = appendOnly h event

def SelectionIdempotent (h : Ledger.Handle) (event : Temporal.VersionRecord) : Prop :=
  Temporal.proposed_applicability h.gamma
      (appendOnly (appendOnly h event) event).state.normHistory =
    Temporal.proposed_applicability h.gamma (appendOnly h event).state.normHistory

def EvaluationIdempotent (h : Ledger.Handle) (event : Temporal.VersionRecord) : Prop :=
  actualEvaluation (appendOnly (appendOnly h event) event) =
    actualEvaluation (appendOnly h event)

theorem three_idempotences_have_inequivalent_finite_witnesses :
    (¬ AppendIdempotent fixtureBefore currentVersion ∧
      ¬ SelectionIdempotent fixtureBefore currentVersion ∧
      EvaluationIdempotent fixtureBefore currentVersion) ∧
    (¬ AppendIdempotent fixtureAfter dormantVersion ∧
      SelectionIdempotent fixtureAfter dormantVersion ∧
      EvaluationIdempotent fixtureAfter dormantVersion) := by
  refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩⟩
  · unfold AppendIdempotent
    decide +kernel
  · unfold SelectionIdempotent
    decide +kernel
  · rfl
  · unfold AppendIdempotent
    decide +kernel
  · unfold SelectionIdempotent
    decide +kernel
  · rfl

/-- 阻断L113：提取实际已评价闭包的一个可见文本，不赋予法律判决地位。 -/
def evaluationText (r : Result (BoundData × HornReport)) : String :=
  match r with
  | .known (_, out) => if 2 ∈ out.closure then "atom 2 derived" else "atom 2 absent"
  | .unknown _ => "unknown"
  | .rejected _ => "rejected"
  | .conflict _ _ => "conflict"

def staleReplay : Ledger.Handle := appendOnly fixtureAfter currentVersion

/-- 同一个真实known评价完整结果及其字符串都可保持，而Select已冲突。
这里只展示日志追加的中间态，未声称它是合法Trace.Step；实际原子refresh仍按联合后置重算。 -/
theorem same_known_result_and_text_do_not_certify_environment_refresh :
    fixtureAfter.state.env =
      Temporal.proposed_applicability fixtureAfter.gamma fixtureAfter.state.normHistory ∧
    staleReplay.state.env = .known 1 ∧
    Temporal.proposed_applicability staleReplay.gamma staleReplay.state.normHistory = .conflict 1 1 ∧
    staleReplay.state.env ≠
      Temporal.proposed_applicability staleReplay.gamma staleReplay.state.normHistory ∧
    (∃ bound out, actualEvaluation fixtureAfter = .known (bound, out) ∧
      actualEvaluation staleReplay = .known (bound, out)) ∧
    evaluationText (actualEvaluation staleReplay) = evaluationText (actualEvaluation fixtureAfter) := by
  obtain ⟨_, bound, out, hk⟩ := actual_fixture_has_refresh_and_known_evaluation
  have same : actualEvaluation staleReplay = actualEvaluation fixtureAfter := by rfl
  refine ⟨?_, ?_, ?_, ?_, ⟨bound, out, hk, same.trans hk⟩, congrArg evaluationText same⟩
  · rfl
  · decide +kernel
  · decide +kernel
  · decide +kernel

/-- 阻断L113：重复的同一Grant不增加任何完整Query许可；直接复用已有真实any见证定理。 -/
theorem duplicate_confirmation_grants_add_no_permissions
    (catalog : List Authorization.Grant) (grant : Authorization.Grant)
    (q : AuthorizationClosureAudit20261104.Query) :
    AuthorizationClosureAudit20261104.permits (catalog ++ [grant, grant]) q =
      AuthorizationClosureAudit20261104.permits (catalog ++ [grant]) q := by
  have same :
      (AuthorizationClosureAudit20261104.permits (catalog ++ [grant, grant]) q = true) ↔
      (AuthorizationClosureAudit20261104.permits (catalog ++ [grant]) q = true) := by
    simp [AuthorizationClosureAudit20261104.permits_exact_current_witness]
  cases hl : AuthorizationClosureAudit20261104.permits (catalog ++ [grant, grant]) q <;>
    cases hr : AuthorizationClosureAudit20261104.permits (catalog ++ [grant]) q <;> simp_all

def repeatedAfter : Ledger.Handle := publishedAfter fixtureAfter currentVersion

/-- 同一已授权事件在实际原子入口重复提交会重算冲突，不以确认次数制造新规范权限。 -/
theorem repeated_actual_confirmation_does_not_self_activate :
    Pipeline.refresh (catalogFor currentVersion) fixtureBefore (changeFor currentVersion) =
      .known fixtureAfter ∧
    Pipeline.refresh (catalogFor currentVersion) fixtureAfter (changeFor currentVersion) =
      .known repeatedAfter ∧
    repeatedAfter.gamma = fixtureAfter.gamma ∧
    repeatedAfter.state.env = .conflict 1 1 ∧
    actualEvaluation repeatedAfter = .conflict 1 1 ∧
    AuthorizationClosureAudit20261104.permits (catalogFor currentVersion)
      { AuthorizationClosureAudit20261104.queryForRefresh fixtureBefore
          ⟨changeFor currentVersion, false, false⟩ with object := .document 2 } = false := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · decide +kernel
  · decide +kernel
  · rfl
  · decide +kernel
  · rfl
  · decide +kernel

#check AppendIdempotent
#check SelectionIdempotent
#check EvaluationIdempotent
#check actual_eval_reads_snapshot_selection
#print axioms actual_eval_reads_snapshot_selection
#check mismatched_request_is_rejected
#print axioms mismatched_request_is_rejected
#check authorized_append_is_not_environment_refresh
#print axioms authorized_append_is_not_environment_refresh
#check actual_finalize_next_eval_reads_selection
#print axioms actual_finalize_next_eval_reads_selection
#check actual_fixture_has_refresh_and_known_evaluation
#print axioms actual_fixture_has_refresh_and_known_evaluation
#check not_yet_effective_is_not_latest_evaluation
#print axioms not_yet_effective_is_not_latest_evaluation
#check unresolved_conflict_stays_in_actual_evaluation
#print axioms unresolved_conflict_stays_in_actual_evaluation
#check historical_cutpoint_is_consumed_by_actual_evaluation
#print axioms historical_cutpoint_is_consumed_by_actual_evaluation
#check three_idempotences_have_inequivalent_finite_witnesses
#print axioms three_idempotences_have_inequivalent_finite_witnesses
#check same_known_result_and_text_do_not_certify_environment_refresh
#print axioms same_known_result_and_text_do_not_certify_environment_refresh
#check duplicate_confirmation_grants_add_no_permissions
#print axioms duplicate_confirmation_grants_add_no_permissions
#check repeated_actual_confirmation_does_not_self_activate
#print axioms repeated_actual_confirmation_does_not_self_activate
#check Temporal.u08_1_selection_stable
#print axioms Temporal.u08_1_selection_stable
#check JurisLean.Candidates.U10_1RefreshRuleProtocol20261030.evaluated_rules_use_actual_environment
#print axioms JurisLean.Candidates.U10_1RefreshRuleProtocol20261030.evaluated_rules_use_actual_environment

end JurisLean.Candidates.FinalizeReadClosureAudit20261105
