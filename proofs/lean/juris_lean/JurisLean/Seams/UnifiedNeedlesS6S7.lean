import Mathlib.Tactic
import JurisLean.Seams.FullProcess
import JurisLean.Seams.PrecedentFlow

/-!
# S6/S7 族十针（附录 I.13 逐名承接，UnifiedNeedlesS6S7）

中文说明：本件承接 `docs/spec/20261007-统一法律数学模型_附录I_Lean施工明细.md` §I.13 中
S6 族的五针（#38-#42）与 S7 族的五针（#43-#47）。每针以**原验收名**命名，按"拟"合同
写成显式前提的定理；锚引理可复用处一律直接实例化（FullProcess/PrecedentFlow 原定理以
全限定名引用，避免与同名本针遮蔽）。降载体处均在语句与本文档内如实声明。

## 逐针人话语义（人话）

- 38 `each_event_preserves_legal_invariants`：实际事件语言（`FullEvent` 六构造子）逐事件
  保全共享字段上的簿记不变式：守恒（履给通道，无需域假设）、回执堆不进入转移、登记债额
  冻结、履行账本只被给付事件写入（字段依赖分型：其余事件一律不写 `perf`）。
- 39 `finite_trace_preserves_legal_invariants`：对**所有**承诺事件（含域外回流与涂改）
  的前缀归纳：守恒与"回执不进入转移"沿每个前缀成立；四分量不变式只在声明域内承诺
  （锚定理原样实例化）。配套见证：实际历史**可以**违反只追加，不冒称实际历史永不违法。
- 40 `trace_concatenation_iff`：多后继关系的双向拼接：终态经轨迹可达，当且仅当存在
  共享中间状态把轨迹拆成两段分别可达（前向引锚 `runTrace_append`，反向取平凡拆分）。
- 41 `receipt_has_semantic_derivation`：以**初态来源合同**（初始账本每条记录都有先行
  事件的语义产物）替代锚定理的"空初账"前提；域内当前事件与初态来源合起来给出被准入
  回执的语义导出；回执堆沿轨迹恒不进入转移（不由回执反造权威）。锚的空初账版即
  `tr₀ = []` 且初账为空时的特例。
- 42 `nontrivial_legal_trace_exists`：实际非空轨迹的存在性见证：demo 载体上"成立＋给付"
  轨迹落入声明域、实际写入一条履行记录、关系账本与历史读数原样（引锚
  `trace_performs_and_keeps_history`）。
- 43 `stat_update_conservative_for_fixed_legal_context`：冻结法律材料与评价许可后，
  纯统计更新（只动经验计数）不改 Eval 读数；若统计合法进入证据（改动了法律材料），
  该更新不在本式覆盖范围内（配套引理显式排除）。
- 44 `precedent_update_preserves_norm_structure`：锚版本结构保持整体实例化，另加授权
  保持、授权范围形状保持（四元组见证形状）、未命中取代名单的旧记录原样留在新环境
  （后续规则选择仍可消费该记录）。
- 45 `feedback_preserves_target_model_when_conditions_hold`：参数化反馈机制在条件成立时
  只做统计层的分层重建，目标模型（法律材料与 Eval 读数）一字不动；条件不成立时不动作。
  不在 (s,n) 上继续 Beta 共轭（仓库无 Beta 载体，见载体差异）。
- 46 `empirical_frequency_not_binding_source`：统计通道自封的"规范草案"无授权见证、
  进不了规范层（引锚 `unauthorized_output_is_not_a_norm`）；经验统计仍可有具许可的
  证据用途（正面见证）。
- 47 `feedback_need_not_converge`：锚周期二反例原样承接，并附 2-周期读数：存在起点使
  相邻迭代永不相等，故不因反馈回流推出收敛；也不冒称一切反馈都不收敛（单调对照侧
  一步即稳，见 `PrecedentFlow.monotoneIter_one_step_stable`）。

## 载体差异（诚实降级声明）

- 仓库内没有真实 Beta 分布载体。第 43/45/46 针的统计层用本件显式有限载体
  `StatContext`（Nat 计数＋许可用途布尔）与 `FrozenLegalContext`（版本环境＋统计体）
  如实建模；"分层重建"是 (s,n) 到 (s+s,n+n) 的显式有限语义，不是 Beta 共轭的继续。
- 第 42 针的"共同十四族网络"载体不在本件 import 预算内（Unified 总入口另接）；本件在
  FullProcess 的 demo 载体上给出实际非空轨迹见证，不冒称十四族网络总见证。
- 第 41 针的"全部当前事件"覆盖 `fullDomain` 域内事件＋初态来源合同；BND04 的绑定级
  消费链不在本件 import 预算内，该侧升级点保持开放。

## 档位

零 `sorry`、零 `admit`、零自定义 `axiom`；`decide` 只用于闭式枚举字面量。
本件 `CI_NOT_RUN`（本地不编译 Lean，fail-closed），以 GitHub Actions 模块轮为唯一
编译权威。
-/

namespace JurisLean.Seams.UnifiedNeedlesS6S7

open JurisLean.Seams.FullProcess
open JurisLean.Seams.PrecedentFlow
open JurisLean.Seams.InstitutionalEffects

/-! ## 第 38 针：each_event_preserves_legal_invariants -/

/-- **第 38 针（S6，I.13）**：each_event_preserves_legal_invariants。
实际事件语言逐事件保全共享字段不变式：守恒（锚 `coreStep_preserves_admissible`，
对全部六类事件成立，不限于旧域读法）；回执堆不读不写（锚
`coreStep_pile_unchanged`）；登记债额 `debt` 冻结；履行账本只被给付事件写入
（字段依赖分型，第四分量）。"只追加"与"不遗忘"在本针**不**声称：它们需要域假设，
见第 39 针的条件分句。 -/
theorem each_event_preserves_legal_invariants {Rel : Type} (st : State Rel)
    (ev : FullEvent Rel) (h : AdmissibleState st) :
    AdmissibleState (coreStep st ev) ∧ (coreStep st ev).pile = st.pile ∧
      (coreStep st ev).debt = st.debt ∧
      ((coreStep st ev).perf = st.perf ∨
        ∃ (eid obligor : String) (rel : Rel) (amount : Nat),
          ev = FullEvent.core (SeamEvent.performance eid obligor rel amount)) := by
  refine ⟨coreStep_preserves_admissible st ev h, coreStep_pile_unchanged st ev, ?_, ?_⟩
  · cases ev with
    | core e =>
        cases e with
        | formative eid rel => rfl
        | terminating eid rel => rfl
        | performance eid obligor rel amount => rfl
        | declaratory eid => rfl
    | normBackflow eid rel => rfl
    | historyRewrite eid keep => rfl
  · cases ev with
    | core e =>
        cases e with
        | formative eid rel => exact Or.inl rfl
        | terminating eid rel => exact Or.inl rfl
        | performance eid obligor rel amount =>
            exact Or.inr ⟨eid, obligor, rel, amount, rfl⟩
        | declaratory eid => exact Or.inl rfl
    | normBackflow eid rel => exact Or.inl rfl
    | historyRewrite eid keep => exact Or.inl rfl

/-! ## 第 39 针：finite_trace_preserves_legal_invariants -/

/-- **第 39 针（S6，I.13）**：finite_trace_preserves_legal_invariants。
对所有承诺事件（含域外回流与涂改）做前缀归纳：守恒（锚 `conservation_along_trace`）
与"回执不进入转移"（锚 `runTrace_pile_unchanged`）沿每个前缀成立，**无域假设**；
四分量不变式（`invariantsHeld`）只在声明域内的轨迹上承诺（锚同名定理以
`fullDomain` 原样实例化）。本针不把实际历史约束成永不违法——见配套见证
`actual_history_not_constrained_never_violating`。 -/
theorem finite_trace_preserves_legal_invariants {Rel : Type} [DecidableEq Rel]
    (st₀ : State Rel) (tr : Trace Rel) (h₀ : AdmissibleState st₀) :
    (∀ pre : Trace Rel, (∃ post, tr = pre ++ post) →
        AdmissibleState (runTrace st₀ pre) ∧ (runTrace st₀ pre).pile = st₀.pile) ∧
      (traceInDomain fullDomain tr →
        ∀ pre : Trace Rel, (∃ post, tr = pre ++ post) →
          invariantsHeld st₀.ledger (runTrace st₀ pre)) := by
  refine ⟨?_, fun hdom pre hpre =>
    JurisLean.Seams.FullProcess.finite_trace_preserves_legal_invariants
      fullDomain st₀ tr h₀ hdom pre hpre⟩
  intro pre _hpre
  exact ⟨conservation_along_trace pre st₀ h₀, runTrace_pile_unchanged pre st₀⟩

/-- 第 39 针的诚实配套：实际历史**可以**违反"只追加"——域外涂改是真实事件语言里的
一个构造子，且它确实破坏只追加（锚 `historyRewrite_breaks_appendOnly`）。故"前缀保全"
是域相对的陈述，不是"实际历史永不违法"的全称主张。 -/
theorem actual_history_not_constrained_never_violating :
    ¬ ∀ tr : Trace Relation, appendOnlyOf st₀Seeded.ledger (runTrace st₀Seeded tr) :=
  fun hall => historyRewrite_breaks_appendOnly (hall rewriteTraceDemo)

/-! ## 第 40 针：trace_concatenation_iff -/

/-- **第 40 针（S6，I.13）**：trace_concatenation_iff。
多后继关系的双向拼接：`runTrace st₀ tr = s` 当且仅当存在轨迹拆分 `tr = a ++ b` 与
共享中间状态 `mid`，使 `a` 从 `st₀` 到达 `mid`、`b` 从 `mid` 到达 `s`。前向引锚
`runTrace_append`（分段执行 = 整体执行），反向取平凡拆分（`b = []`、`mid = 终态`）。
这是有限折叠的代数事实，不是收敛或可达性闭包陈述。 -/
theorem trace_concatenation_iff {Rel : Type} (st₀ s : State Rel) (tr : Trace Rel) :
    runTrace st₀ tr = s ↔
      ∃ (a b : Trace Rel) (mid : State Rel),
        tr = a ++ b ∧ runTrace st₀ a = mid ∧ runTrace mid b = s := by
  constructor
  · intro h
    refine ⟨tr, [], runTrace st₀ tr, (List.append_nil tr).symm, rfl, ?_⟩
    rw [runTrace_nil]
    exact h
  · rintro ⟨a, b, mid, htr, hmid, hfin⟩
    subst htr
    rw [runTrace_append, hmid]
    exact hfin

/-! ## 第 41 针：receipt_has_semantic_derivation -/

/-- **第 41 针（S6，I.13）**：receipt_has_semantic_derivation。
初态来源合同版：只要初始账本每条记录都有先行轨迹 `tr₀` 中的事件导出（`hprov`），
且当前轨迹落在 `fullDomain` 内，则任何被记账准入的回执都带语义导出——导出来自
`tr₀ ++ tr` 中的某个事件（初账记录归 `tr₀`，当前记录归 `tr`，分流引锚
`runTrace_ledger_eq_append` 与 `mem_traceRecords_has_event`）。同时回执堆沿轨迹
恒不进入转移（锚 `runTrace_pile_unchanged`）：不由回执反造权威。锚的"空初账"版是
`st₀.ledger = []`、`tr₀ = []` 时的特例；本针不再要求空初账。 -/
theorem receipt_has_semantic_derivation {Rel : Type}
    (st₀ : State Rel) (tr₀ tr : Trace Rel) (rc : Receipt Rel)
    (hprov : ∀ rec ∈ st₀.ledger, ∃ ev, ev ∈ tr₀ ∧ recordOfEvent ev = some rec)
    (hdom : traceInDomain fullDomain tr)
    (hadm : Admitted (runTrace st₀ tr) rc) :
    HasDerivation (tr₀ ++ tr) rc ∧ (runTrace st₀ tr).pile = st₀.pile := by
  obtain ⟨hmem, _hlvl⟩ := hadm
  refine ⟨?_, runTrace_pile_unchanged tr st₀⟩
  rw [runTrace_ledger_eq_append tr st₀ hdom, List.mem_append] at hmem
  rcases hmem with hinit | htr
  · obtain ⟨ev, hev, heq⟩ := hprov _ hinit
    exact ⟨ev, (List.mem_append).mpr (Or.inl hev), heq⟩
  · obtain ⟨ev, hev, heq⟩ := mem_traceRecords_has_event tr (receiptRecord rc) htr
    exact ⟨ev, (List.mem_append).mpr (Or.inr hev), heq⟩

/-! ## 第 42 针：nontrivial_legal_trace_exists -/

/-- **第 42 针（S6，I.13）**：nontrivial_legal_trace_exists。
实际非空轨迹的存在性见证：存在状态与轨迹，轨迹非空、起点良构、轨迹落在声明域内、
终态确实入账一条履行记录（`perf.length = 1`，实际有给付之效）、关系账本原样
（历史不被涂改）。见证即锚 `trace_performs_and_keeps_history` 的 seeded 起点＋给付
轨迹。载体差异：本见证在 FullProcess 的 demo 载体上；"共同十四族网络"上的总见证
不在本件 import 预算内，不冒称。 -/
theorem nontrivial_legal_trace_exists :
    ∃ (st : State Relation) (tr : Trace Relation),
      tr ≠ [] ∧ AdmissibleState st ∧ traceInDomain fullDomain tr ∧
        (runTrace st tr).perf.length = 1 ∧ (runTrace st tr).ledger = st.ledger :=
  ⟨st₀Seeded, performTraceDemo, List.cons_ne_nil _ _,
    by intro s hs; exact absurd hs List.not_mem_nil,
    performTraceDemo_inDomain,
    trace_performs_and_keeps_history.2.1, trace_performs_and_keeps_history.1⟩

/-! ## S7 族共用有限载体（第 43/45/46 针）

仓库内没有真实 Beta 分布与统计更新载体；本节显式建有限载体，统计层 = Nat 计数 +
许可用途布尔，法律材料层 = S7 的 `VersionEnv`。所有载体差异已在模块 doc 声明。 -/

/-- 统计侧载体：经验计数（成功数、样本量）与该统计是否用于**具许可**的证据用途。 -/
structure StatContext where
  successes : Nat
  trials : Nat
  licensedUse : Bool

/-- 冻结法律语境：法律材料（S7 版本环境）＋统计体。 -/
structure FrozenLegalContext where
  versions : VersionEnv
  stat : StatContext

/-- 冻结语境下的评价读数：Eval 只消费冻结的法律材料（版本环境）。 -/
def evalOn (fc : FrozenLegalContext) : VersionEnv := fc.versions

/-- 一次纯统计观测（增量计数，不含任何法律材料变更）。 -/
structure StatObservation where
  successes : Nat
  trials : Nat

/-- 纯统计更新：只动统计体的两个计数，法律材料一字不动，评价许可随证据原样带过去。 -/
def statOnlyUpdate (fc : FrozenLegalContext) (obs : StatObservation) : FrozenLegalContext :=
  { fc with stat := { successes := fc.stat.successes + obs.successes,
                      trials := fc.stat.trials + obs.trials,
                      licensedUse := fc.stat.licensedUse } }

/-! ## 第 43 针：stat_update_conservative_for_fixed_legal_context -/

/-- **第 43 针（S7，I.13）**：stat_update_conservative_for_fixed_legal_context。
冻结法律材料与评价许可之后，纯统计更新是保守的：法律材料层不动、评价许可用途
不动、Eval 读数不动。若新统计**合法进入证据**（即更新改动了法律材料层），则不套
本式——见配套 `evidence_entering_update_out_of_scope` 的显式排除。 -/
theorem stat_update_conservative_for_fixed_legal_context
    (fc : FrozenLegalContext) (obs : StatObservation) :
    (statOnlyUpdate fc obs).versions = fc.versions ∧
      (statOnlyUpdate fc obs).stat.licensedUse = fc.stat.licensedUse ∧
      evalOn (statOnlyUpdate fc obs) = evalOn fc :=
  ⟨rfl, rfl, rfl⟩

/-- 第 43 针的适用范围排除：任何改动法律材料层的更新（统计合法进入证据的形态）
都不在本式覆盖内——其 Eval 读数确实会动。 -/
theorem evidence_entering_update_out_of_scope
    (u : FrozenLegalContext → FrozenLegalContext) (fc : FrozenLegalContext)
    (hchg : (u fc).versions ≠ fc.versions) :
    evalOn (u fc) ≠ evalOn fc := by
  intro heq
  exact hchg heq

/-! ## 第 45 针：feedback_preserves_target_model_when_conditions_hold -/

/-- 参数化反馈机制：条件成立时只做**统计层的分层重建**——两个同构分层并池，
(s,n) 到 (s+s,n+n)，法律材料层与评价许可不动；条件不成立时不动作。
这是显式有限载体语义，不是在 (s,n) 上继续 Beta 共轭（仓库无 Beta 载体）。 -/
def feedbackStep : FrozenLegalContext → Bool → FrozenLegalContext
  | fc, true =>
      { fc with stat := { successes := fc.stat.successes + fc.stat.successes,
                          trials := fc.stat.trials + fc.stat.trials,
                          licensedUse := fc.stat.licensedUse } }
  | fc, false => fc

/-- **第 45 针（S7，I.13）**：feedback_preserves_target_model_when_conditions_hold。
条件成立时，反馈机制保持目标模型：法律材料层不动、Eval 读数不动（统计层被分层
重建）；条件不成立时机制不动作（不冒称重建发生）。非空洞性见配套
`feedback_step_not_vacuous`：条件成立时统计层确实被改写。 -/
theorem feedback_preserves_target_model_when_conditions_hold (fc : FrozenLegalContext) :
    (feedbackStep fc true).versions = fc.versions ∧
      evalOn (feedbackStep fc true) = evalOn fc ∧
      feedbackStep fc false = fc :=
  ⟨rfl, rfl, rfl⟩

/-- 见证环境（空版本表）与见证统计体（1 成功、2 样本、具许可用途）。 -/
def demoEnv : VersionEnv := { versions := ([] : List SourceVersionRecord) }

def demoFrozen : FrozenLegalContext :=
  { versions := demoEnv, stat := { successes := 1, trials := 2, licensedUse := true } }

/-- 第 45 针的非空洞性见证：条件成立时统计层确实被分层重建（成功数翻倍），
而法律材料层与 Eval 读数不动——"保持目标模型"不是"什么都不做"。 -/
theorem feedback_step_not_vacuous :
    (feedbackStep demoFrozen true).stat.successes = 2 ∧
      (feedbackStep demoFrozen true).versions = demoFrozen.versions :=
  ⟨rfl, rfl⟩

/-! ## 第 46 针：empirical_frequency_not_binding_source -/

/-- 统计通道自封的"规范草案"：把经验频率直接冒充规范内容申报。四元组取
下级法院 × 普通审判程序 × 非故意漏洞 × 单一案件范围（与锚
`PrecedentFlow.lowerCourtDraft` 同形、内容不同），不携带任何授权见证。 -/
def empiricalDraft (se : StatContext) : BackflowProduction :=
  { actor := Actor.intermediateCourt, procedure := Procedure.ordinaryAdjudication,
    gap := Genealogy.Part4.P066.GapSignal.unintentionalGap,
    scope := Scope.withinSingleCase,
    content := { payload := "empirical-frequency" } }

/-- 自封统计草案无授权见证：`Competence` 构造子穷尽性读数——任何见证的主体必为
最高法，而草案申报的是中级法院（闭式枚举判定）。 -/
theorem empirical_draft_unauthorized (se : StatContext) :
    ¬ authorized (empiricalDraft se) := by
  rintro ⟨c⟩
  obtain ⟨h1, _, _⟩ := competence_shape c
  simp only [empiricalDraft] at h1
  exact absurd h1 (by decide)

/-- **第 46 针（S7，I.13）**：empirical_frequency_not_binding_source。
统计更新没有法源授权的规则生成通道：统计通道自封的"规范草案"既无授权见证
（`authorized` 不成立），也没有任何规范层条目申报它（锚
`unauthorized_output_is_not_a_norm` 实例化）。经验统计**仍可有具许可的证据用途**
（正面见证 `licensed_empirical_use_possible`）——被排除的只是"经验频率直接当法源"，
不是统计的一切用途。 -/
theorem empirical_frequency_not_binding_source (se : StatContext) :
    ¬ authorized (empiricalDraft se) ∧
      ¬ ∃ e : NormLayerEntry, e.declared = empiricalDraft se :=
  ⟨empirical_draft_unauthorized se,
    unauthorized_output_is_not_a_norm (empiricalDraft se) (empirical_draft_unauthorized se)⟩

/-- 第 46 针的正面见证：载体不禁止具许可的经验证据用途（licensedUse 可为真）。 -/
theorem licensed_empirical_use_possible :
    ∃ se : StatContext, se.licensedUse = true :=
  ⟨{ successes := 1, trials := 2, licensedUse := true }, rfl⟩

/-! ## 第 44 针：precedent_update_preserves_norm_structure -/

/-- **第 44 针（S7，I.13）**：precedent_update_preserves_norm_structure。
锚版本结构保持（区间良态、supersession 边非自指、失效记录继续失效）由下条
`precedent_update_norm_structure_anchor` 以全限定名整体实例化承接；本针补三件事：
更新入口的授权保持（`AuthorizedDecision` 自带 `Competence` 见证）；授权范围形状保持
（任何授权更新的主体必为最高法、范围必为全国）；后续规则选择消费保持（未命中取代
名单的旧记录原样留在新环境中，规则选择仍能读到它）。开放点：`applicableVersions`
查询层的双向等式重述未在本件展开。 -/
theorem precedent_update_preserves_norm_structure (E : VersionEnv)
    (ad : AuthorizedDecision) (hwf : EnvWf E ad) (t : Int) :
    authorized ad.decision.production ∧
      ad.decision.production.actor = Actor.supremeCourt ∧
      ad.decision.production.scope = Scope.nationwide ∧
      (∀ v : SourceVersionRecord, v ∈ E.versions →
          hitsSupersession ad.decision v ≠ true → v ∈ (precedentUpdate ad E).versions) := by
  constructor
  · exact ⟨ad.witness⟩
  · constructor
    · exact (competence_shape ad.witness).1
    · constructor
      · exact (competence_shape ad.witness).2.2
      · intro v hv hhit
        by_cases hfire : updateFires ad.decision = true
        · rw [update_versions_fires ad E hfire]
          exact List.mem_cons.mpr
            (Or.inr (List.mem_map.mpr ⟨v, hv, supersedeRecord_keeps_unhit ad.decision v hhit⟩))
        · rw [update_versions_silent ad E hfire]
          exact hv

/-- 第 44 针的锚承载体：锚版本结构保持（区间良态、supersession 边非自指、
    失效记录继续失效）以全限定名整体实例化。 -/
theorem precedent_update_norm_structure_anchor (E : VersionEnv)
    (ad : AuthorizedDecision) (hwf : EnvWf E ad) (t : Int) :
    JurisLean.Seams.PrecedentFlow.precedent_update_preserves_norm_structure E ad hwf t :=
  JurisLean.Seams.PrecedentFlow.precedent_update_preserves_norm_structure E ad hwf t

/-! ## 第 47 针：feedback_need_not_converge -/

/-- **第 47 针（S7，I.13）**：feedback_need_not_converge。
锚周期二反例原样承接（全限定名实例化）：存在起点使回流迭代相邻两步永不相等，
故不因反馈回流而推出收敛；并附锚 2-周期读数 `backflowIter_period_two`（轨道
回到起点不是收敛——收敛要求最终固定）。不冒称一切反馈都不收敛：单调对照侧
（`PrecedentFlow.monotoneIter_one_step_stable`）一步即稳。 -/
theorem feedback_need_not_converge :
    (∃ z : Bool, ∀ n : Nat, backflowIter (n + 1) z ≠ backflowIter n z) ∧
      ∀ (n : Nat) (b : Bool), backflowIter (n + 2) b = backflowIter n b :=
  ⟨JurisLean.Seams.PrecedentFlow.feedback_need_not_converge, backflowIter_period_two⟩

end JurisLean.Seams.UnifiedNeedlesS6S7
