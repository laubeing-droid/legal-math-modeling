import JurisLean.LegalModelV2
import Mathlib.Data.Set.Basic

/-!
中文说明：对象定义 v3（冻结版 2026-09-25）的 Lean 内核合同。子命名空间
JurisLean.KernelV3 承载：Judgment 三值、QuestionKind 三分（实体/程序/效力）、
EffectType 四分（确认/形成/给付/程序拘束，对应冻结条款四）、EvalResult 的
Disposition 字段（Option D，非第四值）、B_t=(R_t, K) 双层状态、证据更新只收窄
K、evalBatch 只出被问问题、程序判断不自动生成实体判断、事实时点治理的
ApplicableNorm（t 不单独决定版本）、未决窄化（穷尽四类规则才未决）与三外衣
派生分析类型。三模态互不推出的见证定理在 JurisLean.LegalPower
（LegalModelV2.lean），此处不重复定义。
-/

namespace JurisLean.KernelV3

/-- 中文说明：判断三值：成立/不成立/未决（对象定义 v3 第二条）。 -/
inductive Judgment where
  | established
  | notEstablished
  | undetermined
deriving DecidableEq, Repr

/-- 中文说明：问题三分：实体/程序/效力（对象定义 v3 第三条）。 -/
inductive QuestionKind where
  | substantive
  | procedural
  | effect
deriving DecidableEq, Repr

/-- 中文说明：裁判事件效果四分：确认/形成/给付/程序拘束（对象定义 v3 第四条）。 -/
inductive EffectType where
  | confirmatory
  | constitutive
  | performance
  | proceduralBinding
deriving DecidableEq, Repr

/-- 中文说明：规范本体真值（冻结条款二：Truth ∈ {true, false}）。 -/
abbrev Truth := Bool

structure Question (Q : Type) where
  id : Q
  kind : QuestionKind

/-- 中文说明：Eval(q) 的结果对：Judgment 与 Disposition（Option D，∅ 用 none）。
Disposition 是字段，绝不与三值 Judgment 竞争（冻结条款三）。 -/
structure EvalResult (D : Type) where
  judgment : Judgment
  disposition : Option D

def mkEval {D : Type}
    (judgment : Judgment)
    (disposition : Option D) :
    EvalResult D :=
  {
    judgment := judgment
    disposition := disposition
  }

/-- 中文证明：求值对的两个分量忠实（rfl 级）。 -/
theorem mkEval_judgment {D : Type}
    (judgment : Judgment)
    (disposition : Option D) :
    (mkEval judgment disposition).judgment = judgment :=
  rfl

theorem mkEval_disposition {D : Type}
    (judgment : Judgment)
    (disposition : Option D) :
    (mkEval judgment disposition).disposition = disposition :=
  rfl

/-- 中文说明：Truth 与 Judgment 的分层见证载体。 -/
structure TruthJudgment where
  truth : Truth
  judgment : Judgment

/-- 中文证明：Judgment=不成立 不强制 Truth=false——存在真值为真而不成立的
记录（冻结条款二；类型层见证，不涉规范内容）。 -/
theorem judgment_notEstablished_does_not_force_truth_false :
    ∃ x : TruthJudgment,
      x.truth = true ∧
      x.judgment = Judgment.notEstablished := by
  exact ⟨
    {
      truth := true
      judgment := Judgment.notEstablished
    },
    rfl,
    rfl
  ⟩

/-- 中文说明：R_t 的关系整体（共同约束结构见 LegalModelV2.Relation）。 -/
structure RelationalState (Rel : Type) where
  relations : Set Rel
  sameLoss : Rel → Rel → Prop
  exclusive : Rel → Rel → Prop
  commonReduction : Rel → Rel → Prop

/-- 中文说明：B_t = (R_t, K_{e,t})；K 是候选状态集合（冻结条款一）。 -/
structure KernelState (R K : Type) where
  R_t : R
  K_et : Set K

/-!
裁判事件用归纳类型编码（冻结条款四）：非形成性构造子天然没有携带
nextR 的字段，比构造期校验更强——确认性裁判在类型层就无法创造关系。
-/

inductive JudgmentEvent (R : Type) where
  | confirmatory (judgment : Judgment)
  | constitutive (judgment : Judgment) (nextR : R)
  | performance (judgment : Judgment)
  | proceduralBinding (judgment : Judgment)

def eventEffectType {R : Type} :
    JudgmentEvent R → EffectType
  | .confirmatory _ => .confirmatory
  | .constitutive _ _ => .constitutive
  | .performance _ => .performance
  | .proceduralBinding _ => .proceduralBinding

/-- 中文说明：R_{t+1} = T(R_t, EffectType(JudgmentEvent))；仅形成性裁判
转移实体状态（冻结条款四）。 -/
def transfer {R K : Type}
    (state : KernelState R K) :
    JudgmentEvent R → KernelState R K
  | .confirmatory _ => state
  | .constitutive _ nextR =>
      {
        state with
        R_t := nextR
      }
  | .performance _ => state
  | .proceduralBinding _ => state

theorem transfer_confirmatory_identity {R K : Type}
    (state : KernelState R K)
    (judgment : Judgment) :
    transfer state (.confirmatory judgment) = state :=
  rfl

theorem transfer_performance_identity {R K : Type}
    (state : KernelState R K)
    (judgment : Judgment) :
    transfer state (.performance judgment) = state :=
  rfl

theorem transfer_proceduralBinding_identity {R K : Type}
    (state : KernelState R K)
    (judgment : Judgment) :
    transfer state (.proceduralBinding judgment) = state :=
  rfl

theorem transfer_constitutive_updates_R {R K : Type}
    (state : KernelState R K)
    (judgment : Judgment)
    (nextR : R) :
    (transfer state (.constitutive judgment nextR)).R_t = nextR :=
  rfl

theorem transfer_constitutive_preserves_K {R K : Type}
    (state : KernelState R K)
    (judgment : Judgment)
    (nextR : R) :
    (transfer state (.constitutive judgment nextR)).K_et = state.K_et :=
  rfl

/-- 中文说明：证据更新只收窄 K（子集前提类型化），R 原样返回（冻结条款四）。 -/
def narrowCandidates {R K : Type}
    (state : KernelState R K)
    (nextK : Set K)
    (_subset : nextK ⊆ state.K_et) :
    KernelState R K :=
  {
    R_t := state.R_t
    K_et := nextK
  }

theorem narrowCandidates_preserves_R {R K : Type}
    (state : KernelState R K)
    (nextK : Set K)
    (subset : nextK ⊆ state.K_et) :
    (narrowCandidates state nextK subset).R_t = state.R_t :=
  rfl

theorem narrowCandidates_is_subset {R K : Type}
    (state : KernelState R K)
    (nextK : Set K)
    (subset : nextK ⊆ state.K_et) :
    (narrowCandidates state nextK subset).K_et ⊆ state.K_et :=
  subset

/-- 中文说明：求值只出被问的问题（冻结条款三）。 -/
def evalBatch {Q D : Type}
    (asked : List (Question Q × EvalResult D)) :
    List (Question Q × EvalResult D) :=
  asked

theorem evalBatch_only_returns_asked_questions {Q D : Type}
    (asked : List (Question Q × EvalResult D)) :
    evalBatch asked = asked :=
  rfl

/-- 中文说明：程序判断到实体判断不存在自动派生通道（冻结条款三）。 -/
def autoSubstantiveJudgment
    (_proceduralJudgment : Judgment) :
    Option Judgment :=
  none

theorem procedural_judgment_does_not_auto_create_substantive
    (judgment : Judgment) :
    autoSubstantiveJudgment judgment = none :=
  rfl

/-!
规范版本选择（冻结条款六）的两版本特例化：factsTime 取自 H，
t 只做下界校验——t 单独永不决定版本。Python 侧 NormVersion 列表
选择器（theory/spec/canonical_v2/kernel.py::applicable_norm）的
一般化留后续，本特例钉死同两条纪律。
-/

structure EventHistory where
  eventTimes : List Nat
  factTime : Nat
deriving DecidableEq, Repr

def applicableNorm
    (earlyNorm lateNorm cutoff : Nat)
    (history : EventHistory)
    (t : Nat) :
    Option Nat :=
  if history.factTime ≤ t then
    if history.factTime < cutoff then
      some earlyNorm
    else
      some lateNorm
  else
    none

/-- 中文证明：同一 t、不同 H 可以得到不同版本——H 参与决定，t 单独
不决定版本（冻结条款六）。 -/
theorem applicableNorm_t_not_independent :
    applicableNorm
        100
        200
        10
        {
          eventTimes := [3, 5]
          factTime := 5
        }
        20
      ≠
    applicableNorm
        100
        200
        10
        {
          eventTimes := [3, 15]
          factTime := 15
        }
        20 := by
  decide

/-- 中文证明：t 早于事实时 fail-closed（返回 none）。 -/
theorem applicableNorm_fails_closed_when_t_precedes_fact :
    applicableNorm
        100
        200
        10
        {
          eventTimes := [3, 21]
          factTime := 21
        }
        20
      =
    none := by
  decide

/-!
未决窄化（冻结条款七）：未决结论必须携带四类规则穷尽的证明；
三外衣是派生分析类型（冻结条款八）。
-/

structure Exhaustion where
  burdenRulesExhausted : Prop
  presumptionRulesExhausted : Prop
  obstructionRulesExhausted : Prop
  terminalRulesExhausted : Prop

def FullyExhausted
    (state : Exhaustion) :
    Prop :=
  state.burdenRulesExhausted ∧
  state.presumptionRulesExhausted ∧
  state.obstructionRulesExhausted ∧
  state.terminalRulesExhausted

inductive NarrowResult
    (state : Exhaustion) where
  | decided (judgment : Judgment)
  | undetermined (proof : FullyExhausted state)

inductive DerivedAnalysisKind where
  | probability
  | behavior
  | comparison
deriving DecidableEq, Repr

structure DerivedAnalysis (Payload : Type) where
  kind : DerivedAnalysisKind
  payload : Payload

end JurisLean.KernelV3
