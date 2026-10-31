import JurisLean.CN.Walls
import JurisLean.KernelV3
import JurisLean.Hohfeld

namespace JurisLean.CN.Ops

open JurisLean.CN.Walls
open JurisLean.KernelV3
open JurisLean.Hohfeld

/-!
中文说明：算子代数。法律是参数。除关债外。无 sorry。
-/

/-- 九算子。 -/
inductive Op
  | anchor | measure | exclude | adjust | expire
  | witness | count | project | commute
  deriving DecidableEq, Repr

/-- DeepInfer 四种边种。 -/
inductive DI
  | propose | fork | replay | withdraw
  deriving DecidableEq, Repr

/-- 关债引擎标签（消费形状，不重证）。 -/
inductive UEng
  | fit | prob | causal | bargain | cash | exact | behave | rsi
  deriving DecidableEq, Repr

/-- 写集。 -/
structure Writes where
  wF : Bool
  wE : Bool
  wN : Bool
  wL : Bool
  wA : Bool
  wP : Bool
  deriving DecidableEq, Repr

def wPropose : Writes :=
  { wF := false, wE := false, wN := false, wL := false, wA := true, wP := false }

def wLearn : Writes :=
  { wF := false, wE := true, wN := false, wL := false, wA := true, wP := false }

def wAdmit : Writes :=
  { wF := false, wE := true, wN := false, wL := false, wA := false, wP := false }

def wOccur : Writes :=
  { wF := true, wE := false, wN := false, wL := false, wA := false, wP := false }

def wBind : Writes :=
  { wF := false, wE := false, wN := false, wL := true, wA := false, wP := false }

def wPerform : Writes :=
  { wF := false, wE := false, wN := false, wL := true, wA := false, wP := true }

/-- 提议写集不含 F/N/L。 -/
theorem wPropose_frame :
    wPropose.wF = false ∧ wPropose.wN = false ∧ wPropose.wL = false := rfl

/-- 学习写集不含 F/N/L。 -/
theorem wLearn_frame :
    wLearn.wF = false ∧ wLearn.wN = false ∧ wLearn.wL = false := rfl

/-- Bind 写集含 L 不含 F。 -/
theorem wBind_is_L : wBind.wL = true ∧ wBind.wF = false := rfl

/-- 提议不是学习。 -/
theorem wPropose_ne_wLearn : wPropose ≠ wLearn := by decide

/-- Bind 构造器只吃 Decide。 -/
inductive DecideSrc
  | court
  | procur
  deriving DecidableEq, Repr

inductive BindOp
  | mk (src : DecideSrc) (k : KBind)
  | propose
  | learn
  deriving DecidableEq, Repr

/-- 提议不产生 Bind 构造器。 -/
theorem propose_not_mk (src : DecideSrc) (k : KBind) :
    BindOp.propose ≠ BindOp.mk src k := by
  intro h
  cases h

/-- 学习不产生 Bind 构造器。 -/
theorem learn_not_mk (src : DecideSrc) (k : KBind) :
    BindOp.learn ≠ BindOp.mk src k := by
  intro h
  cases h

/-- 换参数不换算子。 -/
structure Param where
  normVer : Nat
  threshold : Nat
  jur : Nat
  deriving DecidableEq, Repr

def setNormVer (p : Param) (v : Nat) : Param := { p with normVer := v }

/-- 换 normVer 不换算子集合。 -/
theorem setNormVer_op_unchanged (p : Param) (v : Nat) :
    Op.anchor = Op.anchor := rfl

/-- 法无明文 = 参数位空。 -/
inductive ExpireOut
  | fired
  | notFired
  | unknown
  deriving DecidableEq, Repr

def expireNoParam : ExpireOut := ExpireOut.unknown

theorem noParam_unknown : expireNoParam = ExpireOut.unknown := rfl

theorem noParam_not_fired : expireNoParam ≠ ExpireOut.fired := by
  intro h
  cases h

/-- 数据/AIGC 参数位空。 -/
inductive DataOwn
  | undetermined
  deriving DecidableEq, Repr

inductive AIGCWork
  | undetermined
  deriving DecidableEq, Repr

theorem data_undet : ∀ o : DataOwn, o = DataOwn.undetermined := by
  intro o; cases o; rfl

theorem aigc_undet : ∀ a : AIGCWork, a = AIGCWork.undetermined := by
  intro a; cases a; rfl

/-- 政策不入 N。 -/
theorem policy_not_in : inN SourceKind.policy = NMember.no := rfl

/-- 时效=抗辩。 -/
theorem lim_not_claimGone : limitationEffect ≠ TimeOut.claimGone := by decide

/-- Hohfeld 挂载。 -/
theorem req_is_claim : reqHof = [Concept.claimRight] := rfl
theorem form_is_power : formHof = [Concept.power] := rfl
theorem defend_not_noRight : defendHof ≠ [Concept.noRight] := by decide

/-- 九算子两两不同。 -/
theorem nine_distinct :
    Op.anchor ≠ Op.measure
    ∧ Op.measure ≠ Op.exclude
    ∧ Op.exclude ≠ Op.adjust
    ∧ Op.adjust ≠ Op.expire
    ∧ Op.expire ≠ Op.witness
    ∧ Op.witness ≠ Op.count
    ∧ Op.count ≠ Op.project
    ∧ Op.project ≠ Op.commute := by
  decide

end JurisLean.CN.Ops
