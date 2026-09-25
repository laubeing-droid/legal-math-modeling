import JurisLean.Genealogy.Part2
import Mathlib.Data.Finset.Basic

namespace JurisLean.Genealogy.Part3

namespace P042

structure EvidenceWeight where
  reliability : Nat
  integrity : Nat
  authenticity : Nat
deriving DecidableEq, Repr

def grade (w : EvidenceWeight) : Nat :=
  Nat.min w.reliability (Nat.min w.integrity w.authenticity)

theorem equal_factors_fixed (n : Nat) :
    grade { reliability := n, integrity := n, authenticity := n } = n := by
  simp [grade]
-- [定义展开] 置信：只依赖 `Nat.min` 的 simp 归约，不点名任何外部引理。

theorem weakest_factor_witness :
    grade { reliability := 80, integrity := 60, authenticity := 90 } = 60 := by
  decide
-- [decide] 置信：闭式 Nat.min 计算。

end P042

namespace P047

structure ButForCase where
  occurredOutcome : Option Bool
  nonOccurredOutcome : Option Bool
deriving DecidableEq, Repr

def butForTest (c : ButForCase) : Option Bool :=
  match c.occurredOutcome, c.nonOccurredOutcome with
  | some true, some false => some true
  | some _, some _ => some false
  | _, _ => none

theorem two_sided_but_for_true :
    butForTest { occurredOutcome := some true, nonOccurredOutcome := some false }
      = some true := rfl
-- [rfl] 置信：两侧 Option/Bool 构造子精确命中首分支。

theorem one_side_missing_unknown (other : Option Bool) :
    butForTest { occurredOutcome := none, nonOccurredOutcome := other } = none := by
  cases other <;> rfl
-- [cases+rfl] 置信：Option 两构造子都落入缺失分支。

end P047

namespace P048

structure ExemptionGround where
  groundId : String
  requiredElements : List String
deriving DecidableEq, Repr

def exempts (g : ExemptionGround) (satisfied : List String) : Bool :=
  Part0.Util.allStringsIn g.requiredElements satisfied

theorem exemption_requires_own_elements
    (g : ExemptionGround) (satisfied : List String) :
    exempts g satisfied = Part0.Util.allStringsIn g.requiredElements satisfied := rfl
-- [rfl] 置信：定理右侧即定义体。

theorem exemption_complete_witness :
    exempts { groundId := "G", requiredElements := ["a", "b"] }
      ["b", "a", "c"] = true := by
  decide
-- [decide] 置信：List.contains/List.all 对字符串字面量闭式计算。

end P048

namespace P049

structure FilingWindow where
  deadlineDay : Nat
  extendedForGoodCause : Bool
deriving DecidableEq, Repr

def evidenceAdmissible (filedDay : Nat) (w : FilingWindow) : Bool :=
  if filedDay ≤ w.deadlineDay then true else w.extendedForGoodCause

theorem good_cause_extension_admits (filed deadline : Nat) :
    evidenceAdmissible filed
      { deadlineDay := deadline, extendedForGoodCause := true } = true := by
  simp [evidenceAdmissible]
-- [定义展开] 置信：条件两支均化简为 true。

theorem late_without_good_cause_barred :
    evidenceAdmissible 11 { deadlineDay := 10, extendedForGoodCause := false } = false := by
  decide
-- [decide] 置信：Nat 次序与 Bool 字面量闭式计算。

end P049

namespace P050

inductive ExclusionKind where
  | illegallyObtained
  | violatesProcedure
  | unverifiableChain
deriving DecidableEq, Repr

def excluded : List ExclusionKind → Bool
  | [] => false
  | _ :: _ => true

theorem any_listed_illegality_excludes (k : ExclusionKind) (ks : List ExclusionKind) :
    excluded (k :: ks) = true := rfl
-- [rfl] 置信：非空列表只命中一个构造分支。

theorem empty_exclusion_list_does_not_exclude : excluded [] = false := rfl
-- [rfl] 置信：空列表基例。

end P050

namespace P051

structure FreeEvaluationBoundary {α : Type} (inputs : Finset α) where
  provenanceTag : String

def FreeEvaluationBoundary.supplied {α : Type} {inputs : Finset α}
    (_b : FreeEvaluationBoundary inputs) : Finset α := inputs

inductive BoundaryRecord where
  | kernelSuppliesInputsOnly
deriving DecidableEq, Repr

def FreeEvaluationBoundary.record {α : Type} {inputs : Finset α}
    (_b : FreeEvaluationBoundary inputs) : BoundaryRecord :=
  .kernelSuppliesInputsOnly

theorem boundary_inputs_complete {α : Type} (inputs : Finset α)
    (b : FreeEvaluationBoundary inputs) :
    b.supplied = inputs := rfl
-- [rfl] 置信：`supplied` 仅返回依赖参数 `inputs`。

theorem boundary_records_input_only {α : Type} {inputs : Finset α}
    (b : FreeEvaluationBoundary inputs) :
    b.record = .kernelSuppliesInputsOnly := rfl
-- [rfl] 置信：输出类型只有边界记录构造子，没有 Judgment/Relation 字段。

end P051

namespace P052

structure ElementTrace where
  element : String
  facts : List String
  evidence : List String
deriving DecidableEq, Repr

def traceReady (t : ElementTrace) : Bool :=
  !t.facts.isEmpty && !t.evidence.isEmpty

def hasReadyTrace (element : String) : List ElementTrace → Bool
  | [] => false
  | t :: ts =>
      if h : t.element = element then
        match traceReady t with
        | true => true
        | false => hasReadyTrace element ts
      else hasReadyTrace element ts

def mappingComplete (required : List String) (traces : List ElementTrace) : Bool :=
  required.all (fun e => hasReadyTrace e traces)

theorem mapping_complete_iff_all_required_traced
    (required : List String) (traces : List ElementTrace) :
    mappingComplete required traces = true ↔
      required.all (fun e => hasReadyTrace e traces) = true := rfl
-- [rfl] 置信：左侧定义体就是右侧“每要件均有 ready trace”的判定。

theorem mapping_complete_witness :
    mappingComplete ["E"]
      [{ element := "E", facts := ["F"], evidence := ["X"] }] = true := by
  decide
-- [decide] 置信：字符串、List 与 Bool 均闭式可判定。

end P052

namespace P094

structure AnchorRule where
  eventKey : String
deriving DecidableEq, Repr

structure TimedEvent where
  eventKey : String
  day : Nat
deriving DecidableEq, Repr

def lookupEvent : List TimedEvent → String → Option Nat
  | [], _ => none
  | e :: es, key =>
      if h : e.eventKey = key then some e.day else lookupEvent es key

def selectAnchor : List AnchorRule → List TimedEvent → Option Nat
  | [], _ => none
  | r :: rs, events =>
      match lookupEvent events r.eventKey with
      | some day => some day
      | none => selectAnchor rs events

theorem first_present_anchor_witness :
    selectAnchor
      [{ eventKey := "missing" }, { eventKey := "filing" }, { eventKey := "later" }]
      [{ eventKey := "filing", day := 12 }, { eventKey := "later", day := 20 }]
      = some 12 := by
  decide
-- [decide] 置信：有限表按定义顺序闭式扫描。

theorem empty_anchor_rules_unknown (events : List TimedEvent) :
    selectAnchor [] events = none := rfl
-- [rfl] 置信：空规则表即递归基例。

end P094

namespace P095

structure CommencementCell where
  periodKind : String
  eventKind : String
  ruleId : String
deriving DecidableEq, Repr

def lookupCommencement : List CommencementCell → String → String → Option String
  | [], _, _ => none
  | c :: cs, periodKind, eventKind =>
      if h1 : c.periodKind = periodKind then
        if h2 : c.eventKind = eventKind then some c.ruleId
        else lookupCommencement cs periodKind eventKind
      else lookupCommencement cs periodKind eventKind

theorem commencement_cell_hit :
    lookupCommencement
      [{ periodKind := "limitation", eventKind := "knowledge", ruleId := "R1" }]
      "limitation" "knowledge" = some "R1" := by
  decide
-- [decide] 置信：单元格两键均为字符串字面量相等。

theorem empty_commencement_matrix_unknown (p e : String) :
    lookupCommencement [] p e = none := rfl
-- [rfl] 置信：空矩阵基例。

end P095

end JurisLean.Genealogy.Part3
