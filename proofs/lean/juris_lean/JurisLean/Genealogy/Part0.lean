import JurisLean.LegalModelV2

/-!
Genealogy Part0 — L0 / cross-cutting structural disciplines.
These declarations formalize only structure and machine-checkable discipline.
They do not assert substantive legal correctness.
-/

namespace JurisLean.Genealogy.Part0

namespace Util

def present {α : Type} : Option α → Bool
  | none => false
  | some _ => true

def allStringsIn (required satisfied : List String) : Bool :=
  required.all (fun x => satisfied.contains x)

def natMax (a b : Nat) : Nat :=
  if a < b then b else a

def natMin (a b : Nat) : Nat :=
  if a < b then a else b

end Util

namespace P002

structure DefinitionRecord where
  definitionId : String
  intensionId : String
  extensionIds : List String
deriving DecidableEq, Repr

structure Concept where
  definition : DefinitionRecord
  calculusRuleId : String
deriving DecidableEq, Repr

def identity (c : Concept) : String × String :=
  (c.definition.definitionId, c.calculusRuleId)

def sameConcept (a b : Concept) : Bool :=
  decide (identity a = identity b)

theorem same_pair_same_concept (c : Concept) : sameConcept c c = true := by
  simp [sameConcept]
-- [定义展开] 置信：`identity c = identity c` 由反身性直接化简。

theorem different_pair_different_concept (a b : Concept)
    (h : identity a ≠ identity b) : sameConcept a b = false := by
  simp [sameConcept, h]
-- [定义展开] 置信：唯一分支条件正是参数 `h`。

end P002

namespace P003

structure CanonicalTermSlot where
  jurisdictionId : String
  definitionId : String
  canonicalTerm : Option String
deriving DecidableEq, Repr

structure Translation where
  sourceTerm : String
  targetTerm : String
  definitionId : String
deriving DecidableEq, Repr

def translatedDefinitionId (t : Translation) : String := t.definitionId

theorem translation_preserves_definition_id (t : Translation) :
    translatedDefinitionId t = t.definitionId := rfl
-- [rfl] 置信：翻译对象只投影既有 definition id，不生成新意义。

theorem canonical_slot_is_single_valued (s : CanonicalTermSlot) :
    s.canonicalTerm = s.canonicalTerm := rfl
-- [rfl] 置信：单值性由字段类型编码；定理只记录该投影不发生分叉。

end P003

namespace P009

structure VersionedConcept where
  conceptId : String
  version : Nat
deriving DecidableEq, Repr

def registerNextVersion (current candidate : Nat) : Option Nat :=
  if current < candidate then some candidate else none

theorem strictly_increasing_version_enters (current candidate : Nat)
    (h : current < candidate) :
    registerNextVersion current candidate = some candidate := by
  simp [registerNextVersion, h]
-- [定义展开] 置信：分支条件由 `h` 精确决定。

theorem nonincreasing_version_is_outside (current candidate : Nat)
    (h : ¬ current < candidate) :
    registerNextVersion current candidate = none := by
  simp [registerNextVersion, h]
-- [定义展开] 置信：拒绝分支与 `h` 完全同构。

end P009

namespace P010

inductive InfoPath where
  | identification
  | relation
deriving DecidableEq, Repr

structure PersonalInfo where
  itemId : String
  identifiedByPath : Bool
  relatedByPath : Bool
  anonymized : Bool
  sensitive : Bool
  informed : Bool
  expressIntent : Bool
  lawfulPurpose : Bool
deriving DecidableEq, Repr

def isPersonal (i : PersonalInfo) : Bool :=
  (i.identifiedByPath || i.relatedByPath) && !i.anonymized

def anonymize (i : PersonalInfo) : PersonalInfo :=
  { i with anonymized := true }

def tripleConsentPresent (i : PersonalInfo) : Bool :=
  i.informed && i.expressIntent && i.lawfulPurpose

def sensitiveProcessingAllowed (i : PersonalInfo) : Bool :=
  isPersonal i && i.sensitive && tripleConsentPresent i

theorem anonymization_exits_personal_set (i : PersonalInfo) :
    isPersonal (anonymize i) = false := by
  simp [isPersonal, anonymize]
-- [定义展开] 置信：匿名化后 `!true = false`，合取恒为 false。

theorem sensitive_triple_consent_positive :
    sensitiveProcessingAllowed
      { itemId := "synthetic"
        identifiedByPath := true
        relatedByPath := false
        anonymized := false
        sensitive := true
        informed := true
        expressIntent := true
        lawfulPurpose := true } = true := rfl
-- [rfl] 置信：全部 Bool 字面量定义归约即可。

end P010

namespace P036

inductive RelationKind where
  | obligational
  | real
  | family
  | labor
  | inheritance
deriving DecidableEq, Repr

inductive ClassificationStatus where
  | ok
  | mismatch
deriving DecidableEq, Repr

def classifyRelation
    (kind : RelationKind) (againstPerson againstWorld : Bool) : ClassificationStatus :=
  match kind with
  | .obligational => match againstPerson with | true => .ok | false => .mismatch
  | .real => match againstWorld with | true => .ok | false => .mismatch
  | .family => .ok
  | .labor => .ok
  | .inheritance => .ok

theorem obligational_signature_mismatch :
    classifyRelation .obligational false true = .mismatch := rfl
-- [rfl] 置信：构造子与 Bool 分支均为字面量归约。

theorem real_signature_mismatch :
    classifyRelation .real true false = .mismatch := rfl
-- [rfl] 置信：构造子与 Bool 分支均为字面量归约。

end P036

namespace P012

inductive LimitationCause where
  | commence
  | suspend
  | interrupt
  | extend
deriving DecidableEq, Repr

structure LimitationClock where
  running : Bool
  elapsedDays : Nat
  commencedDay : Option Nat
deriving DecidableEq, Repr

def applyLimitationCause
    (clock : LimitationClock) (cause : LimitationCause) (day : Nat) : LimitationClock :=
  match cause with
  | .commence =>
      match clock.commencedDay with
      | some _ => clock
      | none => { running := true, elapsedDays := 0, commencedDay := some day }
  | .suspend =>
      match clock.running with
      | true => { clock with running := false }
      | false => clock
  | .interrupt =>
      match clock.commencedDay with
      | none => clock
      | some _ => { running := true, elapsedDays := 0, commencedDay := some day }
  | .extend => clock

theorem interruption_restarts
    (running : Bool) (elapsed oldDay newDay : Nat) :
    applyLimitationCause
      { running := running, elapsedDays := elapsed, commencedDay := some oldDay }
      .interrupt newDay
      = { running := true, elapsedDays := 0, commencedDay := some newDay } := rfl
-- [rfl] 置信：`interrupt` + `some _` 唯一进入重启分支。

theorem second_commencement_is_identity
    (running : Bool) (elapsed startDay secondDay : Nat) :
    applyLimitationCause
      { running := running, elapsedDays := elapsed, commencedDay := some startDay }
      .commence secondDay
      = { running := running, elapsedDays := elapsed, commencedDay := some startDay } := rfl
-- [rfl] 置信：`commence` 遇到 `some _` 直接返回原状态。

end P012

end JurisLean.Genealogy.Part0
