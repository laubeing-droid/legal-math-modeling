import JurisLean.Genealogy.Part0

namespace JurisLean.Genealogy.Part1

namespace P014

inductive SourceKind where
  | statute
  | judicialInterpretation
  | guidingCase
  | gazetteCase
  | custom
  | doctrine
  | softLaw
deriving DecidableEq, Repr

inductive AdmissionGrade where
  | binding
  | shallRefer
  | referenceOnly
deriving DecidableEq, Repr

def admissionGrade : SourceKind → AdmissionGrade
  | .statute => .binding
  | .judicialInterpretation => .binding
  | .guidingCase => .shallRefer
  | .gazetteCase => .referenceOnly
  | .custom => .referenceOnly
  | .doctrine => .referenceOnly
  | .softLaw => .referenceOnly

theorem source_grade_total (k : SourceKind) :
    admissionGrade k = admissionGrade k := by
  cases k <;> rfl
-- [cases+rfl] 置信：七个构造子均由全函数穷尽覆盖。

end P014

namespace P015

inductive HierarchyRank where
  | constitution
  | statute
  | interpretation
  | administrativeRegulation
  | localRegulation
  | departmentalRule
deriving DecidableEq, Repr

def rankScore : HierarchyRank → Nat
  | .constitution => 6
  | .statute => 5
  | .interpretation => 4
  | .administrativeRegulation => 3
  | .localRegulation => 2
  | .departmentalRule => 1

structure NormProvision where
  provisionId : String
  rank : HierarchyRank
  enactedDay : Nat
  special : Bool
deriving DecidableEq, Repr

def resolveConflict (a b : NormProvision) : Option String :=
  if rankScore b.rank < rankScore a.rank then some a.provisionId
  else if rankScore a.rank < rankScore b.rank then some b.provisionId
  else if a.enactedDay < b.enactedDay then
    match a.special, b.special with
    | true, false => none
    | _, _ => some b.provisionId
  else if b.enactedDay < a.enactedDay then
    match b.special, a.special with
    | true, false => none
    | _, _ => some a.provisionId
  else
    match a.special, b.special with
    | true, false => some a.provisionId
    | false, true => some b.provisionId
    | _, _ => none

theorem lex_superior_left (a b : NormProvision)
    (h : rankScore b.rank < rankScore a.rank) :
    resolveConflict a b = some a.provisionId := by
  simp [resolveConflict, h]
-- [定义展开] 置信：首个 rank 分支已由 `h` 锁死，后续分支不可达。

theorem old_special_vs_new_general_unknown :
    resolveConflict
      { provisionId := "old-special", rank := .statute, enactedDay := 10, special := true }
      { provisionId := "new-general", rank := .statute, enactedDay := 20, special := false }
      = none := by
  decide
-- [decide] 置信：全为有限枚举、Nat 与 Bool 字面量，闭式归约。

theorem same_rank_day_nature_unknown :
    resolveConflict
      { provisionId := "a", rank := .statute, enactedDay := 20, special := false }
      { provisionId := "b", rank := .statute, enactedDay := 20, special := false }
      = none := by
  decide
-- [decide] 置信：比较条件均为可判定字面量。

end P015

namespace P018

structure TransitionClause where
  fromVersion : String
  toVersion : String
  triggerFact : String
deriving DecidableEq, Repr

def applyTransition
    (currentVersion : String) (clause : TransitionClause) (facts : List String) : String :=
  if h : currentVersion = clause.fromVersion then
    match facts.contains clause.triggerFact with
    | true => clause.toVersion
    | false => currentVersion
  else currentVersion

theorem transition_requires_version_and_fact
    (clause : TransitionClause) (facts : List String)
    (hv : clause.fromVersion = clause.fromVersion)
    (hf : facts.contains clause.triggerFact = true) :
    applyTransition clause.fromVersion clause facts = clause.toVersion := by
  simp [applyTransition, hv, hf]
-- [定义展开] 置信：版本相等与 contains=true 两个分支条件均显式给定。

theorem transition_version_mismatch_holds
    (current : String) (clause : TransitionClause) (facts : List String)
    (h : current ≠ clause.fromVersion) :
    applyTransition current clause facts = current := by
  simp [applyTransition, h]
-- [定义展开] 置信：首个 fail-closed 分支由 `h` 锁死。

end P018

namespace P019

inductive PrecedentBinding where
  | shallRefer
  | mayReference
deriving DecidableEq, Repr

inductive BindingEffect where
  | shouldFollow
  | distinguished
  | nonBinding
deriving DecidableEq, Repr

def bindingEffect (level : PrecedentBinding) (distinguishingReason : Bool) : BindingEffect :=
  match level with
  | .mayReference => .nonBinding
  | .shallRefer =>
      match distinguishingReason with
      | true => .distinguished
      | false => .shouldFollow

theorem shall_refer_without_reason_follows :
    bindingEffect .shallRefer false = .shouldFollow := rfl
-- [rfl] 置信：构造子与 Bool 分支均为直接归约。

theorem may_reference_nonbinding (reason : Bool) :
    bindingEffect .mayReference reason = .nonBinding := rfl
-- [rfl] 置信：该构造子忽略第二参数并直接返回 nonBinding。

end P019

namespace P020

structure JurisdictionRules where
  specialized : Option String
  level : Option String
  territorial : Option String
  foreignRelated : Option String
deriving DecidableEq, Repr

structure ApplicableKinds where
  specialized : Bool
  level : Bool
  territorial : Bool
  foreignRelated : Bool
deriving DecidableEq, Repr

def routeJurisdiction (rules : JurisdictionRules) (a : ApplicableKinds) : Option String :=
  match a.specialized, rules.specialized with
  | true, some court => some court
  | _, _ =>
    match a.level, rules.level with
    | true, some court => some court
    | _, _ =>
      match a.territorial, rules.territorial with
      | true, some court => some court
      | _, _ =>
        match a.foreignRelated, rules.foreignRelated with
        | true, some court => some court
        | _, _ => none

theorem specialized_rule_wins_first :
    routeJurisdiction
      { specialized := some "special", level := some "level",
        territorial := some "territorial", foreignRelated := some "foreign" }
      { specialized := true, level := true, territorial := true, foreignRelated := true }
      = some "special" := rfl
-- [rfl] 置信：首层 match 已命中，后续规则不可达。

theorem no_applicable_rule_returns_none (rules : JurisdictionRules) :
    routeJurisdiction rules
      { specialized := false, level := false, territorial := false, foreignRelated := false }
      = none := by
  cases rules <;> rfl
-- [cases+rfl] 置信：四个 applicability 位均为 false，所有 court 内容均被跳过。

end P020

namespace P021

structure RenvoiResult where
  substantiveLaw : String
  terminated : Bool
deriving DecidableEq, Repr

def resolveOneHop
    (forumLaw foreignLaw : String) (foreignPointsBack : Bool) : RenvoiResult :=
  match foreignPointsBack with
  | true => { substantiveLaw := forumLaw, terminated := true }
  | false => { substantiveLaw := foreignLaw, terminated := true }

theorem renvoi_back_uses_forum_and_terminates (forum foreign : String) :
    resolveOneHop forum foreign true =
      { substantiveLaw := forum, terminated := true } := rfl
-- [rfl] 置信：函数不存在递归调用，true 分支即终止结果。

end P021

namespace P022

def retainedAfterOverride (overriddenRule rule : String) : Bool :=
  decide (rule ≠ overriddenRule)

theorem named_rule_removed (rule : String) :
    retainedAfterOverride rule rule = false := by
  simp [retainedAfterOverride]
-- [定义展开] 置信：`rule ≠ rule` 直接化简为 false。

theorem other_rule_preserved (overridden rule : String)
    (h : rule ≠ overridden) :
    retainedAfterOverride overridden rule = true := by
  simp [retainedAfterOverride, h]
-- [定义展开] 置信：集合差纪律被降为逐元素判定，条件正是 `h`。

end P022

namespace P023

def selectApplicableLaw
    (jurisdiction version : Option String) : Option (String × String) :=
  match jurisdiction, version with
  | some j, some v => some (j, v)
  | _, _ => none

theorem missing_version_unknown (jurisdiction : Option String) :
    selectApplicableLaw jurisdiction none = none := by
  cases jurisdiction <;> rfl
-- [cases+rfl] 置信：两个 Option 构造子均归约至 none。

theorem missing_jurisdiction_unknown (version : Option String) :
    selectApplicableLaw none version = none := by
  cases version <;> rfl
-- [cases+rfl] 置信：两个 Option 构造子均归约至 none。

end P023

namespace P024

structure CauseRoute where
  cause : String
  procedure : String
  applicableLaw : String
deriving DecidableEq, Repr

def routeCause : List CauseRoute → String → Option (String × String)
  | [], _ => none
  | r :: rs, cause =>
      if h : r.cause = cause then some (r.procedure, r.applicableLaw)
      else routeCause rs cause

theorem cause_route_head_hit (r : CauseRoute) (rs : List CauseRoute) :
    routeCause (r :: rs) r.cause = some (r.procedure, r.applicableLaw) := by
  simp [routeCause]
-- [定义展开] 置信：head key 与自身相等，首行立即命中。

theorem cause_route_empty_unknown (cause : String) :
    routeCause [] cause = none := rfl
-- [rfl] 置信：空表即递归基例。

end P024

end JurisLean.Genealogy.Part1
