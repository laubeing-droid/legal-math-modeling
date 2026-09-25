import JurisLean.Genealogy.Part1

namespace JurisLean.Genealogy.Part2

namespace P029

inductive BindingKind where
  | primary
  | secondary
deriving DecidableEq, Repr

structure NormBinding where
  kind : BindingKind
  normId : String
  attachesTo : Option String
deriving DecidableEq, Repr

def secondaryAttaches (violatedPrimary : Option String) (n : NormBinding) : Bool :=
  match violatedPrimary with
  | none => false
  | some p =>
      match n.kind, n.attachesTo with
      | .secondary, some q => decide (p = q)
      | _, _ => false

theorem secondary_without_primary_violation_is_false (n : NormBinding) :
    secondaryAttaches none n = false := rfl
-- [rfl] 置信：函数先匹配 violatedPrimary，none 直接返回 false。

theorem matching_secondary_attachment :
    secondaryAttaches (some "P")
      { kind := .secondary, normId := "S", attachesTo := some "P" } = true := by
  decide
-- [decide] 置信：有限枚举与字符串字面量相等性均可计算。

end P029

namespace P034

structure AnspruchBasis where
  basisId : String
  requiredElements : List String
deriving DecidableEq, Repr

def findBasis : List AnspruchBasis → String → Option AnspruchBasis
  | [], _ => none
  | b :: bs, basisId =>
      if h : b.basisId = basisId then some b else findBasis bs basisId

def basisSatisfied (b : AnspruchBasis) (satisfied : List String) : Prop :=
  Part0.Util.allStringsIn b.requiredElements satisfied = true

def claimAvailable
    (bases : List AnspruchBasis) (basisId : String) (satisfied : List String) : Option Bool :=
  match findBasis bases basisId with
  | none => none
  | some b => some (Part0.Util.allStringsIn b.requiredElements satisfied)

theorem claim_available_complete_iff
    (b : AnspruchBasis) (rest : List AnspruchBasis) (satisfied : List String) :
    basisSatisfied b satisfied ↔
      claimAvailable (b :: rest) b.basisId satisfied = some true := by
  simp [basisSatisfied, claimAvailable, findBasis]
-- [定义展开] 置信：head basis 必命中；`some x = some true` 被 simp 化为 `x = true`。

theorem unregistered_basis_unknown (basisId : String) (satisfied : List String) :
    claimAvailable [] basisId satisfied = none := rfl
-- [rfl] 置信：空注册表直接命中 findBasis 基例。

end P034

namespace P035

inductive AgencyKind where
  | agency
  | representation
  | impersonation
deriving DecidableEq, Repr

inductive Attribution where
  | principal
  | principalIfInScope
  | none
deriving DecidableEq, Repr

def effectAttribution
    (kind : AgencyKind) (withinScope ratified : Bool) : Attribution :=
  match kind with
  | .agency => .principal
  | .representation =>
      match withinScope with
      | true => .principalIfInScope
      | false => .none
  | .impersonation =>
      match ratified with
      | true => .principal
      | false => .none

theorem agency_attributes_principal (scope ratified : Bool) :
    effectAttribution .agency scope ratified = .principal := rfl
-- [rfl] 置信：agency 构造子直接返回 principal。

theorem representation_outside_scope_none (ratified : Bool) :
    effectAttribution .representation false ratified = .none := rfl
-- [rfl] 置信：representation/false 分支直接归约。

theorem impersonation_ratified_principal (scope : Bool) :
    effectAttribution .impersonation scope true = .principal := rfl
-- [rfl] 置信：impersonation/true 分支直接归约。

end P035

namespace P038

structure CompetitionRelation where
  competitiveInterest : Bool
  competitiveRelation : Bool
  competitiveLoss : Bool
deriving DecidableEq, Repr

def established (c : CompetitionRelation) : Bool :=
  c.competitiveInterest && c.competitiveRelation && c.competitiveLoss

theorem competition_is_three_way_conjunction (c : CompetitionRelation) :
    established c =
      (c.competitiveInterest && c.competitiveRelation && c.competitiveLoss) := rfl
-- [rfl] 置信：定理右侧即定义体。

theorem all_three_true_establish :
    established
      { competitiveInterest := true, competitiveRelation := true,
        competitiveLoss := true } = true := rfl
-- [rfl] 置信：Bool 合取字面量归约。

end P038

end JurisLean.Genealogy.Part2
