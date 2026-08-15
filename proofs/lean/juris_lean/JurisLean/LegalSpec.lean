import JurisLean.LegalIds

/-!
中文说明：M6 P07 LegalSpec：来源导向的 typed AST。完整保留 source
locator、条件、结论、模态、例外、许可 scope、优先级、解释选择与
不确定字段。来源结构（条/款/项层级与附件）由节点树承载，不接平面
文本。
-/

namespace JurisLean

/-- 中文说明：来源定位器（层级 + anchor）。 -/
structure SpecLocator where
  path : String
  anchor : String
deriving DecidableEq, Repr

/-- 中文说明：规范模态。 -/
inductive SpecModality where
  | obligation
  | prohibition
  | permission
  | constitutive
deriving DecidableEq, Repr

/-- 中文说明：来源节点：保留层级与正文边界。 -/
structure SpecNode where
  locator : SpecLocator
  nodeKind : String
  text : String
deriving DecidableEq

/-- 中文说明：typed 规则节点：LegalSpec 的核心条目。 -/
structure LegalSpecRule where
  id : LegalId .rule
  locator : SpecLocator
  modality : SpecModality
  conditions : List String
  conclusion : String
  exceptions : List String
  permissionScope : Option String
  priorityOver : List (LegalId .rule)
  interpretationChoice : String
  uncertainFields : List String
deriving DecidableEq

/-- 中文说明：LegalSpec：来源导向 typed AST。 -/
structure LegalSpec where
  specId : String
  version : SchemaVersion
  nodes : List SpecNode
  rules : List LegalSpecRule
deriving DecidableEq

/-- 中文说明：规则引用 closure：priorityOver 必须指向 spec 内规则。 -/
def specRuleIds (s : LegalSpec) : List (LegalId .rule) :=
  s.rules.map (fun r => r.id)

/-- 中文证明：规则 id 序列由规则表唯一决定。 -/
theorem spec_rule_ids_determined (s : LegalSpec) :
    specRuleIds s = s.rules.map (fun r => r.id) := rfl

/-- 中文证明：空规则表的 spec 不引用任何规则。 -/
theorem empty_spec_no_rule_references (specId : String) (version : SchemaVersion)
    (nodes : List SpecNode) (rid : LegalId .rule) :
    rid ∉ specRuleIds { specId := specId, version := version, nodes := nodes, rules := [] } := by
  simp [specRuleIds]

end JurisLean
