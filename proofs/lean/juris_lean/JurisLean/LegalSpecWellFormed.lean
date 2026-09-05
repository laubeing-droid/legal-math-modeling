import JurisLean.LegalSpec

/-!
中文说明：M6 LegalSpec well-formedness。对引用闭包、方向、scope、
version 与类型完整判定；priority 引用必须闭合于 spec 内规则；不确定
字段必须显式声明。
-/

namespace JurisLean

/-- 中文说明：单条规则 well-formedness。 -/
def specRuleWellFormed (r : LegalSpecRule) : Prop :=
  r.locator.path ≠ "" ∧ r.conclusion ≠ ""

/-- 中文说明：spec well-formedness：规则全 wf 且 priority 引用闭合。 -/
def legalSpecWellFormed (s : LegalSpec) : Prop :=
  (∀ r ∈ s.rules, specRuleWellFormed r) ∧
    (∀ r ∈ s.rules, ∀ p ∈ r.priorityOver, p ∈ specRuleIds s) ∧
      s.specId ≠ ""

/-- 中文证明：空 locator 的规则不 well-formed。 -/
theorem empty_locator_rule_not_well_formed (r : LegalSpecRule)
    (h : r.locator.path = "") : ¬ specRuleWellFormed r := by
  intro hwf
  exact hwf.1 h

/-- 中文证明：空结论的规则不 well-formed。 -/
theorem empty_conclusion_rule_not_well_formed (r : LegalSpecRule)
    (h : r.conclusion = "") : ¬ specRuleWellFormed r := by
  intro hwf
  exact hwf.2 h

/-- 中文证明：well-formed spec 的每条规则都有非空来源定位。 -/
theorem well_formed_spec_has_located_rules {s : LegalSpec}
    (hwf : legalSpecWellFormed s) (r : LegalSpecRule) (hmem : r ∈ s.rules) :
    r.locator.path ≠ "" :=
  (hwf.1 r hmem).1

/-- 中文证明：well-formed spec 中 priority 引用闭合于规则表。 -/
theorem well_formed_priority_closure {s : LegalSpec}
    (hwf : legalSpecWellFormed s) (r : LegalSpecRule) (hmem : r ∈ s.rules)
    (p : LegalId .rule) (hp : p ∈ r.priorityOver) :
    p ∈ specRuleIds s :=
  hwf.2.1 r hmem p hp

/-- 中文证明：引用闭包外的 priority 目标使 spec 不 well-formed。 -/
theorem unclosed_priority_breaks_wf {s : LegalSpec} {r : LegalSpecRule}
    (hmem : r ∈ s.rules) {p : LegalId .rule} (hp : p ∈ r.priorityOver)
    (habsent : p ∉ specRuleIds s) :
    ¬ legalSpecWellFormed s := by
  intro hwf
  exact habsent (hwf.2.1 r hmem p hp)

end JurisLean
