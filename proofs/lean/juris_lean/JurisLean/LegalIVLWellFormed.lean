import JurisLean.LegalIVL

/-!
中文说明：M6 Legal-IVL well-formedness。attack 必须携带非空输入
witness；norm 引用的规则必须存在；guard 约束必须显式。
-/

namespace JurisLean

/-- 中文说明：IVL 规则 id 集合。 -/
def ivlRuleIds (m : LegalIVL) : List (LegalId .rule) :=
  m.rules.map (fun r => r.id)

/-- 中文说明：IVL well-formedness。 -/
def legalIVLWellFormed (m : LegalIVL) : Prop :=
  (∀ a ∈ m.attacks, a.inputWitness ≠ "") ∧
    (∀ n ∈ m.norms, n.ruleRef ∈ ivlRuleIds m) ∧
      (∀ g ∈ m.guards, g.constraintText ≠ "")

/-- 中文证明：空 witness 的 attack 违反 IVL well-formedness。 -/
theorem empty_witness_attack_breaks_ivl_wf {m : LegalIVL}
    {a : IVLAttackSpec} (hmem : a ∈ m.attacks) (hwit : a.inputWitness = "") :
    ¬ legalIVLWellFormed m := by
  intro hwf
  exact hwf.1 a hmem hwit

/-- 中文证明：引用未知规则的 norm 违反 IVL well-formedness。 -/
theorem unknown_rule_norm_breaks_ivl_wf {m : LegalIVL}
    {n : IVLNorm} (hmem : n ∈ m.norms) (habsent : n.ruleRef ∉ ivlRuleIds m) :
    ¬ legalIVLWellFormed m := by
  intro hwf
  exact habsent (hwf.2.1 n hmem)

/-- 中文证明：空约束的 guard 违反 IVL well-formedness。 -/
theorem empty_guard_breaks_ivl_wf {m : LegalIVL}
    {g : IVLGuard} (hmem : g ∈ m.guards) (hempty : g.constraintText = "") :
    ¬ legalIVLWellFormed m := by
  intro hwf
  exact hwf.2.2 g hmem hempty

/-- 中文证明：well-formed IVL 的每个 attack 都有 witness。 -/
theorem well_formed_ivl_attacks_witnessed {m : LegalIVL}
    (hwf : legalIVLWellFormed m) (a : IVLAttackSpec) (hmem : a ∈ m.attacks) :
    a.inputWitness ≠ "" :=
  hwf.1 a hmem

end JurisLean
