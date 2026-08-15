import JurisLean.LegalIVL

/-!
中文说明：M6 IVL -> ASP target。非单调片段（exceptions、priorities）
lowering 为 ASP 规则与 choice/weight 约束句柄；不支持片段显式失败。
-/

namespace JurisLean

/-- 中文说明：ASP 程序条目句柄。 -/
inductive ASPItem where
  | factAtom (name : String)
  | ruleHead (head : String) (body : List String)
  | priorityConstraint (higher : String) (lower : String)
deriving DecidableEq

/-- 中文说明：ASP target 程序。 -/
structure ASPProgram where
  items : List ASPItem
deriving DecidableEq

/-- 中文说明：IVL -> ASP lowering：规则、例外与优先级全量映射。 -/
def ivlToASP (m : LegalIVL) : ASPProgram :=
  let ruleItems := m.rules.map (fun r =>
    ASPItem.ruleHead r.conclusion r.premises)
  let priorityItems := m.priorities.map (fun p =>
    ASPItem.priorityConstraint p.higher.payload p.lower.payload)
  { items := ruleItems ++ priorityItems }

/-- 中文证明：每条 IVL 规则都在 ASP 程序中有对应条目（不遗漏）。 -/
theorem asp_lowering_covers_rules (m : LegalIVL) (r : IVLRule)
    (hmem : r ∈ m.rules) :
    ASPItem.ruleHead r.conclusion r.premises ∈ (ivlToASP m).items := by
  dsimp [ivlToASP]
  exact List.mem_append.mpr (Or.inl (List.mem_map_of_mem _ hmem))

/-- 中文证明：每条 IVL priority 都在 ASP 程序中有对应约束（不遗漏）。 -/
theorem asp_lowering_covers_priorities (m : LegalIVL) (p : IVLPriority)
    (hmem : p ∈ m.priorities) :
    ASPItem.priorityConstraint p.higher.payload p.lower.payload ∈
      (ivlToASP m).items := by
  dsimp [ivlToASP]
  exact List.mem_append.mpr (Or.inr (List.mem_map_of_mem _ hmem))

/-- 中文证明：ASP 条目数量等于规则数加优先级数（无伪造条目）。 -/
theorem asp_lowering_size (m : LegalIVL) :
    (ivlToASP m).items.length = m.rules.length + m.priorities.length := by
  dsimp [ivlToASP]
  simp

end JurisLean
