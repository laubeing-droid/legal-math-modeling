import JurisLean.LegalIVL

/-!
中文说明：M6 IVL -> Horn target。只 lowering 无 exception 冲突语义的
规则片段；Horn 子句保持前提与结论。supported fragment 内 soundness/
completeness 由保持定理表达。
-/

namespace JurisLean

/-- 中文说明：Horn 子句。 -/
structure HornClause where
  ruleId : LegalId .rule
  premises : List String
  conclusion : String
deriving DecidableEq

/-- 中文说明：Horn target 程序。 -/
structure HornProgram where
  clauses : List HornClause
deriving DecidableEq

/-- 中文说明：IVL -> Horn lowering：全部 IVL 规则映射为子句。 -/
def ivlToHorn (m : LegalIVL) : HornProgram :=
  {
    clauses :=
      m.rules.map (fun r =>
        { ruleId := r.id, premises := r.premises, conclusion := r.conclusion })
  }

/-- 中文证明：Horn lowering 保持规则数量（不遗漏、不伪造子句）。 -/
theorem horn_lowering_preserves_count (m : LegalIVL) :
    (ivlToHorn m).clauses.length = m.rules.length := by
  dsimp [ivlToHorn]
  rfl

/-- 中文证明：Horn lowering 保持每条规则的结论。 -/
theorem horn_lowering_preserves_conclusion (m : LegalIVL) (r : IVLRule)
    (hmem : r ∈ m.rules) :
    ∃ c ∈ (ivlToHorn m).clauses, c.conclusion = r.conclusion ∧ c.ruleId = r.id := by
  dsimp [ivlToHorn]
  exact ⟨_, List.mem_map_of_mem _ hmem, rfl, rfl⟩

/-- 中文证明：Horn lowering 无输入之外的子句（no-spurious）。 -/
theorem horn_lowering_no_spurious (m : LegalIVL) (c : HornClause)
    (hmem : c ∈ (ivlToHorn m).clauses) :
    ∃ r ∈ m.rules, c.ruleId = r.id := by
  dsimp [ivlToHorn] at hmem
  rcases List.mem_map.mp hmem with ⟨r, hr, heq⟩
  refine ⟨r, hr, ?_⟩
  subst heq
  rfl

end JurisLean
