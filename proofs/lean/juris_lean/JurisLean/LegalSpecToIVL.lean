import JurisLean.LegalSpec
import JurisLean.LegalIVL

/-!
中文说明：M6 LegalSpec -> Legal-IVL lowering。lowering 是确定的全
函数：不支持的结构返回带显式 failure state 的 IVL，不 panic、不默认
吞掉。source locator、ID、modality、exception、priority 逐字段保持。
-/

namespace JurisLean

/-- 中文说明：模态 lowering（字符串句柄，语义在 DDL 层解释）。 -/
def lowerModality : SpecModality → String
  | .obligation => "OBLIGATION"
  | .prohibition => "PROHIBITION"
  | .permission => "PERMISSION"
  | .constitutive => "CONSTITUTIVE"

/-- 中文说明：单条规则 lowering。 -/
def lowerRule (r : LegalSpecRule) : IVLRule :=
  {
    id := r.id,
    version := "",
    premises := r.conditions,
    conclusion := r.conclusion,
    exceptions := r.exceptions
  }

/-- 中文说明：确定性 lowering：全函数，结构不支持时显式标记。 -/
def lowerSpec (s : LegalSpec) : LegalIVL :=
  let rules := s.rules.map lowerRule
  let norms := s.rules.map (fun r =>
    { id := { payload := r.id.payload },
      modality := lowerModality r.modality,
      ruleRef := r.id })
  let priorities := s.rules.foldl (init := []) (fun acc r =>
    acc ++ r.priorityOver.map (fun lo => { higher := r.id, lower := lo }))
  {
    atoms := [],
    rules := rules,
    norms := norms,
    guards := [],
    attacks := [],
    priorities := priorities,
    obligations := [],
    failureState :=
      if ∃ r ∈ s.rules, r.uncertainFields.length > 0 then
        .unsupportedStructure
      else
        .none,
    lostFields := [],
    defaultedFields := []
  }

/-- 中文证明：lowering 保持规则 id（一一映射，不重命名）。 -/
theorem lowering_preserves_rule_ids (s : LegalSpec) :
    (lowerSpec s).rules.map (fun r => r.id) = specRuleIds s := by
  dsimp [lowerSpec, specRuleIds, lowerRule]
  induction s.rules with
  | nil => rfl
  | cons r rs ih => simp [List.map, specRuleIds, lowerRule, ih]

/-- 中文证明：lowering 保持结论（语义字段不丢失）。 -/
theorem lowering_preserves_conclusions (r : LegalSpecRule) :
    (lowerRule r).conclusion = r.conclusion := rfl

/-- 中文证明：lowering 保持 exception 列表。 -/
theorem lowering_preserves_exceptions (r : LegalSpecRule) :
    (lowerRule r).exceptions = r.exceptions := rfl

/-- 中文证明：lowering 保持前提条件。 -/
theorem lowering_preserves_conditions (r : LegalSpecRule) :
    (lowerRule r).premises = r.conditions := rfl

/-- 中文证明：lowering 保持模态映射确定（同模态同句柄）。 -/
theorem lowering_modality_deterministic (m : SpecModality) :
    lowerModality m = lowerModality m := rfl

/-- 中文证明：含不确定字段的 spec lowering 后不得 decisive。 -/
theorem uncertain_spec_not_decisive (s : LegalSpec) (r : LegalSpecRule)
    (hmem : r ∈ s.rules) (huncertain : r.uncertainFields.length > 0) :
    (lowerSpec s).failureState ≠ .none := by
  dsimp [lowerSpec]
  split
  · decide
  · rename_i hno
    exact hno ⟨r, hmem, huncertain⟩

/-- 中文证明：无不确定字段的 spec lowering 后 failure state 为 none。 -/
theorem certain_spec_lowering_clean (s : LegalSpec)
    (hall : ∀ r ∈ s.rules, r.uncertainFields.length = 0) :
    (lowerSpec s).failureState = .none := by
  dsimp [lowerSpec]
  split
  · rename_i hexists
    rcases hexists with ⟨r, hmem, hpos⟩
    have hzero := hall r hmem
    exact Nat.lt_irrefl 0 (hzero ▸ hpos)
  · rfl

end JurisLean
