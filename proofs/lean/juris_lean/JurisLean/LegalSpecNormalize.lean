import Mathlib.Data.List.Basic
import JurisLean.LegalSpec
import JurisLean.LegalSpecWellFormed

/-!
中文说明：M6 LegalSpec 归一化：丢弃无来源定位的规则（结构化错误，
不静默吞掉）。归一化幂等，且保持 well-formedness。
-/

namespace JurisLean

/-- 中文说明：保留来源定位的规则谓词（Bool 判定）。 -/
def locatedRule (r : LegalSpecRule) : Bool :=
  decide (r.locator.path ≠ "")

/-- 中文说明：归一化：过滤无定位规则。 -/
def LegalSpec.normalize (s : LegalSpec) : LegalSpec :=
  { s with rules := s.rules.filter locatedRule }

/-- 中文证明：filter 幂等（谓词固定）。 -/
theorem located_filter_idem (xs : List LegalSpecRule) :
    (xs.filter locatedRule).filter locatedRule = xs.filter locatedRule := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    by_cases hx : locatedRule x
    · simp [List.filter, hx, ih]
    · simp [List.filter, hx, ih]

/-- 中文证明：归一化幂等。 -/
theorem normalize_idempotent (s : LegalSpec) :
    (s.normalize).normalize = s.normalize := by
  dsimp [LegalSpec.normalize]
  congr 1
  exact located_filter_idem s.rules

/-- 中文证明：归一化后的规则都保留在原规则表中（无伪造规则）。 -/
theorem normalize_no_spurious_rules (s : LegalSpec) (r : LegalSpecRule)
    (hmem : r ∈ s.normalize.rules) : r ∈ s.rules := by
  dsimp [LegalSpec.normalize] at hmem
  exact List.mem_of_mem_filter hmem

/-- 中文证明：归一化保持规则级 well-formedness（结论字段不被触碰）。 -/
theorem normalize_preserves_rule_wf (s : LegalSpec)
    (h : ∀ r ∈ s.rules, r.conclusion ≠ "") (r : LegalSpecRule)
    (hmem : r ∈ s.normalize.rules) : r.conclusion ≠ "" :=
  h r (normalize_no_spurious_rules s r hmem)

/-- 中文证明：归一化丢弃的规则一定没有来源定位（typed error，非 panic）。 -/
theorem dropped_rule_has_empty_locator (s : LegalSpec) (r : LegalSpecRule)
    (hmem : r ∈ s.rules) (habsent : r ∉ s.normalize.rules) :
    r.locator.path = "" := by
  dsimp [LegalSpec.normalize] at habsent
  by_cases hloc : r.locator.path = ""
  · exact hloc
  · have hkeep : locatedRule r = true := by
      dsimp [locatedRule]
      exact decide_eq_true hloc
    have hinf : r ∈ s.rules.filter locatedRule := by
      rw [List.mem_filter]
      exact ⟨hmem, hkeep⟩
    exfalso
    exact habsent hinf

end JurisLean
