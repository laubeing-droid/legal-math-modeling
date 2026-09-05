import JurisLean.LegalModelV2
import JurisLean.FailureStatus

/-!
中文说明：M1 well-formedness 层。对引用闭包、方向、scope、version 和
类型给出完整判定；未知 schema/semantics/version 一律映射为 fail-closed，
而不是默认回退旧版本。
-/

namespace JurisLean

/-- 中文说明：已准入事实必须绑定来源快照（候选事实不受此约束）。 -/
def factRecordWellFormed (f : LegalFactV2) : Prop :=
  f.admitted = true → f.sourceRef ≠ none

/-- 中文说明：规则不得自循环引用自身结论作为前提。 -/
def ruleRecordWellFormed (r : LegalRuleV2) : Prop :=
  ¬ (r.conclusion ∈ r.premises)

/-- 中文说明：argument 的规则与支持事实必须来自已知注册集合。 -/
def argumentRecordWellFormed (a : ArgumentRecord)
    (knownRules : List (LegalId .rule)) (knownFacts : List (LegalId .fact)) : Prop :=
  a.ruleRef ∈ knownRules ∧ ∀ f ∈ a.support, f ∈ knownFacts

/-- 中文说明：attack 的两端必须已知，且必须携带非空输入 witness。 -/
def attackRecordWellFormed (atk : AttackRecord)
    (knownArguments : List (LegalId .argument)) : Prop :=
  atk.attacker ∈ knownArguments ∧ atk.target ∈ knownArguments ∧
    atk.inputWitness ≠ ""

/-- 中文说明：翻译一跳只有在无 lost/defaulted 字段时才允许声明义务闭合。 -/
def translationStepWellFormed (s : TranslationStep) : Prop :=
  s.obligationDischarged = true → s.lostFields = [] ∧ s.defaultedFields = []

/-- 中文证明：已准入且 well-formed 的事实必然绑定来源快照。 -/
theorem admitted_fact_requires_source {f : LegalFactV2}
    (hwf : factRecordWellFormed f) (hadm : f.admitted = true) :
    f.sourceRef ≠ none :=
  hwf hadm

/-- 中文证明：候选事实（未准入）不受来源绑定约束也不产生准入。 -/
theorem candidate_fact_not_admitted {f : LegalFactV2}
    (h : f.admitted = false) : f.admitted ≠ true := by
  intro hcontra
  rw [h] at hcontra
  cases hcontra

/-- 中文证明：含 lost 字段的翻译一跳不得声明义务闭合。 -/
theorem lost_field_blocks_discharge {s : TranslationStep}
    (hwf : translationStepWellFormed s) (hlost : s.lostFields ≠ []) :
    s.obligationDischarged ≠ true := by
  intro hdis
  have hpair := hwf hdis
  exact hlost hpair.1

/-- 中文证明：含 defaulted 字段的翻译一跳同样不得声明义务闭合。 -/
theorem defaulted_field_blocks_discharge {s : TranslationStep}
    (hwf : translationStepWellFormed s) (hdef : s.defaultedFields ≠ []) :
    s.obligationDischarged ≠ true := by
  intro hdis
  have hpair := hwf hdis
  exact hdef hpair.2

/-- 中文证明：空 witness 的 attack 不满足 well-formedness。 -/
theorem empty_witness_attack_not_well_formed {atk : AttackRecord}
    (knownArguments : List (LegalId .argument))
    (hwit : atk.inputWitness = "") :
    ¬ attackRecordWellFormed atk knownArguments := by
  intro hwf
  exact hwf.2.2 hwit

/-- 中文说明：已知 schema 版本注册表。 -/
def knownSchemaVersions : List SchemaVersion :=
  [{ tag := "spec-schema-v2" }]

/-- 中文说明：已知 semantics 版本注册表。 -/
def knownSemanticsVersions : List SemanticsVersion :=
  [{ tag := "grounded-1" }, { tag := "horn-least-model-1" }]

/-- 中文说明：未知 schema 版本映射为 fail-closed，而不是默认旧版本。 -/
def resolveSchemaVersion (v : SchemaVersion) : FailureStatus :=
  if v ∈ knownSchemaVersions then .success else .error

/-- 中文说明：未知 semantics 版本映射为 fail-closed。 -/
def resolveSemanticsVersion (v : SemanticsVersion) : FailureStatus :=
  if v ∈ knownSemanticsVersions then .success else .error

/-- 中文证明：未知 schema 版本必然 fail-closed。 -/
theorem unknown_schema_fail_closed {v : SchemaVersion}
    (h : v ∉ knownSchemaVersions) : resolveSchemaVersion v = .error := by
  dsimp [resolveSchemaVersion]
  split
  · contradiction
  · rfl

/-- 中文证明：未知 semantics 版本必然 fail-closed。 -/
theorem unknown_semantics_fail_closed {v : SemanticsVersion}
    (h : v ∉ knownSemanticsVersions) : resolveSemanticsVersion v = .error := by
  dsimp [resolveSemanticsVersion]
  split
  · contradiction
  · rfl

/-- 中文证明：注册表内 schema 版本解析为 success（映射确定性）。 -/
theorem registered_schema_resolves {v : SchemaVersion}
    (h : v ∈ knownSchemaVersions) : resolveSchemaVersion v = .success := by
  dsimp [resolveSchemaVersion]
  split
  · rfl
  · contradiction

/-- 中文证明：version 解析是确定的：任何版本只有 success 或 error 两种结果。 -/
theorem version_resolution_decisive (v : SchemaVersion) :
    resolveSchemaVersion v = .success ∨ resolveSchemaVersion v = .error := by
  dsimp [resolveSchemaVersion]
  split
  · exact Or.inl rfl
  · exact Or.inr rfl

end JurisLean
