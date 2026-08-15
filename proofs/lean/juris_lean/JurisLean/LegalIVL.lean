import JurisLean.LegalIds
import JurisLean.LegalSpec

/-!
中文说明：M6 P07 Legal-IVL：backend-neutral 形式核心。包含 typed
atom、rule、norm、guard、attack、priority、temporal/numeric constraint、
proof obligation 与 failure state。lost/defaulted 字段显式记录；有
lost/defaulted 语义字段时不得 decisive compilation。
-/

namespace JurisLean

/-- 中文说明：typed atom。 -/
structure IVLAtom where
  name : String
  locator : SpecLocator
deriving DecidableEq

/-- 中文说明：IVL 规则。 -/
structure IVLRule where
  id : LegalId .rule
  version : String
  premises : List String
  conclusion : String
  exceptions : List String
deriving DecidableEq

/-- 中文说明：IVL 规范：模态以字符串句柄承载，DDL 层解释。 -/
structure IVLNorm where
  id : LegalId .norm
  modality : String
  ruleRef : LegalId .rule
deriving DecidableEq

/-- 中文说明：guard 类别：时态/数值/来源。 -/
inductive IVLGuardKind where
  | temporal
  | numeric
  | source
deriving DecidableEq, Repr

/-- 中文说明：guard：对指定主题的显式约束。 -/
structure IVLGuard where
  kind : IVLGuardKind
  subject : String
  constraintText : String
deriving DecidableEq

/-- 中文说明：IVL attack 规格：每个攻击携带输入 witness。 -/
structure IVLAttackSpec where
  attackerConclusion : String
  targetConclusion : String
  kind : String
  inputWitness : String
deriving DecidableEq

/-- 中文说明：IVL priority。 -/
structure IVLPriority where
  higher : LegalId .rule
  lower : LegalId .rule
deriving DecidableEq

/-- 中文说明：proof obligation。 -/
structure IVLProofObligation where
  obligationId : String
  discharged : Bool
deriving DecidableEq

/-- 中文说明：IVL 失败状态。 -/
inductive IVLFailureState where
  | none
  | unsupportedStructure
  | lostField
  | defaultedField
deriving DecidableEq, Repr

/-- 中文说明：Legal-IVL 全记录。 -/
structure LegalIVL where
  atoms : List IVLAtom
  rules : List IVLRule
  norms : List IVLNorm
  guards : List IVLGuard
  attacks : List IVLAttackSpec
  priorities : List IVLPriority
  obligations : List IVLProofObligation
  failureState : IVLFailureState
  lostFields : List String
  defaultedFields : List String
deriving DecidableEq

/-- 中文说明：IVL 是否允许进入 decisive compilation。 -/
def ivlDecisiveAllowed (m : LegalIVL) : Prop :=
  m.failureState = .none ∧ m.lostFields = [] ∧ m.defaultedFields = []

/-- 中文证明：含 lost 字段的 IVL 不得 decisive。 -/
theorem lost_field_blocks_decisive {m : LegalIVL}
    (hlost : m.lostFields ≠ []) : ¬ ivlDecisiveAllowed m := by
  intro hall
  exact hlost hall.2.1

/-- 中文证明：含 defaulted 字段的 IVL 不得 decisive。 -/
theorem defaulted_field_blocks_decisive {m : LegalIVL}
    (hdef : m.defaultedFields ≠ []) : ¬ ivlDecisiveAllowed m := by
  intro hall
  exact hdef hall.2.2

/-- 中文证明：非 none 失败状态的 IVL 不得 decisive。 -/
theorem failure_state_blocks_decisive {m : LegalIVL}
    (hstate : m.failureState ≠ .none) : ¬ ivlDecisiveAllowed m := by
  intro hall
  exact hstate hall.1

end JurisLean
