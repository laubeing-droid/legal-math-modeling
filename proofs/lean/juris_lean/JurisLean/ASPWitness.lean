import JurisLean.LegalIds
import JurisLean.BackendContract

/-!
中文说明：M5 P04 ASP witness 合同。stable-model witness 可独立重验；
不存在 witness 不等于 UNSAT（fail-closed 为 unknown）。
-/

namespace JurisLean

/-- 中文说明：ASP stable-model witness：模型原子集合绑定问题摘要。 -/
structure ASPWitness where
  modelAtoms : List String
  problemDigest : ContentDigest
  solverId : String
deriving DecidableEq

/-- 中文说明：witness 可重验的最小条件：模型非空且绑定问题。 -/
def aspWitnessRecheckable (w : ASPWitness) (expectedDigest : ContentDigest) :
    Prop :=
  w.modelAtoms ≠ [] ∧ w.problemDigest = expectedDigest

/-- 中文说明：由可选 witness 导出结果：无 witness 是 unknown 而非 UNSAT。 -/
def aspOutcome (w : Option ASPWitness) : SolverOutcome :=
  match w with
  | some _ => .sat
  | none => .unknown

/-- 中文证明：无 witness 不等于 UNSAT。 -/
theorem absent_witness_not_unsat :
    aspOutcome (none : Option ASPWitness) ≠ .unsat := by
  dsimp [aspOutcome]

/-- 中文证明：无 witness 映射为 unknown（fail-closed）。 -/
theorem absent_witness_is_unknown :
    aspOutcome (none : Option ASPWitness) = .unknown := by
  dsimp [aspOutcome]

/-- 中文证明：存在 witness 时结果为 sat。 -/
theorem witness_present_is_sat (w : ASPWitness) :
    aspOutcome (some w) = .sat := rfl

/-- 中文证明：问题摘要不匹配的 witness 不可重验。 -/
theorem digest_mismatch_not_recheckable (w : ASPWitness)
    (expected : ContentDigest) (hdiff : w.problemDigest ≠ expected) :
    ¬ aspWitnessRecheckable w expected := by
  intro hr
  exact hdiff hr.2

/-- 中文证明：空模型的 witness 不可重验。 -/
theorem empty_model_not_recheckable (w : ASPWitness)
    (expected : ContentDigest) (hempty : w.modelAtoms = []) :
    ¬ aspWitnessRecheckable w expected := by
  intro hr
  exact hr.1 hempty

end JurisLean
