import JurisLean.LegalIds
import JurisLean.BackendContract

/-!
中文说明：M5 P04 SMT witness 合同。SAT model 可重验；UNSAT 只有在
持有可接受的 proof/TCB receipt 时才能升级，否则保持 unknown。
-/

namespace JurisLean

/-- 中文说明：SMT SAT model witness。 -/
structure SMTModelWitness where
  assignment : List (String × Int)
  problemDigest : ContentDigest
  solverId : String
deriving DecidableEq

/-- 中文说明：UNSAT proof receipt 句柄；TCB 边界在 receipt 上显式。 -/
structure SMTProofReceipt where
  proofRef : String
  problemDigest : ContentDigest
  tcbBoundary : String
deriving DecidableEq

/-- 中文说明：由可选 model/proof 导出结果。 -/
def smtOutcome (model : Option SMTModelWitness)
    (proof : Option SMTProofReceipt) : SolverOutcome :=
  if model.isSome then .sat
  else if proof.isSome then .unsat
  else .unknown

/-- 中文证明：无 model 无 proof 时保持 unknown，不得升级 UNSAT。 -/
theorem no_model_no_proof_is_unknown :
    smtOutcome (none : Option SMTModelWitness) (none : Option SMTProofReceipt) =
      .unknown := by
  dsimp [smtOutcome]
  simp

/-- 中文证明：UNSAT 只有在持有 proof receipt 时才成立。 -/
theorem unsat_requires_proof_receipt (proof : SMTProofReceipt) :
    smtOutcome (none : Option SMTModelWitness) (some proof) = .unsat := by
  dsimp [smtOutcome]
  simp

/-- 中文证明：存在 SAT model 时结果为 sat。 -/
theorem sat_model_present (model : SMTModelWitness)
    (proof : Option SMTProofReceipt) :
    smtOutcome (some model) proof = .sat := by
  dsimp [smtOutcome]
  simp

/-- 中文证明：model 与 proof 同时存在时 SAT 优先（模型可重验）。 -/
theorem sat_preferred_over_unsat (model : SMTModelWitness)
    (proof : SMTProofReceipt) :
    smtOutcome (some model) (some proof) = .sat := by
  dsimp [smtOutcome]
  simp

/-- 中文证明：unknown 结果不 decisive（承接 BackendContract 语义）。 -/
theorem smt_unknown_not_decisive :
    outcomeDecisive (smtOutcome (none : Option SMTModelWitness)
      (none : Option SMTProofReceipt)) = false := by
  dsimp [smtOutcome]
  simp

end JurisLean
