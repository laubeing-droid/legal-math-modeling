import JurisLean.LegalIds
import JurisLean.BackendContract

/-!
中文说明：M5 P04 solver receipt 身份合同。solver identity、options、
seed、limits 与 problem digest 属于 receipt identity；任一不同即为
不同 receipt，不得互相替代。
-/

namespace JurisLean

/-- 中文说明：solver receipt：身份字段全部显式。 -/
structure SolverReceipt where
  solverId : String
  optionsDigest : ContentDigest
  seed : Nat
  limitSeconds : Nat
  problemDigest : ContentDigest
deriving DecidableEq

/-- 中文说明：receipt 身份相同：全字段一致。 -/
def receiptIdentitySame (r1 r2 : SolverReceipt) : Prop :=
  r1.solverId = r2.solverId ∧
    r1.optionsDigest = r2.optionsDigest ∧
      r1.seed = r2.seed ∧
        r1.limitSeconds = r2.limitSeconds ∧
          r1.problemDigest = r2.problemDigest

/-- 中文证明：problem digest 不同的 receipt 身份不同。 -/
theorem problem_digest_change_changes_identity (r1 r2 : SolverReceipt)
    (hdiff : r1.problemDigest ≠ r2.problemDigest) :
    ¬ receiptIdentitySame r1 r2 := by
  intro hsame
  exact hdiff hsame.2.2.2.2

/-- 中文证明：solver identity 不同的 receipt 身份不同。 -/
theorem solver_change_changes_identity (r1 r2 : SolverReceipt)
    (hdiff : r1.solverId ≠ r2.solverId) :
    ¬ receiptIdentitySame r1 r2 := by
  intro hsame
  exact hdiff hsame.1

/-- 中文证明：seed 不同的 receipt 身份不同。 -/
theorem seed_change_changes_identity (r1 r2 : SolverReceipt)
    (hdiff : r1.seed ≠ r2.seed) :
    ¬ receiptIdentitySame r1 r2 := by
  intro hsame
  exact hdiff hsame.2.2.1

/-- 中文证明：receipt 身份是自反的（同一 receipt 与自身身份相同）。 -/
theorem receipt_identity_reflexive (r : SolverReceipt) :
    receiptIdentitySame r r := by
  dsimp [receiptIdentitySame]
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- 中文证明：身份相同蕴含 problem digest 相同（绑定传递）。 -/
theorem identity_same_implies_problem_binding (r1 r2 : SolverReceipt)
    (hsame : receiptIdentitySame r1 r2) :
    r1.problemDigest = r2.problemDigest :=
  hsame.2.2.2.2

end JurisLean
