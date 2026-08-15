import JurisLean.ReceiptAuthority

/-!
中文说明：M7 authority lattice 补充定理。层级严格有序；任何自动机制
（数量、置信度、模型身份、重复运行）都不构成晋级证据，晋级只能来自
独立且 scope-bound 的外部 receipt。
-/

namespace JurisLean

/-- 中文说明：自动晋级机制类别（全部无效）。 -/
inductive AutoEscalationMechanism where
  | majorityCount
  | confidenceScore
  | modelIdentity
  | repeatedRuns
deriving DecidableEq, Repr

/-- 中文说明：自动机制不产生有效晋级 receipt。 -/
def autoMechanismReceiptValid (_mech : AutoEscalationMechanism) : Prop :=
  False

/-- 中文证明：任何自动机制都不构成晋级依据。 -/
theorem no_auto_escalation (mech : AutoEscalationMechanism) :
    ¬ autoMechanismReceiptValid mech := by
  intro h
  exact h

/-- 中文证明：层级不得非升：若 to 的秩不高于 from，则不是严格晋级。 -/
theorem escalation_requires_rank_increase (fromLevel toLevel : AuthorityLevel)
    (hesc : authorityRank toLevel ≤ authorityRank fromLevel) :
    authorityRank toLevel ≠ authorityRank fromLevel + 1 := by
  intro hinc
  rw [hinc] at hesc
  exact Nat.not_succ_le_self _ hesc

/-- 中文证明：有效 receipt 必然严格晋级一级（与 ReceiptAuthority 一致）。 -/
theorem valid_receipt_strict_step {r : AuthorityReceipt}
    (hv : receiptValid r) :
    authorityRank r.toLevel = authorityRank r.fromLevel + 1 := hv

end JurisLean
