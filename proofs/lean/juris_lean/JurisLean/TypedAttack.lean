import JurisLean.LegalIds

/-!
中文说明：M4 P03 typed attack 语义。显式区分 rebuttal、undercut、
exception、premise challenge、priority defeat。每个 typed attack 必须
有合法 witness；attack identity 对来源 premise 与 rule version 稳定。
self attack 单独建模并保留给 grounded 语义处理。
-/

namespace JurisLean

/-- 中文说明：typed attack 类别。 -/
inductive TypedAttackKind where
  | rebuttal
  | undercut
  | exceptionAttack
  | premiseChallenge
  | priorityDefeat
deriving DecidableEq, Repr

/-- 中文说明：typed attack：有向、带 witness。 -/
structure TypedAttack where
  attacker : LegalId .argument
  target : LegalId .argument
  kind : TypedAttackKind
  witness : String
deriving DecidableEq

/-- 中文说明：attack well-formedness：witness 必须非空。 -/
def typedAttackWellFormed (a : TypedAttack) : Prop :=
  a.witness ≠ ""

/-- 中文说明：self attack 判定。 -/
def isSelfAttack (a : TypedAttack) : Prop :=
  a.attacker = a.target

/-- 中文证明：attack identity 对全部字段稳定（字段相同即同一 attack）。 -/
theorem attack_identity_stable (a b : TypedAttack)
    (h1 : a.attacker = b.attacker) (h2 : a.target = b.target)
    (h3 : a.kind = b.kind) (h4 : a.witness = b.witness) :
    a = b := by
  cases a; cases b
  simp_all

/-- 中文证明：空 witness 的 typed attack 不 well-formed。 -/
theorem empty_witness_attack_rejected {a : TypedAttack}
    (hwit : a.witness = "") : ¬ typedAttackWellFormed a := by
  intro hwf
  exact hwf hwit

/-- 中文证明：priority defeat 必须携带 witness（复用 well-formedness）。 -/
theorem priority_defeat_requires_witness {a : TypedAttack}
    (hkind : a.kind = .priorityDefeat) (hwf : typedAttackWellFormed a) :
    a.witness ≠ "" :=
  hwf

/-- 中文证明：self attack 被正确识别。 -/
theorem self_attack_identified (id : LegalId .argument) (kind : TypedAttackKind)
    (witness : String) :
    isSelfAttack { attacker := id, target := id, kind := kind, witness := witness } := rfl

/-- 中文证明：非自环 attack 不是 self attack。 -/
theorem non_self_attack_not_self {a : TypedAttack}
    (hdiff : a.attacker ≠ a.target) : ¬ isSelfAttack a := by
  intro hself
  exact hdiff hself

end JurisLean
