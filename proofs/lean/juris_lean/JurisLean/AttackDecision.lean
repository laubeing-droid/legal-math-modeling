import JurisLean.HornAAFContract
import JurisLean.DDLDefinitions

/-!
中文说明：本文件只定义 priority defeat 的最小判定接口。
priority 不能在缺少证据、自攻击或循环时默认获胜。
-/

namespace JurisLean

/-- 中文说明：priorityDefeats 表示 p 对 attack 的目标关系已激活且证据核验。 -/
def priorityDefeats (p : Priority) (attack : Attack) : Prop :=
  priorityOrdering p ∧ attack.source = p.higher ∧ attack.target = p.lower

/-- 中文说明：自攻击必须被 runtime/checker 当作不确定或污染输入处理。 -/
def isSelfAttack (attack : Attack) : Prop :=
  attack.source = attack.target

/-- 中文说明：两个 priority 互相反向时形成最小 cycle。 -/
def priorityCycle (left right : Priority) : Prop :=
  left.higher = right.lower ∧ left.lower = right.higher

/-- 中文说明：priority 证据缺失时不能产生 supported defeat。 -/
def missingPriorityEvidence (p : Priority) : Prop :=
  p.evidence.verified = false

/-- 中文证明：priority defeat 必须要求 active priority。 -/
theorem priority_defeat_requires_active
    {p : Priority} {attack : Attack}
    (h : priorityDefeats p attack) : p.active = true :=
  h.1.1

/-- 中文证明：priority defeat 必须要求 verified priority evidence。 -/
theorem priority_defeat_requires_evidence
    {p : Priority} {attack : Attack}
    (h : priorityDefeats p attack) : p.evidence.verified = true :=
  h.1.2

/-- 中文证明：缺少 priority evidence 时不能形成 priorityDefeats。 -/
theorem missing_priority_evidence_no_defeat
    {p : Priority} {attack : Attack}
    (hMissing : missingPriorityEvidence p) :
    ¬ priorityDefeats p attack := by
  intro h
  unfold missingPriorityEvidence at hMissing
  have hVerified := priority_defeat_requires_evidence h
  rw [hMissing] at hVerified
  contradiction

/-- 中文证明：自攻击不能作为 priority-supported result 被直接接受。 -/
theorem self_attack_not_priority_defeat
    {p : Priority} {attack : Attack}
    (hSelf : isSelfAttack attack)
    (hSource : attack.source = p.higher)
    (hTarget : attack.target = p.lower) :
    p.higher = p.lower := by
  unfold isSelfAttack at hSelf
  rw [hSource, hTarget] at hSelf
  exact hSelf

/-- 中文证明：priority cycle 保留双向关系，交由 fail-closed/UNDECIDED gate 处理。 -/
theorem priority_cycle_symmetric
    {left right : Priority} (h : priorityCycle left right) :
    right.higher = left.lower ∧ right.lower = left.higher := by
  exact ⟨h.2.symm, h.1.symm⟩

end JurisLean
