import JurisLean.LegalIds

/-!
中文说明：M4 P03 permission 冲突语义。permission 不被普通正命题吞并；
permission/prohibition 冲突在没有显式 override priority 时 fail-closed
为 undecided，不默认任何一方。exception 作用于 applicability/defeat 的
指定层级。
-/

namespace JurisLean

/-- 中文说明：本地模态句柄（与 LegalSyntax.Modality 平行，避免耦合）。 -/
inductive NormKindM4 where
  | obligation
  | prohibition
  | permission
  | constitutive
deriving DecidableEq, Repr

/-- 中文说明：permission claim。 -/
structure PermissionClaimM4 where
  norm : LegalId .norm
  action : String
deriving DecidableEq

/-- 中文说明：prohibition claim。 -/
structure ProhibitionClaimM4 where
  norm : LegalId .norm
  action : String
deriving DecidableEq

/-- 中文说明：冲突判定：同一 action 上 permission 与 prohibition 相遇。 -/
def permissionConflicts (p : PermissionClaimM4) (q : ProhibitionClaimM4) : Prop :=
  p.action = q.action

/-- 中文说明：冲突解析结果。 -/
inductive ConflictOutcome where
  | permitted
  | prohibited
  | undecided
deriving DecidableEq, Repr

/-- 中文说明：冲突解析：只有显式 override 才能决胜，否则 undecided。 -/
def resolvePermissionConflict (conflict : Bool) (overridePermits : Bool)
    (overrideProhibits : Bool) : ConflictOutcome :=
  if conflict then
    if overridePermits ∧ ¬ overrideProhibits then .permitted
    else if overrideProhibits ∧ ¬ overridePermits then .prohibited
    else .undecided
  else
    .undecided

/-- 中文证明：permission 不是 obligation（不被正命题吞并）。 -/
theorem permission_not_obligation :
    NormKindM4.permission ≠ NormKindM4.obligation := by
  decide

/-- 中文证明：permission 不是 prohibition。 -/
theorem permission_not_prohibition :
    NormKindM4.permission ≠ NormKindM4.prohibition := by
  decide

/-- 中文证明：无 override 的 permission/prohibition 冲突保持 undecided。 -/
theorem unresolved_conflict_fail_closed :
    resolvePermissionConflict true false false = .undecided := by
  decide

/-- 中文证明：显式 permit-override 且无 prohibit-override 时许可生效。 -/
theorem permit_override_decides :
    resolvePermissionConflict true true false = .permitted := by
  decide

/-- 中文证明：双向 override 同时存在时仍 fail-closed。 -/
theorem conflicting_overrides_fail_closed :
    resolvePermissionConflict true true true = .undecided := by
  decide

/-- 中文说明：exception 作用层级：applicability 层或 defeat 层。 -/
inductive ExceptionLayer where
  | applicability
  | defeat
deriving DecidableEq, Repr

/-- 中文说明：exception 记录必须声明作用层级。 -/
structure TypedException where
  trigger : LegalId .fact
  defeats : LegalId .argument
  layer : ExceptionLayer
deriving DecidableEq

/-- 中文证明：exception 作用层级是显式且可判定的。 -/
theorem exception_layer_explicit (e : TypedException) :
    e.layer = .applicability ∨ e.layer = .defeat := by
  cases e.layer <;> simp

end JurisLean
