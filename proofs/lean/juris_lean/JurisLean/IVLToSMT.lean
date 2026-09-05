import JurisLean.LegalIVL

/-!
中文说明：M6 IVL -> SMT target。数值/时态 guard lowering 为显式 sort
约束句柄；guard 缺失约束文本时不 lowering（typed error）。
-/

namespace JurisLean

/-- 中文说明：SMT sort 句柄（Int/Real/BitVec 显式）。 -/
inductive SMTSort where
  | intSort
  | realSort
  | bitVecSort (width : Nat)
deriving DecidableEq, Repr

/-- 中文说明：SMT 约束条目句柄。 -/
structure SMTConstraint where
  subject : String
  sort : SMTSort
  constraintText : String
deriving DecidableEq

/-- 中文说明：SMT target。 -/
structure SMTProblem where
  constraints : List SMTConstraint
deriving DecidableEq

/-- 中文说明：guard -> SMT 约束：时态/数值 guard 用 Int sort。 -/
def lowerGuard (g : IVLGuard) : Option SMTConstraint :=
  if g.constraintText ≠ "" then
    match g.kind with
    | .temporal => some { subject := g.subject, sort := .intSort, constraintText := g.constraintText }
    | .numeric => some { subject := g.subject, sort := .intSort, constraintText := g.constraintText }
    | .source => none
  else
    none

/-- 中文说明：IVL -> SMT lowering。 -/
def ivlToSMT (m : LegalIVL) : SMTProblem :=
  { constraints := m.guards.filterMap lowerGuard }

/-- 中文证明：空约束文本的 guard 不 lowering（fail-closed）。 -/
theorem empty_guard_not_lowered (g : IVLGuard) (hempty : g.constraintText = "") :
    lowerGuard g = none := by
  dsimp [lowerGuard]
  split
  · contradiction
  · rfl

/-- 中文证明：时态 guard lowering 使用 Int sort。 -/
theorem temporal_guard_uses_int_sort (g : IVLGuard)
    (hkind : g.kind = .temporal) (hwit : g.constraintText ≠ "") :
    ∃ c, lowerGuard g = some c ∧ c.sort = .intSort := by
  dsimp [lowerGuard]
  split
  · rw [hkind]
    exact ⟨_, rfl, rfl⟩
  · contradiction

/-- 中文证明：source guard 不进入 SMT（领域隔离）。 -/
theorem source_guard_not_smt (g : IVLGuard)
    (hkind : g.kind = .source) : lowerGuard g = none := by
  dsimp [lowerGuard]
  split
  · rw [hkind]
  · rfl

end JurisLean
