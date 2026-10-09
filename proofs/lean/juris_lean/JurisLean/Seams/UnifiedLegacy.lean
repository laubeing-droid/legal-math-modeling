import Mathlib.Tactic

/-
Unified legacy entry points, layer N (plan §10; I.4.16 L16, fragment for
U30).

The legacy-compatibility face:

* `LegacyIn` is the OLD carrier — `unscoped` inputs lack the scope tag
  the new semantics needs (an expressiveness gap, not a judgment).
* `convertLegacy` is the PARTIAL conversion; the success condition is
  purely structural (the scope tag is present).
* `LegacyObs` carries the seven protected root observations;
  `projectNew` projects a new-pipeline output onto those roots.
* `legacy_projection_commutes`: ON THE COMPATIBLE SUBDOMAIN the
  projection of the new run equals the legacy run — proven by
  computation on the convertible constructor.
* `no_global_behavior_equality`: the legacy ERROR result on an
  unscoped input is preserved as a historical carrier and is equal to
  NO new projection — the compatibility theorem does not claim, and
  cannot be stretched to, global behavioral equality.

Scope, honestly: the fragment's new pipeline is a one-field computation
with a ready bit.  The production seven-root binding over the full
runLegal outputs, and the fate of the historical `Seams.UnifiedModel` /
`instanceM` carriers (they stay as historical/counterexample material),
are recorded in the plan; this fragment proves the conversion/projection
discipline itself.
-/

namespace JurisLean.Seams.UnifiedLegacy

/-! ## 一、旧载体与部分转换 -/

/-- 旧输入：plain 可转换；unscoped 缺作用域标签（表达能力不足）。 -/
inductive LegacyIn : Type
  | plain (v : ℚ)
  | unscoped (v : ℚ)
  deriving DecidableEq

/-- 新输入：带作用域。 -/
inductive NewIn : Type
  | scoped (v : ℚ) (scope : ℕ)
  deriving DecidableEq

/-- 部分转换：成功条件只含结构条件（作用域标签在）。 -/
def convertLegacy : LegacyIn → Option NewIn
  | .plain v => some (.scoped v 0)
  | .unscoped _ => none

/-! ## 二、七根受保护观察与投影 -/

/-- 旧受保护观察（七根：金额＋六个状态位）。 -/
structure LegacyObs where
  root1 : ℚ
  root2 : Bool
  root3 : Bool
  root4 : Bool
  root5 : Bool
  root6 : Bool
  root7 : Bool
  deriving DecidableEq

/-- 新管线输出。 -/
structure NewOut where
  amount : ℚ
  ready : Bool
  deriving DecidableEq

/-- 新结果到旧观察的投影（七根逐一落位）。 -/
def projectNew : NewOut → LegacyObs
  | .mk amount ready =>
      { root1 := amount, root2 := ready, root3 := true, root4 := true,
        root5 := true, root6 := true, root7 := true }

/-- 新管线（片段：金额直通，就绪恒真）。 -/
def newRun : NewIn → NewOut
  | .scoped v _ => { amount := v, ready := true }

/-- 旧管线（unscoped 的旧错误结果按历史载体保留：root2=false 哨兵）。 -/
def legacyRun : LegacyIn → LegacyObs
  | .plain v => { root1 := v, root2 := true, root3 := true, root4 := true,
      root5 := true, root6 := true, root7 := true }
  | .unscoped v => { root1 := v, root2 := false, root3 := true, root4 := true,
      root5 := true, root6 := true, root7 := true }

/-! ## 三、子域交换与全域不等 -/

/-- **旧投影交换**：兼容子域上，投影(新管线(转换(旧输入)))＝旧管线(旧输入)
    ——转换失败处不做任何声称（match 的 none 枝是 True，不是伪造的相等）。 -/
theorem legacy_projection_commutes : ∀ l : LegacyIn,
    match convertLegacy l with
    | some ni => projectNew (newRun ni) = legacyRun l
    | none => True := by
  intro l
  cases l with
  | plain v => simp [convertLegacy, projectNew, newRun, legacyRun]
  | unscoped v => simp [convertLegacy]

/-- **全域行为相等不成立**：unscoped 输入的旧错误结果（root2=false 哨兵）
    是历史载体，与任何新投影都不相等——不得为维持旧错误结果把交换律
    拉伸成全域等式。 -/
theorem no_global_behavior_equality :
    ∀ ni : NewIn, projectNew (newRun ni) ≠ legacyRun (LegacyIn.unscoped 5) := by
  intro ni h
  have h2 : (projectNew (newRun ni)).root2
      = (legacyRun (.unscoped 5)).root2 := by rw [h]
  cases ni with
  | scoped v s => simp [projectNew, newRun, legacyRun] at h2

end JurisLean.Seams.UnifiedLegacy
