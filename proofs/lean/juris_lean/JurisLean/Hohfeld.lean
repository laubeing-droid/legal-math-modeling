import JurisLean.LegalModelV2

/-!
中文说明：ON-01 Hohfeld 八概念代数（对立/相关表）。子命名空间
JurisLean.Hohfeld 承载八概念归纳类型与 opposite/correlative 全函数；
两个映射均为对合且无不动点（decide 级）。本轮不扩展动态义务逻辑。
-/

namespace JurisLean.Hohfeld

/-- 中文说明：Hohfeld 八概念：请求权/义务/特权/无权/权能/责任/豁免/无资格。 -/
inductive Concept where
  | claimRight
  | duty
  | privilege
  | noRight
  | power
  | liability
  | immunity
  | disability
deriving DecidableEq, Repr

/-- 中文说明：对立（opposite）映射。 -/
def opposite :
    Concept → Concept
  | .claimRight => .noRight
  | .noRight => .claimRight
  | .privilege => .duty
  | .duty => .privilege
  | .power => .disability
  | .disability => .power
  | .immunity => .liability
  | .liability => .immunity

/-- 中文说明：相关（correlative）映射。 -/
def correlative :
    Concept → Concept
  | .claimRight => .duty
  | .duty => .claimRight
  | .privilege => .noRight
  | .noRight => .privilege
  | .power => .liability
  | .liability => .power
  | .immunity => .disability
  | .disability => .immunity

/-- 中文证明：对立映射是对合。 -/
theorem opposite_involutive
    (concept : Concept) :
    opposite (opposite concept) = concept := by
  cases concept <;> rfl

/-- 中文证明：相关映射是对合。 -/
theorem correlative_involutive
    (concept : Concept) :
    correlative (correlative concept) = concept := by
  cases concept <;> rfl

/-- 中文证明：对立映射无不动点。 -/
theorem opposite_ne_self
    (concept : Concept) :
    opposite concept ≠ concept := by
  cases concept <;> decide

/-- 中文证明：相关映射无不动点。 -/
theorem correlative_ne_self
    (concept : Concept) :
    correlative concept ≠ concept := by
  cases concept <;> decide

end JurisLean.Hohfeld
