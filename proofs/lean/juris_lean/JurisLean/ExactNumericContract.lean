import JurisLean.LegalIds
import JurisLean.FailureStatus

/-!
中文说明：M5 P04 精确数值合同。整数最小货币单位、有理比例/利率、
currency/unit/scale、rounding node/mode/precision、interval 与范围。
division-by-zero、out-of-range 全部 fail-closed；正式路径禁止 binary
float；rounding policy 缺失时不得 decisive。
-/

namespace JurisLean

/-- 中文说明：精确金额：最小货币单位的整数表示。 -/
structure ExactAmountM5 where
  minorUnits : Int
  currency : String
deriving DecidableEq

/-- 中文说明：精确比率：分子/分母整数，分母非零。 -/
structure ExactRateM5 where
  numerator : Int
  denominator : Int
deriving DecidableEq

/-- 中文说明：金额 well-formed：currency 必须显式非空。 -/
def amountWellFormed (a : ExactAmountM5) : Prop :=
  a.currency ≠ ""

/-- 中文说明：比率 well-formed：分母非零。 -/
def rateWellFormed (r : ExactRateM5) : Prop :=
  r.denominator ≠ 0

/-- 中文说明：精确除法：除零返回 none（fail-closed）。 -/
def divideExact (num den : Int) : Option (Int × Int) :=
  if h : den = 0 then none else some (num, den)

/-- 中文说明：范围判定。 -/
def inRange (v lo hi : Int) : Prop :=
  lo ≤ v ∧ v ≤ hi

/-- 中文说明：rounding policy 缺失时不得 decisive。 -/
def decisiveWithRounding (policy : Option RoundingPolicy) : Prop :=
  policy.isSome

/-- 中文证明：除零 fail-closed。 -/
theorem division_by_zero_fail_closed (num : Int) :
    divideExact num 0 = none := by
  simp [divideExact]

/-- 中文证明：非零除数返回结构化有理对。 -/
theorem division_by_nonzero_structured (num den : Int) (h : den ≠ 0) :
    divideExact num den = some (num, den) := by
  simp [divideExact]
  · contradiction
  · rfl

/-- 中文证明：越界值不在范围内（out-of-range fail-closed 的判定面）。 -/
theorem out_of_range_not_in_range (v lo hi : Int) (h : hi < v) :
    ¬ inRange v lo hi := by
  intro hr
  exact lt_irrefl _ (lt_of_lt_of_le h hr.2)

/-- 中文证明：rounding policy 缺失时不 decisive。 -/
theorem missing_rounding_not_decisive :
    ¬ decisiveWithRounding (none : Option RoundingPolicy) := by
  dsimp [decisiveWithRounding]
  decide

/-- 中文证明：显式 rounding policy 才允许 decisive。 -/
theorem explicit_rounding_decisive (p : RoundingPolicy) :
    decisiveWithRounding (some p) := by
  dsimp [decisiveWithRounding]
  rfl

/-- 中文证明：空 currency 的金额不 well-formed。 -/
theorem currencyless_amount_not_well_formed (units : Int) :
    ¬ amountWellFormed { minorUnits := units, currency := "" } := by
  dsimp [amountWellFormed]
  intro h
  exact h rfl

/-- 中文证明：零分母比率不 well-formed。 -/
theorem zero_denominator_rate_not_well_formed (num : Int) :
    ¬ rateWellFormed { numerator := num, denominator := 0 } := by
  dsimp [rateWellFormed]
  intro h
  exact h rfl

end JurisLean
