import JurisLean.UnifiedV2.FiniteContract

namespace JurisLean.ULM.UnifiedV2
open scoped BigOperators

section Distribution
variable {α : Type} [Fintype α]

def normalize (w : α → ℚ) (x : α) := w x / ∑ y, w y

theorem normalize_sum (w : α → ℚ) (hz : (∑ y, w y) ≠ 0) :
    (∑ x, normalize w x) = 1 := by
  simp only [normalize]
  rw [← Finset.sum_div]
  exact div_self hz

theorem normalize_nonnegative (w : α → ℚ) (hw : ∀ x, 0 ≤ w x) (x : α) :
    0 ≤ normalize w x := by
  exact div_nonneg (hw x) (Finset.sum_nonneg fun y _ => hw y)

/-- Enclosures propagate through positive weighted sums. No arbitrary
probability is assigned to legal argumentation branches. -/
theorem weighted_enclosure (p lower upper value : α → ℚ)
    (hp : ∀ x, 0 ≤ p x)
    (hb : ∀ x, lower x ≤ value x ∧ value x ≤ upper x) :
    (∑ x, p x * lower x) ≤ (∑ x, p x * value x) ∧
    (∑ x, p x * value x) ≤ (∑ x, p x * upper x) := by
  constructor
  · exact Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (hb x).1 (hp x)
  · exact Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (hb x).2 (hp x)
end Distribution

theorem interval_add_sound (l u a b x y : ℚ)
    (hx : l ≤ x ∧ x ≤ u) (hy : a ≤ y ∧ y ≤ b) :
    l+a ≤ x+y ∧ x+y ≤ u+b := by
  constructor <;> linarith [hx.1,hx.2,hy.1,hy.2]

theorem posterior_contamination_sound (lo hi p r eps : ℚ)
    (hp : lo ≤ p ∧ p ≤ hi) (hr : 0 ≤ r ∧ r ≤ 1)
    (he : 0 ≤ eps ∧ eps ≤ 1) :
    (1-eps)*lo ≤ (1-eps)*p+eps*r ∧
    (1-eps)*p+eps*r ≤ (1-eps)*hi+eps := by
  have h1 := mul_le_mul_of_nonneg_left hp.1 (sub_nonneg.mpr he.2)
  have h2 := mul_le_mul_of_nonneg_left hp.2 (sub_nonneg.mpr he.2)
  have h3 := mul_nonneg he.1 hr.1
  have h4 := mul_le_mul_of_nonneg_left hr.2 he.1
  constructor <;> nlinarith

def brierExpected (p q : ℚ) := p*(1-q)^2+(1-p)*q^2

theorem brier_excess (p q : ℚ) :
    brierExpected p q - brierExpected p p = (q-p)^2 := by
  unfold brierExpected
  ring

theorem brier_minimum (p q : ℚ) : brierExpected p p ≤ brierExpected p q := by
  have h := brier_excess p q
  have hn := sq_nonneg (q-p)
  linarith

def quadratic (a b x : ℚ) := a*x^2/2+b*x

theorem quadratic_difference (a b x y : ℚ) :
    quadratic a b y - quadratic a b x =
      (a*x+b)*(y-x)+a*(y-x)^2/2 := by
  unfold quadratic
  ring

theorem quadratic_optimal_from_variational_inequality
    (a b x y : ℚ) (ha : 0 ≤ a) (h : 0 ≤ (a*x+b)*(y-x)) :
    quadratic a b x ≤ quadratic a b y := by
  have hd := quadratic_difference a b x y
  have hn := mul_nonneg ha (sq_nonneg (y-x))
  linarith

def affineStep (a b step x : ℚ) := (1-step*a)*x-step*b

theorem affine_difference (a b step x y : ℚ) :
    affineStep a b step x-affineStep a b step y = (1-step*a)*(x-y) := by
  unfold affineStep
  ring

theorem affine_lipschitz (a b step x y : ℚ) :
    |affineStep a b step x-affineStep a b step y| = |1-step*a|*|x-y| := by
  rw [affine_difference, abs_mul]

theorem contraction_parameter (a step : ℚ) (h : 0 < step*a ∧ step*a < 2) :
    |1-step*a| < 1 := by
  apply abs_lt.mpr
  constructor <;> linarith [h.1,h.2]

theorem settlement_ir (l u s : ℚ) :
    (0 ≤ s-l ∧ 0 ≤ u-s) ↔ (l ≤ s ∧ s ≤ u) := by
  constructor <;> intro h <;> constructor <;> linarith [h.1,h.2]

theorem incentive_condition (gain detection loss : ℚ) :
    gain-detection*loss ≤ 0 ↔ gain ≤ detection*loss := by
  constructor <;> intro h <;> linarith

end JurisLean.ULM.UnifiedV2
