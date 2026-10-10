import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic
import JurisLean.Seams.Probability

/-!
S3a 针位承接件（附录 I.13 第 16–21 针）—— 以原验收名命名的六条真定理。

出处：`docs/spec/20261007-统一法律数学模型_附录I_Lean施工明细.md` §I.13 第 770–775 行
（S3 概率层前六针）；锚定现状见 `docs/full-math/BINDING_217_and_60.md`。

## 一、法律语义（人话）

附录 I.13 把旧 60 针的历史验收句逐名重立为"拟合同"：不得用同名弱式冒充，也不得把
前提外填。本件把第 16–21 针落成可命名的真定理，统一策略是**计数/密度载体 +
锚定理实例化 + 手工可验的闭式积分**。逐针如下：

- 16 `count_measure_event_exact`（I.13:770）：锚 `Probability.lean:183
  finite_distribution_to_pmf_apply` 与 `:232 rationalMass_evMass` 只在一般载体上给
  桥；本件构造具体有限计数载体（四次观测、计数 (2,3,1,0)、总计数 6），把
  `hp0/hp1` 前提真实证出后实例化两锚，使"计数 → 权重 → 事件测度"在同一目标上
  逐层对齐（事件质量 5/6 在 ℚ 层与 ℝ≥0∞ 层同值）。
- 17 `rate_crossmul_iff_rat_le`（I.13:771）：本原名全树未见。ℚ 上正分母乘法消去
  的两条等价（双分数交叉相乘、单分数阈值），外加 1/2 与 100/200 的闭式实例
  （成功率读法，衔接第 19 针的两组证据）。
- 18 `beta_posterior_from_likelihood`（I.13:772）：锚 `Probability.lean:289`
  同 basename 定理实际只有 ℚ 权重层归一（该锚保留不动、不被同名销账）；本针在
  **整型形状参数、多项式密度**载体上做真实密度层的共轭：先验×似然的积分
  （边际似然/归一化常数）、逐点后验密度 = 形状更新后的同族密度、后验归一。
- 19 `equal_rate_different_posterior`（I.13:773）：同一均匀先验（polyBeta 1 1 ≡ 1），
  两组同比率证据 1/2 与 100/200（1 成 1 败 vs 100 成 100 败），后验分别为
  Beta(2,2)/Beta(101,101)，方差 1/20 与 1/812，显式区别比率与证据量。
- 20 `beta_cdf_rat_cast`（I.13:774）：锚 `Probability.lean:311
  beta_predictive_bracket_survives_update` 只证总质量为 1，不能代替；本针在 18 针
  的多项式密度载体上把 CDF 定义为区间积分，证其对有理格点的取值与 ℚ 上的
  三次多项式（部分和闭式 3t²-2t³）经 cast 完全一致。
- 21 `beta_quantile_enclosure`（I.13:775）：本原名全树未见。在 18/20 针载体上
  定义分位函数（有限格点上的精确搜索 `Nat.find`），证特征化等价：
  q+1 是搜索命中 ⟺ CDF(q) ≤ p < CDF(q+1)（夹逼），并给命中范围与 p = 1/2 的
  闭式实例。

## 二、数学对象

- 计数载体：`s3aCount`（Fin 4 上的计数函数）、`s3aMass`（计数/总数的有理权重）、
  `s3aSuccess`（事件侧 Bool）；复用 `JurisLean.Seams.Probability` 的
  `finite_distribution_to_pmf_apply`、`rationalMass_evMass` 与
  `JurisLean.FullMath.Probability.evMass`。
- 多项式 Beta 族：`betaInt m n = ∫₀¹ x^m (1-x)^n dx`（多项式积分）、`betaTwoConst`
  （其阶乘闭式 (m!·n!)/(m+n+1)!）、`polyBeta a b`（整型形状 (a,b) 的归一化
  Beta 密度）、矩与方差引理（E[x] = a/(a+b)，Var = ab/((a+b)²(a+b+1))）。
- CDF/分位：`ratCdf22`（Beta(2,2) 的 CDF 有理闭式 3q²-2q³）、`gridCdf`
  （四分格点上的 CDF 值）、`s3aQuantile`（精确格点搜索分位函数）。

## 三、本件证什么、不证什么

**证**：六针各一条定理，全部由本件内构造或锚定理实例化合成；锚定理的前提
（如 `hp0/hp1`）都在本件内对具体载体真实证出，无一外填为假设；积分侧只使用
微积分基本定理（`integral_eq_sub_of_hasDerivAt`）与闭式多项式反导数，零数值近似。
**不证**（逐针边界，另见各定理 doc 注）：
- 16 只覆盖所构造的单一计数载体，不主张任意计数测度的存在性定理。
- 17 是 ℚ 上以分母正性为前提的交叉相乘等价，不涉及实数完备性或无穷比较。
- 18 的密度是**整型形状参数的多项式密度**：对整数 (a,b)，Beta(a,b) 密度
  x^(a-1)(1-x)^(b-1)/B(a,b) 是多项式且 B(a,b) = (a-1)!(b-1)!/(a+b-1)!，本件证明的
  正是这一族；不涉及 Gamma 函数、非整形状或测度论绝对连续性的一般理论。
- 19 的方差是"E[x²] - E[x]²"的代数式取值，两组证据的似然是伯努利计数似然
  x^k(1-x)^l；不主张任何真实审判数据下的后验分布。
- 20 的 CDF 一致性只在 Beta(2,2) 载体与有理点上陈述；一般形状的 CDF 闭式
  （部分和系数的通式）不在本件。
- 21 的分位函数定义在四分有理格点上（0,1/4,…,1），夹逼特征化限 q ≤ 3；
  一般可计算 CDF 的双点缩区不在本件。

## 四、档位

六针均为[已证，认定待 CI]。本件不含占位证明、不引入未证公理、不用 `native_decide`、
无 `: True :=` 逃避式；`decide` 只用于闭式有理/自然数归约，`rfl` 只用于本件内可定义
展开的闭式计算。按仓库边界约定，Lean 权威认定在 CI；本机不运行 Lean，当前状态
CI_NOT_RUN（fail-closed），本地静态自检仅为 provisional。
-/

namespace JurisLean.Seams.UnifiedNeedlesS3a

open BigOperators

/-! ## 第 16 针公共底座：有限计数载体 -/

/-- 计数载体：四个结果位上的观测计数 (2,3,1,0)，总计数 6。 -/
def s3aCount (i : Fin 4) : ℕ :=
  if i = 0 then 2 else if i = 1 then 3 else if i = 2 then 1 else 0

/-- 计数转有理权重：每个结果位的概率 = 计数/总数。 -/
def s3aMass (i : Fin 4) : ℚ := (s3aCount i : ℚ) / 6

/-- 事件侧：前两个结果位构成"胜诉侧"事件。 -/
def s3aSuccess (i : Fin 4) : Bool := decide (i.val < 2)

/-- 计数层总量：四结果位计数之和恰为 6。 -/
theorem s3aCount_sum : ∑ i : Fin 4, s3aCount i = 6 := by decide

/-- 计数层事件质量：胜诉侧计数之和恰为 5。 -/
theorem s3aEventCount : ∑ i : Fin 4, (if s3aSuccess i = true then s3aCount i else 0) = 5 := by
  decide

/-- 权重层非负（桥定理前提之一，对具体载体证出）。 -/
theorem s3aMass_nonneg : ∀ i : Fin 4, 0 ≤ s3aMass i := by
  intro i
  fin_cases i <;> norm_num [s3aCount, s3aMass, s3aSuccess]

/-- 权重层归一（桥定理前提之二，对具体载体证出）。 -/
theorem s3aMass_sum : ∑ i : Fin 4, s3aMass i = 1 := by
  norm_num [s3aCount, s3aMass, s3aSuccess]

/-- 权重层事件质量：事件测度（ℚ 侧 `evMass` 读法）= 5/6。 -/
theorem s3aEventMass : JurisLean.FullMath.Probability.evMass s3aMass s3aSuccess = 5 / 6 := by
  norm_num [s3aCount, s3aMass, s3aSuccess, JurisLean.FullMath.Probability.evMass]

/-- **第 16 针（S3，I.13:770；BINDING 行 16）**：计数→权重→事件测度同一目标桥。
    四层逐层对齐：(1) 计数总量与事件计数（5/6 的分子分母来源）；(2) 权重非负与
    归一（`finite_distribution_to_pmf` 桥的真实前提，非外填）；(3) 权重层事件质量
    = 5/6；(4) PMF 桥原子质量守恒（锚 `Probability.lean:183
    finite_distribution_to_pmf_apply` 的实例化）；(5) 证据质量在桥下保持
    （锚 `Probability.lean:232 rationalMass_evMass` 的实例化，ℝ≥0∞ 侧同为 5/6 的像）。
    边界：只覆盖本载体，不主张任意计数测度的一般存在定理。 -/
theorem count_measure_event_exact :
    (∑ i : Fin 4, s3aCount i = 6) ∧
    (∑ i : Fin 4, (if s3aSuccess i = true then s3aCount i else 0) = 5) ∧
    (∀ i : Fin 4, 0 ≤ s3aMass i) ∧
    (∑ i : Fin 4, s3aMass i = 1) ∧
    (∑ i : Fin 4, (if s3aSuccess i = true then s3aMass i else 0) = 5 / 6) ∧
    (∀ i : Fin 4, JurisLean.Seams.Probability.finite_distribution_to_pmf s3aMass
        s3aMass_nonneg s3aMass_sum i = ENNReal.ofReal (s3aMass i)) ∧
    (∑ i : Fin 4, (if s3aSuccess i = true
          then JurisLean.Seams.Probability.rationalMass s3aMass i else 0)
        = ENNReal.ofReal (((5 / 6 : ℚ)) : ℝ)) :=
  ⟨s3aCount_sum, s3aEventCount, s3aMass_nonneg, s3aMass_sum, by norm_num [s3aCount, s3aMass, s3aSuccess],
    fun i => JurisLean.Seams.Probability.finite_distribution_to_pmf_apply s3aMass
      s3aMass_nonneg s3aMass_sum i, by
      have h := JurisLean.Seams.Probability.rationalMass_evMass s3aMass s3aMass_nonneg
        s3aSuccess
      rwa [s3aEventMass] at h⟩

/-! ## 第 17 针：rate_crossmul_iff_rat_le -/

/-- **第 17 针（S3，I.13:771；BINDING 行 17，原 UNBOUND）**：正分母乘法消去。
    (1) 双分数交叉相乘：分母 r,d > 0 时 n/r ≤ m/d ⟺ n·d ≤ m·r（比率比较的
    精确等价，来自 `div_le_div_iff₀`）；(2) 单分数阈值：s·r ≤ n ⟺ s ≤ n/r
    （来自 `le_div_iff₀`，成功率对阈值的读法）；(3) 闭式实例：1/2 ≤ 100/200
    与其交叉相乘形式（衔接第 19 针的两组证据数）。
    边界：ℚ 上的序等价，不涉及实数完备性；分子无符号要求（只要求分母为正）。 -/
theorem rate_crossmul_iff_rat_le {s n m r d : ℚ} (hr : 0 < r) (hd : 0 < d) :
    (n / r ≤ m / d ↔ n * d ≤ m * r) ∧
    (s * r ≤ n ↔ s ≤ n / r) ∧
    (((1 : ℚ) / 2 ≤ 100 / 200) ∧ ((1 : ℚ) * 200 ≤ 100 * 2)) :=
  ⟨div_le_div_iff₀ hr hd, (le_div_iff₀ hr).symm, by norm_num⟩

/-! ## 第 18–21 针公共底座：整型形状多项式 Beta 族 -/

/-- 多项式权重的导数（对全体点成立）：d/dy [y^p (1-y)^q]
    = p·y^(p-1)(1-y)^q - q·y^p(1-y)^(q-1)。边界消失论证的微分核。 -/
theorem s3aPowDeriv (p q : ℕ) (x : ℝ) :
    HasDerivAt (fun y => y ^ p * (1 - y) ^ q)
      (((p : ℝ) * (x ^ (p - 1) * (1 - x) ^ q)
        - (q : ℝ) * (x ^ p * (1 - x) ^ (q - 1)))) x := by
  have hsub : HasDerivAt (fun y : ℝ => 1 - y) (0 - 1) x :=
    HasDerivAt.sub (hasDerivAt_const (1 : ℝ) x) (hasDerivAt_id x)
  have hq : HasDerivAt (fun y => (1 - y) ^ q) (-((q : ℝ) * (1 - x) ^ (q - 1))) x := by
    refine (HasDerivAt.scomp_of_eq (hasDerivAt_pow q (1 - x)) hsub rfl).congr_deriv ?_
    rw [smul_eq_mul]
    ring
  exact ((hasDerivAt_pow p x).mul hq).congr_deriv (by ring)

/-- 多项式 Beta 积分：I(m,n) = ∫₀¹ y^m (1-y)^n dy。 -/
noncomputable def betaInt (m n : ℕ) : ℝ := ∫ y in 0..1, y ^ m * (1 - y) ^ n

/-- 基线值：I(0,n) = 1/(n+1)（反导数 -(1-y)^(n+1)/(n+1)，边界值手工归约）。 -/
theorem betaInt_zero_left (n : ℕ) : betaInt 0 n = 1 / (((n + 1 : ℕ) : ℝ)) := by
  have hD : ∀ x : ℝ, HasDerivAt (fun y => -((1 - y) ^ (n + 1) / ((n + 1 : ℕ) : ℝ)))
      ((1 - x) ^ n) x := by
    intro x
    have hsub : HasDerivAt (fun y : ℝ => 1 - y) (0 - 1) x :=
      HasDerivAt.sub (hasDerivAt_const (1 : ℝ) x) (hasDerivAt_id x)
    have h1 : HasDerivAt (fun y => (1 - y) ^ (n + 1))
        (-(((n + 1 : ℕ) : ℝ) * (1 - x) ^ n)) x := by
      refine (HasDerivAt.scomp_of_eq (hasDerivAt_pow (n + 1) (1 - x)) hsub rfl).congr_deriv ?_
      rw [smul_eq_mul, Nat.add_sub_cancel]
      ring
    have h2 := (h1.div_const ((n + 1 : ℕ) : ℝ)).neg
    refine h2.congr_deriv ?_
    have hn1 : ((n + 1 : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.succ_ne_zero n)
    field_simp [hn1]
  have hII : IntervalIntegrable (fun y => (1 - y) ^ n) MeasureTheory.volume 0 1 :=
    Continuous.intervalIntegrable (by continuity) 0 1
  have hFT0 := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun y => -((1 - y) ^ (n + 1) / ((n + 1 : ℕ) : ℝ))) (f' := fun y => (1 - y) ^ n)
    (a := 0) (b := 1) (fun x _ => hD x) hII
  have hFT : (∫ y in 0..1, (1 - y) ^ n)
      = (fun y : ℝ => -((1 - y) ^ (n + 1) / ((n + 1 : ℕ) : ℝ))) 1
        - (fun y : ℝ => -((1 - y) ^ (n + 1) / ((n + 1 : ℕ) : ℝ))) 0 := hFT0
  have hb : ((fun y : ℝ => -((1 - y) ^ (n + 1) / ((n + 1 : ℕ) : ℝ))) 1
      - (fun y : ℝ => -((1 - y) ^ (n + 1) / ((n + 1 : ℕ) : ℝ))) 0)
      = 1 / ((n + 1 : ℕ) : ℝ) := by
    have h1 : -(((1 : ℝ) - 1) ^ (n + 1) / ((n + 1 : ℕ) : ℝ)) = 0 := by
      rw [sub_self, zero_pow (by omega), zero_div, neg_zero]
    have h0 : -(((1 : ℝ) - 0) ^ (n + 1) / ((n + 1 : ℕ) : ℝ))
        = -(1 / ((n + 1 : ℕ) : ℝ)) := by
      rw [sub_zero, one_pow]
    show -(((1 : ℝ) - 1) ^ (n + 1) / ((n + 1 : ℕ) : ℝ))
      - -(((1 : ℝ) - 0) ^ (n + 1) / ((n + 1 : ℕ) : ℝ)) = 1 / ((n + 1 : ℕ) : ℝ)
    rw [h1, h0, zero_sub, neg_neg]
  show (∫ y in 0..1, y ^ 0 * (1 - y) ^ n) = 1 / ((n + 1 : ℕ) : ℝ)
  rw [intervalIntegral.integral_congr (g := fun y => (1 - y) ^ n)
    (fun y _ => by simp [pow_zero])]
  rw [hFT, hb]

/-- 递推（边界消失的分部积分）：m ≥ 1 时
    I(m,n) = m/(n+1) · I(m-1,n+1)。 -/
theorem betaInt_step (m n : ℕ) (hm : 1 ≤ m) :
    betaInt m n = ((m : ℝ) / ((n + 1 : ℕ) : ℝ)) * betaInt (m - 1) (n + 1) := by
  have hIIA : IntervalIntegrable (fun y => (m : ℝ) * (y ^ (m - 1) * (1 - y) ^ (n + 1)))
      MeasureTheory.volume 0 1 := Continuous.intervalIntegrable (by continuity) 0 1
  have hIIB : IntervalIntegrable (fun y => ((n + 1 : ℕ) : ℝ) * (y ^ m * (1 - y) ^ n))
      MeasureTheory.volume 0 1 := Continuous.intervalIntegrable (by continuity) 0 1
  have hII : IntervalIntegrable
      (fun y => ((m : ℝ) * (y ^ (m - 1) * (1 - y) ^ (n + 1))
        - ((n + 1 : ℕ) : ℝ) * (y ^ m * (1 - y) ^ n))) MeasureTheory.volume 0 1 :=
    Continuous.intervalIntegrable (by continuity) 0 1
  have hD : ∀ x : ℝ, HasDerivAt (fun y => y ^ m * (1 - y) ^ (n + 1))
      (((m : ℝ) * (x ^ (m - 1) * (1 - x) ^ (n + 1))
        - ((n + 1 : ℕ) : ℝ) * (x ^ m * (1 - x) ^ n))) x :=
    fun x => s3aPowDeriv m (n + 1) x
  have hFT := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun y => y ^ m * (1 - y) ^ (n + 1))
    (f' := fun y => ((m : ℝ) * (y ^ (m - 1) * (1 - y) ^ (n + 1))
      - ((n + 1 : ℕ) : ℝ) * (y ^ m * (1 - y) ^ n)))
    (a := 0) (b := 1) (fun x _ => hD x) hII
  have hb : ((fun y : ℝ => y ^ m * (1 - y) ^ (n + 1)) 1
      - (fun y : ℝ => y ^ m * (1 - y) ^ (n + 1)) 0) = 0 := by
    have h1 : ((1 : ℝ) ^ m * (1 - 1) ^ (n + 1)) = 0 := by
      rw [one_pow, sub_self, zero_pow (by omega), mul_zero]
    have h0 : ((0 : ℝ) ^ m * (1 - 0) ^ (n + 1)) = 0 := by
      rw [zero_pow (by omega), sub_zero, one_pow, zero_mul]
    show ((1 : ℝ) ^ m * (1 - 1) ^ (n + 1)) - ((0 : ℝ) ^ m * (1 - 0) ^ (n + 1)) = 0
    rw [h1, h0, sub_zero]
  have hz : ((∫ y in 0..1, ((m : ℝ) * (y ^ (m - 1) * (1 - y) ^ (n + 1))))
      - (∫ y in 0..1, ((n + 1 : ℕ) : ℝ) * (y ^ m * (1 - y) ^ n))) = 0 := by
    rw [← intervalIntegral.integral_sub hIIA hIIB]
    exact hFT.trans hb
  have key : ((n + 1 : ℕ) : ℝ) * betaInt m n = (m : ℝ) * betaInt (m - 1) (n + 1) := by
    have e1 : ((n + 1 : ℕ) : ℝ) * betaInt m n
        = ∫ y in 0..1, ((n + 1 : ℕ) : ℝ) * (y ^ m * (1 - y) ^ n) :=
      (intervalIntegral.integral_const_mul _ _).symm
    have e2 : (m : ℝ) * betaInt (m - 1) (n + 1)
        = ∫ y in 0..1, (m : ℝ) * (y ^ (m - 1) * (1 - y) ^ (n + 1)) :=
      (intervalIntegral.integral_const_mul _ _).symm
    rw [e1, e2]
    linarith [hz]
  have hn1 : ((n + 1 : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.succ_ne_zero n)
  calc betaInt m n = ((n + 1 : ℕ) : ℝ) * betaInt m n / ((n + 1 : ℕ) : ℝ) := by
        field_simp [hn1]
    _ = (m : ℝ) * betaInt (m - 1) (n + 1) / ((n + 1 : ℕ) : ℝ) := by rw [key]
    _ = (m : ℝ) / ((n + 1 : ℕ) : ℝ) * betaInt (m - 1) (n + 1) := by
        field_simp [hn1]

/-- 多项式 Beta 积分的阶乘闭式（ℚ 值）：I(m,n) = (m!·n!)/(m+n+1)!。 -/
def betaTwoConst (m n : ℕ) : ℚ :=
  ((Nat.factorial m * Nat.factorial n : ℕ) : ℚ) / ((Nat.factorial (m + n + 1) : ℕ) : ℚ)

/-- 阶乘的 ℚ 像恒正（闭式常数的非退化来源）。 -/
theorem s3aFactPos (k : ℕ) : (0 : ℚ) < ((Nat.factorial k : ℕ) : ℚ) :=
  Nat.cast_pos.mpr (Nat.factorial_pos k)

/-- 闭式常数恒正。 -/
theorem betaTwoConst_pos (m n : ℕ) : 0 < betaTwoConst m n := by
  have h1 : (0 : ℚ) < ((Nat.factorial m * Nat.factorial n : ℕ) : ℚ) :=
    Nat.cast_pos.mpr (Nat.mul_pos (Nat.factorial_pos m) (Nat.factorial_pos n))
  have h2 : (0 : ℚ) < ((Nat.factorial (m + n + 1) : ℕ) : ℚ) := s3aFactPos _
  exact div_pos h1 h2

/-- 闭式定理：I(m,n) 的实积分值恰为 ℚ 闭式常数的 cast（对 m 归纳，n 泛化）。 -/
theorem betaInt_eq (m : ℕ) : ∀ n : ℕ, betaInt m n = ((betaTwoConst m n : ℚ) : ℝ) := by
  induction m with
  | zero =>
    intro n
    rw [betaInt_zero_left]
    have hq : betaTwoConst 0 n = 1 / ((n : ℚ) + 1) := by
      have hfn : (0 : ℚ) < ((Nat.factorial n : ℕ) : ℚ) := s3aFactPos n
      have hn1 : (0 : ℚ) < ((n : ℕ) + 1 : ℚ) := by
        exact_mod_cast (Nat.succ_pos n)
      unfold betaTwoConst
      simp only [Nat.factorial_zero, Nat.zero_add, one_mul]
      rw [Nat.factorial_succ]
      push_cast at hn1 ⊢
      field_simp [hfn.ne', hn1.ne']
    exact_mod_cast hq.symm
  | succ m ih =>
    intro n
    rw [betaInt_step (m + 1) n (by omega), Nat.add_sub_cancel, ih (n + 1)]
    have hq : ((m : ℕ) + 1 : ℚ) / ((n : ℕ) + 1 : ℚ) * (betaTwoConst m (n + 1) : ℚ)
        = betaTwoConst (m + 1) n := by
      have hfa : (0 : ℚ) < ((Nat.factorial m : ℕ) : ℚ) := s3aFactPos m
      have hfb : (0 : ℚ) < ((Nat.factorial n : ℕ) : ℚ) := s3aFactPos n
      have hfab : (0 : ℚ) < ((Nat.factorial (m + n + 1) : ℕ) : ℚ) := s3aFactPos _
      have hfab2 : (0 : ℚ) < ((Nat.factorial (m + n + 2) : ℕ) : ℚ) := s3aFactPos _
      have hidx : m + (n + 1) + 1 = m + 1 + n + 1 := by omega
      unfold betaTwoConst
      rw [hidx]
      simp only [Nat.factorial_succ]
      push_cast
      field_simp [hfa.ne', hfb.ne', hfab.ne', hfab2.ne'] <;> ring
    rw_mod_cast [hq]

/-- 闭式比值一：I(a+1,b)/I(a,b) = (a+1)/(a+b+2)（一阶矩的归一化比值）。 -/
theorem betaTwoConst_ratio1 (a b : ℕ) :
    betaTwoConst (a + 1) b / betaTwoConst a b = ((a : ℕ) + 1 : ℚ) / ((a : ℕ) + b + 2) := by
  have hfa : (0 : ℚ) < ((Nat.factorial a : ℕ) : ℚ) := s3aFactPos a
  have hfb : (0 : ℚ) < ((Nat.factorial b : ℕ) : ℚ) := s3aFactPos b
  have hfab : (0 : ℚ) < ((Nat.factorial (a + b + 1) : ℕ) : ℚ) := s3aFactPos _
  have hidx : (a : ℕ) + 1 + b + 1 = (a : ℕ) + b + 1 + 1 := by omega
  unfold betaTwoConst
  rw [hidx]
  simp only [Nat.factorial_succ]
  push_cast
  field_simp [hfa.ne', hfb.ne', hfab.ne'] <;> ring

/-- 闭式比值二：I(a+2,b)/I(a,b) = (a+1)(a+2)/((a+b+2)(a+b+3))（二阶矩的归一化比值）。 -/
theorem betaTwoConst_ratio2 (a b : ℕ) :
    betaTwoConst (a + 2) b / betaTwoConst a b
      = (((a : ℕ) + 1) * ((a : ℕ) + 2) : ℚ) / (((a : ℕ) + b + 2) * ((a : ℕ) + b + 3)) := by
  have hfa : (0 : ℚ) < ((Nat.factorial a : ℕ) : ℚ) := s3aFactPos a
  have hfb : (0 : ℚ) < ((Nat.factorial b : ℕ) : ℚ) := s3aFactPos b
  have hfab : (0 : ℚ) < ((Nat.factorial (a + b + 1) : ℕ) : ℚ) := s3aFactPos _
  have hfabb : (0 : ℚ) < ((Nat.factorial (a + b + 2) : ℕ) : ℚ) := s3aFactPos _
  have ha2 : (a : ℕ) + 2 = ((a : ℕ) + 1) + 1 := by omega
  have hidx : ((a : ℕ) + 1) + 1 + b + 1 = ((a : ℕ) + b + 2) + 1 := by omega
  unfold betaTwoConst
  rw [ha2, hidx]
  simp only [Nat.factorial_succ]
  push_cast
  field_simp [hfa.ne', hfb.ne', hfab.ne', hfabb.ne'] <;> ring

/-- **整型形状多项式 Beta 密度**：polyBeta a b x = B(a-1,b-1)⁻¹ · x^(a-1)(1-x)^(b-1)，
    其中整数形状的 Beta 函数值 B(a-1,b-1) = (a-1)!(b-1)!/(a+b-1)! 由本件 `betaTwoConst`
    闭式给出。对整数 (a,b) 这就是（归一化的）Beta(a,b) 密度；非整形状与 Gamma 函数
    一般理论不在本件。 -/
def polyBeta (a b : ℕ) (x : ℝ) : ℝ :=
  (((betaTwoConst (a - 1) (b - 1) : ℚ)⁻¹ : ℚ) : ℝ) * (x ^ (a - 1) * (1 - x) ^ (b - 1))

/-- 密度归一：整型形状的多项式 Beta 密度在 [0,1] 上积分为 1。 -/
theorem polyBeta_integral_one (a b : ℕ) : (∫ x in 0..1, polyBeta (a + 1) (b + 1) x) = 1 := by
  show (∫ x in 0..1, (((betaTwoConst a b : ℚ)⁻¹ : ℚ) : ℝ) * (x ^ a * (1 - x) ^ b)) = 1
  rw [intervalIntegral.integral_const_mul]
  have hI : (∫ x in 0..1, x ^ a * (1 - x) ^ b) = ((betaTwoConst a b : ℚ) : ℝ) :=
    betaInt_eq a b
  rw [hI]
  exact_mod_cast inv_mul_cancel₀ (betaTwoConst_pos a b).ne'

/-- 整型形状多项式 Beta 的一、二阶矩：E[x] = (a+1)/(a+b+2)，
    E[x²] = (a+1)(a+2)/((a+b+2)(a+b+3))（形状参数取 (a+1,b+1)）。 -/
theorem polyBeta_moments (a b : ℕ) :
    ((∫ x in 0..1, x * polyBeta (a + 1) (b + 1) x)
       = ((a : ℕ) + 1 : ℚ) / ((a : ℕ) + b + 2)) ∧
    ((∫ x in 0..1, x * x * polyBeta (a + 1) (b + 1) x)
       = (((a : ℕ) + 1) * ((a : ℕ) + 2) : ℚ)
          / (((a : ℕ) + b + 2) * ((a : ℕ) + b + 3))) := by
  constructor
  · have hshape : ∀ x : ℝ, x * polyBeta (a + 1) (b + 1) x
        = (((betaTwoConst a b : ℚ)⁻¹ : ℚ) : ℝ)
          * (x ^ ((a : ℕ) + 1) * (1 - x) ^ b) := by
      intro x
      show x * ((((betaTwoConst a b : ℚ)⁻¹ : ℚ) : ℝ) * (x ^ a * (1 - x) ^ b)) = _
      rw [pow_succ']; ring
    have hI : (∫ x in 0..1, x ^ ((a : ℕ) + 1) * (1 - x) ^ b)
        = ((betaTwoConst ((a : ℕ) + 1) b : ℚ) : ℝ) := betaInt_eq ((a : ℕ) + 1) b
    rw [intervalIntegral.integral_congr (fun x _ => hshape x),
      intervalIntegral.integral_const_mul, hI]
    have hq : ((betaTwoConst a b : ℚ)⁻¹) * ((betaTwoConst ((a : ℕ) + 1) b : ℚ))
        = ((a : ℕ) + 1 : ℚ) / ((a : ℕ) + b + 2) := by
      rw [inv_mul_eq_div, betaTwoConst_ratio1]
    exact_mod_cast hq
  · have hshape : ∀ x : ℝ, x * x * polyBeta (a + 1) (b + 1) x
        = (((betaTwoConst a b : ℚ)⁻¹ : ℚ) : ℝ)
          * (x ^ (((a : ℕ) + 1) + 1) * (1 - x) ^ b) := by
      intro x
      show x * x * ((((betaTwoConst a b : ℚ)⁻¹ : ℚ) : ℝ) * (x ^ a * (1 - x) ^ b)) = _
      rw [pow_succ', pow_succ']; ring
    have hI : (∫ x in 0..1, x ^ (((a : ℕ) + 1) + 1) * (1 - x) ^ b)
        = ((betaTwoConst ((a : ℕ) + 2) b : ℚ) : ℝ) := betaInt_eq ((a : ℕ) + 2) b
    rw [intervalIntegral.integral_congr (fun x _ => hshape x),
      intervalIntegral.integral_const_mul, hI]
    have hq : ((betaTwoConst a b : ℚ)⁻¹) * ((betaTwoConst ((a : ℕ) + 2) b : ℚ))
        = (((a : ℕ) + 1) * ((a : ℕ) + 2) : ℚ)
          / (((a : ℕ) + b + 2) * ((a : ℕ) + b + 3)) := by
      rw [inv_mul_eq_div, betaTwoConst_ratio2]
    exact_mod_cast hq

/-- 整型形状多项式 Beta 的方差（E[x²] - E[x]² 的代数式）：
    Var = (a+1)(b+1)/((a+b+2)²(a+b+3))（形状参数取 (a+1,b+1)）。 -/
theorem polyBeta_variance (a b : ℕ) :
    ((∫ x in 0..1, x * x * polyBeta (a + 1) (b + 1) x)
        - ((∫ x in 0..1, x * polyBeta (a + 1) (b + 1) x)
          * (∫ x in 0..1, x * polyBeta (a + 1) (b + 1) x))
      = (((a : ℕ) + 1) * ((b : ℕ) + 1) : ℚ)
        / (((a : ℕ) + b + 2) * ((a : ℕ) + b + 2) * (((a : ℕ) + b + 2) + 1))) := by
  obtain ⟨h1, h2⟩ := polyBeta_moments a b
  have hq : ((((a : ℕ) + 1) * ((a : ℕ) + 2) : ℚ) / (((a : ℕ) + b + 2) * ((a : ℕ) + b + 3)))
      - (((a : ℕ) + 1 : ℚ) / ((a : ℕ) + b + 2))
          * (((a : ℕ) + 1 : ℚ) / ((a : ℕ) + b + 2))
      = (((a : ℕ) + 1) * ((b : ℕ) + 1) : ℚ)
        / (((a : ℕ) + b + 2) * ((a : ℕ) + b + 2) * (((a : ℕ) + b + 2) + 1)) := by
    field_simp <;> ring
  rw [h1, h2]
  exact_mod_cast hq

/-! ## 第 18 针：beta_posterior_from_likelihood -/

/-- **第 18 针（S3，I.13:772；BINDING 行 18）**：真实密度层的共轭更新
    （**整型形状参数、多项式密度**，如实标注）。
    锚 `Probability.lean:289` 同 basename 定理只有 ℚ 权重层归一（该锚保留不动，
    不能同名销账）：本针交出三段——
    (1) 边际似然：先验密度×伯努利计数似然（x^k(1-x)^l）在 [0,1] 上的积分
        = B(a+k,b+l)/B(a,b)（后验归一化常数的精确值）；
    (2) 逐点共轭：归一化后的乘积恰为形状更新后的同族密度
        polyBeta (a+k+1) (b+l+1)；
    (3) 后验密度归一（衔接 (1)(2)）。
    边界：密度族限于整数形状（多项式 + 阶乘闭式 Beta 值），非 Gamma 一般理论；
    似然限于成败计数似然。 -/
theorem beta_posterior_from_likelihood (a b k l : ℕ) :
    ((∫ x in 0..1, polyBeta (a + 1) (b + 1) x * (x ^ k * (1 - x) ^ l))
      = ((betaTwoConst ((a : ℕ) + k) ((b : ℕ) + l) : ℚ) / (betaTwoConst a b : ℚ) : ℚ)) ∧
    (∀ x : ℝ, polyBeta (a + 1) (b + 1) x * (x ^ k * (1 - x) ^ l)
        * ((betaTwoConst a b : ℚ) / (betaTwoConst ((a : ℕ) + k) ((b : ℕ) + l) : ℚ) : ℚ)
      = polyBeta (((a : ℕ) + k) + 1) (((b : ℕ) + l) + 1) x) ∧
    ((∫ x in 0..1, polyBeta (((a : ℕ) + k) + 1) (((b : ℕ) + l) + 1) x) = 1) := by
  refine ⟨?_, ?_, polyBeta_integral_one ((a : ℕ) + k) ((b : ℕ) + l)⟩
  · have hshape : ∀ x : ℝ, polyBeta (a + 1) (b + 1) x * (x ^ k * (1 - x) ^ l)
        = (((betaTwoConst a b : ℚ)⁻¹ : ℚ) : ℝ)
          * (x ^ ((a : ℕ) + k) * (1 - x) ^ ((b : ℕ) + l)) := by
      intro x
      show ((((betaTwoConst a b : ℚ)⁻¹ : ℚ) : ℝ) * (x ^ a * (1 - x) ^ b))
          * (x ^ k * (1 - x) ^ l) = _
      rw [pow_add, pow_add]; ring
    have hI : (∫ x in 0..1, x ^ ((a : ℕ) + k) * (1 - x) ^ ((b : ℕ) + l))
        = ((betaTwoConst ((a : ℕ) + k) ((b : ℕ) + l) : ℚ) : ℝ) :=
      betaInt_eq ((a : ℕ) + k) ((b : ℕ) + l)
    rw [intervalIntegral.integral_congr (fun x _ => hshape x),
      intervalIntegral.integral_const_mul, hI]
    have hq : ((betaTwoConst a b : ℚ)⁻¹)
        * ((betaTwoConst ((a : ℕ) + k) ((b : ℕ) + l) : ℚ))
        = ((betaTwoConst ((a : ℕ) + k) ((b : ℕ) + l) : ℚ) / (betaTwoConst a b : ℚ)) := by
      rw [inv_mul_eq_div]
    exact_mod_cast hq
  · intro x
    have hBR : ((betaTwoConst a b : ℚ) : ℝ) ≠ 0 := by
      exact_mod_cast (betaTwoConst_pos a b).ne'
    have hB'R : ((betaTwoConst ((a : ℕ) + k) ((b : ℕ) + l) : ℚ) : ℝ) ≠ 0 := by
      exact_mod_cast (betaTwoConst_pos _ _).ne'
    simp only [polyBeta, Nat.add_sub_cancel]
    rw [pow_add, pow_add]
    push_cast
    field_simp [hBR, hB'R] <;> ring

/-! ## 第 19 针：equal_rate_different_posterior -/

/-- **第 19 针（S3，I.13:773；BINDING 行 19，原 UNBOUND）**：同比率、不同证据量
    的后验见证。(1) 比率相同：1/2 = 100/200；(2) 同一先验：均匀密度 polyBeta 1 1 ≡ 1；
    (3) 两组证据（1 成 1 败 / 100 成 100 败）经第 18 针共轭更新分别得到
    polyBeta 2 2（Beta(2,2)）与 polyBeta 101 101（Beta(101,101)）；(4) 两个后验的
    方差（E[x²] - E[x]²）分别为 1/20 与 1/812，显式不同——比率无法区分的证据量
    在后验集中度上被区分。
    边界：方差是代数式取值，不涉及任何真实审判数据；证据似然为成败计数。 -/
theorem equal_rate_different_posterior :
    ((1 : ℚ) / 2 = 100 / 200) ∧
    (∀ x : ℝ, polyBeta 1 1 x = 1) ∧
    (∀ x : ℝ, polyBeta 1 1 x * (x ^ 1 * (1 - x) ^ 1)
        * ((betaTwoConst 0 0 : ℚ) / (betaTwoConst 1 1 : ℚ) : ℚ)
      = polyBeta 2 2 x) ∧
    (∀ x : ℝ, polyBeta 1 1 x * (x ^ 100 * (1 - x) ^ 100)
        * ((betaTwoConst 0 0 : ℚ) / (betaTwoConst 100 100 : ℚ) : ℚ)
      = polyBeta 101 101 x) ∧
    ((∫ x in 0..1, x * x * polyBeta 2 2 x)
        - ((∫ x in 0..1, x * polyBeta 2 2 x) * (∫ x in 0..1, x * polyBeta 2 2 x))
      = ((1 / 20 : ℚ) : ℝ)) ∧
    ((∫ x in 0..1, x * x * polyBeta 101 101 x)
        - ((∫ x in 0..1, x * polyBeta 101 101 x) * (∫ x in 0..1, x * polyBeta 101 101 x))
      = ((1 / 812 : ℚ) : ℝ)) ∧
    (((1 / 20 : ℚ) : ℝ) ≠ ((1 / 812 : ℚ) : ℝ)) := by
  refine ⟨by norm_num, ?_, (beta_posterior_from_likelihood 0 0 1 1).2.1,
    (beta_posterior_from_likelihood 0 0 100 100).2.1, ?_, ?_, by norm_num⟩
  · intro x
    have hc : betaTwoConst 0 0 = 1 := by
      unfold betaTwoConst; norm_num
    show (((betaTwoConst 0 0 : ℚ)⁻¹ : ℚ) : ℝ) * (x ^ 0 * (1 - x) ^ 0) = 1
    rw [hc]
    simp
  · have hv := polyBeta_variance 1 1
    norm_num at hv ⊢
    exact hv
  · have hv := polyBeta_variance 100 100
    norm_num at hv ⊢
    exact hv

/-! ## 第 20 针：beta_cdf_rat_cast -/

/-- Beta(2,2) 的 CDF 有理闭式（部分和）：3q² - 2q³。 -/
def ratCdf22 (q : ℚ) : ℚ := 3 * q * q - 2 * q * q * q

/-- **第 20 针（S3，I.13:774；BINDING 行 20）**：有限多项式与 Beta 测度积分的同义
    （CDF 的有理转换）。锚 `Probability.lean:311 beta_predictive_bracket_survives_update`
    只证更新后总质量为 1，不能代替本针；本针在第 18 针的多项式密度载体上把 CDF
    定义为区间积分（polyBeta 2 2 = 6x(1-x)，归一化常数 B(1,1)⁻¹ = 6 由 decide 给出），
    并证其对任意有理点 q 的取值与 ℚ 闭式 ratCdf22 q = 3q²-2q³ 经 cast 完全一致
    （反导数 3t²-2t³，微积分基本定理）。
    边界：一致性在 Beta(2,2) 载体上陈述；一般形状的 CDF 部分和通式不在本件。 -/
theorem beta_cdf_rat_cast (q : ℚ) :
    (∫ x in 0..((q : ℝ)), polyBeta 2 2 x) = ((ratCdf22 q : ℚ) : ℝ) := by
  have hshape : ∀ y : ℝ, polyBeta 2 2 y = 6 * (y * (1 - y)) := by
    intro y
    have hc : betaTwoConst 1 1 = 1 / 6 := by
      unfold betaTwoConst; norm_num
    show (((betaTwoConst 1 1 : ℚ)⁻¹ : ℚ) : ℝ) * (y ^ 1 * (1 - y) ^ 1) = 6 * (y * (1 - y))
    rw [hc]
    push_cast
    field_simp <;> ring
  have hD : ∀ x : ℝ, HasDerivAt (fun t => 3 * t ^ 2 - 2 * t ^ 3) (6 * (x * (1 - x))) x := by
    intro x
    have h2 := ((hasDerivAt_pow 2 x).const_mul 3)
    have h3 := ((hasDerivAt_pow 3 x).const_mul 2)
    simpa using h2.sub h3
  have hII : IntervalIntegrable (fun y => 6 * (y * (1 - y))) MeasureTheory.volume 0 ((q : ℝ)) :=
    Continuous.intervalIntegrable (by continuity) 0 _
  have hFT0 := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun t => 3 * t ^ 2 - 2 * t ^ 3) (f' := fun y => 6 * (y * (1 - y)))
    (a := 0) (b := ((q : ℝ))) (fun x _ => hD x) hII
  have hFT : (∫ y in 0..((q : ℝ)), 6 * (y * (1 - y)))
      = (fun t : ℝ => 3 * t ^ 2 - 2 * t ^ 3) ((q : ℝ))
        - (fun t : ℝ => 3 * t ^ 2 - 2 * t ^ 3) 0 := hFT0
  have h0 : (fun t : ℝ => 3 * t ^ 2 - 2 * t ^ 3) 0 = 0 := by simp
  rw [intervalIntegral.integral_congr (g := fun y => 6 * (y * (1 - y)))
    (fun y _ => hshape y), hFT, h0, sub_zero]
  unfold ratCdf22
  push_cast
  ring

/-! ## 第 21 针：beta_quantile_enclosure -/

/-- 四分格点（0, 1/4, …, 1）上的 Beta(2,2) 精确 CDF 值（ℚ 闭式）。 -/
def gridCdf (k : ℕ) : ℚ := ratCdf22 ((k : ℚ) / 4)

/-- 格点 CDF 单调性的有限验证（Fin 5 全枚举，闭式 ℚ 比较）。 -/
theorem gridCdf_mono_bounded :
    ∀ (j k : Fin 5), (j : ℕ) ≤ (k : ℕ) → gridCdf (j : ℕ) ≤ gridCdf (k : ℕ) := by
      intro j k hjk
      fin_cases j <;> fin_cases k <;>
        first
        | exact absurd hjk (by omega)
        | norm_num [gridCdf, ratCdf22]

/-- 格点 CDF 在 0..4 上单调（由有限枚举版转换）。 -/
theorem gridCdf_mono (j k : ℕ) (hjk : j ≤ k) (hk : k ≤ 4) : gridCdf j ≤ gridCdf k :=
  gridCdf_mono_bounded (⟨j, by omega⟩ : Fin 5) (⟨k, by omega⟩ : Fin 5) hjk

/-- 搜索存在性：p < 1 时必有格点 CDF 越过 p（k = 4 处 CDF = 1）。 -/
theorem s3aEx (p : ℚ) (hp : p < 1) : ∃ k : ℕ, p < gridCdf k := by
  have hg4 : gridCdf 4 = 1 := by norm_num [gridCdf, ratCdf22]
  refine ⟨4, ?_⟩
  rw [hg4]
  exact hp

/-- 分位函数：有限格点上的精确搜索（`Nat.find`：最小使 CDF 严格越过 p 的格点）。 -/
def s3aQuantile (p : ℚ) (hp : p < 1) : ℕ := Nat.find (s3aEx p hp)

/-- p = 1/2 的搜索前提（闭式）。 -/
theorem s3aHalfLt : (1 / 2 : ℚ) < 1 := by norm_num

/-- **第 21 针（S3，I.13:775；BINDING 行 21，原 UNBOUND）**：整数形状精确 CDF
    比较二分，分位封闭。在 18/20 针的格点载体上定义分位函数 `s3aQuantile`
    （有限精确搜索），并证特征化等价：对 q ≤ 3，
    q+1 是搜索命中 ⟺ gridCdf q ≤ p < gridCdf (q+1)（CDF(q) 与 CDF(q+1) 夹逼）；
    搜索命中落在 1..4（p ≥ 0 保证不取 0，k = 4 保证上界）；并给 p = 1/2 的闭式实例：
    命中 3，夹逼 1/2 ≤ 1/2 < 27/32。
    边界：分位定义在四分有理格点上，夹逼特征化限 q ≤ 3；一般可计算 CDF 的
    双点缩区不在本件。 -/
theorem beta_quantile_enclosure (p : ℚ) (hp0 : 0 ≤ p) (hp1 : p < 1) :
    (∀ q : ℕ, q ≤ 3 → ((q + 1 = s3aQuantile p hp1)
        ↔ ((gridCdf q ≤ p) ∧ (p < gridCdf (q + 1)))))
    ∧ ((1 ≤ s3aQuantile p hp1) ∧ (s3aQuantile p hp1 ≤ 4))
    ∧ ((s3aQuantile (1 / 2) s3aHalfLt = 3)
      ∧ ((gridCdf 2 ≤ 1 / 2 ∧ 1 / 2 < gridCdf 3)
        ∧ (gridCdf 2 = 1 / 2 ∧ gridCdf 3 = 27 / 32))) := by
  refine ⟨?_, ?_, ?_⟩
  · intro q hq3
    constructor
    · intro h
      rw [show s3aQuantile p hp1 = Nat.find (s3aEx p hp1) from rfl] at h
      refine ⟨le_of_not_gt (Nat.find_min (H := s3aEx p hp1) (by omega)), ?_⟩
      have hspec := Nat.find_spec (H := s3aEx p hp1)
      rwa [← h] at hspec
    · intro hqc
      have hle : s3aQuantile p hp1 ≤ q + 1 := Nat.find_min' (H := s3aEx p hp1) hqc.2
      have hge : q + 1 ≤ s3aQuantile p hp1 := by
        by_contra hlt
        have hQle : s3aQuantile p hp1 ≤ q := by omega
        have hmono : gridCdf (s3aQuantile p hp1) ≤ gridCdf q :=
          gridCdf_mono _ _ hQle (by omega)
        have hspec := Nat.find_spec (H := s3aEx p hp1)
        exact absurd (lt_of_lt_of_le hspec (le_trans hmono hqc.1)) (lt_irrefl p)
      omega
  · refine ⟨?_, ?_⟩
    · rcases Nat.eq_zero_or_pos (s3aQuantile p hp1) with h | h
      · have hg0 : gridCdf 0 = 0 := by norm_num [gridCdf, ratCdf22]
        have hspec : p < gridCdf (s3aQuantile p hp1) := Nat.find_spec (H := s3aEx p hp1)
        rw [h, hg0] at hspec
        exact absurd (lt_of_le_of_lt hp0 hspec) (lt_irrefl 0)
      · exact h
    · have hg4 : gridCdf 4 = 1 := by norm_num [gridCdf, ratCdf22]
      exact Nat.find_min' (H := s3aEx p hp1) (by rw [hg4]; exact hp1)
  · refine ⟨?_, ⟨⟨by norm_num [gridCdf, ratCdf22], by norm_num [gridCdf, ratCdf22]⟩, by norm_num [gridCdf, ratCdf22]⟩⟩
    have hg3 : (1 / 2 : ℚ) < gridCdf 3 := by norm_num [gridCdf, ratCdf22]
    have hg2 : gridCdf 2 ≤ 1 / 2 := by norm_num [gridCdf, ratCdf22]
    have hle : s3aQuantile (1 / 2) s3aHalfLt ≤ 3 :=
      Nat.find_min' (H := s3aEx (1 / 2) s3aHalfLt) hg3
    have hge : 3 ≤ s3aQuantile (1 / 2) s3aHalfLt := by
      by_contra hlt
      have hQ2 : s3aQuantile (1 / 2) s3aHalfLt ≤ 2 := by omega
      have hmono : gridCdf (s3aQuantile (1 / 2) s3aHalfLt) ≤ gridCdf 2 :=
        gridCdf_mono _ _ hQ2 (by omega)
      have hspec := Nat.find_spec (H := s3aEx (1 / 2) s3aHalfLt)
      exact absurd (lt_of_lt_of_le hspec (le_trans hmono hg2)) (lt_irrefl (1 / 2))
    omega

end JurisLean.Seams.UnifiedNeedlesS3a
