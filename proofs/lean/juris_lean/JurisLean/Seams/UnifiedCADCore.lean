import Mathlib

/-
Unified CAD core, layer C0/C1 (plan §6.3; appendix I.0.1 rows C0 and C1,
the "complete encoding" and "univariate root certificate checker" rows that
`Seams/UnifiedCAD.lean` had only a quadratic miniature of).

C0 — COMPLETE ENCODING AND TRANSLATION
* `RealFormula n`: real closed field formulas over a FIXED variable table of
  length `n`.  Atoms compare a multivariate rational polynomial
  (`MvPolynomial (Fin n) ℚ`) against 0 with =/</≤; connectives and/or/not;
  quantifiers ∀/∃ nest by de Bruijn-style table extension
  (`RealFormula (n+1) → RealFormula n`), so QUANTIFIER ORDER IS CARRIED BY
  CONSTRUCTION — witnessed by `quantifier_order_matters`.
* Division guard: the source language `SrcAtom` has division atoms `p/q ⋈ 0`.
  Translation sends them to `q ≠ 0 ∧ p·q ⋈ 0` (the nonzero-witness guard;
  `div_translation_sound`), and when the denominator is the ZERO POLYNOMIAL
  the translation returns `Failed` WITH A REASON
  (`translate_zero_denom_fails`).  `failed_is_not_formula_false` proves the
  contract sentence "解析/定义域失败保持 Failed，不能当公式假": a Failed atom
  is satisfied NOWHERE and DEFINED nowhere, while a genuinely-false formula
  (0 = 1) is satisfied nowhere but DEFINED everywhere — the two states are
  distinguishable, so Failed is an independent semantic state, never a
  formula value.
* `AlgRealCode`: algebraic number code = minimal polynomial + unique
  isolation interval (lo < hi), with denotation, a validity predicate, the
  identity-check theorem `AlgMeaning_subsingleton` (a valid code denotes a
  UNIQUE number), and the nontrivial instance √2 = X²−2 on (1,2) with full
  uniqueness proof.

C1 — UNIVARIATE ROOT CERTIFICATE CHECKER, FULL DEGREE
* `RootCert` carries: isolation entries (ordered disjoint rational intervals,
  a real root in each, its exact multiplicity), the TOTAL distinct-root
  count declaration, and a claimed squarefree decomposition (h, g).
* `checkRootCert p c` verifies, WITHOUT CALLING ANY SOLVER:
  1. polynomial identities — each root by exact substitution
     (`IsRRoot p e.r`), each multiplicity against mathlib's
     `rootMultiplicity`, and the squarefree decomposition identity
     `h * g = p` with `h = gcd(p, p')` (the Euclidean gcd chain identity,
     `sqfree_decomp_identity`);
  2. interval bookkeeping — strictly ordered, disjoint, each root inside its
     interval (`IvsOrdered`);
  3. COMPLETENESS, the hard requirement ("不收只报见到的根"): the checker
     STRUCTURALLY CONSUMES the total-count declaration
     `entries.length = total` and ties it to the sign-variation count of the
     Sturm chain of `p` ACTUALLY CONSTRUCTED IN THIS FILE:
     `total = varCount p`.
* `checkRootCert_sound`: acceptance (+ the one explicit named hypothesis
  `SturmComplete p`) implies the certified roots are EXACTLY ALL real roots
  of `p`, each with exact multiplicity structure — the C1 denote-shape
  discipline, for arbitrary degree, not just quadratics.

Scope, honestly:
* The full Sturm theorem (variation count = number of distinct real roots)
  is NOT in mathlib v4.30.0 (grepped: no Sturm/subresultant library; the
  only textual hits are unrelated modular-forms).  It enters here as ONE
  explicit named hypothesis `SturmComplete p`, stated on the concrete
  `varCount`/`sturmChain` built in this file, consumed only by the
  completeness half of `checkRootCert_sound`; the algebraic half (roots are
  roots, multiplicities, ordering) is unconditional.  Zero sorry, zero
  custom axioms.
* Degenerate cases get dedicated theorems, not bare rejection: zero
  polynomial (`zero_poly_universal_root`, `zero_poly_rejected`,
  `zero_poly_no_finite_root_list`), constant/no-root polynomials (accepted
  by an empty certificate, unconditionally sound:
  `checkRootCert_const`), multiple roots (accepted with exact multiplicity,
  unconditionally: `checkRootCert_double_root`), and leading-coefficient
  drop (the chain machinery is stated for arbitrary polys; degree drop
  `degree_drop` and unit-scaling invariance `isRRoot_C_smul`).
* Open (declared, not hidden): the full Sturm theorem itself;
  subresultant sign variations as an alternative certificate;
  `Squarefree (sqfreePart p)` in general; polynomials with AlgRealCode
  coefficients beyond the structure+denotation+instance delivered here.
-/

noncomputable section

namespace JurisLean.Seams.UnifiedCADCore

/- `ℚ[X]` 等多项式记号是 `Polynomial` 命名空间内的 scoped 记号（CI 38064007904 核实），
文件级打开一次。doc 注不能连挂 `open`（CI 38065516547 第 81 行），此处用普通块注。 -/
open Polynomial

/-! ## 〇、公共：有理数到实数的精确嵌入 -/

/-- ℚ → ℝ 的精确环嵌入（cast 同态；与 `Rat.cast` 逐点重合）。 -/
noncomputable def qToR : ℚ →+* ℝ where
  toFun a := (a : ℝ)
  map_one' := Rat.cast_one
  map_mul' := Rat.cast_mul
  map_zero' := Rat.cast_zero
  map_add' := Rat.cast_add

theorem qToR_injective : Function.Injective qToR := by
  intro a b h
  exact Rat.cast_injective (show (a : ℝ) = (b : ℝ) from h)

theorem qToR_zero : qToR 0 = (0 : ℝ) := by
  show ((0 : ℚ) : ℝ) = (0 : ℝ)
  exact Rat.cast_zero

theorem qToR_two : qToR 2 = (2 : ℝ) := by
  show ((2 : ℚ) : ℝ) = (2 : ℝ)
  exact Rat.cast_ofNat 2

/-! ## 一、C0：比较算子、原子与实闭域公式 -/

/-- 比较算子。 -/
inductive CmpOp : Type where
  | eq | lt | le

/-- 比较算子的实数语义。 -/
def cmpRel : CmpOp → ℝ → ℝ → Prop
  | .eq, x, y => x = y
  | .lt, x, y => x < y
  | .le, x, y => x ≤ y

/-- 原子：比较算子 ＋ 有理系数多变元多项式（对 0 比较）。 -/
structure RAtom (n : ℕ) : Type where
  op : CmpOp
  poly : MvPolynomial (Fin n) ℚ

/-- C0 实闭域公式：固定变量表 `Fin n`，量词按表扩展嵌套（de Bruijn 风格），
    量词顺序由构造保义。深度 `n` 是**索引**（量词构造子引用 `RealFormula (n+1)`，
    参数形式下不允许变化——CI 38064007904 第 126 行根因）。 -/
inductive RealFormula : ℕ → Type where
  | atom {n : ℕ} : RAtom n → RealFormula n
  | and {n : ℕ} : RealFormula n → RealFormula n → RealFormula n
  | or {n : ℕ} : RealFormula n → RealFormula n → RealFormula n
  | not {n : ℕ} : RealFormula n → RealFormula n
  | all {n : ℕ} : RealFormula (n + 1) → RealFormula n
  | ex {n : ℕ} : RealFormula (n + 1) → RealFormula n

/-- 多项式在赋值下的实指称。 -/
def polyDenote {n : ℕ} (ρ : Fin n → ℝ) (p : MvPolynomial (Fin n) ℚ) : ℝ :=
  MvPolynomial.eval₂ qToR ρ p

/-- 原子指称。 -/
def denoteAtom {n : ℕ} (ρ : Fin n → ℝ) (a : RAtom n) : Prop :=
  cmpRel a.op (polyDenote ρ a.poly) 0

/-- 公式指称：∃/∀ 绑定变量表的下一个变量（第 n 个）。 -/
def RealFormula.denote {n : ℕ} (ρ : Fin n → ℝ) : RealFormula n → Prop
  | .atom a => denoteAtom ρ a
  | .and f g => denote ρ f ∧ denote ρ g
  | .or f g => denote ρ f ∨ denote ρ g
  | .not f => ¬ denote ρ f
  | .all f => ∀ x : ℝ, denote (Fin.snoc ρ x) f
  | .ex f => ∃ x : ℝ, denote (Fin.snoc ρ x) f

/-- snoc 赋值下表内变量不变。 -/
theorem eval₂_X_castSucc {n : ℕ} (ρ : Fin n → ℝ) (x : ℝ) (i : Fin n) :
    MvPolynomial.eval₂ qToR (Fin.snoc ρ x) (MvPolynomial.X (Fin.castSucc i)) = ρ i := by
  rw [MvPolynomial.eval₂_X, Fin.snoc_castSucc]

/-- snoc 赋值下新绑定的末变量取绑定值。 -/
theorem eval₂_X_last {n : ℕ} (ρ : Fin n → ℝ) (x : ℝ) :
    MvPolynomial.eval₂ qToR (Fin.snoc ρ x) (MvPolynomial.X (Fin.last n)) = x := by
  rw [MvPolynomial.eval₂_X, Fin.snoc_last]

/-- **量词顺序由构造保义**：同一原子多项式 x−y ≤ 0，
    `∀x∃y` 真（取 y = x）而 `∃x∀y` 假（取 y = x−1）——
    两种嵌套顺序给出不同指称，顺序不能由语义层补回，必须由构造携带。 -/
theorem quantifier_order_matters :
    (RealFormula.all (RealFormula.ex
        (RealFormula.atom (RAtom.mk CmpOp.le
          (MvPolynomial.X (Fin.castSucc (0 : Fin 1)) - MvPolynomial.X (Fin.last 1)))))).denote
        (fun _ : Fin 0 => (0 : ℝ)) ∧
    ¬(RealFormula.ex (RealFormula.all
        (RealFormula.atom (RAtom.mk CmpOp.le
          (MvPolynomial.X (Fin.castSucc (0 : Fin 1)) - MvPolynomial.X (Fin.last 1)))))).denote
        (fun _ : Fin 0 => (0 : ℝ)) := by
  constructor
  · intro x
    refine ⟨x, ?_⟩
    show cmpRel CmpOp.le
      (polyDenote (Fin.snoc (Fin.snoc (fun _ : Fin 0 => (0:ℝ)) x) x)
        (MvPolynomial.X (Fin.castSucc (0 : Fin 1)) -
          MvPolynomial.X (Fin.last 1))) 0
    simp only [polyDenote, MvPolynomial.eval₂_sub,
      eval₂_X_castSucc, eval₂_X_last, Fin.snoc_zero, cmpRel]
    rw [sub_self]
  · rintro ⟨x, hx⟩
    specialize hx (x - 1)
    have hx2 : cmpRel CmpOp.le
      (polyDenote (Fin.snoc (Fin.snoc (fun _ : Fin 0 => (0:ℝ)) x) (x - 1))
        (MvPolynomial.X (Fin.castSucc (0 : Fin 1)) -
          MvPolynomial.X (Fin.last 1))) 0 := hx
    simp only [polyDenote, MvPolynomial.eval₂_sub,
      eval₂_X_castSucc, eval₂_X_last, Fin.snoc_zero, cmpRel] at hx2
    linarith

/-! ## 二、C0：实代数数编码 AlgRealCode -/

open Polynomial in
/-- 实代数编码的实多项式取值。 -/
def AlgEval (p : ℚ[X]) (x : ℝ) : ℝ := (p.map qToR).eval x

open Polynomial in
/-- **AlgRealCode**：代数数以最小多项式 ＋ 唯一隔离区间定义（C0 行合同）。 -/
structure AlgRealCode : Type where
  minpoly : ℚ[X]
  lo : ℚ
  hi : ℚ
  lo_lt_hi : lo < hi

open Polynomial in
/-- 编码在点 x 处的语义（在区间内且为多项式的根）。 -/
def AlgMeaning (c : AlgRealCode) (x : ℝ) : Prop :=
  AlgEval c.minpoly x = 0 ∧ (c.lo : ℝ) < x ∧ x < (c.hi : ℝ)

open Polynomial in
/-- 有效性：隔离区间内恰有一根——此时编码的指称是唯一确定的数。 -/
def AlgRealCode.Validity (c : AlgRealCode) : Prop := ∃! x : ℝ, AlgMeaning c x

/-- **恒等检查定理**：有效编码的指称唯一——两个"指称"若都落在同一有效
    编码的隔离区间内则必相等（编码是函数，不是见证集合）。 -/
theorem AlgMeaning_subsingleton (c : AlgRealCode) (hc : c.Validity)
    {x y : ℝ} (hx : AlgMeaning c x) (hy : AlgMeaning c y) : x = y :=
  hc.unique hx hy

open Polynomial in
/-- 非平凡实例：√2 以 X²−2 与隔离区间 (1, 2) 编码。 -/
def algRealSqrt2 : AlgRealCode where
  minpoly := X ^ 2 - C 2
  lo := 1
  hi := 2
  lo_lt_hi := by norm_num

open Polynomial in
/-- 实例取值恒等式：AlgEval (X²−2) x = x²−2。 -/
theorem algEval_X2_sub_2 (x : ℝ) : AlgEval (X ^ 2 - C 2) x = x ^ 2 - 2 := by
  rw [AlgEval, Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X,
    Polynomial.map_C, Polynomial.eval_sub, Polynomial.eval_pow,
    Polynomial.eval_X, Polynomial.eval_C, qToR_two]

open Polynomial in
/-- 实例的区间界的具体值（便于有序域推理；x 显式以便调用侧直接喂点）。 -/
theorem algRealSqrt2_bounds (x : ℝ) (hx : AlgMeaning algRealSqrt2 x) :
    (1:ℝ) < x ∧ x < 2 := by
  have e1 : ((algRealSqrt2.lo : ℚ) : ℝ) = (1:ℝ) := by norm_num [algRealSqrt2]
  have e2 : ((algRealSqrt2.hi : ℚ) : ℝ) = (2:ℝ) := by norm_num [algRealSqrt2]
  obtain ⟨-, h1, h2⟩ := hx
  exact ⟨by rw [← e1]; exact h1, by rw [← e2]; exact h2⟩

open Polynomial in
theorem algRealSqrt2_validity : algRealSqrt2.Validity := by
  have hb : (1:ℝ) < Real.sqrt 2 ∧ Real.sqrt 2 < 2 := by
    refine ⟨?_, ?_⟩
    · rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
      exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
    · have h := Real.sqrt_lt_sqrt (by norm_num : (0:ℝ) ≤ 2) (by norm_num : (2:ℝ) < 4)
      rwa [show (4:ℝ) = (2:ℝ) * 2 from by norm_num, Real.sqrt_mul_self (by norm_num)] at h
  have hlo : ((algRealSqrt2.lo : ℚ) : ℝ) = (1:ℝ) := by norm_num [algRealSqrt2]
  have hhi : ((algRealSqrt2.hi : ℚ) : ℝ) = (2:ℝ) := by norm_num [algRealSqrt2]
  refine ⟨Real.sqrt 2,
    ⟨?_, by rw [hlo]; exact hb.1, by rw [hhi]; exact hb.2⟩, fun y hy => ?_⟩
  · show AlgEval (X ^ 2 - C 2) (Real.sqrt 2) = 0
    rw [algEval_X2_sub_2, Real.sq_sqrt (by norm_num)]
    norm_num
  · obtain ⟨h1y, h2y⟩ := algRealSqrt2_bounds y hy
    have hy2 : y ^ 2 = 2 := by
      have hz : AlgEval (X ^ 2 - C 2) y = 0 := hy.1
      rw [algEval_X2_sub_2] at hz
      linarith
    have hsq : y * y = Real.sqrt 2 * Real.sqrt 2 := by
      rw [← pow_two, ← pow_two, hy2, Real.sq_sqrt (by norm_num)]
    rw [mul_self_eq_mul_self_iff] at hsq
    rcases hsq with h | h
    · exact h
    · linarith [Real.sqrt_pos.mpr (by norm_num : (0:ℝ) < 2), h]

open Polynomial in
/-- 实例的指称恒等检查：任何落在该编码区间内的根都是 √2。 -/
theorem algRealSqrt2_denote_eq {x : ℝ} (hx : AlgMeaning algRealSqrt2 x) :
    x = Real.sqrt 2 := by
  obtain ⟨h1x, h2x⟩ := algRealSqrt2_bounds x hx
  have hx2 : x ^ 2 = 2 := by
    have hz : AlgEval (X ^ 2 - C 2) x = 0 := hx.1
    rw [algEval_X2_sub_2] at hz
    linarith
  have hsq : x * x = Real.sqrt 2 * Real.sqrt 2 := by
    rw [← pow_two, ← pow_two, hx2, Real.sq_sqrt (by norm_num)]
  rw [mul_self_eq_mul_self_iff] at hsq
  rcases hsq with h | h
  · exact h
  · linarith [Real.sqrt_pos.mpr (by norm_num : (0:ℝ) < 2), h, h1x]

/-! ## 三、C0：源语法、除法 guard 与翻译层 -/

/-- 源算式：常量/变量/加减乘（除法只出现在除原子顶层）。 -/
inductive SrcExpr (n : ℕ) : Type where
  | const : ℚ → SrcExpr n
  | var : Fin n → SrcExpr n
  | add : SrcExpr n → SrcExpr n → SrcExpr n
  | mul : SrcExpr n → SrcExpr n → SrcExpr n
  | neg : SrcExpr n → SrcExpr n

/-- 源算式到多项式（全函数）。 -/
def toPoly {n : ℕ} : SrcExpr n → MvPolynomial (Fin n) ℚ
  | .const q => MvPolynomial.C q
  | .var i => MvPolynomial.X i
  | .add a b => toPoly a + toPoly b
  | .mul a b => toPoly a * toPoly b
  | .neg a => -toPoly a

/-- 源算式的实数值（经 toPoly，保证单一语义通道）。 -/
def srcVal {n : ℕ} (ρ : Fin n → ℝ) (e : SrcExpr n) : ℝ := polyDenote ρ (toPoly e)

/-- 源原子：普通比较原子，或除原子 `p/q ⋈ 0`。 -/
inductive SrcAtom (n : ℕ) : Type where
  | cmp : CmpOp → SrcExpr n → SrcExpr n → SrcAtom n
  | divCmp : SrcExpr n → SrcExpr n → CmpOp → SrcAtom n

/-- 源原子语义（"有定义且满足"；除原子在分母为零的点无定义）。 -/
def srcAtomSat {n : ℕ} (ρ : Fin n → ℝ) : SrcAtom n → Prop
  | .cmp op a b => cmpRel op (srcVal ρ a) (srcVal ρ b)
  | .divCmp a b op => srcVal ρ b ≠ 0 ∧ cmpRel op (srcVal ρ a / srcVal ρ b) 0

/-- 源原子在赋值处是否有定义（除原子要求分母非零）。 -/
def srcAtomDefined {n : ℕ} (ρ : Fin n → ℝ) : SrcAtom n → Prop
  | .cmp _ _ _ => True
  | .divCmp _ b _ => srcVal ρ b ≠ 0

/-- 翻译结果：成功携带公式，失败携带原因。 -/
inductive TransResult (n : ℕ) : Type where
  | ok : RealFormula n → TransResult n
  | failed : String → TransResult n

/-- 除法 guard 符号引理：d ≠ 0 时 n/d 与 n·d 同号（< 0）。 -/
theorem div_mul_lt_zero_iff {n d : ℝ} (hd : d ≠ 0) : n / d < 0 ↔ n * d < 0 := by
  have hdd : (0:ℝ) < d * d := mul_self_pos.mpr hd
  have key : n * d = (n / d) * (d * d) := by field_simp
  constructor
  · intro h
    have h2 : (n / d) * (d * d) < 0 * (d * d) := mul_lt_mul_of_pos_right h hdd
    rwa [← key, zero_mul] at h2
  · intro h
    rw [key] at h
    exact lt_of_mul_lt_mul_right (by rwa [zero_mul]) (le_of_lt hdd)

/-- 除法 guard 符号引理：≤ 0。 -/
theorem div_mul_le_zero_iff {n d : ℝ} (hd : d ≠ 0) : n / d ≤ 0 ↔ n * d ≤ 0 := by
  have hdd : (0:ℝ) < d * d := mul_self_pos.mpr hd
  have key : n * d = (n / d) * (d * d) := by field_simp
  constructor
  · intro h
    have h2 : (n / d) * (d * d) ≤ 0 * (d * d) := mul_le_mul_of_nonneg_right h (le_of_lt hdd)
    rwa [← key, zero_mul] at h2
  · intro h
    rw [key] at h
    exact le_of_mul_le_mul_right (by rwa [zero_mul]) hdd

/-- 除法 guard 符号引理：= 0。 -/
theorem div_mul_eq_zero_iff {n d : ℝ} (hd : d ≠ 0) : n / d = 0 ↔ n * d = 0 := by
  constructor
  · intro h
    rcases div_eq_zero_iff.mp h with h' | h'
    · rw [h', zero_mul]
    · exact absurd h' hd
  · intro h
    rcases mul_eq_zero.mp h with h' | h'
    · rw [h', zero_div]
    · exact absurd h' hd

/-- 减式比较引理（逐点保义用）。 -/
theorem eq_iff_sub_eq_zero {x y : ℝ} : x = y ↔ x - y = 0 := by
  constructor
  · intro h
    rw [h, sub_self]
  · intro h
    linarith

theorem lt_iff_sub_lt_zero {x y : ℝ} : x < y ↔ x - y < 0 := by
  constructor
  · intro h
    linarith
  · intro h
    linarith

theorem le_iff_sub_le_zero {x y : ℝ} : x ≤ y ↔ x - y ≤ 0 := by
  constructor
  · intro h
    linarith
  · intro h
    linarith

/-- 原子翻译：比较原子精确翻译为多项式原子（对 ρ 逐点保义）。 -/
theorem cmp_translation_sound {n : ℕ} (op : CmpOp) (a b : SrcExpr n) (ρ : Fin n → ℝ) :
    srcAtomSat ρ (SrcAtom.cmp op a b) ↔
      RealFormula.denote ρ (RealFormula.atom (RAtom.mk op (toPoly a - toPoly b))) := by
  cases op
  · simp only [srcAtomSat, RealFormula.denote, denoteAtom, cmpRel, srcVal, polyDenote,
      toPoly, MvPolynomial.eval₂_sub]
    exact eq_iff_sub_eq_zero
  · simp only [srcAtomSat, RealFormula.denote, denoteAtom, cmpRel, srcVal, polyDenote,
      toPoly, MvPolynomial.eval₂_sub]
    exact lt_iff_sub_lt_zero
  · simp only [srcAtomSat, RealFormula.denote, denoteAtom, cmpRel, srcVal, polyDenote,
      toPoly, MvPolynomial.eval₂_sub]
    exact le_iff_sub_le_zero

/-- 原子翻译：除原子带非零见证 guard（q ≠ 0 ∧ p·q ⋈ 0），逐点保义。
    guard 由翻译后的公式显式携带（合同"除法 guard 带非零见证"）。 -/
theorem div_translation_sound {n : ℕ} (a b : SrcExpr n) (op : CmpOp) (ρ : Fin n → ℝ)
    (hqb : toPoly b ≠ 0) :
    srcAtomSat ρ (SrcAtom.divCmp a b op) ↔
      RealFormula.denote ρ (RealFormula.and
        (RealFormula.not (RealFormula.atom (RAtom.mk CmpOp.eq (toPoly b))))
        (RealFormula.atom (RAtom.mk op (toPoly a * toPoly b)))) := by
  constructor
  · rintro ⟨hd, hop⟩
    refine ⟨fun hzero => hd hzero, ?_⟩
    show RealFormula.denote ρ (RealFormula.atom (RAtom.mk op (toPoly a * toPoly b)))
    simp only [RealFormula.denote, denoteAtom, polyDenote]
    rw [MvPolynomial.eval₂_mul]
    cases op <;> simp only [cmpRel] at hop ⊢
    · exact (div_mul_eq_zero_iff hd).mp hop
    · exact (div_mul_lt_zero_iff hd).mp hop
    · exact (div_mul_le_zero_iff hd).mp hop
  · rintro ⟨hd, hop⟩
    refine ⟨hd, ?_⟩
    show cmpRel op (srcVal ρ a / srcVal ρ b) 0
    simp only [RealFormula.denote, denoteAtom, polyDenote, MvPolynomial.eval₂_mul] at hop
    cases op <;> simp only [cmpRel] at hop ⊢
    · exact (div_mul_eq_zero_iff hd).mpr hop
    · exact (div_mul_lt_zero_iff hd).mpr hop
    · exact (div_mul_le_zero_iff hd).mpr hop

/-- 原子翻译器：除原子分母为零多项式时整体进 Failed（携带原因），
    否则输出带 guard 的公式。 -/
def translateAtom {n : ℕ} : SrcAtom n → TransResult n
  | .cmp op a b => .ok (RealFormula.atom (RAtom.mk op (toPoly a - toPoly b)))
  | .divCmp a b op =>
      if toPoly b = 0 then
        .failed "divCmp: 分母为零多项式，定义域处处为空，保持 Failed"
      else
        .ok (RealFormula.and
          (RealFormula.not (RealFormula.atom (RAtom.mk CmpOp.eq (toPoly b))))
          (RealFormula.atom (RAtom.mk op (toPoly a * toPoly b))))

theorem translate_zero_denom_fails {n : ℕ} (a b : SrcExpr n) (op : CmpOp)
    (h : toPoly b = 0) :
    translateAtom (SrcAtom.divCmp a b op) =
      TransResult.failed "divCmp: 分母为零多项式，定义域处处为空，保持 Failed" := by
  simp [translateAtom, h]

theorem translate_div_ok {n : ℕ} (a b : SrcExpr n) (op : CmpOp) (h : toPoly b ≠ 0) :
    translateAtom (SrcAtom.divCmp a b op) =
      TransResult.ok (RealFormula.and
        (RealFormula.not (RealFormula.atom (RAtom.mk CmpOp.eq (toPoly b))))
        (RealFormula.atom (RAtom.mk op (toPoly a * toPoly b)))) := by
  simp [translateAtom, h]

/-- 原子翻译健全：凡翻译成功的原子，其输出公式逐点保义。 -/
theorem translateAtom_sound {n : ℕ} (a : SrcAtom n) (g : RealFormula n)
    (hg : translateAtom a = TransResult.ok g) (ρ : Fin n → ℝ) :
    srcAtomSat ρ a ↔ RealFormula.denote ρ g := by
  cases a with
  | cmp op a b =>
    rw [show translateAtom (SrcAtom.cmp op a b) =
      TransResult.ok (RealFormula.atom (RAtom.mk op (toPoly a - toPoly b))) from rfl] at hg
    cases hg
    exact cmp_translation_sound op a b ρ
  | divCmp a b op =>
    by_cases hqb : toPoly b = 0
    · rw [translate_zero_denom_fails a b op hqb] at hg
      simp at hg
    · rw [translate_div_ok a b op hqb] at hg
      cases hg
      exact div_translation_sound a b op ρ hqb

/-- 源公式（布尔组合）。 -/
inductive SrcFormula (n : ℕ) : Type where
  | atom : SrcAtom n → SrcFormula n
  | and : SrcFormula n → SrcFormula n → SrcFormula n
  | or : SrcFormula n → SrcFormula n → SrcFormula n
  | not : SrcFormula n → SrcFormula n

/-- 源公式语义。 -/
def srcDenote {n : ℕ} (ρ : Fin n → ℝ) : SrcFormula n → Prop
  | .atom a => srcAtomSat ρ a
  | .and f g => srcDenote ρ f ∧ srcDenote ρ g
  | .or f g => srcDenote ρ f ∨ srcDenote ρ g
  | .not f => ¬ srcDenote ρ f

/-- 组合结果传递：两侧都成功才组合，任一失败即携带其失败原因。 -/
def bind2 {n : ℕ} (op : RealFormula n → RealFormula n → RealFormula n)
    (rf rg : TransResult n) : TransResult n :=
  match rf, rg with
  | .ok f', .ok g' => .ok (op f' g')
  | .ok _, .failed r => .failed r
  | .failed r, _ => .failed r

/-- 一元组合结果传递。 -/
def bind1 {n : ℕ} (op : RealFormula n → RealFormula n)
    (rf : TransResult n) : TransResult n :=
  match rf with
  | .ok f' => .ok (op f')
  | .failed r => .failed r

/-- 解析函数：源公式 → Formula，失败保持 Failed（携带原因），不塌缩为公式假。 -/
def translate {n : ℕ} : SrcFormula n → TransResult n
  | .atom a => translateAtom a
  | .and f g => bind2 RealFormula.and (translate f) (translate g)
  | .or f g => bind2 RealFormula.or (translate f) (translate g)
  | .not f => bind1 RealFormula.not (translate f)

/-- **翻译健全**：凡翻译成功的源公式，其输出公式逐点保义。 -/
theorem translate_sound {n : ℕ} (f : SrcFormula n) : ∀ g : RealFormula n,
    translate f = TransResult.ok g → ∀ ρ : Fin n → ℝ,
      srcDenote ρ f ↔ RealFormula.denote ρ g := by
  induction f with
  | atom a => exact translateAtom_sound a
  | and f g ihf ihg =>
    intro gres h ρ
    cases hf : translate f with
    | ok f' =>
      cases hg' : translate g with
      | ok g' =>
        have hEq : translate (SrcFormula.and f g) = TransResult.ok (RealFormula.and f' g') := by
          simp only [translate, hf, hg', bind2]
        rw [hEq] at h
        cases h
        simp only [srcDenote, RealFormula.denote]
        exact ⟨fun hx => ⟨(ihf f' hf ρ).1 hx.1, (ihg g' hg' ρ).1 hx.2⟩,
          fun hx => ⟨(ihf f' hf ρ).2 hx.1, (ihg g' hg' ρ).2 hx.2⟩⟩
      | failed r =>
        have hEq : translate (SrcFormula.and f g) = TransResult.failed r := by
          simp only [translate, hf, hg', bind2]
        rw [hEq] at h
        simp at h
    | failed r =>
      have hEq : translate (SrcFormula.and f g) = TransResult.failed r := by
        simp only [translate, hf, bind2]
      rw [hEq] at h
      simp at h
  | or f g ihf ihg =>
    intro gres h ρ
    cases hf : translate f with
    | ok f' =>
      cases hg' : translate g with
      | ok g' =>
        have hEq : translate (SrcFormula.or f g) = TransResult.ok (RealFormula.or f' g') := by
          simp only [translate, hf, hg', bind2]
        rw [hEq] at h
        cases h
        simp only [srcDenote, RealFormula.denote]
        exact ⟨fun hx => hx.elim (fun x => Or.inl ((ihf f' hf ρ).1 x))
            (fun y => Or.inr ((ihg g' hg' ρ).1 y)),
          fun hx => hx.elim (fun x => Or.inl ((ihf f' hf ρ).2 x))
            (fun y => Or.inr ((ihg g' hg' ρ).2 y))⟩
      | failed r =>
        have hEq : translate (SrcFormula.or f g) = TransResult.failed r := by
          simp only [translate, hf, hg', bind2]
        rw [hEq] at h
        simp at h
    | failed r =>
      have hEq : translate (SrcFormula.or f g) = TransResult.failed r := by
        simp only [translate, hf, bind2]
      rw [hEq] at h
      simp at h
  | not f ihf =>
    intro gres h ρ
    cases hf : translate f with
    | ok f' =>
      have hEq : translate (SrcFormula.not f) = TransResult.ok (RealFormula.not f') := by
        simp only [translate, hf, bind1]
      rw [hEq] at h
      cases h
      simp only [srcDenote, RealFormula.denote]
      exact ⟨fun hx hfx => hx ((ihf f' hf ρ).2 hfx),
        fun hx hsrc => hx ((ihf f' hf ρ).1 hsrc)⟩
    | failed r =>
      have hEq : translate (SrcFormula.not f) = TransResult.failed r := by
        simp only [translate, hf, bind1]
      rw [hEq] at h
      simp at h

/-- **Failed 不是公式假**：翻译失败与恒假公式语义可分——
    零分母除原子处处无定义（翻译 Failed），而恒假公式 0 = 1 处处有定义；
    两者都永不满足，但"无定义"与"假"是不同的语义态，Failed 不塌缩为任何公式值。 -/
theorem failed_is_not_formula_false :
    ∃ a : SrcAtom 1,
      translateAtom a = TransResult.failed "divCmp: 分母为零多项式，定义域处处为空，保持 Failed" ∧
      (∀ ρ : Fin 1 → ℝ, ¬ srcAtomSat ρ a) ∧
      (∀ ρ : Fin 1 → ℝ, ¬ srcAtomDefined ρ a) ∧
      (∀ ρ : Fin 1 → ℝ,
        srcAtomDefined ρ (SrcAtom.cmp CmpOp.eq (SrcExpr.const 0) (SrcExpr.const 1))) := by
  refine ⟨SrcAtom.divCmp (SrcExpr.const 1) (SrcExpr.const 0) CmpOp.eq, ?_, ?_, ?_, ?_⟩
  · exact translate_zero_denom_fails _ _ _ (by simp [toPoly])
  · rintro ρ ⟨hd, -⟩
    exact hd (by
      show srcVal ρ (SrcExpr.const 0) = 0
      simp [srcVal, polyDenote, toPoly, MvPolynomial.eval₂_C, qToR_zero])
  · intro ρ hd
    exact hd (by
      show srcVal ρ (SrcExpr.const 0) = 0
      simp [srcVal, polyDenote, toPoly, MvPolynomial.eval₂_C, qToR_zero])
  · intro ρ
    trivial

/-! ## 四、C1：一元多项式实根基础设施 -/

open Polynomial in
/-- ℚ 多项式在实数处的取值（经精确嵌入）。 -/
def reval (p : ℚ[X]) (x : ℝ) : ℝ := (p.map qToR).eval x

open Polynomial in
/-- p 在实数 x 处为根（定义即嵌入后多项式的根，故与 `IsRoot` 定义性重合）。 -/
def IsRRoot (p : ℚ[X]) (x : ℝ) : Prop := reval p x = 0

open Polynomial in
/-- 嵌入后的实多项式。 -/
def rp (p : ℚ[X]) : ℝ[X] := p.map qToR

open Polynomial in
/-- x 作为 p 的根的重数（mathlib `rootMultiplicity`，按 (X−x) 幂整除性精确计算）。 -/
def rmult (p : ℚ[X]) (x : ℝ) : ℕ := (rp p).rootMultiplicity x

open Polynomial in
theorem map_qToR_ne_zero {p : ℚ[X]} (hp : p ≠ 0) : p.map qToR ≠ 0 :=
  fun h => hp ((Polynomial.map_eq_zero_iff qToR_injective).mp h)

open Polynomial in
theorem isrroot_iff_IsRoot {p : ℚ[X]} {x : ℝ} : IsRRoot p x ↔ (rp p).IsRoot x := Iff.rfl

/-! ## 五、C1：平方自由分解（欧几里得 gcd 链）与恒等式检查 -/

open Polynomial in
/-- 平方自由分解的 gcd 因子：h = gcd(p, p′)（ℚ[X] 上欧几里得 gcd 链）。 -/
def sqfreeGcd (p : ℚ[X]) : ℚ[X] := EuclideanDomain.gcd p (Polynomial.derivative p)

open Polynomial in
/-- 平方自由部分：g = p / h。 -/
def sqfreePart (p : ℚ[X]) : ℚ[X] := p / sqfreeGcd p

open Polynomial in
theorem sqfreeGcd_dvd (p : ℚ[X]) : sqfreeGcd p ∣ p :=
  EuclideanDomain.gcd_dvd_left p (Polynomial.derivative p)

open Polynomial in
theorem sqfreeGcd_ne_zero {p : ℚ[X]} (hp : p ≠ 0) : sqfreeGcd p ≠ 0 :=
  fun h => hp (EuclideanDomain.gcd_eq_zero_iff.mp h).1

open Polynomial in
/-- **平方自由分解乘回恒等式（恒等式检查定理）**：
    p = gcd(p, p′) · (p / gcd(p, p′))——分解恰以带重数的方式乘回原多项式；
    证书中的 (h, g) 由检查器以多项式恒等式 `h * g = p ∧ h = gcd(p, p′)` 核验。 -/
theorem sqfree_decomp_identity {p : ℚ[X]} (hp : p ≠ 0) :
    sqfreeGcd p * sqfreePart p = p :=
  EuclideanDomain.mul_div_cancel' (sqfreeGcd_ne_zero hp) (sqfreeGcd_dvd p)

open Polynomial in
/-- 分解存在性（builder 侧片段）：对每个非零 p 都有被检查器接受形式的分解。 -/
theorem sq_decomp_exists {p : ℚ[X]} (hp : p ≠ 0) :
    ∃ h g : ℚ[X], h * g = p ∧ h = EuclideanDomain.gcd p (Polynomial.derivative p) :=
  ⟨sqfreeGcd p, sqfreePart p, sqfree_decomp_identity hp, rfl⟩

open Polynomial in
/-- 每根带重数精确分解（mathlib）：p = (X−a)^m · q 且 (X−a) ∤ q。 -/
theorem rmult_exact {p : ℚ[X]} (hp : p ≠ 0) (x : ℝ) :
    ∃ q : ℝ[X], rp p = (X - C x) ^ rmult p x * q ∧ ¬ (X - C x) ∣ q := by
  obtain ⟨q, hq, hdvd⟩ :=
    Polynomial.exists_eq_pow_rootMultiplicity_mul_and_not_dvd (rp p) (map_qToR_ne_zero hp) x
  exact ⟨q, hq, hdvd⟩

/-! ## 六、C1：Sturm 链构造与符号变差计数 -/

/-- 有理数符号函数（ℤ 值）。 -/
def qsign (q : ℚ) : ℤ := if q < 0 then -1 else if 0 < q then 1 else 0

theorem qsign_of_pos {q : ℚ} (h : 0 < q) : qsign q = 1 := by
  show (if q < 0 then (-1 : ℤ) else if 0 < q then 1 else 0) = 1
  rw [if_neg (not_lt.mpr (by linarith)), if_pos h]

theorem qsign_of_neg {q : ℚ} (h : q < 0) : qsign q = -1 := by
  show (if q < 0 then (-1 : ℤ) else if 0 < q then 1 else 0) = -1
  rw [if_pos h]

/-- 符号变差数：相邻符号严格异号的位置数。 -/
def signVariations : List ℤ → ℕ
  | [] => 0
  | [_] => 0
  | a :: b :: t => (if a * b < 0 then 1 else 0) + signVariations (b :: t)

/-- x → +∞ 时首项符号。 -/
def signAtPosInf (p : ℚ[X]) : ℤ := qsign p.leadingCoeff

/-- 自然数奇偶（自建 Bool 版；此工具链无 `Nat.beven`——CI 38064007904 核实），
    字面输入由内核归约，decide 可判定。 -/
def natEven : ℕ → Bool
  | 0 => true
  | 1 => false
  | n + 2 => natEven n

/-- x → −∞ 时首项符号（含次数奇偶翻转；对任意存储形多项式定义，
    首系数零降次由 natDegree/leadingCoeff 的实际值自动处理）。 -/
def signAtNegInf (p : ℚ[X]) : ℤ :=
  if natEven p.natDegree then qsign p.leadingCoeff else -qsign p.leadingCoeff

/-- 余式链（fuel 有界；余式次数严格下降由 `degree_drop` 保证足够 fuel 时完整）。 -/
def chainAux : ℕ → ℚ[X] → ℚ[X] → List (ℚ[X])
  | 0, _, _ => []
  | n + 1, prev, q => if q = 0 then [] else q :: chainAux n q (-(prev % q))

/-- 本文件实际构造的 Sturm 链：S₀ = p, S₁ = p′, S_{k+1} = −(S_{k−1} mod S_k)。 -/
def sturmChain (p : ℚ[X]) : List (ℚ[X]) :=
  if p = 0 then [] else p :: chainAux (p.natDegree + 1) p (Polynomial.derivative p)

/-- 链在 −∞ 端的符号变差。 -/
def varNegInf (p : ℚ[X]) : ℕ := signVariations ((sturmChain p).map signAtNegInf)

/-- 链在 +∞ 端的符号变差。 -/
def varPosInf (p : ℚ[X]) : ℕ := signVariations ((sturmChain p).map signAtPosInf)

/-- 全根计数声明所锚定的具体数值：V(−∞) − V(+∞)（ℤ 减法，无截断）。 -/
def varCount (p : ℚ[X]) : ℤ :=
  (varNegInf p : ℤ) - (varPosInf p : ℤ)

/-- **度数下降（首系数零降次的机器保证）**：非零除式的余式度数严格下降——
    Sturm 链每步实际度数只减不增，燃料 `natDegree p + 1` 足够。 -/
theorem degree_drop (p q : ℚ[X]) (hq : q ≠ 0) : (p % q).degree < q.degree :=
  Polynomial.degree_mod_lt p hq

/-- 常数多项式的计数可精确计算：varCount (C c) = 0（无条件，不需 Sturm 假设）。 -/
theorem varCount_C (c : ℚ) (hc : c ≠ 0) : varCount (Polynomial.C c) = 0 := by
  have hder0 : Polynomial.derivative (Polynomial.C c) = 0 := Polynomial.derivative_C
  have hchain : sturmChain (Polynomial.C c) = [Polynomial.C c] := by
    rw [sturmChain, if_neg (Polynomial.C_ne_zero.mpr hc)]
    have step : chainAux (Polynomial.natDegree (Polynomial.C c) + 1) (Polynomial.C c)
        (Polynomial.derivative (Polynomial.C c)) =
        chainAux (Polynomial.natDegree (Polynomial.C c) + 1) (Polynomial.C c) 0 := by
      rw [hder0]
    rw [step]
    have hzero : chainAux (Polynomial.natDegree (Polynomial.C c) + 1) (Polynomial.C c) 0
        = [] := if_pos rfl
    rw [hzero]
  show ((signVariations ((sturmChain (Polynomial.C c)).map signAtNegInf) : ℕ) : ℤ) -
      ((signVariations ((sturmChain (Polynomial.C c)).map signAtPosInf) : ℕ) : ℤ) = 0
  rw [hchain]
  rfl

/-- **显式具名假设（C1 唯一开放点；非 axiom，仅定理假设参数）**：
    本文件构造的 Sturm 变差计数满足完备性——
    varCount p 等于 p 的相异实根个数。mathlib v4.30.0 无 Sturm 库（已 grep 核实），
    该定理的全量自证为显式开放义务，见头注。 -/
def SturmComplete (p : ℚ[X]) : Prop :=
  varCount p = (((rp p).roots.toFinset.card : ℕ) : ℤ)

/-! ## 七、C1：根证书、检查器与健全性总定理 -/

/-- 单条隔离记录：区间 (lo, hi) 内的根 r 及其重数 m。 -/
structure IsoEntry : Type where
  lo : ℚ
  hi : ℚ
  r : ℝ
  m : ℕ

/-- **全局有序互斥**：每条目的区间整体落在其后所有条目区间之左——
    蕴含两两互斥且按序完备（隔离区间完备排序）。 -/
def IvsOrdered : List IsoEntry → Prop
  | [] => True
  | e :: es => (∀ e' ∈ es, e.hi ≤ e'.lo) ∧ IvsOrdered es

/-- 一元根证书：隔离条目 + 总相异根数声明 + 平方自由分解 (h, g)。
    检查器只认这里的数据，不认任何来历（不调求解器）。 -/
structure RootCert : Type where
  entries : List IsoEntry
  total : ℕ
  sqH : ℚ[X]
  sqG : ℚ[X]

open Polynomial in
/-- **C1 检查器**（命题形，体例同 UnifiedCAD.checkCAD2；不调用任何求解器）：
    ① p ≠ 0（零多项式另有专门处理）；② 区间全局有序互斥；
    ③ 每条目：区间非空、根在区间内、代入恒等式、重数恒等式；
    ④ 平方自由分解恒等式（整数/有理多项式恒等式核验）；
    ⑤ **完备性硬要求**：条目数 = 总数声明 = 本文件 Sturm 链变差计数——
       结构性消费总计数声明，不收"只报见到的根"的证书。 -/
def checkRootCert (p : ℚ[X]) (c : RootCert) : Prop :=
  p ≠ 0 ∧
  IvsOrdered c.entries ∧
  (∀ e ∈ c.entries, e.lo < e.hi ∧ e.lo < e.r ∧ e.r < e.hi ∧
    IsRRoot p e.r ∧ rmult p e.r = e.m) ∧
  c.sqH * c.sqG = p ∧
  c.sqH = EuclideanDomain.gcd p (Polynomial.derivative p) ∧
  c.entries.length = c.total ∧
  (c.total : ℤ) = varCount p

/-- 有序隔离条目的根两两不同（检查器条件②③的推论）。 -/
theorem entries_r_nodup :
    ∀ l : List IsoEntry, IvsOrdered l → (∀ e ∈ l, e.lo < e.r ∧ e.r < e.hi) →
      (l.map (fun e => e.r)).Nodup := by
  intro l
  induction l with
  | nil => intro _ _; exact List.nodup_nil
  | cons e es ih =>
    intro hord hmem
    rw [List.map_cons, List.nodup_cons]
    refine ⟨?_, ih hord.2 (fun e' he' => hmem e' (List.Mem.tail _ he'))⟩
    intro hmemr
    obtain ⟨e', he', hr⟩ := List.mem_map.mp hmemr
    have h1 := hmem e (List.Mem.head _)
    have h2 := hmem e' (List.Mem.tail _ he')
    -- IsoEntry 的界在 ℚ、根在 ℝ：把 ℚ 端界单调升到 ℝ 再串链（CI 794 根因）
    have hsep : ((e.hi : ℚ) : ℝ) ≤ ((e'.lo : ℚ) : ℝ) := Rat.cast_le.mpr (hord.1 e' he')
    have hlt : e.r < e'.r := by linarith [h1.2, hsep, h2.1]
    rw [← hr] at hlt
    exact absurd hlt (lt_irrefl _)

open Polynomial in
/-- **C1 检查器健全性总定理**：接受 ⇒ 隔离列表恰为该多项式全部实根
    （x 是 p 的实根 ↔ x 出现在证书根列表中；重数结构由检查器逐条目按
    `rootMultiplicity` 精确核验）。代数半边（根是根、互斥有序、重数）无条件；
    完备半边（不漏根）消耗唯一显式具名假设 `SturmComplete p`。 -/
theorem checkRootCert_sound (p : ℚ[X]) (c : RootCert) (h : checkRootCert p c)
    (hsturm : SturmComplete p) (x : ℝ) :
    IsRRoot p x ↔ x ∈ c.entries.map (fun e => e.r) := by
  obtain ⟨hp0, hord, hmem, -, -, hlen, htot⟩ := h
  have hrp0 : rp p ≠ 0 := map_qToR_ne_zero hp0
  -- 每个证书根都是 p 的实根
  have hmemR : ∀ e ∈ c.entries, e.r ∈ (rp p).roots.toFinset := by
    intro e he
    exact Multiset.mem_toFinset.mpr
      ((Polynomial.mem_roots hrp0).mpr (isrroot_iff_IsRoot.mp (hmem e he).2.2.2.1))
  -- 证书根两两不同 ⇒ toFinset 计数 = 条目数
  have hnodup : (c.entries.map (fun e => e.r)).Nodup :=
    entries_r_nodup c.entries hord
      (fun e he => And.intro (hmem e he).2.1 (hmem e he).2.2.1)
  have hcardS : ((c.entries.map (fun e => e.r)).toFinset).card = c.entries.length := by
    rw [List.toFinset_card_of_nodup hnodup, List.length_map]
  -- 总计数声明与 Sturm 计数对齐 ⇒ 与相异实根个数对齐
  have hcount : c.total = (rp p).roots.toFinset.card := by
    have hz : ((c.total : ℕ) : ℤ) = (((rp p).roots.toFinset.card : ℕ) : ℤ) :=
      htot.trans hsturm
    exact Nat.cast_injective hz
  -- 子集 + 计数相等 ⇒ 根集相等
  have hsub : ((c.entries.map (fun e => e.r)).toFinset) ⊆ ((rp p).roots.toFinset) := by
    intro y hy
    have hy' : y ∈ c.entries.map (fun e => e.r) := List.mem_toFinset.mp hy
    obtain ⟨e, he, hr⟩ := List.mem_map.mp hy'
    rw [← hr]
    exact hmemR e he
  have heq : ((c.entries.map (fun e => e.r)).toFinset) = ((rp p).roots.toFinset) :=
    Finset.eq_of_subset_of_card_le hsub (by rw [hcardS, hlen, hcount])
  constructor
  · intro hx
    have hxR : x ∈ (rp p).roots.toFinset :=
      Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hrp0).mpr (isrroot_iff_IsRoot.mp hx))
    rw [← heq] at hxR
    exact List.mem_toFinset.mp hxR
  · intro hx
    obtain ⟨e, he, hr⟩ := List.mem_map.mp hx
    rw [← hr]
    exact isrroot_iff_IsRoot.mpr (hmem e he).2.2.2.1

open Polynomial in
/-- 重数结构推论：被接受的证书对每个条目给出精确带重数分解。 -/
theorem checkRootCert_mult_exact (p : ℚ[X]) (c : RootCert) (h : checkRootCert p c)
    (e : IsoEntry) (he : e ∈ c.entries) :
    ∃ q : ℝ[X], rp p = (X - C e.r) ^ e.m * q ∧ ¬ (X - C e.r) ∣ q := by
  have hm : rmult p e.r = e.m := (h.2.2.1 e he).2.2.2.2
  obtain ⟨q, hq, hdvd⟩ := rmult_exact h.1 e.r
  rw [hm] at hq
  exact ⟨q, hq, hdvd⟩

/-! ## 八、C1：退化情形专门定理 -/

open Polynomial in
/-- **零多项式（专门定理 1）**：零多项式处处为根——它是全实轴的解集，
    语义上不能被任何有限证书捕获。 -/
theorem zero_poly_universal_root (x : ℝ) : IsRRoot 0 x := by
  show ((0 : ℚ[X]).map qToR).eval x = 0
  rw [Polynomial.map_zero, Polynomial.eval_zero]

open Polynomial in
/-- **零多项式（专门定理 2）**：检查器结构上拒绝零多项式（p ≠ 0 是检查条件）。 -/
theorem zero_poly_rejected (c : RootCert) : ¬ checkRootCert 0 c :=
  fun h => h.1 rfl

/-- **零多项式（专门定理 3）**：任何有限实数列表都漏掉零多项式的根——
    拒绝不是因为实现偷懒，而是零多项式的解集不可有限列举。 -/
theorem zero_poly_no_finite_root_list (l : List ℝ) :
    ∃ x : ℝ, IsRRoot 0 x ∧ x ∉ l := by
  have hexists : ∃ b : ℝ, ∀ y ∈ l, y < b := by
    induction l with
    | nil => exact ⟨0, by intro y hy; exact absurd hy (by simp)⟩
    | cons a t ih =>
      obtain ⟨b, hb⟩ := ih
      refine ⟨max a b + 1, ?_⟩
      intro y hy
      rcases List.mem_cons.mp hy with hy' | hy'
      · rw [hy']
        linarith [le_max_left a b]
      · linarith [le_max_right a b, hb y hy']
  obtain ⟨b, hb⟩ := hexists
  refine ⟨b + 1, zero_poly_universal_root _, ?_⟩
  intro hm
  linarith [hb (b + 1) hm]

/-- 空证书（用于无解与退化判定）。 -/
def emptyCert (h g : ℚ[X]) : RootCert where
  entries := []
  total := 0
  sqH := h
  sqG := g

open Polynomial in
/-- **无解 / 常数多项式（专门定理）**：非零常数 c 没有任何实根，
    且空证书被检查器无条件接受（total = varCount (C c) = 0 直接计算，
    不需 Sturm 假设）。 -/
theorem checkRootCert_const (c : ℚ) (hc : c ≠ 0) :
    checkRootCert (Polynomial.C c) (emptyCert (EuclideanDomain.gcd (Polynomial.C c) 0) 1) := by
  have hivs : IvsOrdered (emptyCert (EuclideanDomain.gcd (Polynomial.C c) 0) 1).entries := by
    simp only [emptyCert, IvsOrdered]
  have hmem : ∀ e ∈ (emptyCert (EuclideanDomain.gcd (Polynomial.C c) 0) 1).entries,
      e.lo < e.hi ∧ e.lo < e.r ∧ e.r < e.hi ∧ IsRRoot (Polynomial.C c) e.r ∧
        rmult (Polynomial.C c) e.r = e.m := by
    intro e he
    exact absurd he (by simp [emptyCert])
  have hid : (emptyCert (EuclideanDomain.gcd (Polynomial.C c) 0) 1).sqH *
      (emptyCert (EuclideanDomain.gcd (Polynomial.C c) 0) 1).sqG = Polynomial.C c := by
    simp only [emptyCert]
    rw [mul_one, EuclideanDomain.gcd_zero_right]
  have hid2 : (emptyCert (EuclideanDomain.gcd (Polynomial.C c) 0) 1).sqH =
      EuclideanDomain.gcd (Polynomial.C c) (Polynomial.derivative (Polynomial.C c)) := by
    simp only [emptyCert]
    rw [Polynomial.derivative_C, EuclideanDomain.gcd_zero_right]
  have hlen : (emptyCert (EuclideanDomain.gcd (Polynomial.C c) 0) 1).entries.length =
      (emptyCert (EuclideanDomain.gcd (Polynomial.C c) 0) 1).total := by
    simp only [emptyCert, List.length_nil]
  have htot : ((emptyCert (EuclideanDomain.gcd (Polynomial.C c) 0) 1).total : ℤ) =
      varCount (Polynomial.C c) := by
    show ((0 : ℕ) : ℤ) = varCount (Polynomial.C c)
    rw [varCount_C c hc]
    norm_num
  exact ⟨Polynomial.C_ne_zero.mpr hc, hivs, hmem, hid, hid2, hlen, htot⟩

open Polynomial in
/-- 无解情形的健全性（无条件）：非零常数处处非根——被接受的空证书判定"没有实根"。 -/
theorem checkRootCert_const_sound (c : ℚ) (hc : c ≠ 0) (x : ℝ) :
    ¬ IsRRoot (Polynomial.C c) x := by
  intro hx
  replace hx : ((Polynomial.C c).map qToR).eval x = 0 := hx
  rw [Polynomial.map_C, Polynomial.eval_C] at hx
  exact hc (qToR_injective (by rw [qToR_zero]; exact hx))

open Polynomial in
/-- 重根实例的链：sturmChain ((X−0)²) = [(X−0)², C 2·(X−0)]——
    余式 (X−0)² mod (C 2·(X−0)) = 0（由 C 2 是单位给出整除），链止于第二步。 -/
theorem double_root_chain :
    sturmChain ((X - C 0 : ℚ[X]) ^ 2) = [(X - C 0 : ℚ[X]) ^ 2, C 2 * (X - C 0 : ℚ[X])] := by
  have hne : (X - C 0 : ℚ[X]) ^ 2 ≠ 0 := by
    rw [pow_two, Polynomial.C_0, sub_zero]
    exact mul_ne_zero Polynomial.X_ne_zero Polynomial.X_ne_zero
  have hder : Polynomial.derivative ((X - C 0 : ℚ[X]) ^ 2) = C 2 * (X - C 0 : ℚ[X]) := by
    rw [Polynomial.derivative_sq, map_sub, Polynomial.derivative_X,
      Polynomial.derivative_C, sub_zero, mul_one]
  have hdvd : (C 2 * (X - C 0 : ℚ[X])) ∣ (X - C 0 : ℚ[X]) ^ 2 := by
    have hu : IsUnit (C (2 : ℚ) : ℚ[X]) :=
      Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr (by norm_num))
    have h1 : (C 2 * (X - C 0 : ℚ[X])) ∣ (X - C 0 : ℚ[X]) :=
      (associated_unit_mul_left _ _ hu).dvd
    exact h1.trans (dvd_pow_self _ (by norm_num))
  have hmod : ((X - C 0 : ℚ[X]) ^ 2) % (C 2 * (X - C 0 : ℚ[X])) = 0 :=
    EuclideanDomain.mod_eq_zero.mpr hdvd
  have hX0 : (X - C 0 : ℚ[X]) ≠ 0 := by
    rw [Polynomial.C_0, sub_zero]
    exact Polynomial.X_ne_zero
  -- 燃料取字面值（stuck 的 natDegree 会卡住 chainAux 匹配展开——CI 969/972 根因）
  have hnd2 : Polynomial.natDegree ((X - C 0 : ℚ[X]) ^ 2) = 2 := by
    rw [pow_two, Polynomial.C_0, sub_zero, Polynomial.natDegree_mul' (by
      rw [Polynomial.leadingCoeff_X]; norm_num),
      Polynomial.natDegree_X]
  rw [sturmChain, if_neg hne, hder, hnd2]
  have step : chainAux (2 + 1) ((X - C 0 : ℚ[X]) ^ 2) (C 2 * (X - C 0 : ℚ[X])) =
      (C 2 * (X - C 0 : ℚ[X])) :: chainAux 2 (C 2 * (X - C 0 : ℚ[X]))
        (-(((X - C 0 : ℚ[X]) ^ 2) % (C 2 * (X - C 0 : ℚ[X])))) := by
    simp only [chainAux, if_neg (mul_ne_zero (Polynomial.C_ne_zero.mpr two_ne_zero) hX0)]
  rw [step, hmod, neg_zero]
  have hzero : chainAux 2 (C 2 * (X - C 0 : ℚ[X])) 0 = [] := if_pos rfl
  rw [hzero]

open Polynomial in
/-- 重根实例的计数：varCount ((X−0)²) = 1（无条件直接计算：链 [p, p′]，
    −∞ 端符号 [1, −1] 一处变差，+∞ 端 [1, 1] 零变差）。 -/
theorem varCount_double_root : varCount ((X - C 0 : ℚ[X]) ^ 2) = 1 := by
  have hsq : ((X - C 0 : ℚ[X]) ^ 2) = (X : ℚ[X]) ^ 2 := by
    rw [pow_two, Polynomial.C_0, sub_zero, pow_two]
  have hnd : Polynomial.natDegree ((X - C 0 : ℚ[X]) ^ 2) = 2 := by
    rw [hsq]
    exact Polynomial.natDegree_X_pow
  have hlc : Polynomial.leadingCoeff ((X - C 0 : ℚ[X]) ^ 2) = 1 := by
    rw [hsq]
    exact Polynomial.leadingCoeff_X_pow (R := ℚ) 2
  have hnd' : Polynomial.natDegree (C 2 * (X - C 0 : ℚ[X])) = 1 := by
    rw [Polynomial.C_0, sub_zero, mul_comm, Polynomial.natDegree_mul_C (by norm_num)]
    exact Polynomial.natDegree_X
  have hlc' : Polynomial.leadingCoeff (C 2 * (X - C 0 : ℚ[X])) = 2 := by
    rw [Polynomial.C_0, sub_zero, mul_comm,
      Polynomial.leadingCoeff_mul' (by
        rw [Polynomial.leadingCoeff_X, Polynomial.leadingCoeff_C]; norm_num),
      Polynomial.leadingCoeff_X, Polynomial.leadingCoeff_C]
    norm_num
  have hs1 : signAtNegInf ((X - C 0 : ℚ[X]) ^ 2) = 1 := by
    rw [signAtNegInf, hnd, hlc, if_pos (by decide : natEven 2 = true)]
    exact qsign_of_pos (by norm_num)
  have hs2 : signAtNegInf (C 2 * (X - C 0 : ℚ[X])) = -1 := by
    rw [signAtNegInf, hnd', hlc', if_neg (by decide : ¬(natEven 1 = true)),
      qsign_of_pos (by norm_num)]
  have hs3 : signAtPosInf ((X - C 0 : ℚ[X]) ^ 2) = 1 := by
    rw [signAtPosInf, hlc]
    exact qsign_of_pos (by norm_num)
  have hs4 : signAtPosInf (C 2 * (X - C 0 : ℚ[X])) = 1 := by
    rw [signAtPosInf, hlc']
    exact qsign_of_pos (by norm_num)
  have hchain := double_root_chain
  show ((signVariations ((sturmChain ((X - C 0 : ℚ[X]) ^ 2)).map signAtNegInf) : ℕ) : ℤ) -
      ((signVariations ((sturmChain ((X - C 0 : ℚ[X]) ^ 2)).map signAtPosInf) : ℕ) : ℤ) = 1
  rw [hchain]
  simp only [List.map_cons, List.map_nil, hs1, hs2, hs3, hs4]
  rfl

open Polynomial in
/-- 重根证书：p = (X−0)²，根 0 重数 2，区间 (−1, 1)，total = 1，
    分解 h = gcd(p, p′)，g = p / h。被检查器无条件接受（计数直接计算，
    不需 Sturm 假设）——重根与重数结构被完整核验，不是"拒绝了事"。 -/
theorem checkRootCert_double_root :
    checkRootCert ((X - C 0 : ℚ[X]) ^ 2)
      { entries := [{ lo := -1, hi := 1, r := 0, m := 2 }]
        total := 1
        sqH := EuclideanDomain.gcd ((X - C 0 : ℚ[X]) ^ 2)
          (Polynomial.derivative ((X - C 0 : ℚ[X]) ^ 2))
        sqG := ((X - C 0 : ℚ[X]) ^ 2) /
          EuclideanDomain.gcd ((X - C 0 : ℚ[X]) ^ 2)
            (Polynomial.derivative ((X - C 0 : ℚ[X]) ^ 2)) } := by
  have hpne : ((X - C 0 : ℚ[X]) ^ 2) ≠ 0 := by
    rw [pow_two, Polynomial.C_0, sub_zero]
    exact mul_ne_zero Polynomial.X_ne_zero Polynomial.X_ne_zero
  have hmap : ((X - C 0 : ℚ[X]) ^ 2).map qToR = (X - C (0:ℝ)) ^ 2 := by
    rw [Polynomial.map_pow, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C,
      qToR_zero]
  have hivs : IvsOrdered [{ lo := -1, hi := 1, r := 0, m := 2 }] := by
    simp only [IvsOrdered]
    exact ⟨by simp, trivial⟩
  refine ⟨hpne, hivs, ?_, sqfree_decomp_identity hpne, rfl, rfl, ?_⟩
  · intro e he
    simp at he
    obtain rfl := he
    refine ⟨by norm_num, by norm_num, by norm_num, ?_, ?_⟩
    · show (((X - C 0 : ℚ[X]) ^ 2).map qToR).eval (0:ℝ) = 0
      rw [hmap, Polynomial.eval_pow, Polynomial.eval_sub, Polynomial.eval_X,
        Polynomial.eval_C]
      norm_num
    · show (((X - C 0 : ℚ[X]) ^ 2).map qToR).rootMultiplicity (0:ℝ) = 2
      rw [hmap]
      exact Polynomial.rootMultiplicity_X_sub_C_pow 0 2
  · show ((1 : ℕ) : ℤ) = varCount ((X - C 0 : ℚ[X]) ^ 2)
    rw [varCount_double_root]
    norm_num

open Polynomial in
/-- **首系数零降次（专门定理 1）**：首系数单位缩放不改变根集——
    存储形的首系数（含多余的零高次项、非首一形）不影响检查器的代入与重数核验。 -/
theorem isRRoot_C_smul (a : ℚ) (ha : a ≠ 0) (p : ℚ[X]) (x : ℝ) :
    IsRRoot p x ↔ IsRRoot (Polynomial.C a * p) x := by
  have haR : qToR a ≠ 0 := by
    intro h
    exact ha (qToR_injective (by rw [h]; exact qToR_zero.symm))
  constructor
  · intro hx
    show ((Polynomial.C a * p).map qToR).eval x = 0
    rw [Polynomial.map_mul, Polynomial.map_C, Polynomial.eval_mul, Polynomial.eval_C]
    show qToR a * ((p.map qToR).eval x) = 0
    rw [show (p.map qToR).eval x = (0:ℝ) from hx]
    exact mul_zero (qToR a)
  · intro hx
    show ((p.map qToR).eval x) = 0
    have hmul : ((Polynomial.C a * p).map qToR).eval x =
        qToR a * ((p.map qToR).eval x) := by
      rw [Polynomial.map_mul, Polynomial.map_C, Polynomial.eval_mul, Polynomial.eval_C]
    have h0 : qToR a * ((p.map qToR).eval x) = 0 := hmul.symm.trans hx
    exact (mul_eq_zero.mp h0).resolve_left haR

/-! ## 九、STATUS -/

/- STATUS（诚实边界）：
- 已闭合（本文件，全部零 sorry／零自定义 axiom；本地状态 CI_NOT_RUN，以 CI 模块构建为准）：
  C0：RealFormula 全量编码（原子 =/</≤ ＋ and/or/not ＋ ∃/∀ 按固定变量表 de Bruijn 嵌套）、
  指称函数 denote、量词顺序由构造保义（quantifier_order_matters 给出 ∃∀/∀∃ 指称分叉实例）、
  除法 guard 翻译（div_translation_sound：q≠0 ∧ p·q⋈0 逐点保义）、
  零分母除原子保持 Failed 并携带原因（translate_zero_denom_fails）、
  全式翻译健全（translate_sound，含失败传播）、
  Failed 不是公式假（failed_is_not_formula_false：Failed 处处无定义 vs 恒假公式处处有定义）、
  AlgRealCode（最小多项式＋唯一隔离区间）结构＋指称＋有效性＋恒等检查定理
  （AlgMeaning_subsingleton）＋非平凡实例 √2=X²−2 于 (1,2) 全证
  （algRealSqrt2_validity / algRealSqrt2_denote_eq）。
  C1：平方自由分解 gcd 链恒等式（sqfree_decomp_identity，gcd(p,p′)·(p/gcd)=p）＋分解存在性、
  每根带重数精确分解（rmult_exact，mathlib rootMultiplicity）、
  Sturm 链/varCount 实际构造（本文件可计算定义）、度数下降 degree_drop、
  有序互斥隔离条目 IvsOrdered、检查器 checkRootCert 五条件（含结构性消费总计数声明）、
  健全性总定理 checkRootCert_sound（代数半边无条件，完备半边消耗显式具名假设 SturmComplete）、
  重数推论 checkRootCert_mult_exact、退化全专门定理：
  零多项式三条（universal_root / rejected / no_finite_root_list）、
  无解常数（checkRootCert_const 接受＋checkRootCert_const_sound，均无条件）、
  重根（checkRootCert_double_root 接受＋varCount_double_root 直接计算，均无条件）、
  首系数缩放不变 isRRoot_C_smul。
- 显式假设开放点（仅一个）：SturmComplete p——本文件 varCount/sturmChain 构造满足
  "变差数＝相异实根数"。mathlib v4.30.0 无 Sturm/子结式库（已 grep：唯一文本命中为无关的
  模形式文件）；该定理全量自证为开放义务，头注已声明。除该假设外健全性定理无任何前提收窄，
  输入域保持全定义域（任意 ℚ[X] 与任意证书）。
- 其他开放（如实申报，未混入已完成面）：子结式符号变差作为替代证书语言；
  一般 p 的 Squarefree (sqfreePart p)；AlgRealCode 作为系数表示向多项式系数层的推广；
  C2/C3/C4/C5 不在本文件范围。
- 本文件未加入根 `JurisLean.lean`；按仓库规则，CI 模块构建通过前保持 CI_NOT_RUN。 -/

end JurisLean.Seams.UnifiedCADCore
