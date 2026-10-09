import Mathlib.Tactic

/-
Unified CAD fragment, layer O (plan §6.3; appendix I.0.1 C0–C5, the
checker-first discipline instantiated on the nondegenerate univariate
quadratic over ℚ).

The three mandated obligations, in miniature and honestly scoped:

1. CHECKER SOUNDNESS — `checkCAD2` verifies a certificate by
   SUBSTITUTION and DISTINCTNESS only (it never calls the builder);
   `checkCAD2_sound` : acceptance implies ∀x,
   eval2 p x = 0 ↔ (x = root1 ∨ x = root2) — the denote φ ↔ denote ψ
   shape of obligation 1.  Completeness of the root set is carried by
   `quad_at_most_two_roots` (the degree-2 Vandermonde argument).
2. BUILDER TOTALITY — `buildCAD2` is a non-recursive total function
   (Lean definability IS the termination proof for a fuel-free
   function); `buildCAD2_total` records the every-input reading of
   obligation 2.  The algebraic input s carries s² = b² − 4ac (the
   C0 miniature of an algebraic number given by its defining relation).
3. CERTIFICATE ACCEPTED — `buildCAD2_accepted` : the builder's
   certificate always passes the checker (obligation 3 — no shortcut
   domain where the checker rejects its own reference output).

Cell sign-invariance (C2 miniature): `sign_invariant_cells` — with a
verified root pair, the polynomial has one sign per open cell of the
three-cell decomposition (below / between / above).

Scope, honestly: ONE polynomial, degree 2, distinct rational roots.
Multivariate projection, Sturm/subresultant checkers, sector
completeness and the QEPCAD adapter (C2/C4/C5 full) remain open
obligations; this fragment delivers the three-obligation DISCIPLINE on
a class where every step is exact algebra.
-/

namespace JurisLean.Seams.UnifiedCAD

/-! ## 一、C0 微型：多项式编码与求值 -/

/-- 二次多项式 a·x² + b·x + c（ℚ 系数）。 -/
structure Poly2 where
  a : ℚ
  b : ℚ
  c : ℚ

/-- 求值。 -/
def eval2 (p : Poly2) (x : ℚ) : ℚ := p.a * x * x + p.b * x + p.c

/-- 根证书（两相异根；检查器只认代入验证，不认来历）。 -/
structure QuadCert where
  root1 : ℚ
  root2 : ℚ

/-! ## 二、次数引理（完整性之基） -/

/-- 一次函数两点为零则恒为零。 -/
theorem linear_two_roots_zero (m k r1 r2 : ℚ)
    (h1 : m * r1 + k = 0) (h2 : m * r2 + k = 0) (hne : r1 ≠ r2) :
    m = 0 ∧ k = 0 := by
  have hsub : m * (r1 - r2) = 0 := by
    have : m * r1 - m * r2 = 0 := by linarith
    linear_combination this
  rcases mul_eq_zero.mp hsub with h | h
  · refine ⟨h, ?_⟩
    rw [h, zero_mul] at h1
    linarith
  · exact absurd (sub_eq_zero.mp h) hne

/-- **二次分解**：两相异根＋首项非零 ⇒ 处处 p(x) = a·(x−r₁)(x−r₂)。 -/
theorem quad_factors (p : Poly2) (r1 r2 : ℚ)
    (h1 : eval2 p r1 = 0) (h2 : eval2 p r2 = 0) (hne : r1 ≠ r2) :
    ∀ x, eval2 p x = p.a * (x - r1) * (x - r2) := by
  simp only [eval2] at h1 h2
  obtain ⟨hm1, hm2⟩ := linear_two_roots_zero
    (p.b + p.a * (r1 + r2)) (p.c - p.a * r1 * r2) r1 r2
    (by linear_combination h1) (by linear_combination h2) hne
  intro x
  simp only [eval2]
  linear_combination hm1 * x + hm2

/-- **至多两根**（二次的 Vandermonde：第三根必与已知根之一重合）。 -/
theorem quad_at_most_two_roots (p : Poly2) (ha : p.a ≠ 0)
    (r1 r2 r3 : ℚ)
    (h1 : eval2 p r1 = 0) (h2 : eval2 p r2 = 0) (h3 : eval2 p r3 = 0)
    (h12 : r1 ≠ r2) :
    r3 = r1 ∨ r3 = r2 := by
  have hf : p.a * (r3 - r1) * (r3 - r2) = 0 := by
    rw [← quad_factors p r1 r2 h1 h2 h12 r3, h3]
  rcases mul_eq_zero.mp hf with hleft | hright
  · rcases mul_eq_zero.mp hleft with ha' | h
    · exact absurd ha' ha
    · exact Or.inl (sub_eq_zero.mp h)
  · exact Or.inr (sub_eq_zero.mp hright)

/-! ## 三、义务一：检查器健全（检查器不调求解器） -/

/-- 证书检查器（命题形）：代入验证两根＋两根相异＋首项非零。不调用任何求解器。 -/
def checkCAD2 (p : Poly2) (cert : QuadCert) : Prop :=
      p.a ≠ 0 ∧ eval2 p cert.root1 = 0 ∧ eval2 p cert.root2 = 0 ∧ cert.root1 ≠ cert.root2

/-- 检查器接受 ⇒ 首项非零。 -/
theorem checkCAD2_a (p : Poly2) (cert : QuadCert) (h : checkCAD2 p cert) : p.a ≠ 0 := h.1

/-- 检查器接受 ⇒ 第一根代入为零。 -/
theorem checkCAD2_r1 (p : Poly2) (cert : QuadCert) (h : checkCAD2 p cert) :
    eval2 p cert.root1 = 0 := h.2.1

/-- 检查器接受 ⇒ 第二根代入为零。 -/
theorem checkCAD2_r2 (p : Poly2) (cert : QuadCert) (h : checkCAD2 p cert) :
    eval2 p cert.root2 = 0 := h.2.2.1

/-- 检查器接受 ⇒ 两根相异。 -/
theorem checkCAD2_ne (p : Poly2) (cert : QuadCert) (h : checkCAD2 p cert) :
    cert.root1 ≠ cert.root2 := h.2.2.2

/-- **检查器健全**：接受 ⇒ ∀x，p(x)=0 ↔ (x=r₁ ∨ x=r₂)
    ——即 checkCAD φ cert ψ=true ⇒ ∀x, denote φ x ↔ denote ψ x 的片段形。 -/
theorem checkCAD2_sound (p : Poly2) (cert : QuadCert)
    (h : checkCAD2 p cert) :
    ∀ x, eval2 p x = 0 ↔ (x = cert.root1 ∨ x = cert.root2) := by
  have ha := checkCAD2_a p cert h
  have h1 := checkCAD2_r1 p cert h
  have h2 := checkCAD2_r2 p cert h
  have hne := checkCAD2_ne p cert h
  intro x
  constructor
  · intro hzero
    have hf : p.a * (x - cert.root1) * (x - cert.root2) = 0 := by
      rw [← quad_factors p cert.root1 cert.root2 h1 h2 hne x, hzero]
    rcases mul_eq_zero.mp hf with hleft | hright
    · rcases mul_eq_zero.mp hleft with ha' | hx
      · exact absurd ha' ha
      · exact Or.inl (sub_eq_zero.mp hx)
    · exact Or.inr (sub_eq_zero.mp hright)
  · intro hx
    rcases hx with rfl | rfl
    · exact h1
    · exact h2

/-! ## 四、C2 微型：三胞腔符号不变 -/

/-- **符号不变**：验证过的根对诱导的三胞腔分解（双下方/两根之间/双上方）上，
    多项式逐胞同号（乘积非负）。双下方与双上方两腔与根的排序无关。 -/
theorem sign_invariant_cells (p : Poly2) (cert : QuadCert)
    (h : checkCAD2 p cert) (x y : ℚ)
    (hcell : (x < cert.root1 ∧ x < cert.root2 ∧ y < cert.root1 ∧ y < cert.root2)
      ∨ (cert.root1 < x ∧ x < cert.root2 ∧ cert.root1 < y ∧ y < cert.root2)
      ∨ (cert.root1 < x ∧ cert.root2 < x ∧ cert.root1 < y ∧ cert.root2 < y)) :
    0 ≤ eval2 p x * eval2 p y := by
  have ha := checkCAD2_a p cert h
  have h1 := checkCAD2_r1 p cert h
  have h2 := checkCAD2_r2 p cert h
  have hne := checkCAD2_ne p cert h
  have hfx := quad_factors p cert.root1 cert.root2 h1 h2 hne x
  have hfy := quad_factors p cert.root1 cert.root2 h1 h2 hne y
  rw [hfx, hfy]
  have hnn : (0 : ℚ) ≤ p.a * p.a := mul_self_nonneg p.a
  rcases hcell with ⟨hx1, hx2, hy1, hy2⟩ | ⟨h1x, h2x, h1y, h2y⟩ | ⟨hx1, hx2, hy1, hy2⟩
  · have hx : (x - cert.root1) * (x - cert.root2) > 0 :=
      mul_pos_of_neg_of_neg (by linarith) (by linarith)
    have hy : (y - cert.root1) * (y - cert.root2) > 0 :=
      mul_pos_of_neg_of_neg (by linarith) (by linarith)
    nlinarith [mul_nonneg (mul_nonneg hnn hx) hy]
  · have hx : (x - cert.root1) * (x - cert.root2) < 0 := by
      have hpos : x - cert.root2 < 0 := by linarith
      have hneg : x - cert.root1 > 0 := by linarith
      exact mul_neg_of_pos_of_neg hneg hpos
    have hy : (y - cert.root1) * (y - cert.root2) < 0 := by
      have hpos : y - cert.root2 < 0 := by linarith
      have hneg : y - cert.root1 > 0 := by linarith
      exact mul_neg_of_pos_of_neg hneg hpos
    nlinarith [mul_nonneg hnn (mul_pos_of_neg_of_neg hx hy)]
  · have hx : (x - cert.root1) * (x - cert.root2) > 0 :=
      mul_pos (by linarith) (by linarith)
    have hy : (y - cert.root1) * (y - cert.root2) > 0 :=
      mul_pos (by linarith) (by linarith)
    nlinarith [mul_nonneg (mul_nonneg hnn hx) hy]

/-! ## 五、义务二/三：构造器全与证书必被接受 -/

/-- 构造器（判别式平方根 s 作代数输入：s² = b²−4ac）。非递归全函数。 -/
def buildCAD2 (p : Poly2) (s : ℚ) : QuadCert where
  root1 := (-p.b + s) / (2 * p.a)
  root2 := (-p.b - s) / (2 * p.a)

/-- **义务二**：构造器对每个输入都产出证书（非递归全函数——可定义性即终止证明）。 -/
theorem buildCAD2_total (p : Poly2) (s : ℚ) :
    ∃ cert : QuadCert, buildCAD2 p s = cert := ⟨_, rfl⟩

/-- **义务三**：构造器证书必被检查器接受（无偷缩可完成域）。 -/
theorem buildCAD2_accepted (p : Poly2) (ha : p.a ≠ 0) (s : ℚ)
    (hs : s * s = p.b * p.b - 4 * p.a * p.c) (hs0 : s ≠ 0) :
    checkCAD2 p (buildCAD2 p s) := by
  have h2a : (2 * p.a) ≠ 0 := by
    exact mul_ne_zero (by norm_num) ha
  have hr1 : eval2 p ((-p.b + s) / (2 * p.a)) = 0 := by
    unfold eval2
    field_simp
    linear_combination hs
  have hr2 : eval2 p ((-p.b - s) / (2 * p.a)) = 0 := by
    unfold eval2
    field_simp
    linear_combination hs
  refine ⟨ha, hr1, hr2, ?_⟩
  intro heq
  apply hs0
  have hd : ((-p.b + s) / (2 * p.a)) - ((-p.b - s) / (2 * p.a)) = 0 := by
    rw [sub_eq_zero]
    exact heq
  field_simp at hd
  linarith

end JurisLean.Seams.UnifiedCAD
