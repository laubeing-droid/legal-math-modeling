import Mathlib.Tactic

/-
Unified utility and strategy, layer H (plan §8; I.4.11 L11, fragment for
U19–U20).

Mirrors the Python behavioral layer
(`tools/unified_math_v2/unified/win_model.py`): exact pure-strategy
verification over ℚ, the utility channel factoring through consequences,
display-rename invariance, a per-case regret bound (the G05 face), and
the discipline that an equilibrium is a STABILITY statement — it never
asserts that play occurred or will occur there.

* `pureNash`: no unilateral profitable deviation inside the ATTEMPT
  menu (the attempt domain admits illegal/irrational actions by design).
* `utility_factorization_through_consequences`: when utility is defined
  as φ ∘ consequences, profiles with equal consequences have equal
  utility (utility is not itself a legal object; preferences live in φ).
* `utility_invariant_under_display_rename`: when a display bijection
  does not touch the consequence semantics, utilities are unchanged.
* `case_regret_bound`: a certified per-alternative slack B bounds the
  menu regret by B.
* `equilibrium_does_not_assert_occurrence`: matching pennies — all four
  profiles are playable and NONE is a pure equilibrium; stability says
  nothing about occurrence.

Menus are LISTS (nonempty by field): the attempt domain is finite and
carries no computational Finset machinery (Finset.toList is
noncomputable and would poison the regret function).

Scope, honestly: pure strategies with finite menus and exact ℚ payoffs.
Mixed strategies, sequential rationality/consistent beliefs (§8.3) and
the Kakutani/Brouwer existence limits stay on their own tracks (the
CAD track owns "all solutions" for polynomial systems).
-/

namespace JurisLean.Seams.UnifiedUtility

variable {P A C : Type} [DecidableEq P]

/-! ## 一、载体：尝试菜单与效用 -/

/-- 规范形有限博弈：每方一个**尝试菜单**（非空列表，违法/非理性动作
    照列），效用只读策略组合。 -/
structure NormGame (P A : Type) where
  /-- 各方尝试菜单。 -/
  menu : P → List A
  /-- 效用（读整组合；ℚ 精确求值）。 -/
  u : (∀ p : P, A) → P → ℚ
  /-- 尝试菜单非空（主文 §8：尝试行动域非空）。 -/
  menuNonempty : ∀ p : P, menu p ≠ []

/-- 组合可发生（每个分量都在自己的尝试菜单内）。 -/
def playable (g : NormGame P A) (s : ∀ p : P, A) : Prop := ∀ p, s p ∈ g.menu p

/-- 单方偏离后的组合。 -/
def dev (s : ∀ p : P, A) (p : P) (a : A) : ∀ p : P, A := fun q => if q = p then a else s q

/-- **纯策略 Nash（尝试域内）**：菜单内任何单方偏离都不增该方效用。 -/
def pureNash (g : NormGame P A) (s : ∀ p : P, A) : Prop :=
  ∀ (p : P) (a : A), a ∈ g.menu p → g.u (dev s p a) p ≤ g.u s p

/-! ## 二、效用经后果分解与显示改名不变 -/

/-- 后果通道（抽象后果载体 C 与读数 φ）。 -/
structure FactoredGame (P A C : Type) where
  /-- 组合的法定后果。 -/
  consequences : (∀ p : P, A) → C
  /-- 各方对后果的效用读数。 -/
  phi : C → P → ℚ

/-- 因子化博弈的效用。 -/
def FactoredGame.utility (fg : FactoredGame P A C) (s : ∀ p : P, A) (p : P) : ℚ :=
  fg.phi (fg.consequences s) p

/-- **效用经后果分解**：后果相同的组合效用相同（同一法定后果可因不同
    偏好产生不同效用——偏好活在 φ 里，效用不是法律对象本身）。 -/
theorem utility_factorization_through_consequences (fg : FactoredGame P A C)
    (s t : ∀ p : P, A) (h : fg.consequences s = fg.consequences t) (p : P) :
    fg.utility s p = fg.utility t p := by
  unfold FactoredGame.utility
  rw [h]

/-- **显示改名不变**：动作显示名经双射重贴而后果语义不动时，效用不变。 -/
theorem utility_invariant_under_display_rename (fg : FactoredGame P A C)
    (r : A ≃ A) (s : ∀ p : P, A)
    (hcon : fg.consequences (fun q => r (s q)) = fg.consequences s) (p : P) :
    fg.utility (fun q => r (s q)) p = fg.utility s p :=
  utility_factorization_through_consequences fg _ _ hcon p

/-! ## 三、悔恨界（G05 面） -/

/-- 列表最大（空表 0；界引理要求非空）。 -/
def maxQ : List ℚ → ℚ
  | [] => 0
  | x :: xs => max x (maxQ xs)

/-- 非空列表的整体最大不超过逐元素上界。 -/
theorem maxQ_le (l : List ℚ) (hne : l ≠ []) (B : ℚ)
    (h : ∀ x ∈ l, x ≤ B) : maxQ l ≤ B := by
  induction l with
  | nil => exact absurd rfl hne
  | cons x xs ih =>
      cases xs with
      | nil => exact h x (by simp)
      | cons y ys =>
          have hx : x ≤ B := h x (by simp)
          have hrest : maxQ (y :: ys) ≤ B :=
            ih (by simp) (fun z hz => h z (by simp [hz]))
          change max x (maxQ (y :: ys)) ≤ B
          exact max_le hx hrest

/-- 菜单内悔恨：最好偏离增益减现效用（经列表 max）。 -/
def regret (g : NormGame P A) (s : ∀ p : P, A) (p : P) : ℚ :=
  maxQ (g.menu p).map (fun a => g.u (dev s p a) p) - g.u s p

/-- **悔恨界**：对菜单内每个替代都有松弛 B，则悔恨 ≤ B
    （证书式上界，不重算 maxQ）。 -/
theorem case_regret_bound (g : NormGame P A) (s : ∀ p : P, A) (p : P) (B : ℚ)
    (hB : ∀ a ∈ g.menu p, g.u (dev s p a) p ≤ g.u s p + B) :
    regret g s p ≤ B := by
  have h1 : ∀ x ∈ (g.menu p).map (fun a => g.u (dev s p a) p),
      x ≤ g.u s p + B := by
    intro x hx
    obtain ⟨a, ham, hxa⟩ := List.mem_map.mp hx
    subst hxa
    exact hB a ham
  have hmax := maxQ_le _ (g.menuNonempty p) (g.u s p + B) h1
  unfold regret
  linarith

/-! ## 四、配硬币见证：无纯均衡且全组合可玩 -/

/-- 配硬币：两方（Bool 承载），菜单 [false,true]；同则甲方得 1 乙方 0，
    异则反之。 -/
def pennies : NormGame Bool Bool where
  menu := fun _ => [false, true]
  u := fun s p => if s true = s false then (if p then 1 else 0) else (if p then 0 else 1)
  menuNonempty := fun _ => by simp

theorem pennies_menu_full (b : Bool) : b ∈ ([false, true] : List Bool) := by
  cases b <;> simp

/-- 全组合可玩（尝试域不挑均衡）。 -/
theorem pennies_all_playable : ∀ s : Bool → Bool, playable pennies s := by
  intro s p
  exact pennies_menu_full (s p)

/-- 无纯均衡：任何组合下输家都可在菜单内翻盘。 -/
theorem pennies_no_pure_nash : ∀ s : Bool → Bool, ¬ pureNash pennies s := by
  intro s hs
  rcases ht : s true with st | st <;> rcases hf : s false with sf | sf
  · have hsdef : s = fun _ : Bool => false := by funext q; cases q <;> simp [ht, hf]
    subst hsdef
    have e1 : pennies.u (dev (fun _ : Bool => false) false true) false = 1 := by rfl
    have e2 : pennies.u (fun _ : Bool => false) false = 0 := by rfl
    have hle := hs false true (pennies_menu_full true)
    rw [e1, e2] at hle
    exact absurd hle (by norm_num)
  · have hsdef : s = fun q : Bool => !q := by funext q; cases q <;> simp [ht, hf]
    subst hsdef
    have e1 : pennies.u (dev (fun q : Bool => !q) true true) true = 1 := by rfl
    have e2 : pennies.u (fun q : Bool => !q) true = 0 := by rfl
    have hle := hs true true (pennies_menu_full true)
    rw [e1, e2] at hle
    exact absurd hle (by norm_num)
  · have hsdef : s = fun q : Bool => q := by funext q; cases q <;> simp [ht, hf]
    subst hsdef
    have e1 : pennies.u (dev (fun q : Bool => q) true false) true = 1 := by rfl
    have e2 : pennies.u (fun q : Bool => q) true = 0 := by rfl
    have hle := hs true false (pennies_menu_full false)
    rw [e1, e2] at hle
    exact absurd hle (by norm_num)
  · have hsdef : s = fun _ : Bool => true := by funext q; cases q <;> simp [ht, hf]
    subst hsdef
    have e1 : pennies.u (dev (fun _ : Bool => true) false false) false = 1 := by rfl
    have e2 : pennies.u (fun _ : Bool => true) false = 0 := by rfl
    have hle := hs false false (pennies_menu_full false)
    rw [e1, e2] at hle
    exact absurd hle (by norm_num)

/-- **均衡不断言发生**：配硬币四组合全可玩且无一纯均衡——稳定性陈述
    对"实际发生了什么/将发生什么"零断言（违法/非理性行动照常可发生，
    见 Python 尝试行动域同合同）。 -/
theorem equilibrium_does_not_assert_occurrence :
    (∀ s : Bool → Bool, playable pennies s) ∧ (∀ s : Bool → Bool, ¬ pureNash pennies s) :=
  ⟨pennies_all_playable, pennies_no_pure_nash⟩

end JurisLean.Seams.UnifiedUtility
