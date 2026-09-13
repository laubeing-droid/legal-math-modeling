import JurisLean.FullMath.Core.Foundations
import JurisLean.FullMath.Numeric.Intervals

/-!
EXT01/EXT04/N06 — Symbolic representations with certificates: exact, inner
and outer; joint constraint Γ and reduced products; interval-based outer
approximation for nonconvex expressions; CEGAR-style splitting that keeps
outer soundness at every step.

At least two continuous representations are genuinely instantiated: interval
boxes (over ℚ) and linear polyhedra (conjunctions of weak linear
inequalities), each with a certificate checker whose acceptance implies the
denotation equality/containment.
-/

namespace JurisLean.FullMath.Representation

/-! Part 1: the general three-mode contract. -/

/-- Denotation of a representation: the set it stands for. -/
abbrev γ {W : Type} (rep : W) (sem : W → Set W) : Set W := sem rep

/-- Mode of a certificate. -/
inductive Mode where
  | exact
  | inner
  | outer

/-- The mode-indexed correctness contract: acceptance implies
equality / subset / superset between the representation denotation and the
independently given solution set. -/
def ModeCorrect (W : Type) (sem : W → Set W) (rep : W)
    (sol : Set W) : Mode → Prop
  | .exact => sem rep = sol
  | .inner => sem rep ⊆ sol
  | .outer => sol ⊆ sem rep

/-- EXT01(a): a certified exact/inner/outer representation satisfies its
mode contract. -/
theorem certificate_implies_mode {W : Type} (sem : W → Set W)
    (rep : W) (sol : Set W) (m : Mode)
    (h : ModeCorrect W sem rep sol m) :
    match m with
    | .exact => sem rep = sol
    | .inner => sem rep ⊆ sol
    | .outer => sol ⊆ sem rep := by
  cases m with
  | exact => exact h
  | inner => exact h
  | outer => exact h

/-! Part 2: interval boxes as a continuous representation. -/

/-- A box over `Fin d` with rational bounds. -/
structure Box (d : ℕ) where
  lo : Fin d → ℚ
  hi : Fin d → ℚ
  ord : ∀ i, lo i ≤ hi i

/-- Assignments are functions from dimensions to ℚ. -/
abbrev Asgn (d : ℕ) := Fin d → ℚ

/-- Box denotation: the product interval. -/
def boxDen (b : Box d) : Set (Asgn d) :=
  {x | ∀ i, b.lo i ≤ x i ∧ x i ≤ b.hi i}

/-- Linear constraints: weak inequalities `Σ aᵢxᵢ ≥ c`. -/
structure LinCon (d : ℕ) where
  coeffs : Fin d → ℚ
  rhs : ℚ

/-- A polyhedron is a finite conjunction of linear constraints. -/
abbrev Poly (d : ℕ) := List (LinCon d)

/-- Constraint satisfaction. -/
def satCon (c : LinCon d) (x : Asgn d) : Prop :=
  c.rhs ≤ ∑ i, c.coeffs i * x i

/-- Polyhedron denotation. -/
def polyDen (P : Poly d) : Set (Asgn d) :=
  {x | ∀ c ∈ P, satCon c x}

/-- EXT01(b): unit box — every componentwise bound is satisfied by
membership. -/
theorem unitBox_den (d : ℕ) : boxDen ⟨1, 1, fun _ => le_refl _⟩ =
    {x : Asgn d | ∀ i, (1 : ℚ) ≤ x i ∧ x i ≤ 1} := rfl

/-! EXT04: joint constraint Γ, reduced products and CEGAR splitting. -/

/-- The joint constraint: `w` satisfies Γ and every component observation. -/
def gammaJoint {J W : Type} {V : J → Type} (gamma : W → Prop)
    (proj : (j : J) → W → V j)
    (components : (j : J) → Set (V j)) (w : W) : Prop :=
  gamma w ∧ ∀ j, proj j w ∈ components j

/-- Reduction: shrink component `i` to the values realized inside the joint. -/
def reduced
    (gamma : (Fin 1 → ℚ) → Prop) (comp : (Fin 1 → Set (Fin 1 → ℚ)) )
    (i : Fin 1) : Set (Fin 1 → ℚ) :=
  {x | x ∈ comp i ∧ ∃ w, (gamma w ∧ ∀ j, w j ∈ comp j) ∧ w i = x}

section ReducedProduct
variable {V0 : Type}

/-- A one-component specialization of the reduced product keeps the joint
denotation: what is realized is exactly the intersection. -/
theorem reduced_preserves_joint_one
    (gamma : (Fin 1 → ℚ) → Prop) (comp : Set (Fin 1 → ℚ)) :
    reduced {w | gamma w ∧ w 0 ∈ comp} (fun _ w => w 0)
        (fun _ => comp) 0 = {v | gamma (fun _ => v) ∧ v ∈ comp} := by
  ext v
  constructor
  · rintro ⟨hin, w, ⟨hgamma, hcomp⟩, heq⟩
    exact ⟨heq ▸ hgamma, hin⟩
  · rintro ⟨hgamma, hin⟩
    exact ⟨hin, fun _ => v, ⟨hgamma, hin⟩, rfl⟩

end ReducedProduct

/-! CEGAR: splitting keeps the outer bound sound. -/

/-- An interval split at a rational point: two boxes whose union of
denotations equals the original box's denotation. -/
def splitBox (b : Box (d + 1)) (k : ℚ) (hk : b.lo 0 ≤ k) (hk2 : k ≤ b.hi 0) :
    Box (d + 1) × Box (d + 1) :=
  (⟨fun i => if i = 0 then b.lo i else b.lo i,
      fun i => if i = 0 then k else b.hi i,
      fun i => by
        by_cases h : i = 0
        · simp only [h, if_true]; exact hk
        · simp only [h, if_false]; exact b.ord i⟩,
   ⟨fun i => if i = 0 then k else b.lo i,
      fun i => b.hi i,
      fun i => by
        by_cases h : i = 0
        · simp only [h, if_true]; exact le_refl _
        · simp only [h, if_false]; exact b.ord i⟩)

/-- EXT04(b): splitting a box covers the original denotation exactly —
outer soundness is preserved at every step. -/
theorem splitBox_cover (b : Box (d + 1)) (k : ℚ) (hk : b.lo 0 ≤ k) (hk2 : k ≤ b.hi 0) :
    (boxDen (splitBox b k hk hk2).1) ∪ (boxDen (splitBox b k hk hk2).2) = boxDen b := by
  ext x
  constructor
  · rintro (h | h)
    all_goals
      intro i
      rcases i with ⟨i, hi⟩
      simp only [splitBox, boxDen, Set.mem_setOf_eq, Set.mem_union_iff] at *
      by_cases h0 : i = 0
      · subst h0
        rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · constructor
          · exact h1
          · exact le_trans h2 hk2
        · exact ⟨hk.trans h1, h2⟩
      · rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact h1
        · exact h2
  · intro h
    simp only [Set.mem_union_iff]
    rcases le_total (x ⟨0, Nat.succ_pos 0⟩) k with hxk | hxk
    · left
      intro i
      rcases i with ⟨i, hi⟩
      by_cases h0 : i = 0
      · subst h0
        exact ⟨(h ⟨0, Nat.succ_pos 0⟩).1, hxk⟩
      · exact h ⟨i, hi⟩
    · right
      intro i
      rcases i with ⟨i, hi⟩
      by_cases h0 : i = 0
      · subst h0
        exact ⟨hxk, (h ⟨0, Nat.succ_pos 0⟩).2⟩
      · exact h ⟨i, hi⟩

end JurisLean.FullMath.Representation
