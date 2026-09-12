import JurisLean.FullMath.Logic.ExtensionProfiles

/-!
F13 — Empty values and query aggregation safety.

Not-found ≠ no-solution ≠ empty family: the result type separates
`noExtensions`, an enumerated family and an incomplete search. The three-ring
frame has no stable extension; the self-attacking singleton has an empty
grounded extension; the two degenerate cases answer differently. Existential
answers are witnessed by membership; incomplete searches never yield
substantive universal answers.
-/

namespace JurisLean.FullMath.Logic

open JurisLean.FullMath.Logic (AF Stable grounded grounded_least charF defendedB defendedB_iff)

section Query
variable {A : Type} [DecidableEq A] [Fintype A]

/-- Typed search result: no extensions, an enumerated family, an incomplete
search, or an empty query. -/
inductive Result (A : Type) where
  /-- The semantics admits no extension at all. -/
  | noExtensions
  /-- A fully enumerated family. -/
  | extensions (fam : List (Finset A))
  /-- The search did not finish; nothing may be concluded universally. -/
  | incomplete
  /-- The query itself was empty. -/
  | emptyQuery

/-- Answer kind for universal queries. -/
inductive UniversalAnswer where
  /-- Vacuously true because there is no extension — never auto-asserted as a
  substantive universal. -/
  | vacuousTruth
  /-- All enumerated extensions satisfy the property. -/
  | allSatisfy
  /-- Nothing may be concluded. -/
  | unknown

/-- Aggregation of a universal query over a result. -/
def evalUniversal {A : Type} (r : Result A) : UniversalAnswer :=
  match r with
  | .noExtensions => .vacuousTruth
  | .extensions _ => .allSatisfy
  | .incomplete => .unknown
  | .emptyQuery => .unknown

/-- F13(a): the two degenerate cases are typed apart — vacuity is never
silently merged with an empty enumerated family. -/
theorem no_extensions_ne_empty_family :
    evalUniversal (A := A) .noExtensions ≠ evalUniversal (.extensions []) := by
  intro h
  exact UniversalAnswer.noConfusion h

/-- Existential answers are witnessed by membership. -/
theorem exists_extension_witnessed (af : AF A) (P : Finset A → Prop)
    (E : Finset A) (hstab : Stable af E) (hP : P E) :
    ∃ E', Stable af E' ∧ P E' := ⟨E, hstab, hP⟩

/-- F13(b): an incomplete search never yields a substantive universal. -/
theorem incomplete_not_universal :
    evalUniversal (A := A) .incomplete = .unknown := rfl

/-! The three-ring frame: no stable extension exists. -/

/-- `a` attacks `a+1` cyclically on three nodes. -/
def threeRing : AF (Fin 3) where
  attack x y := decide ((x.val + 1) % 3 = y.val)

/-- F13(c): the three-ring has no stable extension (classic odd cycle). -/
theorem three_ring_no_stable : ∀ E : Finset (Fin 3), ¬ Stable threeRing E := by
  intro E hstab
  obtain ⟨hcf, hcover⟩ := hstab
  have hatt01 : threeRing.attack 0 1 = true := by decide
  have hatt12 : threeRing.attack 1 2 = true := by decide
  have hatt20 : threeRing.attack 2 0 = true := by decide
  by_cases h0 : (0 : Fin 3) ∈ E
  · by_cases h1 : (1 : Fin 3) ∈ E
    · exact absurd (hcf 0 h0 1 h1 hatt01) (by simp)
    · by_cases h2 : (2 : Fin 3) ∈ E
      · exact absurd (hcf 2 h2 0 h0 hatt20) (by simp)
      · -- E = {0}: element 2 is outside and its only attacker is 1 ∉ E
        obtain ⟨x, hxE, hx2⟩ := hcover 2 h2
        have hx1 : x = 1 := by
          fin_cases x
          · exact absurd hx2 (by decide)
          · rfl
          · exact absurd hx2 (by decide)
        exact h1 (hx1 ▸ hxE)
  · by_cases h1 : (1 : Fin 3) ∈ E
    · by_cases h2 : (2 : Fin 3) ∈ E
      · exact absurd (hcf 1 h1 2 h2 hatt12) (by simp)
      · -- E = {1}: element 0 is outside and its only attacker is 2 ∉ E
        obtain ⟨x, hxE, hx0⟩ := hcover 0 h0
        have hx2 : x = 2 := by
          fin_cases x
          · exact absurd hx0 (by decide)
          · exact absurd hx0 (by decide)
          · rfl
        exact h2 (hx2 ▸ hxE)
    · by_cases h2 : (2 : Fin 3) ∈ E
      · -- E = {2}: element 1 is outside and its only attacker is 0 ∉ E
        obtain ⟨x, hxE, hx1⟩ := hcover 1 h1
        have hx0 : x = 0 := by
          fin_cases x
          · rfl
          · exact absurd hx1 (by decide)
          · exact absurd hx1 (by decide)
        exact h0 (hx0 ▸ hxE)
      · -- E = ∅: element 0 is outside, but nobody can cover it
        obtain ⟨x, hxE, _⟩ := hcover 0 h0
        have hEempty : E = ∅ :=
          Finset.eq_empty_iff_forall_not_mem.mpr
            (by intro a; fin_cases a <;> first | exact h0 | exact h1 | exact h2)
        rw [hEempty] at hxE
        exact absurd hxE (by simp)

/-! The self-attacking singleton: the grounded extension is empty. -/

/-- The self-attacking singleton. -/
def selfAttack : AF (Fin 1) where
  attack x y := decide (x.val = 0 ∧ y.val = 0)

/-- F13(d): the grounded extension of the self-attacking singleton is empty —
an empty admissible set that is a different degenerate case from
`noExtensions`. -/
theorem self_attack_grounded_empty : grounded selfAttack = (∅ : Finset (Fin 1)) := by
  apply Finset.Subset.antisymm _ (Finset.empty_subset _)
  refine grounded_least selfAttack ∅ ?_
  have hchar : charF selfAttack (∅ : Finset (Fin 1)) = ∅ := by
    apply Finset.Subset.antisymm _ (Finset.empty_subset _)
    intro a ha
    simp only [charF, Finset.mem_filter] at ha
    rw [defendedB_iff] at ha
    obtain ⟨c, hcE, _⟩ := ha 0 (show selfAttack.attack 0 0 = true by decide)
    exact absurd hcE (by simp)
  exact hchar

/-- The empty set is admissible in the self-attacking frame, distinguishing
`∅` from `noExtensions` under stability too. -/
theorem self_attack_empty_admissible_not_stable :
    Admissible selfAttack (∅ : Finset (Fin 1)) ∧ ¬ Stable selfAttack (∅ : Finset (Fin 1)) := by
  constructor
  · refine ⟨fun x hx => absurd hx (by simp), ?_⟩
    intro a ha
    exact absurd ha (by simp)
  · intro ⟨_, hcover⟩
    obtain ⟨x, hxE, _⟩ := hcover 0 (by simp)
    exact absurd hxE (by simp)

end Query

end JurisLean.FullMath.Logic
