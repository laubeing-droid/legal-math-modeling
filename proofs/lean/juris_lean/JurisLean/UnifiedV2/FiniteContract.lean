import JurisLean.ULM16TheoryComposition
import Mathlib.Tactic

/-! Proof seeds. NOT accepted until compiled in GitHub Actions. The list
carrier is independently specified. A finite scan is not a proof that a
real-world domain, legal interpretation, or empirical model is complete. -/
namespace JurisLean.ULM.UnifiedV2

variable {α β γ δ : Type}

def sweep (p : α → Bool) : List α → List α
  | [] => []
  | x :: xs => if p x then x :: sweep p xs else sweep p xs

theorem mem_sweep_iff (p : α → Bool) (xs : List α) (x : α) :
    x ∈ sweep p xs ↔ x ∈ xs ∧ p x = true := by
  induction xs with
  | nil => simp [sweep]
  | cons a xs ih =>
      cases hp : p a <;> simp [sweep, hp, ih] <;> aesop

def scan (p : α → Bool) : Nat → List α → List α
  | 0, _ => []
  | _ + 1, [] => []
  | n + 1, x :: xs => if p x then x :: scan p n xs else scan p n xs

theorem scan_member_sound (p : α → Bool) (n : Nat) (xs : List α) (x : α)
    (h : x ∈ scan p n xs) : x ∈ xs ∧ p x = true := by
  induction n generalizing xs with
  | zero => simp [scan] at h
  | succ n ih =>
      cases xs with
      | nil => simp [scan] at h
      | cons a xs =>
          cases hp : p a
          · simp [scan, hp] at h
            obtain ⟨hm, hv⟩ := ih xs h
            exact ⟨by simp [hm], hv⟩
          · simp [scan, hp] at h
            rcases h with h | h
            · subst x
              exact ⟨by simp, hp⟩
            · obtain ⟨hm, hv⟩ := ih xs h
              exact ⟨by simp [hm], hv⟩

theorem full_scan_eq_sweep (p : α → Bool) (xs : List α) :
    scan p xs.length xs = sweep p xs := by
  induction xs with
  | nil => simp [scan, sweep]
  | cons a xs ih =>
      cases hp : p a <;> simp [scan, sweep, hp, ih]

def denotation (P : α → Prop) : Set α := {x | P x}
def outputSet (p : α → Bool) (n : Nat) (xs : List α) : Set α :=
  {x | x ∈ scan p n xs}

/-- Predicate reflection is a module interface theorem, not an assumed claim
that a whole runtime is correct. Each concrete predicate must discharge it. -/
theorem scan_partial (p : α → Bool) (P : α → Prop)
    (reflects : ∀ x, p x = true ↔ P x) (n : Nat) (xs : List α) :
    outputSet p n xs ⊆ denotation P := by
  intro x hx
  exact (reflects x).mp (scan_member_sound p n xs x hx).2

theorem scan_complete (p : α → Bool) (P : α → Prop)
    (reflects : ∀ x, p x = true ↔ P x)
    (xs : List α) (covers : ∀ x, P x → x ∈ xs) :
    outputSet p xs.length xs = denotation P := by
  ext x
  constructor
  · intro hx
    exact scan_partial p P reflects xs.length xs hx
  · intro hx
    change x ∈ scan p xs.length xs
    rw [full_scan_eq_sweep, mem_sweep_iff]
    exact ⟨covers x hx, (reflects x).mpr hx⟩

def RComp (R : α → β → Prop) (S : β → γ → Prop) : α → γ → Prop :=
  fun x z => ∃ y, R x y ∧ S y z

theorem composition_associative
    (R : α → β → Prop) (S : β → γ → Prop) (T : γ → δ → Prop) :
    RComp (RComp R S) T = RComp R (RComp S T) := by
  funext x w
  apply propext
  simp only [RComp]
  aesop

theorem composition_partial
    (L R : α → β → Prop) (M S : β → γ → Prop)
    (hL : ∀ x y, L x y → R x y)
    (hM : ∀ y z, M y z → S y z) :
    ∀ x z, RComp L M x z → RComp R S x z := by
  rintro x z ⟨y, hy, hz⟩
  exact ⟨y, hL x y hy, hM y z hz⟩

theorem composition_complete
    (L R : α → β → Prop) (M S : β → γ → Prop)
    (hL : ∀ x y, L x y ↔ R x y)
    (hM : ∀ y z, M y z ↔ S y z) :
    ∀ x z, RComp L M x z ↔ RComp R S x z := by
  intro x z
  simp only [RComp]
  constructor
  · rintro ⟨y, hy, hz⟩
    exact ⟨y, (hL x y).mp hy, (hM y z).mp hz⟩
  · rintro ⟨y, hy, hz⟩
    exact ⟨y, (hL x y).mpr hy, (hM y z).mpr hz⟩

theorem projection_partial (L S : Set α) (f : α → β) (h : L ⊆ S) :
    f '' L ⊆ f '' S := by
  rintro y ⟨x, hx, rfl⟩
  exact ⟨x, h hx, rfl⟩

/-- Subject equality is the real typed join guard; same textual claim alone is
not enough to combine two cases, branches, rule versions or model versions. -/
structure Binding where
  request : String
  lawVersion : String
  scenario : String
  semanticScope : String
  deriving DecidableEq

def joinBound (a b : Binding) : Bool := decide (a = b)

theorem joinBound_sound (a b : Binding) (h : joinBound a b = true) : a = b := by
  exact of_decide_eq_true h

theorem foreign_request_rejected (a b : Binding) (h : a.request ≠ b.request) :
    joinBound a b = false := by
  simp only [joinBound, decide_eq_false_iff_not]
  intro heq
  exact h (congrArg Binding.request heq)

end JurisLean.ULM.UnifiedV2
