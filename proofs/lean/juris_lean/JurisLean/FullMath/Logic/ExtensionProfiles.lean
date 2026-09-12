import JurisLean.FullMath.Core.Foundations

/-!
F10 — Argumentation extension profiles and membership reflection.

Conflict-freeness, defence, admissibility, completeness, preferredness,
stability and the grounded extension are defined independently over a finite
attack frame; boolean membership decisions reflect the definitions. The
grounded extension is the stabilized iterate of the characteristic function
and is the least of its fixed points (every complete extension is a fixed
point, so the grounded extension is contained in all of them). Preferred
extensions exist by finiteness.
-/

namespace JurisLean.FullMath.Logic

section Extension
variable {A : Type} [DecidableEq A] [Fintype A]

/-- A finite abstract argumentation frame: a boolean attack relation. -/
structure AF (A : Type) where
  attack : A → A → Bool

/-- Conflict-freeness. -/
def CF (af : AF A) (E : Finset A) : Prop :=
  ∀ x ∈ E, ∀ y ∈ E, af.attack x y = false

/-- `E` defends `a`: every attacker of `a` is counter-attacked by `E`. -/
def defends (af : AF A) (E : Finset A) (a : A) : Prop :=
  ∀ b, af.attack b a = true → ∃ c ∈ E, af.attack c b = true

/-- Admissible: conflict-free and defends all its members. -/
def Admissible (af : AF A) (E : Finset A) : Prop :=
  CF af E ∧ ∀ a ∈ E, defends af E a

/-- Complete: admissible and contains everything it defends. -/
def Complete (af : AF A) (E : Finset A) : Prop :=
  Admissible af E ∧ ∀ a, defends af E a → a ∈ E

/-- Stable: conflict-free and attacks every outsider. -/
def Stable (af : AF A) (E : Finset A) : Prop :=
  CF af E ∧ ∀ b ∉ E, ∃ x ∈ E, af.attack x b = true

/-- Preferred: admissible and maximal among admissible sets. -/
def Preferred (af : AF A) (E : Finset A) : Prop :=
  Admissible af E ∧ ∀ E' : Finset A, E ⊂ E' → ¬ Admissible af E'

/-- Boolean defender check: every attacker is counter-attacked by `E`. -/
noncomputable def defendedB (af : AF A) (E : Finset A) (a : A) : Bool :=
  (Finset.univ.filter (fun b => af.attack b a)).toList.all
    (fun b => ((Finset.univ.filter (fun c => af.attack c b)).toList.any
      (fun c => decide (c ∈ E))))

/-- Reflection: the boolean defender check mirrors the definition. -/
theorem defendedB_iff (af : AF A) (E : Finset A) (a : A) :
    defendedB af E a = true ↔ defends af E a := by
  constructor
  · intro h b hb
    have h1 : b ∈ Finset.univ.filter (fun x => af.attack x a) := by
      simp only [Finset.mem_filter, Finset.mem_univ, hb, and_self]
    have hall : ((Finset.univ.filter (fun x => af.attack x a)).toList.all
        (fun b => ((Finset.univ.filter (fun c => af.attack c b)).toList.any
          (fun c => decide (c ∈ E))))) = true := h
    have h2 := (List.all_eq_true.mp hall) b (Finset.mem_toList.mpr h1)
    obtain ⟨c, hc2, hcE⟩ := List.any_eq_true.mp h2
    have hc2' : c ∈ Finset.univ.filter (fun x => af.attack x b) :=
      Finset.mem_toList.mp hc2
    simp only [Finset.mem_filter, Finset.mem_univ] at hc2'
    exact ⟨c, of_decide_eq_true hcE, hc2'.2⟩
  · intro h
    refine List.all_eq_true.mpr ?_
    intro b hb
    have hb' : b ∈ Finset.univ.filter (fun x => af.attack x a) :=
      Finset.mem_toList.mp hb
    simp only [Finset.mem_filter, Finset.mem_univ] at hb'
    obtain ⟨c, hcE, hcb⟩ := h b hb'.2
    refine List.any_eq_true.mpr ⟨c, ?_, decide_eq_true hcE⟩
    exact Finset.mem_toList.mpr (by
      simp only [Finset.mem_filter, Finset.mem_univ, hcb, and_true])

/-- Characteristic function as a Finset transform. -/
noncomputable def charF (af : AF A) (E : Finset A) : Finset A :=
  Finset.univ.filter (fun a => defendedB af E a)

/-- charF is monotone. -/
theorem charF_mono (af : AF A) {E F : Finset A} (h : E ⊆ F) :
    charF af E ⊆ charF af F := by
  intro a ha
  simp only [charF, Finset.mem_filter] at ha ⊢
  obtain ⟨_, hd⟩ := ha
  have hd' : defends af E a := (defendedB_iff af E a).mp hd
  refine ⟨Finset.mem_univ a, (defendedB_iff af F a).mpr ?_⟩
  intro b hb
  obtain ⟨c, hcE, hcb⟩ := hd' b hb
  exact ⟨c, h hcE, hcb⟩

/-- Iterates of charF from ∅. -/
noncomputable def gIter (af : AF A) (n : ℕ) : Finset A := (charF af)^[n] ∅

theorem gIter_zero (af : AF A) : gIter af 0 = ∅ := rfl

theorem gIter_succ (af : AF A) (n : ℕ) : gIter af (n+1) = charF af (gIter af n) := by
  show (charF af)^[n+1] (∅ : Finset A) = charF af ((charF af)^[n] ∅)
  rw [Function.iterate_succ_apply']

theorem gIter_mono_step (af : AF A) (n : ℕ) : gIter af n ⊆ gIter af (n+1) := by
  induction n with
  | zero => exact Finset.empty_subset _
  | succ n ih => rw [gIter_succ, gIter_succ]; exact charF_mono af ih

/-- Dung's lemma: admissibility is preserved by the characteristic function. -/
theorem dung_admissible_step (af : AF A) {E : Finset A} (hE : Admissible af E) :
    Admissible af (charF af E) := by
  obtain ⟨hcf, hdef⟩ := hE
  constructor
  · intro x hx y hy
    simp only [charF, Finset.mem_filter] at hx hy
    obtain ⟨_, hxw⟩ := hx
    obtain ⟨_, hyw⟩ := hy
    have hx' : defends af E x := (defendedB_iff af E x).mp hxw
    have hy' : defends af E y := (defendedB_iff af E y).mp hyw
    cases hxy : af.attack x y with
    | false => exact hxy
    | true =>
      obtain ⟨c, hcE, hcx⟩ := hy' x hxy
      obtain ⟨d, hdE, hdc⟩ := hx' c hcx
      exact absurd hdc (hcf d hdE c hcE)
  · intro a ha
    simp only [charF, Finset.mem_filter] at ha
    obtain ⟨_, haw⟩ := ha
    have ha' : defends af E a := (defendedB_iff af E a).mp haw
    have hsub : E ⊆ charF af E := by
      intro c hcE
      simp only [charF, Finset.mem_filter]
      exact ⟨Finset.mem_univ c, (defendedB_iff af E c).mpr (hdef c hcE)⟩
    intro b hb
    obtain ⟨c, hcE, hcb⟩ := ha' b hb
    exact ⟨c, hsub hcE, hcb⟩

/-- Each grounded iterate is admissible. -/
theorem gIter_admissible (af : AF A) : ∀ n, Admissible af (gIter af n) := by
  intro n
  induction n with
  | zero =>
    exact ⟨fun x hx => absurd hx (by simp [gIter_zero]),
      fun a ha => absurd ha (by simp [gIter_zero])⟩
  | succ n ih =>
    rw [gIter_succ]
    exact dung_admissible_step af ih

/-- Stabilization of charF within the carrier bound. -/
theorem gIter_stabilizes (af : AF A) :
    ∃ k, k ≤ (Finset.univ : Finset A).card ∧ charF af (gIter af k) = gIter af k := by
  by_contra hno
  push_neg at hno
  have hgrow : ∀ k ≤ (Finset.univ : Finset A).card + 1, k ≤ (gIter af k).card := by
    intro k
    induction k with
    | zero => intro _; exact Nat.zero_le _
    | succ k ih =>
      intro hkN
      have hk : k ≤ (Finset.univ : Finset A).card := by omega
      have hne := hno k hk
      have hsub : gIter af k ⊆ gIter af (k+1) := gIter_mono_step af k
      have hc1 : (gIter af k).card ≤ (gIter af (k+1)).card := Finset.card_le_card hsub
      have hcardne : (gIter af k).card ≠ (gIter af (k+1)).card := by
        intro heq
        have hEq : gIter af k = gIter af (k + 1) := by
          apply Finset.eq_of_subset_of_card_le hsub
          exact le_of_eq heq.symm
        exact hne hEq
      have hcard : (gIter af k).card < (gIter af (k+1)).card := lt_of_le_of_ne hc1 hcardne
      have hih : k ≤ (gIter af k).card := ih hk
      omega
  have huniv : (gIter af ((Finset.univ : Finset A).card + 1)).card ≤
      (Finset.univ : Finset A).card :=
    Finset.card_le_card (Finset.subset_univ _)
  have hg := hgrow ((Finset.univ : Finset A).card + 1) (Nat.le_refl _)
  omega

/-- The grounded extension: the stabilized iterate. -/
noncomputable def grounded (af : AF A) : Finset A :=
  gIter af (gIter_stabilizes af).choose

theorem grounded_fixpoint (af : AF A) : charF af (grounded af) = grounded af :=
  (gIter_stabilizes af).choose_spec.2

theorem grounded_admissible (af : AF A) : Admissible af (grounded af) :=
  gIter_admissible af (gIter_stabilizes af).choose

/-- F10(a): the grounded extension is complete — it contains everything it
defends, by the fixpoint equation. -/
theorem grounded_complete (af : AF A) : Complete af (grounded af) := by
  refine ⟨grounded_admissible af, ?_⟩
  intro a ha
  have h1 : a ∈ charF af (grounded af) := by
    simp only [charF, Finset.mem_filter]
    exact ⟨Finset.mem_univ a, (defendedB_iff af (grounded af) a).mpr ha⟩
  rwa [grounded_fixpoint] at h1

/-- F10(b): the grounded extension is the least fixed point of charF. -/
theorem grounded_least (af : AF A) (P : Finset A) (hP : charF af P = P) :
    grounded af ⊆ P := by
  have hiter : ∀ n, gIter af n ⊆ P := by
    intro n
    induction n with
    | zero => exact Finset.empty_subset _
    | succ n ih =>
      rw [gIter_succ]
      exact (charF_mono af ih).trans (by rw [hP]; exact Finset.Subset.rfl)
  exact hiter (gIter_stabilizes af).choose

/-- Complete extensions are fixed points of charF. -/
theorem complete_is_fixpoint (af : AF A) (E : Finset A) (hE : Complete af E) :
    charF af E = E := by
  obtain ⟨_, hcontains⟩ := hE
  apply Finset.Subset.antisymm
  · intro a ha
    simp only [charF, Finset.mem_filter] at ha
    obtain ⟨_, hd⟩ := ha
    rw [defendedB_iff] at hd
    exact hcontains a hd
  · intro a ha
    simp only [charF, Finset.mem_filter]
    refine ⟨Finset.mem_univ a, ?_⟩
    rw [defendedB_iff]
    exact hE.1.2 a ha

/-- F10(c): every complete extension contains the grounded extension. -/
theorem grounded_subset_complete (af : AF A) (E : Finset A) (hE : Complete af E) :
    grounded af ⊆ E :=
  grounded_least af E (complete_is_fixpoint af E hE)

/-- Bounded nonempty sets of naturals attain a maximum. -/
private theorem nat_bounded_has_max (S : Set ℕ) (N : ℕ)
    (hne : S.Nonempty) (hbdd : ∀ n ∈ S, n ≤ N) :
    ∃ k ∈ S, ∀ m ∈ S, m ≤ k := by
  induction N with
  | zero =>
    obtain ⟨k, hk⟩ := hne
    refine ⟨k, hk, ?_⟩
    intro m hm
    have : m ≤ 0 := hbdd m hm
    have : k ≤ 0 := hbdd k hk
    omega
  | succ N ih =>
    by_cases hmax : ∃ m ∈ S, m = N + 1
    · obtain ⟨m, hm, rfl⟩ := hmax
      exact ⟨N + 1, hm, fun n hn => hbdd n hn⟩
    · refine ih (fun n hn => Nat.le_of_lt_succ ?_)
      rcases Nat.lt_or_ge n (N + 1) with h | h
      · exact h
      · exact absurd ⟨n, hn, Nat.le_antisymm h (hbdd n hn)⟩ hmax

/-- F10(d): preferred extensions exist (finiteness argument). -/
theorem preferred_exists (af : AF A) : ∃ E, Preferred af E := by
  have hempty : Admissible af (∅ : Finset A) :=
    ⟨fun x hx => absurd hx (by simp), fun a ha => absurd ha (by simp)⟩
  obtain ⟨k, hkS, hkmax⟩ :=
    nat_bounded_has_max {n | ∃ F : Finset A, Admissible af F ∧ F.card = n}
  obtain ⟨E, hE, hkE⟩ := hkS
      (Finset.univ : Finset A).card
      ⟨0, ∅, hempty, rfl⟩
      (by
        rintro n ⟨F, hF, rfl⟩
        exact Finset.card_le_card (Finset.subset_univ F))
  refine ⟨E, hE, ?_⟩
  intro F hF hFadm
  have hcard : E.card < F.card := Finset.card_lt_card hF
  have := hkmax F.card ⟨F, hFadm, rfl⟩
  rw [hkE] at this
  omega

/-- F10(e): grounded membership reflects defence by the grounded set itself. -/
theorem grounded_membership (af : AF A) (a : A) :
    a ∈ grounded af ↔ defends af (grounded af) a := by
  rw [← grounded_fixpoint af, charF, Finset.mem_filter, defendedB_iff]
  exact and_iff_right (Finset.mem_univ a)

end Extension

end JurisLean.FullMath.Logic
