import JurisLean.Candidates.Final20261021.Compiler

/-!
Original question 03.4 / U03.2: termination and query completeness of the
actual duplicate-list Horn closure in `Compiler.proposed_rule_input`.

The fuel bound counts distinct facts and rule conclusions. It does not assume
that the list is duplicate-free or that a round adds at most one list entry.
The accepted result is relative to exactly the supplied facts and rules;
neither source truth nor validity of a legal rule follows from saturation.
-/

namespace JurisLean.Candidates.Final20261021.Compiler

theorem mem_advance_iff (rules : List (Rule Nat)) (known : List Nat) (a : Nat) :
    a ∈ advance rules known ↔ a ∈ known ∨
      ∃ r ∈ rules, r.conclusion = a ∧ ∀ b ∈ r.premises, b ∈ known := by
  constructor
  · intro h
    rcases List.mem_append.mp h with old | added
    · exact Or.inl old
    · obtain ⟨r, hr, ha⟩ := List.mem_flatMap.mp added
      split at ha
      next enabled =>
        have eq : a = r.conclusion := List.mem_singleton.mp ha
        exact Or.inr ⟨r, hr, eq.symm, by
          simpa only [List.all_eq_true, decide_eq_true_eq] using enabled⟩
      next disabled => simp at ha
  · rintro (old | ⟨r, hr, eq, premises⟩)
    · exact advance_contains rules known a old
    · apply List.mem_append.mpr
      apply Or.inr
      apply List.mem_flatMap.mpr
      refine ⟨r, hr, ?_⟩
      have enabled : r.premises.all (fun b => decide (b ∈ known)) = true := by
        simpa only [List.all_eq_true, decide_eq_true_eq] using premises
      simp [enabled, eq]

theorem computed_succ (rules : List (Rule Nat)) (fuel : Nat) (facts : List Nat) :
    proposed_rule_input rules (fuel + 1) facts =
      advance rules (proposed_rule_input rules fuel facts) := by
  induction fuel generalizing facts with
  | zero => rfl
  | succ n ih =>
      simpa only [proposed_rule_input] using ih (advance rules facts)

theorem computed_add (rules : List (Rule Nat)) (m n : Nat) (facts : List Nat) :
    proposed_rule_input rules (m + n) facts =
      proposed_rule_input rules n (proposed_rule_input rules m facts) := by
  induction m generalizing facts with
  | zero => rfl
  | succ m ih =>
      simpa only [Nat.succ_add, proposed_rule_input] using ih (advance rules facts)

def finiteCarrier (rules : List (Rule Nat)) (facts : List Nat) : Finset Nat :=
  (facts ++ rules.map Rule.conclusion).toFinset

theorem computed_subset_carrier (rules : List (Rule Nat)) (facts : List Nat)
    (fuel : Nat) :
    (proposed_rule_input rules fuel facts).toFinset ⊆ finiteCarrier rules facts := by
  intro a ha
  have derived := u03_1_computed_sound rules facts fuel a (List.mem_toFinset.mp ha)
  induction derived with
  | fact a ha => simp [finiteCarrier, ha]
  | fire r hr premises ih =>
      have h : r.conclusion ∈ rules.map Rule.conclusion := List.mem_map.mpr ⟨r, hr, rfl⟩
      simp [finiteCarrier, h]

theorem closed_iff_advance_subset (rules : List (Rule Nat)) (known : List Nat) :
    closed rules known = true ↔ ∀ a ∈ advance rules known, a ∈ known := by
  rw [closed_reflects]
  constructor
  · intro h a ha
    rcases (mem_advance_iff rules known a).mp ha with old | ⟨r, hr, eq, premises⟩
    · exact old
    · rw [← eq]
      exact h r hr premises
  · intro h r hr premises
    exact h r.conclusion ((mem_advance_iff rules known r.conclusion).mpr
      (Or.inr ⟨r, hr, rfl, premises⟩))

theorem advance_closed (rules : List (Rule Nat)) (known : List Nat)
    (h : closed rules known = true) : closed rules (advance rules known) = true := by
  apply (closed_reflects rules _).mpr
  intro r hr premises
  apply advance_contains rules known r.conclusion
  apply (closed_reflects rules known).mp h r hr
  intro a ha
  exact (closed_iff_advance_subset rules known).mp h a (premises a ha)

theorem computed_closed (rules : List (Rule Nat)) (fuel : Nat) (known : List Nat)
    (h : closed rules known = true) :
    closed rules (proposed_rule_input rules fuel known) = true := by
  induction fuel generalizing known with
  | zero => exact h
  | succ n ih => exact ih _ (advance_closed rules known h)

theorem exists_closed_fuel_le_carrier (rules : List (Rule Nat)) (facts : List Nat) :
    ∃ k ≤ (finiteCarrier rules facts).card,
      closed rules (proposed_rule_input rules k facts) = true := by
  by_contra! none
  let bound := (finiteCarrier rules facts).card
  have growth : ∀ k ≤ bound,
      (proposed_rule_input rules k facts).toFinset.card <
        (proposed_rule_input rules (k + 1) facts).toFinset.card := by
    intro k hk
    apply Finset.card_lt_card
    constructor
    · intro a ha
      rw [computed_succ]
      exact List.mem_toFinset.mpr
        (advance_contains rules _ a (List.mem_toFinset.mp ha))
    · intro reverse
      apply none k hk
      apply (closed_iff_advance_subset rules _).mpr
      intro a ha
      apply List.mem_toFinset.mp
      apply reverse
      rw [computed_succ]
      exact List.mem_toFinset.mpr ha
  have lower : ∀ k, k ≤ bound + 1 →
      k ≤ (proposed_rule_input rules k facts).toFinset.card := by
    intro k
    induction k with
    | zero => intro _; exact Nat.zero_le _
    | succ k ih =>
        intro hk
        have hk' : k ≤ bound := by omega
        have prev := ih (by omega)
        have strict := growth k hk'
        omega
  have upper := Finset.card_le_card (computed_subset_carrier rules facts (bound + 1))
  have impossible := lower (bound + 1) (by omega)
  change (proposed_rule_input rules (bound + 1) facts).toFinset.card ≤ bound at upper
  omega

theorem u03_2_closed_at_finite_fuel (rules : List (Rule Nat)) (facts : List Nat)
    (fuel : Nat) (enough : (finiteCarrier rules facts).card ≤ fuel) :
    closed rules (proposed_rule_input rules fuel facts) = true := by
  obtain ⟨k, hk, stable⟩ := exists_closed_fuel_le_carrier rules facts
  have h := computed_closed rules (fuel - k) _ stable
  rw [← computed_add] at h
  have eq : k + (fuel - k) = fuel := by omega
  simpa only [eq] using h

theorem u03_2_bounded_executable_closure_complete (rules : List (Rule Nat))
    (facts : List Nat) (fuel : Nat)
    (enough : (finiteCarrier rules facts).card ≤ fuel) :
    ∃ known, proposed_checked_rule_input rules fuel facts = .known known ∧
      ∀ a, a ∈ known ↔ Derives (· ∈ facts) (· ∈ rules) a := by
  let known := proposed_rule_input rules fuel facts
  have checked : proposed_checked_rule_input rules fuel facts = .known known := by
    simp only [proposed_checked_rule_input, u03_2_closed_at_finite_fuel rules facts fuel enough,
      if_true, known]
  exact ⟨known, checked, u03_2_checked_closure_complete rules facts fuel known checked⟩

end JurisLean.Candidates.Final20261021.Compiler
