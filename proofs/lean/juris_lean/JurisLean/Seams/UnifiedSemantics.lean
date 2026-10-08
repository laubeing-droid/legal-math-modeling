/-
Unified legal semantics, layer A (plan §2–§3.1; I.3, I.4.2).

Norm selection over named exclusion graphs: a selection S is *stable*
when S ⊆ C, S is internally exclusion-free, and EVERY non-adopted
candidate is excluded by an adopted one.  The coverage conjunct
quantifies over all of C \ S — an isolated candidate with no excluder
must be adopted, so the family is not the set of global maxima (the
A > B > C, A∥C profile keeps {A, C}).

Escalation pairs ban co-adoption without creating exclusion edges; a
profile whose only conflict is an escalation pair has no stable
selection and yields a referral, never a fabricated choice.

STATUS: the four layer-A targets below are proved theorems; their
compilation evidence is the CI run recorded for this module's subject
(see the construction ledger).  No `sorry`, `admit`, custom `axiom`,
`: True :=`, or `native_decide` appears here.
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

namespace JurisLean.Seams.UnifiedSemantics

/-- Directed exclusion edge: `(a, b)` means adopting `a` excludes
candidate `b` under a named conflict rule (plan §3.1). -/
abbrev NormExclusion (C : Type) := C × C

/-- A norm-selection profile: the candidate set that passed validity,
the exclusion edges produced by named conflict rules, and the same-rank
conflict pairs the law routes to referral (co-adoption banned, no
exclusion edges created). -/
structure SelectionProfile (C : Type) where
  candidates : Finset C
  exclusions : Finset (C × C)
  escalationPairs : Finset (C × C)

/-- Structural well-formedness of a profile: every edge and escalation
pair names actual candidates. -/
def ProfileWF {C : Type} (prof : SelectionProfile C) : Prop :=
  (∀ p ∈ prof.exclusions, p.1 ∈ prof.candidates ∧ p.2 ∈ prof.candidates)
  ∧ (∀ p ∈ prof.escalationPairs, p.1 ∈ prof.candidates ∧ p.2 ∈ prof.candidates)

/-- The §3.1 stability condition, stated exactly: a selection is a
SUBSET of the candidates, internally exclusion-free (including
self-loops), covering EVERY non-adopted candidate by an adopted
excluder, and free of escalation co-adoption. -/
def StableSelection {C : Type} [DecidableEq C] (prof : SelectionProfile C)
    (S : Finset C) : Prop :=
  S ⊆ prof.candidates
  ∧ (∀ a ∈ S, ∀ b ∈ S, (a, b) ∉ prof.exclusions)
  ∧ (∀ n ∈ prof.candidates, n ∉ S → ∃ s ∈ S, (s, n) ∈ prof.exclusions)
  ∧ (∀ p ∈ prof.escalationPairs, ¬(p.1 ∈ S ∧ p.2 ∈ S))

/-- U03 (§3.1): an isolated candidate — no incoming exclusion edge from
anywhere — belongs to every stable selection.  This is the coverage
conjunct's contrapositive and the formal reason global-maximal
screening is not the algorithm. -/
theorem isolated_in_every_stable_selection {C : Type} [DecidableEq C]
    (prof : SelectionProfile C) (S : Finset C)
    (hS : StableSelection prof S) (n : C)
    (hn : n ∈ prof.candidates)
    (hnoex : ∀ s : C, (s, n) ∉ prof.exclusions) :
    n ∈ S := by
  by_contra hout
  obtain ⟨_sub, _free, cover, _esc⟩ := hS
  obtain ⟨s, _hs, hse⟩ := cover n hn hout
  exact hnoex s hse

/-- U03 (§3.1): an escalation-only conflict — one escalation pair, no
exclusion edges, exactly the two candidates — admits no stable
selection: coverage forces both into S while the escalation pair bans
co-adoption.  The outcome is a referral, never a fabricated choice. -/
theorem escalation_only_has_no_stable_selection {C : Type} [DecidableEq C]
    (prof : SelectionProfile C) (hwf : ProfileWF prof) (p : C × C)
    (hp : p ∈ prof.escalationPairs)
    (hnedges : prof.exclusions = ∅)
    (hcand : prof.candidates = {p.1, p.2}) :
    ¬∃ S : Finset C, StableSelection prof S := by
  rintro ⟨S, hsub, hfree, hcover, hesc⟩
  have hc1 : p.1 ∈ prof.candidates := by simp [hcand]
  have hc2 : p.2 ∈ prof.candidates := by simp [hcand]
  have h1 : p.1 ∈ S := by
    by_contra hout
    obtain ⟨_s, _hs, hse⟩ := hcover p.1 hc1 hout
    simp [hnedges] at hse
  have h2 : p.2 ∈ S := by
    by_contra hout
    obtain ⟨_s, _hs, hse⟩ := hcover p.2 hc2 hout
    simp [hnedges] at hse
  exact hesc p hp ⟨h1, h2⟩

/-- The A > B > C witness profile: candidates {A, B, C} with edges
A excludes B and B excludes C; A and C are compatible. -/
def abcProfile : SelectionProfile (Fin 3) where
  candidates := {0, 1, 2}
  exclusions := {(0, 1), (1, 2)}
  escalationPairs := ∅

/-- §3.1's counterexample to global-maximal screening: `{A, C}` is a
stable selection of the witness profile. -/
theorem abc_stable_AC : StableSelection abcProfile {0, 2} := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx ⊢
    tauto
  · intro a ha b hb hab
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
    simp only [abcProfile, Finset.mem_insert, Finset.mem_singleton] at hab
    rcases ha with h1 | h1 | h1 <;>
      rcases hb with h2 | h2 | h2 <;>
      simp_all
  · intro n hn hout
    simp only [abcProfile, Finset.mem_insert, Finset.mem_singleton] at hn
    rcases hn with h | h | h
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hout
      exact absurd rfl hout
    · subst h
      exact ⟨0, by decide, by simp [abcProfile]⟩
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hout
      tauto
  · intro p hp
    simp [abcProfile] at hp

/-- `{A}` alone is NOT stable: the compatible candidate C is non-adopted
with no excluder — the exact hole in a global-maximal screen. -/
theorem abc_A_alone_unstable : ¬StableSelection abcProfile {0} := by
  rintro ⟨_sub, _free, hcover, _esc⟩
  obtain ⟨s, hs, hse⟩ := hcover 2 (by simp [abcProfile]) (by decide)
  simp only [Finset.mem_singleton] at hs
  subst hs
  simp [abcProfile] at hse

end JurisLean.Seams.UnifiedSemantics
