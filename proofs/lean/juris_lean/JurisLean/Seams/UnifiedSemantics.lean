/-
Unified legal semantics, layer A (plan §2–§3.1; I.3, I.4.2).

This file lands the independent semantics of norm selection over named
exclusion graphs: a selection S ⊆ C is *stable* when it is internally
exclusion-free and EVERY non-adopted candidate is excluded by an adopted
one.  The second conjunct quantifies over all of C \ S — an isolated
candidate with no excluder must be adopted, so the family is not the set
of global maxima (the A > B > C, A∥C profile keeps {A, C}).

Escalation pairs ban co-adoption without creating exclusion edges; a
profile whose only conflict is an escalation pair has no stable
selection and yields a referral, never a fabricated choice.

STATUS OF THIS FILE (per AGENTS.md change rules): definitions below are
the construction contract; the named `*_statement` targets are UNPROVED
`Prop`-valued definitions awaiting an authorized CI compile-and-prove
round.  Local Lean execution is forbidden on this machine, so this file
carries `CI_NOT_RUN` status until then.  No `sorry`, `admit`, custom
`axiom`, or `: True :=` appears here, and no theorem body is claimed.
-/

import Mathlib.Data.Finset.Basic

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

/-- The §3.1 stability condition, stated exactly: internal exclusion
freedom (including self-loops), coverage of EVERY non-adopted candidate
by an adopted excluder, and the escalation co-adoption ban. -/
def StableSelection {C : Type} [DecidableEq C] (prof : SelectionProfile C)
    (S : Finset C) : Prop :=
  (∀ a ∈ S, ∀ b ∈ S, (a, b) ∉ prof.exclusions)
  ∧ (∀ n ∈ prof.candidates, n ∉ S → ∃ s ∈ S, (s, n) ∈ prof.exclusions)
  ∧ (∀ p ∈ prof.escalationPairs, ¬(p.1 ∈ S ∧ p.2 ∈ S))

/-- UNPROVED target (U03): an isolated candidate — no incoming
exclusion edge from anywhere — belongs to every stable selection.  This
is the contrapositive of the coverage conjunct and the formal reason
global-maximal screening is not the algorithm. -/
def isolated_in_every_stable_selection {C : Type} [DecidableEq C]
    (prof : SelectionProfile C) : Prop :=
  ∀ S : Finset C, StableSelection prof S →
    ∀ n ∈ prof.candidates,
      (∀ s : C, (s, n) ∉ prof.exclusions) → n ∈ S

/-- UNPROVED target (U03): an escalation-only conflict — one
escalation pair, no exclusion edges — admits no stable selection, so
the outcome is a referral, never a fabricated choice. -/
def escalation_only_has_no_stable_selection {C : Type} [DecidableEq C]
    (prof : SelectionProfile C) : Prop :=
  ProfileWF prof
  → ∀ p ∈ prof.escalationPairs,
      prof.exclusions = ∅
      → prof.candidates = {p.1, p.2}
      → ¬∃ S : Finset C, StableSelection prof S

/-- The A > B > C witness profile: candidates {A, B, C} with edges
A excludes B and B excludes C; A and C are compatible. -/
def abcProfile : SelectionProfile (Fin 3) where
  candidates := {0, 1, 2}
  exclusions := {(0, 1), (1, 2)}
  escalationPairs := ∅

/-- UNPROVED target: `{A, C}` is a stable selection of the witness
profile — the counterexample to global-maximal screening, which would
keep only `{A}` and drop the compatible candidate C. -/
def abc_stable_AC : Prop := StableSelection abcProfile {0, 2}

/-- UNPROVED target: `{A}` alone is NOT stable — C is non-adopted with
no excluder. -/
def abc_A_alone_unstable : Prop := ¬StableSelection abcProfile {0}

end JurisLean.Seams.UnifiedSemantics
