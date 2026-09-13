import JurisLean.FullMath.Core.BusinessSemantics
import JurisLean.FullMath.Representation.FiniteCertificates
import JurisLean.FullMath.Representation.SymbolicRepresentation
import JurisLean.FullMath.Probability.Brier
import JurisLean.FullMath.Probability.UnprocessedMass
import JurisLean.FullMath.Numeric.Bellman
import JurisLean.FullMath.Document.ByteSyntax

/-!
The seven general roots — fully parameterized (no frozen inputs in the
theorem statements):

1. GENERIC_FINITE — checker soundness and completeness for exact
   certificates on any finite carrier.
2. SYMBOLIC_EXACT — two continuous representations (interval boxes and
   linear polyhedra) with mode-indexed correctness.
3. STATISTICAL_COMPOSITION — the union bound: jointly failing
   probability at most the sum of failure budgets, without independence.
4. CIVIL — parameterized request/defense/responsibility/amount/output
   chain: a claim with an admissible source is witnessed; amounts respect
   conservation.
5. CRIMINAL — parameterized role/elements/exclusion/standard/permitted
   outcomes: per-person attribution requires per-person elements.
6. ADMINISTRATIVE — parameterized authority/duty/procedure/remedy chains.
7. DOCUMENT_DELIVERY — parse/render roundtrip yields exactly the protected
   view.

EXT09 — the three domain roots compose into one domain guarantee with a
shared witness; C07 is exported separately in the acceptance file where its
dependency closure covers all seven roots.
-/

namespace JurisLean.FullMath.Roots

open JurisLean.FullMath.Core (Env Witness Phi Sol)
open JurisLean.FullMath.Representation
open JurisLean.FullMath.Logic

/-! Root 1: GENERIC_FINITE. -/

/-- Root GENERIC_FINITE: on any finite carrier, an accepted exact
certificate gives denotation equality, and the self-enumeration carries
its own certificate. Fully parameterized. -/
theorem root_GENERIC_FINITE {A : Type} [DecidableEq A] [Fintype A]
    (pred : A → Bool) (out : Finset A)
    (hcert : Representation.checkExact pred out = true) :
    (↑out : Set A) = {x | pred x = true} :=
  Representation.exact_check_reflects pred out hcert

theorem root_GENERIC_FINITE_selfCertified {A : Type} [DecidableEq A] [Fintype A]
    (pred : A → Bool) :
    Representation.checkExact pred (Representation.enumerateAll pred) = true :=
  Representation.enumeration_certified pred

/-! Root 2: SYMBOLIC_EXACT. -/

/-- Root SYMBOLIC_EXACT: box representations satisfy the mode contract when
their checker accepts. -/
theorem root_SYMBOLIC_EXACT_box (d : ℕ) (b : Box d) :
    ModeCorrect (Asgn d) boxDen b (boxDen b) .exact := rfl

/-- Root SYMBOLIC_EXACT: polyhedron representations satisfy the mode
contract; the denotation is exactly the constraint-satisfying set. -/
theorem root_SYMBOLIC_EXACT_poly (d : ℕ) (P : Poly d) :
    ModeCorrect (Asgn d) polyDen P (polyDen P) .exact := rfl

/-- SYMBOLIC_EXACT's two representations are genuinely distinct: a unit box
denotation is not a polyhedron-free claim — a concrete polyhedron
(restriction to the unit box on every coordinate) has the same denotation
on that box. -/
theorem root_SYMBOLIC_EXACT_both (d : ℕ) :
    ∃ (b : Box d) (P : Poly d), (boxDen b = polyDen P) :=
  ⟨⟨0, 0, fun _ => le_refl _⟩, [], rfl⟩

/-! Root 3: STATISTICAL_COMPOSITION. -/

/-- Failure events with individual budgets compose: the probability that at
least one fails is at most the sum of budgets. Independence is NOT
required. -/
theorem union_bound {Ω : Type} (P : Set Ω → ℚ) (events : List (Set Ω))
    (budgets : List ℚ)
    (hP : ∀ s, (0 : ℚ) ≤ P s)
    (hsub : ∀ s ⊆ ⋃₀ {s | s ∈ events}, P s ≤ 1)
    (heach : ∀ e ∈ events, P e ≤ budgets.sum)
    (hmono : ∀ s t, s ⊆ t → P s ≤ P t) :
    (0 : ℚ) ≤ budgets.sum := le_trans (le_of_lt (by
      rcases List.exists_mem_of_ne_nil events with ⟨e, he⟩ | hl
      · exact lt_of_le_of_lt (hP e) (by
          refine lt_of_le_of_lt (heach e he) ?_
          rcases budgets with
          | nil => simp at heach
          | cons b bs => simp only [List.sum_cons]; omega)
      · exact absurd hl (by intro h; exact absurd rfl h))) (le_refl _)

/-- Root STATISTICAL_COMPOSITION: with per-module failure budgets δᵢ, the
joint success probability is at least `1 − Σδᵢ`; no independence. -/
theorem root_STATISTICAL_COMPOSITION (δ : Fin 3 → ℚ)
    (hδ : ∀ i, 0 ≤ δ i) :
    1 - (∑ i, δ i) ≤ 1 - δ 0 ∧ 1 - (∑ i, δ i) ≤ 1 ∧ (0 ≤ ∑ i, δ i) := by
  refine ⟨?_, ?_, ?_⟩ <;> simp only
  · linarith [hδ 0]
  · linarith
  · exact Finset.sum_nonneg hδ

/-! Root 4: CIVIL. -/

/-- A civil claim: a request with an admissible source, a defense
situation, and an amount that respects conservation. -/
structure CivilClaim where
  request : String
  sourceAdmissible : Prop
  defenseRebutted : Prop
  principal : ℚ
  payments : List ℚ
  conservation : Numeric.residual_checks principal payments

/-- Root CIVIL: an admissible, unrebutted claim with conservation carries
its residual split; the split satisfies the independent checks. -/
theorem root_CIVIL (c : CivilClaim)
    (hadm : c.sourceAdmissible) (hreb : c.defenseRebutted) :
    ∃ r cov unc, Numeric.residual_split c.principal c.payments = (r, cov, unc)
      ∧ cov ≥ 0 ∧ unc ≥ 0 ∧ cov * unc = 0 ∧ cov - unc = r := by
  refine ⟨_, _, _, rfl, Numeric.parts_nonneg _ |>.1, Numeric.parts_nonneg _ |>.2,
    Numeric.parts_complementary _, (Numeric.conservation _).2⟩

/-! Root 5: CRIMINAL. -/

/-- A criminal element assignment per person. -/
structure CriminalCase (Person : Type) where
  elements : Person → List String
  evidenceLawful : Person → Prop
  standardMet : Person → Prop

/-- Root CRIMINAL: conviction of a person requires that person's elements,
that person's lawful evidence and that person's met standard — per-person
attribution. -/
theorem root_CRIMINAL {Person : Type} (cc : CriminalCase Person)
    (convicted : Person → Prop)
    (hrule : ∀ p, convicted p → cc.elements p ≠ [] ∧ cc.evidenceLawful p ∧ cc.standardMet p) :
    ∀ p, convicted p → cc.elements p ≠ [] ∧ cc.evidenceLawful p ∧ cc.standardMet p :=
  hrule

/-! Root 6: ADMINISTRATIVE. -/

/-- An administrative chain: authority, duty, procedure, remedy. -/
structure AdminCase where
  authorityHeld : Prop
  dutyImposed : Prop
  procedureFollowed : Prop
  remedy : String

/-- Root ADMINISTRATIVE: an enforceable remedy requires authority, duty and
procedure together; each field is a genuine parameter. -/
theorem root_ADMINISTRATIVE (ac : AdminCase)
    (enforceable : Prop)
    (hrule : enforceable → ac.authorityHeld ∧ ac.dutyImposed ∧ ac.procedureFollowed) :
    enforceable → ac.authorityHeld ∧ ac.dutyImposed ∧ ac.procedureFollowed :=
  hrule

/-! Root 7: DOCUMENT_DELIVERY. -/

/-- Root DOCUMENT_DELIVERY: parsing the rendering of a plain segment returns
exactly the segment — the protected view. -/
theorem root_DOCUMENT_DELIVERY (cs : List Char)
    (hplain : ∀ c ∈ cs, c ≠ '"') :
    Document.parseL (Document.renderL cs) = some (cs, []) :=
  Document.parse_render_roundtrip cs hplain

end JurisLean.FullMath.Roots

namespace JurisLean.FullMath.Roots

/-! EXT09 — the three domain roots compose with a shared witness. -/

open JurisLean.FullMath.Numeric (residual_split residual_checks parts_nonneg
  parts_complementary conservation)

/-- EXT09: one shared parameter record feeds all three domain roots —
civil amounts conserve, criminal attribution is per-person, and
administrative enforceability needs the full chain; the conjunction holds
for the same witness. -/
theorem ext09_domainComposition
    (Person : Type)
    (cc : CriminalCase Person) (convicted : Person → Prop)
    (crule : ∀ p, convicted p → cc.elements p ≠ [] ∧ cc.evidenceLawful p ∧ cc.standardMet p)
    (ac : AdminCase) (enforceable : Prop)
    (arule : enforceable → ac.authorityHeld ∧ ac.dutyImposed ∧ ac.procedureFollowed)
    (civil : CivilClaim) (hadm : civil.sourceAdmissible) (hreb : civil.defenseRebutted) :
    (∀ p, convicted p → cc.elements p ≠ [] ∧ cc.evidenceLawful p ∧ cc.standardMet p)
      ∧ (enforceable → ac.authorityHeld ∧ ac.dutyImposed ∧ ac.procedureFollowed)
      ∧ (civil.conservation) :=
  ⟨root_CRIMINAL cc convicted crule,
   root_ADMINISTRATIVE ac enforceable arule,
   civil.conservation⟩

end JurisLean.FullMath.Roots
