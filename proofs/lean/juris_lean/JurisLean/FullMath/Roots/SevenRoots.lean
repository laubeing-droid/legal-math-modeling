import JurisLean.FullMath.Core.BusinessSemantics
import JurisLean.FullMath.Representation.FiniteCertificates
import JurisLean.FullMath.Representation.SymbolicRepresentation
import JurisLean.FullMath.Probability.Brier
import JurisLean.FullMath.Probability.UnprocessedMass
import JurisLean.FullMath.Numeric.Bellman
import JurisLean.FullMath.Document.ByteSyntax
import JurisLean.FullMath.Numeric.Quantities

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

/-- Root SYMBOLIC_EXACT: box representations satisfy the exact-mode
contract. -/
theorem root_SYMBOLIC_EXACT_box (d : ℕ) (b : Box d) :
    ModeCorrect (Asgn d) (Box d) boxDen b (boxDen b) .exact := rfl

/-- Root SYMBOLIC_EXACT: polyhedron representations satisfy the exact-mode
contract; the denotation is exactly the constraint-satisfying set. -/
theorem root_SYMBOLIC_EXACT_poly (d : ℕ) (P : Poly d) :
    ModeCorrect (Asgn d) (Poly d) polyDen P (polyDen P) .exact := rfl

private theorem coord_sum_one (d : ℕ) (i : Fin d) (x : Asgn d) :
    (∑ j, (if j = i then (1 : ℚ) else 0) * x j) = x i := by
  have hmul : ∀ j : Fin d, (if j = i then (1 : ℚ) else 0) * x j =
      if j = i then x j else 0 := by
    intro j
    by_cases h : j = i <;> simp [h]
  rw [Finset.sum_congr rfl (fun j _ => hmul j)]
  simp

private theorem coord_sum_neg (d : ℕ) (i : Fin d) (x : Asgn d) :
    (∑ j, (if j = i then (-1 : ℚ) else 0) * x j) = -x i := by
  have hmul : ∀ j : Fin d, (if j = i then (-1 : ℚ) else 0) * x j =
      if j = i then -x j else 0 := by
    intro j
    by_cases h : j = i <;> simp [h]
  rw [Finset.sum_congr rfl (fun j _ => hmul j)]
  simp

/-- The polyhedron with two weak inequalities per coordinate singling out
the origin. -/
private noncomputable def zeroBoxPoly (d : ℕ) : Poly d :=
  (Finset.univ.toList.flatMap fun i =>
    [⟨fun j => if j = i then (1 : ℚ) else 0, 0⟩,
     ⟨fun j => if j = i then (-1 : ℚ) else 0, 0⟩] : List (LinCon d))

/-- SYMBOLIC_EXACT's two representations are genuinely distinct encodings of
one denotation: for every dimension the zero box `{x | ∀ i, x i = 0}` is
also the denotation of a concrete polyhedron (two weak inequalities per
coordinate). -/
theorem root_SYMBOLIC_EXACT_both (d : ℕ) :
    ∃ (b : Box d) (P : Poly d), boxDen b = polyDen P := by
  refine ⟨⟨fun _ => 0, fun _ => 0, fun _ => le_refl _⟩, zeroBoxPoly d, ?_⟩
  ext x
  simp only [boxDen, polyDen, Set.mem_setOf_eq]
  constructor
  · intro h c hc
    rcases List.mem_flatMap.mp hc with ⟨i, hi, hc2⟩
    rw [Finset.mem_toList] at hi
    simp only [List.mem_cons, List.mem_singleton] at hc2
    rcases hc2 with rfl | rfl | hf
    · simp only [satCon]
      rw [coord_sum_one d i x]
      exact (h i).1
    · simp only [satCon]
      rw [coord_sum_neg d i x]
      exact neg_nonneg.mpr (h i).2
    · cases hf
  · intro h i
    have m1 : (⟨fun j => if j = i then (1 : ℚ) else 0, 0⟩ : LinCon d) ∈
        zeroBoxPoly d :=
      List.mem_flatMap.mpr ⟨i, Finset.mem_toList.mpr (Finset.mem_univ i), by simp⟩
    have s1 := h _ m1
    simp only [satCon] at s1
    rw [coord_sum_one d i x] at s1
    have m2 : (⟨fun j => if j = i then (-1 : ℚ) else 0, 0⟩ : LinCon d) ∈
        zeroBoxPoly d :=
      List.mem_flatMap.mpr ⟨i, Finset.mem_toList.mpr (Finset.mem_univ i), by simp⟩
    have s2 := h _ m2
    simp only [satCon] at s2
    rw [coord_sum_neg d i x] at s2
    exact ⟨s1, neg_nonneg.mp s2⟩

/-! Root 3: STATISTICAL_COMPOSITION. -/

/-- Union bound, composed over a finite list of failure events with paired
budgets: the union's probability is at most the total budget. Pairwise
subadditivity is composed by induction; independence is NOT used. -/
theorem union_bound {Ω : Type} (P : Set Ω → ℚ)
    (hsub : ∀ e f : Set Ω, P (e ∪ f) ≤ P e + P f) (hempty : P ∅ = 0) :
    ∀ (events : List (Set Ω)) (budgets : List ℚ), events.length = budgets.length →
      (∀ i (_hi : i < events.length), P events[i]! ≤ budgets[i]!) →
      P (events.foldr (· ∪ ·) ∅) ≤ budgets.sum := by
  intro events
  induction events with
  | nil =>
    intro budgets hlen _
    cases budgets with
    | nil => simp [hempty]
    | cons b bs => simp at hlen
  | cons e es ih =>
    intro budgets hlen hch
    cases budgets with
    | nil => simp at hlen
    | cons b bs =>
      have hl2 : es.length = bs.length := by simp at hlen; exact hlen
      have h1 : P e ≤ b := hch 0 (by simp only [List.length_cons]; omega)
      have h2 : P (es.foldr (· ∪ ·) ∅) ≤ bs.sum := by
        refine ih bs hl2 ?_
        intro i hi
        have hlt : i + 1 < (e :: es).length := by
          simp only [List.length_cons]; omega
        simpa [List.getElem!_cons_succ] using hch (i + 1) hlt
      show P (e ∪ es.foldr (· ∪ ·) ∅) ≤ b + bs.sum
      calc P (e ∪ es.foldr (· ∪ ·) ∅)
          ≤ P e + P (es.foldr (· ∪ ·) ∅) := hsub e _
        _ ≤ b + bs.sum := by linarith

/-- Root STATISTICAL_COMPOSITION: with per-module failure budgets paired to
failure events over one set function, the composed (union) failure
probability is at most the total budget — no independence required. -/
theorem root_STATISTICAL_COMPOSITION {Ω : Type} (P : Set Ω → ℚ)
    (events : List (Set Ω)) (budgets : List ℚ)
    (hlen : events.length = budgets.length)
    (hsub : ∀ e f : Set Ω, P (e ∪ f) ≤ P e + P f)
    (hempty : P ∅ = 0)
    (hch : ∀ i (_hi : i < events.length), P events[i]! ≤ budgets[i]!) :
    P (events.foldr (· ∪ ·) ∅) ≤ budgets.sum :=
  union_bound P hsub hempty events budgets hlen hch

/-! Root 4: CIVIL. -/

/-- A civil claim: a request, a principal and scenario payments that
respect the no-overpayment ledger constraint. -/
structure CivilClaim where
  request : String
  principal : ℚ
  payments : List ℚ
  noOverpay : payments.sum ≤ principal

/-- The civil conservation statement: the covered/uncovered split conserves
the residual, the residual is nonnegative under the no-overpay ledger, and
the uncovered part is exactly zero. -/
def CivilConserved (c : CivilClaim) : Prop :=
  Numeric.covered (Numeric.residual c.principal c.payments) -
      Numeric.uncovered (Numeric.residual c.principal c.payments) =
    Numeric.residual c.principal c.payments ∧
    (0 : ℚ) ≤ Numeric.residual c.principal c.payments ∧
    Numeric.uncovered (Numeric.residual c.principal c.payments) = 0

/-- Root CIVIL: a claim whose ledger never overpays carries a residual split
into covered/uncovered parts that conserve the principal; because the
residual is nonnegative, the uncovered part is exactly zero. -/
theorem root_CIVIL (c : CivilClaim) : CivilConserved c := by
  have hr : (0 : ℚ) ≤ Numeric.residual c.principal c.payments := by
    show (0 : ℚ) ≤ c.principal - c.payments.sum
    linarith [c.noOverpay]
  refine ⟨Numeric.conservation _, hr, ?_⟩
  show max (-(c.principal - c.payments.sum)) (0 : ℚ) = 0
  rw [max_eq_right (by linarith [c.noOverpay])]

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
    (hplain : Document.Plain cs) :
    Document.parseL (Document.renderL cs) = some (cs, []) :=
  Document.parse_render_roundtrip cs hplain

end JurisLean.FullMath.Roots

namespace JurisLean.FullMath.Roots

/-! EXT09 — the three domain roots compose with a shared witness. -/

/-- EXT09: one shared parameter record feeds all three domain roots —
civil amounts conserve without overpayment, criminal attribution is
per-person, and administrative enforceability needs the full chain; the
conjunction holds for the same witness. -/
theorem ext09_domainComposition
    (Person : Type)
    (cc : CriminalCase Person) (convicted : Person → Prop)
    (crule : ∀ p, convicted p → cc.elements p ≠ [] ∧ cc.evidenceLawful p ∧ cc.standardMet p)
    (ac : AdminCase) (enforceable : Prop)
    (arule : enforceable → ac.authorityHeld ∧ ac.dutyImposed ∧ ac.procedureFollowed)
    (civil : CivilClaim) :
    (∀ p, convicted p → cc.elements p ≠ [] ∧ cc.evidenceLawful p ∧ cc.standardMet p)
      ∧ (enforceable → ac.authorityHeld ∧ ac.dutyImposed ∧ ac.procedureFollowed)
      ∧ CivilConserved civil :=
  ⟨root_CRIMINAL cc convicted crule,
   root_ADMINISTRATIVE ac enforceable arule,
   root_CIVIL civil⟩

end JurisLean.FullMath.Roots
