import JurisLean.UnifiedV2.ConcreteBridge

namespace JurisLean.ULM.UnifiedV2

/-- The accepted witness carries a concrete normative element and quantitative
bounds. F is the independently defined full heterogeneous witness predicate.
For probabilistic/strategic components F means model-relative semantics, not
that predictions equal future outcomes or that model utilities are lawful. -/
structure Witness (α : Type) where
  normative : α
  probability : ℚ
  amount : ℚ
  strategy : String


def ReportValid {α : Type} (F : Witness α → Prop)
    (out : Set (Witness α)) (pLo pHi aLo aHi : ℚ) : Prop :=
  out ⊆ denotation F ∧
  (∀ w, F w → pLo ≤ w.probability ∧ w.probability ≤ pHi) ∧
  (∀ w, F w → aLo ≤ w.amount ∧ w.amount ≤ aHi)

/-- Root proof seed: actual finite scanner + independent predicate reflection
+ universal enclosures. Universal envelope proofs are separate obligations;
checking endpoints of only the found subset cannot discharge them. -/
theorem unified_partial_report {α : Type}
    (F : Witness α → Prop) (p : Witness α → Bool)
    (reflects : ∀ w, p w = true ↔ F w)
    (xs : List (Witness α)) (budget : Nat)
    (pLo pHi aLo aHi : ℚ)
    (probBounds : ∀ w, F w → pLo ≤ w.probability ∧ w.probability ≤ pHi)
    (amountBounds : ∀ w, F w → aLo ≤ w.amount ∧ w.amount ≤ aHi) :
    ReportValid F (outputSet p budget xs) pLo pHi aLo aHi := by
  exact ⟨scan_partial p F reflects budget xs, probBounds, amountBounds⟩

theorem unified_complete_report {α : Type}
    (F : Witness α → Prop) (p : Witness α → Bool)
    (reflects : ∀ w, p w = true ↔ F w)
    (xs : List (Witness α)) (covers : ∀ w, F w → w ∈ xs)
    (pLo pHi aLo aHi : ℚ)
    (probBounds : ∀ w, F w → pLo ≤ w.probability ∧ w.probability ≤ pHi)
    (amountBounds : ∀ w, F w → aLo ≤ w.amount ∧ w.amount ≤ aHi) :
    outputSet p xs.length xs = denotation F ∧
    ReportValid F (outputSet p xs.length xs) pLo pHi aLo aHi := by
  exact ⟨scan_complete p F reflects xs covers,
    unified_partial_report F p reflects xs xs.length pLo pHi aLo aHi probBounds amountBounds⟩

/-- Explicit quantifier obstruction: a found subset cannot certify a universal
property of all semantic solutions. A real counterexample remains in Lean. -/
theorem partial_minimum_counterexample :
    ({(20 : ℚ), 30} : Set ℚ) ⊆ {0,20,30,100} ∧
    ¬ (∀ x ∈ ({0,20,30,100} : Set ℚ), 20 ≤ x ∧ x ≤ 30) := by
  constructor
  · intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
    aesop
  · intro h
    have hz := h 0 (by simp)
    norm_num at hz

end JurisLean.ULM.UnifiedV2
