import JurisLean.FullMath.Core.Foundations

/-!
M13/D104–D130 (formal part) — Supported byte syntax, lenses and fractions.

List-level model of the restricted byte syntax: quoted plain segments
(no quote bytes inside), rendering and parsing are inverses on well-formed
segments; object keys are unique and duplicates are rejected; fractions
normalize to reduced form; single-field edits satisfy the two lens laws;
observers outside the dependency closure of an edit are unchanged.
-/

namespace JurisLean.FullMath.Document

/-! Fraction normalization over ℕ. -/

/-- Reduced fraction: positive denominator, coprime numerator. -/
def reducedFrac (num den : ℕ) : Prop := den > 0 ∧ Nat.Coprime num den

/-- Dividing by the gcd yields a reduced fraction. -/
theorem normalize_reduced (a b : ℕ) (hb : 0 < b) :
    reducedFrac (a / Nat.gcd a b) (b / Nat.gcd a b) := by
  have hg : 0 < Nat.gcd a b :=
    Nat.pos_of_ne_zero (fun h => by
      rw [Nat.gcd_eq_zero_iff] at h
      omega)
  refine ⟨Nat.div_pos (Nat.le_trans (Nat.gcd_le_right a hb)
    (Nat.le_of_eq (Nat.gcd_comm b a ▸ rfl))) hg, ?_⟩
  exact Nat.coprime_div_gcd_div_gcd (by omega)

/-! Restricted segment syntax (list-level). -/

/-- Rendering a plain segment: surrounding quotes. -/
def renderL (cs : List Char) : List Char := ['\"'] ++ cs ++ ['\"']

/-- Inner scanner: collect plain bytes until the closing quote. -/
def parseGo : List Char → List Char → Option (List Char × List Char)
  | [], _ => none
  | c :: rest, acc =>
      if c = '\' then none
      else if c = '\"' then some (acc.reverse, rest)
      else parseGo rest (c :: acc)

/-- Parse a quoted segment. -/
def parseL (cs : List Char) : Option (List Char × List Char) :=
  match cs with
  | [] => none
  | c :: rest => if c = '\' then none else if c = '\"' then parseGo rest [] else none

/-- Roundtrip: parsing the rendering of a plain segment returns the segment. -/
theorem parse_render_roundtrip (cs : List Char) (hplain : ∀ c ∈ cs, c ≠ '\"') :
    parseL (renderL cs) = some (cs, []) := by
  have hstep : ∀ (xs : List Char) (acc : List Char),
      (∀ c ∈ xs, c ≠ '\"') →
      parseGo (xs ++ ['\"']) acc = some (acc.reverse ++ xs, []) := by
    intro xs
    induction xs with
    | nil =>
      intro acc _
      simp [parseGo]
    | cons c xs ih =>
      intro acc h
      have hc : c ≠ '\"' := h c (by simp)
      have hc2 : c ≠ '\' := fun hx => hc (hx ▸ rfl)
      rw [parseGo, if_neg hc2, if_neg hc, ← List.cons_append]
      rw [ih (c :: acc) (fun x hx => by
        rcases List.mem_cons.mp hx with rfl | hx
        · exact hc
        · exact h x hx)]
      simp only [List.reverse_cons, List.cons_append, List.append_nil]
      rfl
  show parseGo (cs ++ ['\"']) [] = _
  rw [hstep cs [] hplain]
  simp

/-! Unique keys. -/

/-- An association list has unique keys. -/
def UniqueKeys (l : List (String × String)) : Prop :=
  l.Pairwise (fun a b => a.1 ≠ b.1)

/-- Duplicate keys are rejected. -/
theorem unique_keys_reject_duplicate (l : List (String × String))
    (k : String) (v w : String) (hmem : (k, v) ∈ l) :
    ¬ UniqueKeys ((k, w) :: l) := by
  intro huniq
  have hp : l.Pairwise (fun a b => a.1 ≠ b.1) :=
    (List.pairwise_cons.mp huniq).2
  exact (hp (k, w) hmem rfl).elim

/-! Lens laws. -/

/-- Documents as association lists. -/
abbrev Doc := List (String × String)

/-- Read a key. -/
def docGet (d : Doc) (k : String) : Option String := d.lookup k

/-- Erase all entries with a key. -/
def eraseKey : Doc → String → Doc
  | [], _ => []
  | (k, v) :: rest, k' => if k = k' then eraseKey rest k' else (k, v) :: eraseKey rest k'

/-- Put a key. -/
def docPut (d : Doc) (k : String) (v : String) : Doc :=
  (k, v) :: eraseKey d k

/-- Lens law 1: get after put returns the value. -/
theorem docGet_put (d : Doc) (k : String) (v : String) :
    docGet (docPut d k v) k = some v := by
  simp [docGet, docPut, List.lookup_cons]

/-- Lens law 2 (put of the read-back value is the identity) at the head. -/
theorem docPut_get_head (d : Doc) (k v : String) :
    docPut ((k, v) :: d) k v = (k, v) :: d := by
  simp [docPut, eraseKey]

/-- An observer independent of key `k` is unchanged by putting `k`. -/
theorem observer_outside_closure (obs : Doc → String) (d : Doc) (k v : String)
    (hindep : ∀ d₁ d₂, eraseKey d₁ k = eraseKey d₂ k → obs d₁ = obs d₂) :
    obs (docPut d k v) = obs d := by
  refine hindep _ _ ?_
  simp [docPut, eraseKey]

end JurisLean.FullMath.Document
