import JurisLean.FullMath.Core.Foundations

/-!
M13/D104-D130 (formal part) - Supported byte syntax, lenses and fractions.
Plain segments exclude both the quote byte and the backslash byte; that
exclusion is an explicit hypothesis of the roundtrip theorem.
-/

namespace JurisLean.FullMath.Document

/-! Fraction normalization over N. -/

def reducedFrac (num den : Nat) : Prop := den > 0 ∧ Nat.Coprime num den

theorem normalize_reduced (a b : Nat) (hb : 0 < b) :
    reducedFrac (a / Nat.gcd a b) (b / Nat.gcd a b) := by
  have hg : 0 < Nat.gcd a b :=
    Nat.pos_of_ne_zero (fun h => by
      rw [Nat.gcd_eq_zero_iff] at h
      omega)
  have hgb : Nat.gcd a b ≤ b := Nat.gcd_le_right a hb
  exact ⟨Nat.div_pos hgb hg, Nat.coprime_div_gcd_div_gcd (by omega)⟩

/-! Restricted segment syntax (list-level). -/

def renderL (cs : List Char) : List Char := ['"'] ++ cs ++ ['"']

def parseGo : List Char → List Char → Option (List Char × List Char)
  | [], _ => none
  | c :: rest, acc =>
      if c = '\\' then none
      else if c = '"' then some (acc.reverse, rest)
      else parseGo rest (c :: acc)

def parseL (cs : List Char) : Option (List Char × List Char) :=
  match cs with
  | [] => none
  | c :: rest => if c = '\\' then none else if c = '"' then parseGo rest [] else none

/-- Plainness: neither the quote nor the backslash byte occurs. -/
def Plain (cs : List Char) : Prop :=
  ∀ c ∈ cs, c ≠ '"' ∧ c ≠ '\\'

theorem parse_render_roundtrip (cs : List Char) (hplain : Plain cs) :
    parseL (renderL cs) = some (cs, []) := by
  have hstep : ∀ (xs : List Char) (acc : List Char),
      Plain xs →
      parseGo (xs ++ ['"']) acc = some (acc.reverse ++ xs, []) := by
    intro xs
    induction xs with
    | nil =>
      intro acc _
      simp [parseGo]
    | cons c xs ih =>
      intro acc h
      obtain ⟨hcq, hcb⟩ := h c (by simp)
      rw [parseGo, if_neg hcb, if_neg hcq, ← List.cons_append]
      rw [ih (c :: acc) (fun x hx => by
        rcases List.mem_cons.mp hx with rfl | hx
        · exact ⟨hcq, hcb⟩
        · exact h x hx)]
      simp only [List.reverse_cons, List.cons_append, List.append_nil]
      rfl
  show parseGo (cs ++ ['"']) [] = _
  rw [hstep cs [] hplain]
  simp

/-! Unique keys. -/

def UniqueKeys (l : List (String × String)) : Prop :=
  l.Pairwise (fun a b => a.1 ≠ b.1)

theorem unique_keys_reject_duplicate (l : List (String × String))
    (k : String) (v w : String) (hmem : (k, v) ∈ l) :
    ¬ UniqueKeys ((k, w) :: l) := by
  intro huniq
  obtain ⟨hp, _⟩ := List.pairwise_cons.mp huniq
  exact (hp (k, w) hmem rfl).elim

/-! Lens laws. -/

abbrev Doc := List (String × String)

def docGet (d : Doc) (k : String) : Option String := d.lookup k

def eraseKey : Doc → String → Doc
  | [], _ => []
  | (k, v) :: rest, k' => if k = k' then eraseKey rest k' else (k, v) :: eraseKey rest k'

def docPut (d : Doc) (k : String) (v : String) : Doc :=
  (k, v) :: eraseKey d k

theorem docGet_put (d : Doc) (k : String) (v : String) :
    docGet (docPut d k v) k = some v := by
  simp [docGet, docPut]

theorem docPut_get_head (d : Doc) (k v : String) :
    docPut ((k, v) :: d) k v = (k, v) :: d := by
  simp [docPut, eraseKey]

/-- Erasing twice is idempotent. -/
theorem eraseKey_idem (d : Doc) (k : String) :
    eraseKey (eraseKey d k) k = eraseKey d k := by
  induction d with
  | nil => rfl
  | cons (k', v') rest ih =>
    by_cases hk : k' = k
    · simp [eraseKey, hk, ih]
    · simp [eraseKey, hk, ih]

/-- An observer independent of key `k` is unchanged by putting `k`. -/
theorem observer_outside_closure (obs : Doc → String) (d : Doc) (k v : String)
    (hindep : ∀ d₁ d₂, eraseKey d₁ k = eraseKey d₂ k → obs d₁ = obs d₂) :
    obs (docPut d k v) = obs d :=
  hindep _ _ (eraseKey_idem d k)

end JurisLean.FullMath.Document
