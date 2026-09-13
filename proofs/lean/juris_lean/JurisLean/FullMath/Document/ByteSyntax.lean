import JurisLean.FullMath.Core.Foundations

/-!
M13/D104-D130 (formal part) - Supported byte syntax, lenses and fractions.
Plain segments exclude the quote and backslash bytes; that exclusion is an
explicit hypothesis of the roundtrip theorem.
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

/-- The canonical delimiters of the supported byte syntax. -/
def quoteByte : Char := '"'
def escapeByte : Char := '\\'

theorem quote_ne_escape : quoteByte ≠ escapeByte := by decide

/-- Rendering a plain segment: surrounding quotes. -/
def renderL (cs : List Char) : List Char := [quoteByte] ++ cs ++ [quoteByte]

/-- Inner scanner: `none` on a stray escape byte, closes on the quote. -/
def parseGo : List Char → List Char → Option (List Char × List Char)
  | [], _ => none
  | c :: rest, acc =>
      if c = escapeByte then none
      else if c = quoteByte then some (acc.reverse, rest)
      else parseGo rest (c :: acc)

theorem parseGo_nil : parseGo ([] : List Char) acc = none := rfl

theorem parseGo_cons (c : Char) (rest acc : List Char) :
    parseGo (c :: rest) acc =
      (if c = escapeByte then none
      else if c = quoteByte then some (acc.reverse, rest)
      else parseGo rest (c :: acc)) := rfl

/-- Parse a quoted segment. -/
def parseL (cs : List Char) : Option (List Char × List Char) :=
  match cs with
  | [] => none
  | c :: rest =>
      if c = escapeByte then none
      else if c = quoteByte then parseGo rest []
      else none

theorem parseL_open : parseL (quoteByte :: rest) = parseGo rest [] := rfl

/-- Plainness: neither delimiter byte occurs. -/
def Plain (cs : List Char) : Prop :=
  ∀ c ∈ cs, c ≠ quoteByte ∧ c ≠ escapeByte

theorem parse_render_roundtrip (cs : List Char) (hplain : Plain cs) :
    parseL (renderL cs) = some (cs, []) := by
  have hstep : ∀ (xs : List Char) (acc : List Char),
      Plain xs →
      parseGo (xs ++ [quoteByte]) acc = some (acc.reverse ++ xs, []) := by
    intro xs
    induction xs with
    | nil =>
      intro acc _
      show parseGo [quoteByte] acc = _
      rw [parseGo_cons, if_neg quote_ne_escape, if_pos rfl, List.append_nil]
      rfl
    | cons c xs ih =>
      intro acc h
      obtain ⟨hcq, hcb⟩ := h c (by simp)
      show parseGo (c :: (xs ++ [quoteByte])) acc = _
      rw [parseGo_cons, if_neg hcb, if_neg hcq,
        ih (c :: acc) h]
      simp only [List.reverse_cons, List.singleton_append, List.append_assoc]
      rfl
  show parseL (quoteByte :: (cs ++ [quoteByte])) = _
  rw [parseL_open, hstep cs [] hplain]
  rfl

/-! Unique keys. -/

def UniqueKeys (l : List (String × String)) : Prop :=
  l.Pairwise (fun a b => a.1 ≠ b.1)

theorem unique_keys_reject_duplicate (l : List (String × String))
    (k : String) (v w : String) (hmem : (k, v) ∈ l) :
    ¬ UniqueKeys ((k, w) :: l) := by
  intro huniq
  obtain ⟨hp, _⟩ := List.pairwise_cons.mp huniq
  have hne : (k, w).1 ≠ (k, v).1 := hp (k, v) hmem
  exact hne rfl

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

/-- Lens law (putput): repeated puts to the same key agree with the last put. -/
theorem docPut_docPut (d : Doc) (k v v' : String) :
    docPut (docPut d k v) k v' = docPut d k v' := by
  simp only [docPut]
  rw [eraseKey_cons_hit _ _ _ _ rfl, eraseKey_idem]

theorem eraseKey_cons_hit (k v : String) (rest : Doc) (k' : String) (h : k = k') :
    eraseKey ((k, v) :: rest) k' = eraseKey rest k' := by
  simp [eraseKey, h]

theorem eraseKey_cons_miss (k v : String) (rest : Doc) (k' : String) (h : ¬ k = k') :
    eraseKey ((k, v) :: rest) k' = (k, v) :: eraseKey rest k' := by
  simp [eraseKey, h]

/-- Erasing twice is idempotent. -/
theorem eraseKey_idem (d : Doc) (k : String) :
    eraseKey (eraseKey d k) k = eraseKey d k := by
  induction d with
  | nil => rfl
  | cons head rest ih =>
    obtain ⟨k', v'⟩ := head
    by_cases hk : k' = k
    · rw [eraseKey_cons_hit _ _ _ _ hk]
      exact ih
    · rw [eraseKey_cons_miss _ _ _ _ hk, eraseKey_cons_miss _ _ _ _ hk]
      rw [ih]

/-- Putting then erasing the same key erases the base document. -/
theorem eraseKey_docPut (d : Doc) (k v : String) :
    eraseKey (docPut d k v) k = eraseKey d k := by
  simp only [docPut]
  exact eraseKey_cons_hit _ _ _ _ rfl

/-- An observer independent of key `k` is unchanged by putting `k`. -/
theorem observer_outside_closure (obs : Doc → String) (d : Doc) (k v : String)
    (hindep : ∀ d₁ d₂, eraseKey d₁ k = eraseKey d₂ k → obs d₁ = obs d₂) :
    obs (docPut d k v) = obs d :=
  hindep _ _ (eraseKey_docPut d k v)

end JurisLean.FullMath.Document
