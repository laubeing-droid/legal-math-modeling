import JurisLean.FullMath.Core.Foundations

/-!
P04 — Observation identity: keyed acceptance is idempotent per id (a
duplicate resubmission never double-counts; a later conflicting value
leaves the accepted id set unchanged), and excluding observations by id
commutes with deduplication — derived aggregates over the retained set
never depend on excluded ids.
-/

namespace JurisLean.FullMath.Probability

/-- An observation with an explicit identity. -/
structure Obs where
  id : ℕ
  value : ℚ

/-- First-accepted deduplication with an explicit seen-id set (structural). -/
def dedupAux : List Obs → List ℕ → List Obs
  | [], _ => []
  | o :: rest, seen =>
      if o.id ∈ seen then dedupAux rest seen else o :: dedupAux rest (o.id :: seen)

/-- The accepted observations of a submission list (dedup by id). -/
def dedup (l : List Obs) : List Obs := dedupAux l []

/-- The aggregate over deduplicated observations. -/
def obsTotal (l : List Obs) : ℚ := (dedup l).map Obs.value |>.sum

theorem dedupAux_cons_seen (o : Obs) (rest : List Obs) (seen : List ℕ)
    (h : o.id ∈ seen) : dedupAux (o :: rest) seen = dedupAux rest seen := by
  simp only [dedupAux, if_pos h]

theorem dedupAux_cons_fresh (o : Obs) (rest : List Obs) (seen : List ℕ)
    (h : ¬ (o.id ∈ seen)) :
    dedupAux (o :: rest) seen = o :: dedupAux rest (o.id :: seen) := by
  simp only [dedupAux, if_neg h]

/-- P04(a): resubmitting the same observation does not update twice. -/
theorem dedup_no_double_update (o : Obs) (l : List Obs) :
    obsTotal (o :: o :: l) = obsTotal (o :: l) := by
  simp only [obsTotal, dedup]
  rw [dedupAux_cons_fresh o (o :: l) [] (by simp),
    dedupAux_cons_seen o l [o.id] (by simp),
    dedupAux_cons_fresh o l [] (by simp)]

/-- P04(b): a later conflicting value under the same id changes nothing
about the accepted set — the id was already bound by first acceptance. -/
theorem dedup_conflict_not_overwrite (k : ℕ) (v v' : ℚ) (l : List Obs) :
    (dedup (⟨k, v'⟩ :: ⟨k, v⟩ :: l)).map Obs.id = (dedup (⟨k, v⟩ :: l)).map Obs.id := by
  simp only [dedup]
  rw [dedupAux_cons_fresh ⟨k, v'⟩ (⟨k, v⟩ :: l) [] (by simp),
    dedupAux_cons_seen ⟨k, v⟩ l [k] (by simp),
    dedupAux_cons_fresh ⟨k, v⟩ l [] (by simp)]

/-- Exclusion predicate on observation ids. -/
private def exclP (k : ℕ) (o : Obs) : Bool := decide (o.id != k)

/-- Pre-seeding the exclusion id in the seen set is invisible after
filtering it out: acceptance relative to `k :: seen` and to `seen` agree
once id-`k` observations are removed. -/
theorem dedupAux_k_insensitive (k : ℕ) : ∀ (l : List Obs) (seen : List ℕ),
    ((dedupAux l (k :: seen)).filter (exclP k)).map Obs.id
      = ((dedupAux l seen).filter (exclP k)).map Obs.id := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons o rest ih =>
    intro seen
    by_cases hseen : o.id ∈ seen
    · rw [dedupAux_cons_seen o rest (k :: seen) (by simp [hseen]),
        dedupAux_cons_seen o rest seen hseen, ih seen]
    · by_cases hko : o.id = k
      · rw [dedupAux_cons_seen o rest (k :: seen) (by rw [hko]; simp)]
        rw [dedupAux_cons_fresh o rest seen hseen]
        have hp : exclP k o = false := by simp [exclP, hko]
        simp only [List.filter, hp, if_false]
        rw [hko]
      · rw [dedupAux_cons_fresh o rest (k :: seen) (by simp [hseen, hko]),
          dedupAux_cons_fresh o rest seen hseen]
        have hp : exclP k o = true := by simp [exclP, hko]
        simp only [List.filter, hp, if_true, List.map_cons]
        exact congrArg _ (ih (o.id :: seen))

/-- P04(c): excluding an observation id commutes with deduplication —
no derived quantity over the retained set depends on excluded ids. -/
theorem exclusion_no_linger (k : ℕ) : ∀ (l : List Obs) (seen : List ℕ),
    (dedupAux (l.filter (exclP k)) seen).map Obs.id
      = ((dedupAux l seen).filter (exclP k)).map Obs.id := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons o rest ih =>
    intro seen
    by_cases hko : o.id = k
    · have hp : exclP k o = false := by simp [exclP, hko]
      by_cases hseen : o.id ∈ seen
      · rw [dedupAux_cons_seen o rest seen hseen]
        rw [show (o :: rest).filter (exclP k) = rest.filter (exclP k) from by
          simp only [List.filter, hp, if_false]]
        rw [ih seen]
        rfl
      · rw [dedupAux_cons_fresh o rest seen hseen]
        rw [show (o :: rest).filter (exclP k) = rest.filter (exclP k) from by
          simp only [List.filter, hp, if_false]]
        rw [ih seen]
        simp only [List.filter, hp, if_false]
        rw [hko, dedupAux_k_insensitive k rest seen]
    · have hp : exclP k o = true := by simp [exclP, hko]
      by_cases hseen : o.id ∈ seen
      · rw [dedupAux_cons_seen o rest seen hseen]
        rw [show (o :: rest).filter (exclP k) = o :: rest.filter (exclP k) from by
          simp only [List.filter, hp, if_true]]
        rw [dedupAux_cons_seen o (rest.filter (exclP k)) seen hseen]
        rw [ih seen]
        simp only [List.filter, hp, if_true]
        rfl
      · rw [dedupAux_cons_fresh o rest seen hseen]
        rw [show (o :: rest).filter (exclP k) = o :: rest.filter (exclP k) from by
          simp only [List.filter, hp, if_true]]
        rw [dedupAux_cons_fresh o (rest.filter (exclP k)) seen
          (by simp only [exclP, Bool.decide_eq_true] at hp ⊢; exact ⟨by simp, hp⟩)]
        rw [ih (o.id :: seen)]
        simp only [List.filter, hp, if_true, List.map_cons]
        rfl

/-- Top-level exclusion commutation (empty initial seen set). -/
theorem exclusion_no_linger_top (k : ℕ) (l : List Obs) :
    (dedup (l.filter (exclP k))).map Obs.id
      = ((dedup l).filter (exclP k)).map Obs.id :=
  exclusion_no_linger k l []

end JurisLean.FullMath.Probability
