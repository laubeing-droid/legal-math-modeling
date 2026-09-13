import JurisLean.FullMath.Core.Foundations

/-!
P04 — Observation identity: keyed acceptance is idempotent per id (a
duplicate resubmission never double-counts; a later conflicting value
leaves the accepted id set unchanged), and excluding observations by id
commutes with deduplication — derived aggregates over the retained set
never depend on excluded ids. The seen-set is a Boolean predicate, so
acceptance is order-free by construction.
-/

namespace JurisLean.FullMath.Probability

/-- An observation with an explicit identity. -/
structure Obs where
  id : ℕ
  value : ℚ

/-- First-accepted deduplication with a Boolean seen-id predicate. -/
def dedupAux : List Obs → (ℕ → Bool) → List Obs
  | [], _ => []
  | o :: rest, seen =>
      if seen o.id = true then dedupAux rest seen
      else o :: dedupAux rest (fun x => decide (x = o.id) || seen x)

/-- The accepted observations of a submission list (dedup by id). -/
def dedup (l : List Obs) : List Obs := dedupAux l (fun _ => false)

/-- The aggregate over deduplicated observations. -/
def obsTotal (l : List Obs) : ℚ := (dedup l).map Obs.value |>.sum

theorem dedupAux_cons_seen (o : Obs) (rest : List Obs) (seen : ℕ → Bool)
    (h : seen o.id = true) : dedupAux (o :: rest) seen = dedupAux rest seen := by
  simp only [dedupAux, if_pos h]

theorem dedupAux_cons_fresh (o : Obs) (rest : List Obs) (seen : ℕ → Bool)
    (h : ¬ (seen o.id = true)) :
    dedupAux (o :: rest) seen
      = o :: dedupAux rest (fun x => decide (x = o.id) || seen x) := by
  simp only [dedupAux, if_neg h]

/-- P04(a): resubmitting the same observation does not update twice. -/
theorem dedup_no_double_update (o : Obs) (l : List Obs) :
    obsTotal (o :: o :: l) = obsTotal (o :: l) := by
  simp only [obsTotal, dedup]
  rw [dedupAux_cons_fresh o (o :: l) _ (by simp),
    dedupAux_cons_seen o l _ (by simp),
    dedupAux_cons_fresh o l _ (by simp)]
  rfl

/-- P04(b): a later conflicting value under the same id changes nothing
about the accepted set — the id was already bound by first acceptance. -/
theorem dedup_conflict_not_overwrite (k : ℕ) (v v' : ℚ) (l : List Obs) :
    (dedup (⟨k, v'⟩ :: ⟨k, v⟩ :: l)).map Obs.id = (dedup (⟨k, v⟩ :: l)).map Obs.id := by
  simp only [dedup]
  rw [dedupAux_cons_fresh ⟨k, v'⟩ (⟨k, v⟩ :: l) _ (by simp),
    dedupAux_cons_seen ⟨k, v⟩ l _ (by simp),
    dedupAux_cons_fresh ⟨k, v⟩ l _ (by simp)]
  rfl

/-- Exclusion predicate on observation ids. -/
private def exclP (k : ℕ) (o : Obs) : Bool := decide (o.id != k)

/-- Seen-set with id `k` pre-seeded. -/
private def exclSeen (k : ℕ) (seen : ℕ → Bool) : ℕ → Bool :=
  fun x => decide (x = k) || seen x

theorem upd_eq_exclSeen (k : ℕ) (seen : ℕ → Bool) (hko : o.id = k) :
    (fun x => decide (x = o.id) || seen x) = exclSeen k seen := by
  funext x
  simp [exclSeen, hko]

/-- Pre-seeding the exclusion id in the seen set is invisible after
filtering: acceptance relative to the seeded and unseeded sets agrees
once id-`k` observations are removed. -/
theorem dedupAux_k_insensitive (k : ℕ) : ∀ (l : List Obs) (seen : ℕ → Bool),
    ((dedupAux l (exclSeen k seen)).filter (exclP k)).map Obs.id
      = ((dedupAux l seen).filter (exclP k)).map Obs.id := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons o rest ih =>
    intro seen
    by_cases hseen : seen o.id = true
    · rw [dedupAux_cons_seen o rest seen hseen,
        dedupAux_cons_seen o rest (exclSeen k seen) (by simp [exclSeen, hseen]),
        ih seen]
    · by_cases hko : o.id = k
      · rw [dedupAux_cons_seen o rest (exclSeen k seen) (by simp [exclSeen, hko])]
        rw [dedupAux_cons_fresh o rest seen hseen]
        have hp : exclP k o = false := by simp [exclP, hko]
        simp only [List.filter, hp, if_false]
        rw [upd_eq_exclSeen k seen hko]
      · rw [dedupAux_cons_fresh o rest (exclSeen k seen) (by simp [exclSeen, hseen, hko]),
          dedupAux_cons_fresh o rest seen hseen]
        have hp : exclP k o = true := by simp [exclP, hko]
        simp only [List.filter, hp, if_true, List.map_cons]
        refine congrArg (List.cons o.id) ?_
        have hupd : (fun x => decide (x = o.id) || exclSeen k seen x)
            = exclSeen k (fun x => decide (x = o.id) || seen x) := by
          funext x
          simp only [exclSeen]
          cases h1 : decide (x = o.id) <;>
            cases h2 : decide (x = k) <;> simp [h1, h2]
        rw [hupd]
        exact ih (fun x => decide (x = o.id) || seen x)

/-- P04(c): excluding an observation id commutes with deduplication —
no derived quantity over the retained set depends on excluded ids. -/
theorem exclusion_no_langer (k : ℕ) : ∀ (l : List Obs) (seen : ℕ → Bool),
    (dedupAux (l.filter (exclP k)) seen).map Obs.id
      = ((dedupAux l seen).filter (exclP k)).map Obs.id := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons o rest ih =>
    intro seen
    by_cases hko : o.id = k
    · have hp : exclP k o = false := by simp [exclP, hko]
      by_cases hseen : seen o.id = true
      · rw [show (o :: rest).filter (exclP k) = rest.filter (exclP k) from by
          simp only [List.filter, hp, if_false]]
        rw [dedupAux_cons_seen o rest seen hseen, ih seen]
        rfl
      · rw [show (o :: rest).filter (exclP k) = rest.filter (exclP k) from by
          simp only [List.filter, hp, if_false]]
        rw [dedupAux_cons_fresh o rest seen hseen]
        simp only [List.filter, hp, if_false]
        rw [upd_eq_exclSeen k seen hko, dedupAux_k_insensitive k rest seen,
          ih seen]
    · have hp : exclP k o = true := by simp [exclP, hko]
      by_cases hseen : seen o.id = true
      · rw [show (o :: rest).filter (exclP k) = o :: rest.filter (exclP k) from by
          simp only [List.filter, hp, if_true]]
        rw [dedupAux_cons_seen o rest seen hseen,
          dedupAux_cons_seen o (rest.filter (exclP k)) seen hseen, ih seen]
        simp only [List.filter, hp, if_true]
        rfl
      · rw [show (o :: rest).filter (exclP k) = o :: rest.filter (exclP k) from by
          simp only [List.filter, hp, if_true]]
        rw [dedupAux_cons_fresh o rest seen hseen,
          dedupAux_cons_fresh o (rest.filter (exclP k)) seen
            (by simp [exclP, hko])]
        rw [ih (fun x => decide (x = o.id) || seen x)]
        simp only [List.filter, hp, if_true, List.map_cons]
        rfl

/-- Top-level exclusion commutation (empty initial seen set). -/
theorem exclusion_no_langer_top (k : ℕ) (l : List Obs) :
    (dedup (l.filter (exclP k))).map Obs.id
      = ((dedup l).filter (exclP k)).map Obs.id :=
  exclusion_no_langer k l (fun _ => false)

end JurisLean.FullMath.Probability
