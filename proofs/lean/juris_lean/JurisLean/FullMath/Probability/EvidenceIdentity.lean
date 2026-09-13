import JurisLean.FullMath.Core.Foundations

/-!
P04 — Observation identity: keyed acceptance is idempotent per id (a
duplicate resubmission never double-counts; a later conflicting value
leaves the accepted id set unchanged), and excluding observations by id
commutes with deduplication, so derived aggregates over the retained set
never depend on excluded ones.
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

/-- The accepted multiset of observations (dedup by id, first wins). -/
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
    dedupAux_cons_seen o l [o.id] (by simp)]

/-- P04(b): a later conflicting value under the same id changes nothing
about the accepted set — the id was already bound by first acceptance. -/
theorem dedup_conflict_not_overwrite (o o' : Obs) (h : o'.id = o.id)
    (l : List Obs) :
    (dedup (o' :: o :: l)).map Obs.id = (dedup (o :: l)).map Obs.id := by
  simp only [dedup]
  rw [dedupAux_cons_fresh o l [] (by simp),
    dedupAux_cons_seen o' l [o.id] (by rw [h]; simp)]

/-- Exclusion by id commutes with deduplication (general seen-set form). -/
theorem dedupAux_filter_comm (l : List Obs) (seen : List ℕ) (k : ℕ) :
    (dedupAux (l.filter (fun o' => decide (o'.id != k))) seen).map Obs.id
      = ((dedupAux l seen).filter (fun o' => decide (o'.id != k))).map Obs.id := by
  induction l generalizing seen with
  | nil => rfl
  | cons o rest ih =>
    by_cases hko : o.id = k
    · have hp : (fun o' => decide (o'.id != k)) o = false := by
        simp [hko]
      by_cases hseen : o.id ∈ seen
      · rw [dedupAux_cons_seen o rest seen hseen]
        rw [show (o :: rest).filter (fun o' => decide (o'.id != k))
            = rest.filter (fun o' => decide (o'.id != k)) from by
          simp only [List.filter, hp, if_false]]
        rw [ih seen]
        rfl
      · rw [dedupAux_cons_fresh o rest seen hseen]
        rw [show (o :: rest).filter (fun o' => decide (o'.id != k))
            = rest.filter (fun o' => decide (o'.id != k)) from by
          simp only [List.filter, hp, if_false]]
        rw [ih (o.id :: seen)]
        simp only [List.filter, hp, if_false]
        rfl
    · have hp : (fun o' => decide (o'.id != k)) o = true := by
        simp [hko]
      by_cases hseen : o.id ∈ seen
      · rw [dedupAux_cons_seen o rest seen hseen]
        rw [show (o :: rest).filter (fun o' => decide (o'.id != k))
            = o :: rest.filter (fun o' => decide (o'.id != k)) from by
          simp only [List.filter, hp, if_true]]
        rw [dedupAux_cons_seen o (rest.filter (fun o' => decide (o'.id != k))) seen hseen]
        rw [ih seen]
        simp only [List.filter, hp, if_true]
        rfl
      · rw [dedupAux_cons_fresh o rest seen hseen]
        rw [show (o :: rest).filter (fun o' => decide (o'.id != k))
            = o :: rest.filter (fun o' => decide (o'.id != k)) from by
          simp only [List.filter, hp, if_true]]
        rw [dedupAux_cons_fresh o (rest.filter (fun o' => decide (o'.id != k))) seen
          (by simp only [List.mem_filter]; exact ⟨by simp, by simp [hko]⟩)]
        rw [ih (o.id :: seen)]
        simp only [List.filter, hp, if_true, List.map_cons]
        rfl

/-- P04(c): excluding an observation id commutes with deduplication —
no derived quantity over the retained set depends on excluded ids. -/
theorem exclusion_no_linger (k : ℕ) (l : List Obs) :
    (dedup (l.filter (fun o' => decide (o'.id != k)))).map Obs.id
      = ((dedup l).filter (fun o' => decide (o'.id != k))).map Obs.id :=
  dedupAux_filter_comm l [] k

end JurisLean.FullMath.Probability
