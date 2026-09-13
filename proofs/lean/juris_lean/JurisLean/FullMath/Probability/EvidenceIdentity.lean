import JurisLean.FullMath.Core.Foundations

/-!
P04 — Observation identity: keyed updates are idempotent per observation
id (a duplicate submission never double-updates, a conflicting value never
overwrites), and exclusion of an observation commutes with deduplication,
so no derived quantity computed from the remaining set depends on the
excluded one.
-/

namespace JurisLean.FullMath.Probability

/-- An observation with an explicit identity. -/
structure Obs where
  id : ℕ
  value : ℚ

/-- First-wins deduplication by observation id. -/
def dedup : List Obs → List Obs
  | [] => []
  | o :: rest => o :: dedup (rest.filter (fun o' => decide (o'.id != o.id)))
termination_by l => l.length
decreasing_by
  simp_wf
  have hle := List.length_filter_le (fun o' => decide (o'.id != o.id)) rest
  omega

/-- The aggregate over deduplicated observations. -/
def obsTotal (l : List Obs) : ℚ := (dedup l).map Obs.value |>.sum

/-- P04(a): resubmitting the same observation does not update twice. -/
theorem dedup_no_double_update (o : Obs) (l : List Obs) :
    obsTotal (o :: o :: l) = obsTotal (o :: l) := by
  simp only [obsTotal, dedup]
  have hfil : (o :: l).filter (fun o' => decide (o'.id != o.id))
      = l.filter (fun o' => decide (o'.id != o.id)) := by
    have hb : decide (o.id != o.id) = false := by simp
    simp [List.filter, hb]
  rw [hfil]

/-- P04(b): a conflicting value under the same id does not overwrite the
first accepted value (idempotent keyed update). -/
theorem dedup_conflict_not_overwrite (o1 o2 : Obs) (h : o1.id = o2.id)
    (l : List Obs) : obsTotal (o1 :: o2 :: l) = obsTotal (o2 :: l) := by
  simp only [obsTotal, dedup]
  have hfil : (o2 :: l).filter (fun o' => decide (o'.id != o1.id))
      = l.filter (fun o' => decide (o'.id != o1.id)) := by
    have hb : decide (o2.id != o1.id) = false := by simp [h]
    simp [List.filter, hb]
  rw [hfil]

/-- P04(c): exclusion of observations by an id-determined predicate
commutes with deduplication — aggregates over the retained set never
depend on excluded observations. -/
theorem exclusion_no_linger (p : Obs → Bool) (l : List Obs)
    (hp : ∀ o1 o2 : Obs, o1.id = o2.id → p o1 = p o2) :
    dedup (l.filter p) = (dedup l).filter p := by
  induction l with
  | nil => rfl
  | cons o rest ih =>
    by_cases hpo : p o = true
    · have hf1 : (o :: rest).filter p = o :: rest.filter p := by
        simp [List.filter, hpo]
      simp only [dedup, hf1, List.filter]
      rw [hpo, if_pos rfl]
      have hcomm : (rest.filter p).filter (fun o' => decide (o'.id != o.id))
          = (rest.filter (fun o' => decide (o'.id != o.id))).filter p := by
        rw [List.filter_filter, List.filter_filter]
        congr 1
        funext x
        simp [and_comm]
      rw [hcomm, ih]
      rfl
    · have hf2 : (dedup (o :: rest)).filter p
          = (dedup rest.filter (fun o' => decide (o'.id != o.id))).filter p := by
        simp only [dedup, List.filter, hpo]
      rw [hf2, ← ih]
      have hq : (rest.filter p).filter (fun o' => decide (o'.id != o.id))
          = rest.filter p := by
        refine List.filter_eq_self.mpr (fun x hx => ?_)
        by_cases hxi : x.id = o.id
        · have hpx : p x = p o := hp x o hxi
          rw [hpx, hpo] at hx
          simp at hx
        · simp [hxi]
      rw [hq]

end JurisLean.FullMath.Probability
