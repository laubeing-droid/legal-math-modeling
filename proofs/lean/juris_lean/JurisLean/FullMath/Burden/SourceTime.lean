import JurisLean.FullMath.Core.Foundations

/-!
B07 — Legal-source time and semantic coverage: applicability is decided
by publish/effective/repeal times versus the event/handling time, never
by the last fetch time; a slot with no applicable source stays pending
(unknown is not inapplicable); and any change of source version
invalidates cached conclusions — certificates never cross versions.
-/

namespace JurisLean.FullMath.Burden

/-- A frozen legal-source version with its time line. -/
structure SourceVersion where
  published : ℕ
  effective : ℕ
  repealed : Option ℕ

def appliesAt (v : SourceVersion) (t : ℕ) : Bool :=
  if v.effective ≤ t then
    match v.repealed with
    | none => true
    | some r => decide (t < r)
  else false

/-- B07(a): applicability needs the effective time — an event before the
effective date is not covered, regardless of when we fetched. -/
theorem not_yet_effective (v : SourceVersion) (t : ℕ)
    (h : t < v.effective) : appliesAt v t = false := by
  simp only [appliesAt]
  rw [if_neg (by omega : ¬ (v.effective ≤ t))]

theorem repealed_not_applicable (v : SourceVersion) (r t : ℕ)
    (hrep : v.repealed = some r) (hr : r ≤ t) : appliesAt v t = false := by
  simp only [appliesAt, hrep]
  by_cases heff : v.effective ≤ t
  · rw [if_pos heff, decide_eq_false (by omega)]
  · rw [if_neg heff]

theorem effective_window_applicable (v : SourceVersion) (t : ℕ)
    (h1 : v.effective ≤ t) (h2 : ∀ r, v.repealed = some r → t < r) :
    appliesAt v t = true := by
  by_cases heff : v.effective ≤ t
  · show (if v.effective ≤ t then
        match v.repealed with
        | none => true
        | some r => decide (t < r)
      else false) = true
    rw [if_pos heff]
    cases hrep : v.repealed with
    | none => rfl
    | some r => rw [decide_eq_true (h2 r hrep)]
  · simp only [appliesAt, if_neg heff]

/-- B07(b): unknown is not inapplicable — with no applicable source and no
explicit exclusion ground the slot stays pending. -/
inductive SlotStatus where
  | applies (src : SourceVersion)
  | notApplicable (ground : String)
  | pending

def applicableSources (sources : List SourceVersion) (t : ℕ) :
    List SourceVersion := sources.filter (fun v => appliesAt v t)

def decideSlot (sources : List SourceVersion) (t : ℕ) (exclusions : List String)
    (s : String) : SlotStatus :=
  match applicableSources sources t with
  | [] => if s ∈ exclusions then .notApplicable "excluded" else .pending
  | v :: _ => .applies v

theorem unknown_is_pending (sources : List SourceVersion) (t : ℕ)
    (exclusions : List String) (s : String)
    (hnone : applicableSources sources t = []) (hnot : ¬ (s ∈ exclusions)) :
    decideSlot sources t exclusions s = SlotStatus.pending := by
  simp only [decideSlot, hnone]
  rw [if_neg hnot]

theorem pending_not_inapplicable (sources : List SourceVersion) (t : ℕ)
    (exclusions : List String) (s : String) (g : String)
    (h : decideSlot sources t exclusions s = SlotStatus.pending) :
    ¬ (decideSlot sources t exclusions s = SlotStatus.notApplicable g) := by
  rw [h]
  intro hc
  cases hc

/-- B07(c): cached conclusions are keyed by the full version triple; any
version change misses the cache — certificates never cross versions. -/
def cacheKey (v : SourceVersion) : ℕ × ℕ × Option ℕ :=
  (v.published, v.effective, v.repealed)

def cacheHit (v v' : SourceVersion) : Bool := decide (cacheKey v = cacheKey v')

theorem version_change_invalidates (v v' : SourceVersion)
    (h : cacheKey v ≠ cacheKey v') : cacheHit v v' = false := by
  simp only [cacheHit]
  rw [decide_eq_false h]

theorem cache_hit_only_same_version (v v' : SourceVersion)
    (h : cacheHit v v' = true) : v.published = v'.published
      ∧ v.effective = v'.effective ∧ v.repealed = v'.repealed := by
  have hkey : cacheKey v = cacheKey v' := of_decide_eq_true h
  refine ⟨?_, ?_, ?_⟩ <;> simp_all [cacheKey]

end JurisLean.FullMath.Burden
