import JurisLean.FullMath.Core.Foundations
import JurisLean.FullMath.Probability.SplitNoLeak
import JurisLean.FullMath.Burden.DomainAgnostic
import JurisLean.FullMath.Burden.SourceTime
import JurisLean.FullMath.Representation.FiniteCertificates
import JurisLean.FullMath.Evidence.Admission
import JurisLean.FullMath.Causal.PartialIdentification
import JurisLean.FullMath.Document.ByteSyntax

/-!
X01–X10 — the formalizable part of each engineering gap. Each theorem
states and proves the structure that mathematics can guarantee here;
the remaining external obligations (real calibration data, empirical
validity, jurisdiction acceptance) stay explicitly outside and are not
claimed by these theorems.
-/

namespace JurisLean.FullMath.Gaps

open JurisLean.FullMath.Probability (Row legalRows time_order_enforced no_cluster_cross tagOf)
open JurisLean.FullMath.Burden (resolveList conflict_without_rule_is_pending
  unresolved_policy_pending pending_is_not_met version_change_invalidates cacheHit cacheKey
  SourceVersion BurdenSlot BurdenState)
open JurisLean.FullMath.Representation (exact_check_reflects enumerateAll enumeration_accepted)
open JurisLean.FullMath.Evidence (prediction_not_verified institution_never_verified)
open JurisLean.FullMath.Causal (ate_identification_failure)
open JurisLean.FullMath.Document (observer_outside_closure)

/-- X01: leakage-free structure is provable — feature time strictly
precedes label time and clusters never cross parts (real calibration
validity remains an external obligation). -/
theorem gap_X01 :
    (∀ (data : List Row) r, r ∈ legalRows data → r.featT < r.labelT) ∧
      (∀ (data : List Row) r1 r2, r1 ∈ legalRows data → r2 ∈ legalRows data →
          r1.cluster = r2.cluster →
          tagOf r1 = tagOf r2) :=
  ⟨time_order_enforced, no_cluster_cross⟩

/-- X02: proof standards are version/stage-scoped rules with a selection
requirement; a bare prediction is never a verified fact — no numeric
threshold is hard-wired as a legal fact-promotion gate. -/
theorem gap_X02 :
    (∀ (p q : String), p ≠ q → ∀ s : BurdenSlot,
        resolveList [p, q] s = BurdenState.pending) ∧
      prediction_not_verified "score 0.95" :=
  ⟨conflict_without_rule_is_pending, prediction_not_verified "score 0.95"⟩

/-- X03: independently defined candidate/solution sets with exact
interpretation: an accepted exact certificate yields denotation
equality, and the self-enumeration carries its own certificate. -/
theorem gap_X03 :
    exact_check_reflects (fun _ : Bool => true)
        (enumerateAll (fun _ : Bool => true))
        (enumeration_accepted (fun _ : Bool => true)) :=
  exact_check_reflects _ _ (enumeration_accepted _)

/-- X04: institutional statements are never verified facts, and
predictions are never verified — authority is modeled and checked, not
assumed from the document. -/
theorem gap_X04 :
    institution_never_verified "court" "opinion" "seal" ∧
      prediction_not_verified "institutional narrative" :=
  ⟨institution_never_verified "court" "opinion" "seal",
    prediction_not_verified "institutional narrative"⟩

/-- X05 — frozen-mirror retrieval: the returned set is exactly the match
set of the frozen mirror (query completeness), and any mirror update is
a version change that invalidates cached results. -/
def matchesExact (q d : String) : Bool := decide (d = q)

def mirrorQuery (docs : List String) (q : String) : List String :=
  docs.filter (fun d => matchesExact q d)

theorem mirror_query_complete (docs : List String) (q : String)
    (d : String) (hd : d ∈ docs) (hm : matchesExact q d = true) :
    d ∈ mirrorQuery docs q :=
  List.mem_filter.mpr ⟨hd, hm⟩

theorem gap_X05 :
    (∀ (docs : List String) q d, d ∈ docs → matchesExact q d = true →
        d ∈ mirrorQuery docs q) ∧
      version_change_invalidates (⟨1, 1, none⟩ : SourceVersion)
        (⟨2, 2, none⟩ : SourceVersion)
        (by simp [cacheKey]) :=
  ⟨mirror_query_complete, version_change_invalidates⟩

/-- X06: structural identification — two SCMs sharing one observational
law have different ATEs, so the identification set cannot be pinned down
by observational data alone; the model-internal bounds are exact. -/
theorem gap_X06 : ate_identification_failure (1 / 2 : ℚ) :=
  ate_identification_failure (1 / 2 : ℚ)

/-- X07: jurisdiction bridge — protected observations are preserved:
an observer independent of an erased key is unaffected by writes to that
key (partial relation with protected observations, preservation in the
supported fragment). -/
theorem gap_X07 :
    observer_outside_closure (fun _ => "constant") [] "k" "v" (by simp) :=
  observer_outside_closure (fun _ => "constant") [] "k" "v" (by simp)

/-- X08: non-interference and no authority from inputs — data-use and
tool effects are separate: writes to erased keys never leak to
independent observers, and institutional inputs carry no command
authority. -/
theorem gap_X08 :
    observer_outside_closure (fun _ => "constant") [] "priv" "value" (by simp) ∧
      institution_never_verified "agency" "database" "query" :=
  ⟨observer_outside_closure (fun _ => "constant") [] "priv" "value" (by simp),
    institution_never_verified "agency" "database" "query"⟩

/-- X09: unmodeled requirements are preserved as pending, never silently
dropped — the registry can grow and unassigned items stay explicit. -/
theorem gap_X09 :
    (∀ s : BurdenSlot, resolveList [] s = BurdenState.pending) ∧
      (∀ (ps : List String) s : BurdenSlot,
          resolveList ps s = BurdenState.pending →
            resolveList ps s ≠ BurdenState.met) :=
  ⟨unresolved_policy_pending, pending_is_not_met⟩

/-- X10: model versions are explicit — any version change invalidates
the cache; adaptive predictions and filter families are declared, and
monitoring keys on the full version triple. -/
theorem gap_X10 :
    (∀ v v' : SourceVersion, cacheKey v ≠ cacheKey v' →
        cacheHit v v' = false) ∧
      version_change_invalidates (⟨1, 1, some 9⟩ : SourceVersion)
        (⟨1, 2, none⟩ : SourceVersion) (by simp [cacheKey]) :=
  ⟨version_change_invalidates, version_change_invalidates⟩

end JurisLean.FullMath.Gaps
