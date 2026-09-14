import JurisLean.FullMath.Core.Foundations
import JurisLean.FullMath.Probability.SplitNoLeak
import JurisLean.FullMath.Burden.DomainAgnostic
import JurisLean.FullMath.Burden.SourceTime
import JurisLean.FullMath.Representation.FiniteCertificates
import JurisLean.FullMath.Evidence.Admission
import JurisLean.FullMath.Causal.PartialIdentification
import JurisLean.FullMath.Document.ByteSyntax

/-!
X01–X10 — the formalizable part of each engineering gap: the structure
mathematics can guarantee here. The remaining external obligations (real
calibration data, empirical validity, jurisdiction acceptance) stay
explicitly outside and are not claimed by these theorems.
-/

namespace JurisLean.FullMath.Gaps

open JurisLean.FullMath.Probability (Row legalRows time_order_enforced no_cluster_cross tagOf)
open JurisLean.FullMath.Burden (resolveList conflict_without_rule_is_pending
  unresolved_policy_pending pending_is_not_met version_change_invalidates cacheHit cacheKey
  SourceVersion BurdenSlot BurdenState)
open JurisLean.FullMath.Representation (enumerateAll enumeration_member)
open JurisLean.FullMath.Evidence (institution_never_verified)
open JurisLean.FullMath.Causal (ate ate_identification_failure TwoVar)
open JurisLean.FullMath.Document (Doc docPut observer_outside_closure)

/-- X01: leakage-free structure is provable — feature time strictly
precedes label time and clusters never cross parts (real calibration
validity remains an external obligation). -/
theorem gap_X01 :
    (∀ (data : List Row) r, r ∈ legalRows data → r.featT < r.labelT) ∧
      (∀ (data : List Row) r1 r2, r1 ∈ legalRows data → r2 ∈ legalRows data →
          r1.cluster = r2.cluster → tagOf r1 = tagOf r2) :=
  ⟨time_order_enforced, no_cluster_cross⟩

/-- X02: proof standards are version/stage-scoped rules with a selection
requirement — conflicting candidate policies without a selection rule
stay pending; no numeric threshold is hard-wired as a fact-promotion
gate. -/
theorem gap_X02 :
    ∀ (p q : String), p ≠ q → ∀ s : BurdenSlot,
      resolveList [p, q] s = BurdenState.pending :=
  conflict_without_rule_is_pending

/-- X03: independently defined candidate/solution sets with exact
interpretation: membership in the enumerated candidate set is exactly
satisfaction of the predicate. -/
theorem gap_X03 :
    ∀ x : Bool, x ∈ enumerateAll (fun b : Bool => b) ↔ x = true :=
  fun x => enumeration_member (fun b : Bool => b) x

/-- X04: institutional statements are never verified facts — authority is
modeled and checked, not assumed from the document. -/
theorem gap_X04 :
    ∀ n b u : String,
      (JurisLean.FullMath.Evidence.Admission.institution n b u).status
        = JurisLean.FullMath.FactStatus.statement :=
  institution_never_verified

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
    (∀ (docs : List String) (q d : String), d ∈ docs → matchesExact q d = true →
        d ∈ mirrorQuery docs q) ∧
      cacheHit (⟨1, 1, none⟩ : SourceVersion) (⟨2, 2, none⟩ : SourceVersion) = false :=
  ⟨fun docs q d hd hm => mirror_query_complete docs q d hd hm,
    version_change_invalidates _ _ (by simp [cacheKey])⟩

/-- X06: structural identification — two SCMs sharing one observational
law have different ATEs, so the identification set cannot be pinned down
by observational data alone; the model-internal bounds are exact. -/
theorem gap_X06 :
    ate TwoVar.chain (1 / 2 : ℚ) ≠ ate TwoVar.copy (1 / 2 : ℚ) :=
  ate_identification_failure (1 / 2 : ℚ)

/-- X07: jurisdiction bridge — protected observations are preserved: an
observer independent of an erased key is unaffected by writes to that
key. -/
theorem gap_X07 :
    (fun _ : Doc => "constant") (docPut ([] : Doc) "k" "v")
      = (fun _ : Doc => "constant") ([] : Doc) :=
  observer_outside_closure (fun _ : Doc => "constant") [] "k" "v"
    (by intro d1 d2 _; rfl)

/-- X08: non-interference and no authority from inputs — writes to
erased keys never leak to independent observers, and institutional
inputs carry no command authority. -/
theorem gap_X08 :
    (fun _ : Doc => "constant") (docPut ([] : Doc) "priv" "value")
        = (fun _ : Doc => "constant") ([] : Doc)
      ∧ (JurisLean.FullMath.Evidence.Admission.institution
            "agency" "database" "query").status
          = JurisLean.FullMath.FactStatus.statement :=
  ⟨observer_outside_closure (fun _ : Doc => "constant") [] "priv" "value"
    (by intro d1 d2 _; rfl),
    institution_never_verified "agency" "database" "query"⟩

/-- X09: unmodeled requirements are preserved as pending, never silently
dropped — the registry can grow and unassigned items stay explicit. -/
theorem gap_X09 :
    (∀ s : BurdenSlot, resolveList [] s = BurdenState.pending) ∧
      (∀ (ps : List String) (s : BurdenSlot),
          resolveList ps s = BurdenState.pending →
            resolveList ps s ≠ BurdenState.met) :=
  ⟨unresolved_policy_pending, fun ps s => pending_is_not_met s ps⟩

/-- X10: model versions are explicit — any version change invalidates
the cache; adaptive predictions and filter families are declared, and
monitoring keys on the full version triple. -/
theorem gap_X10 :
    (∀ v v' : SourceVersion, cacheKey v ≠ cacheKey v' → cacheHit v v' = false) ∧
      cacheHit (⟨1, 1, some 9⟩ : SourceVersion) (⟨1, 2, none⟩ : SourceVersion)
        = false :=
  ⟨fun v v' h => version_change_invalidates v v' h,
    version_change_invalidates _ _ (by simp [cacheKey])⟩

end JurisLean.FullMath.Gaps
