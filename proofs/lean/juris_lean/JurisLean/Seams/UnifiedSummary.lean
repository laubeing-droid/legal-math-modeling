import Mathlib.Tactic
import JurisLean.Seams.UnifiedGuards

/-
Unified summary saturation, the Lean reflection of the Python section-4
summary layer (main doc 8.2 leftover: summary-saturation reflection).

Python contract of record: `tools/unified_math_v2/unified/argument_grammar.py`
- `last_of` (leaf empty / defeasible root {j} / strict root union),
- `_own_site` + `summarize` (sites = own + children; ordinary leaves are
  attackable positions, axiom/exempt leaves are not),
- `_delta` (summary transfer),
- `saturate_summaries` (least fixed point from leaf productions with one
  generating witness per summary).

Reflection design, honestly scoped:
1. Mutual `STree`/`SForest` trees; `Summ` the finite observable (the Python
   `tags` field is constant-empty in this fragment and is omitted, noted).
2. Well-formedness is the function: `summarize` returns none exactly where
   Python constructor validation rejects (child conclusions must match
   premise order). Determinism of the observable is definitional.
3. `deltaS` mirrors `_delta` field by field; the own site carries the
   rule's guard slots.
4. Height-indexed `SaturatedN` (children live at level n, the composed
   summary at n+1); `saturatedN_witness` is saturation soundness (every
   saturated summary has a realizing tree); `saturatedN_into_closed` says
   Saturated is the LEAST delta-closed set containing the leaf seeds.
   Finite-domain termination is carried by the height index, not re-proved.

STATUS: proved theorems pending their CI compile round; this file contains
no sorry, no admit, no custom axiom, no `: True :=`, no native_decide.
-/

namespace JurisLean.Seams.UnifiedSummary

open JurisLean.Seams.UnifiedGuards (GuardSlot)

/-! ## Carriers -/

/-- Argument mode (Python `ArgMode`). -/
inductive SMode where
  | strictS | defeasible

/-- Site summaries: ordinary-leaf sites (empty last, no instance, no
guards) and rule-node sites (mode/instance/last/guard slots). -/
inductive SiteSum (A : Type) where
  | leafS (conc : A)
  | ruleS (conc : A) (m : SMode) (inst : A) (lastI : List A)
      (guards : List (GuardSlot A))

/-- The finite observable (Python `Summary`; `tags` is constant empty
in this fragment and is deliberately omitted). -/
structure Summ (A : Type) where
  conc : A
  mode : SMode
  rootRule : Option A
  lastI : List A
  leafSrcs : List A
  sites : List (SiteSum A)

/-- Grammar rule (Python `GrammarRule`); guard slots reuse the
UnifiedGuards carrier. -/
structure SRule (A : Type) where
  rid : A
  premises : List A
  head : A
  mode : SMode
  guards : List (GuardSlot A)

mutual
inductive STree (A : Type) where
  | sLeaf (ordinary : Bool) (atom src : A)
  | sNode (r : SRule A) (fs : SForest A)
inductive SForest (A : Type) where
  | fNil
  | fCons (t : STree A) (fs : SForest A)
end

/-- Head conclusion of a tree (reads the root only). -/
def headT {A : Type} : STree A → A
  | .sLeaf _ a _ => a
  | .sNode r _ => r.head

/-! ## Transfer delta and leaf seeds -/

/-- Last policy, rule side: defeasible root takes {rid}, strict root
takes the union of child lasts. -/
def lastOfRule {A : Type} (r : SRule A) (qs : List (Summ A)) : List A :=
  match r.mode with
  | .defeasible => [r.rid]
  | .strictS => qs.flatMap Summ.lastI

/-- The node's own site (carries the rule's guard slots). -/
def ownSiteOf {A : Type} (r : SRule A) (qs : List (Summ A)) : SiteSum A :=
  .ruleS r.head r.mode r.rid (lastOfRule r qs) r.guards

/-- Summary transfer delta_r(q1..qk), field by field as in Python. -/
def deltaS {A : Type} (r : SRule A) (qs : List (Summ A)) : Summ A where
  conc := r.head
  mode := r.mode
  rootRule := some r.rid
  lastI := lastOfRule r qs
  leafSrcs := qs.flatMap Summ.leafSrcs
  sites := ownSiteOf r qs :: qs.flatMap Summ.sites

/-- Seed summary of an ordinary leaf. -/
def leafOrdSum {A : Type} (a src : A) : Summ A where
  conc := a
  mode := .strictS
  rootRule := none
  lastI := []
  leafSrcs := [src]
  sites := [.leafS a]

/-- Seed summary of an axiom/exempt leaf: not an attackable position. -/
def leafExemptSum {A : Type} (a src : A) : Summ A where
  conc := a
  mode := .strictS
  rootRule := none
  lastI := []
  leafSrcs := [src]
  sites := []

/-! ## summarize: well-formedness embedded in the function -/

mutual
def summarize {A : Type} [DecidableEq A] : STree A → Option (Summ A)
  | .sLeaf true a src => some (leafOrdSum a src)
  | .sLeaf false a src => some (leafExemptSum a src)
  | .sNode r fs =>
      match summs fs with
      | none => none
      | some qs =>
          if qs.map Summ.conc = r.premises then some (deltaS r qs) else none
def summs {A : Type} [DecidableEq A] : SForest A → Option (List (Summ A))
  | .fNil => some []
  | .fCons t fs =>
      match summarize t, summs fs with
      | some q, some qs => some (q :: qs)
      | _, _ => none
end

theorem summarize_leafOrd {A : Type} [DecidableEq A] (a src : A) :
    summarize (.sLeaf true a src) = some (leafOrdSum a src) := by
  simp [summarize]

theorem summarize_leafExempt {A : Type} [DecidableEq A] (a src : A) :
    summarize (.sLeaf false a src) = some (leafExemptSum a src) := by
  simp [summarize]

theorem summs_nil {A : Type} [DecidableEq A] :
    summs (.fNil : SForest A) = some [] := by
  simp [summs]

/-- Constructor lemma for node summaries. -/
theorem summarize_node_of {A : Type} [DecidableEq A] {r : SRule A}
    {fs : SForest A} {qs : List (Summ A)} (h1 : summs fs = some qs)
    (hp : qs.map Summ.conc = r.premises) :
    summarize (.sNode r fs) = some (deltaS r qs) := by
  simp only [summarize, h1, if_pos hp]

/-- Constructor lemma for forest summaries. -/
theorem summs_cons_of {A : Type} [DecidableEq A] {t : STree A} {fs : SForest A}
    {q : Summ A} {qs : List (Summ A)} (h1 : summarize t = some q)
    (h2 : summs fs = some qs) :
    summs (.fCons t fs) = some (q :: qs) := by
  simp only [summs, h1, h2]

/-- Forest summary, elementwise characterization. -/
theorem summs_cons_iff {A : Type} [DecidableEq A] (t : STree A) (fs : SForest A)
    (qs : List (Summ A)) :
    summs (.fCons t fs) = some qs ↔
      ∃ q qs', summarize t = some q ∧ summs fs = some qs' ∧ qs = q :: qs' := by
  constructor
  · intro h
    simp only [summs] at h
    have key : ∀ v1 : Option (Summ A), ∀ v2 : Option (List (Summ A)),
        (match v1, v2 with
         | some q, some qs => some (q :: qs)
         | _, _ => none) = some qs →
        ∃ q qs', v1 = some q ∧ v2 = some qs' ∧ qs = q :: qs' := by
      intro v1 v2 hm
      cases v1 with
      | none => simp at hm
      | some q =>
        cases v2 with
        | none => simp at hm
        | some qs' =>
          dsimp only at hm
          injection hm with hm2
          exact ⟨q, qs', rfl, rfl, hm2.symm⟩
    obtain ⟨q, qs', h1, h2, h3⟩ := key _ _ h
    exact ⟨q, qs', h1, h2, h3⟩
  · rintro ⟨q, qs', h1, h2, h3⟩
    rw [summs_cons_of h1 h2, h3]

/-- Node summary, iff characterization. -/
theorem summarize_node_iff {A : Type} [DecidableEq A] (r : SRule A)
    (fs : SForest A) (q : Summ A) :
    summarize (.sNode r fs) = some q ↔
      ∃ qs, summs fs = some qs ∧ qs.map Summ.conc = r.premises ∧
        q = deltaS r qs := by
  constructor
  · intro h
    simp only [summarize] at h
    have key : ∀ v : Option (List (Summ A)),
        (match v with
         | none => none
         | some qs =>
             if qs.map Summ.conc = r.premises then some (deltaS r qs)
             else none) = some q →
        ∃ qs, v = some qs ∧ qs.map Summ.conc = r.premises ∧
          q = deltaS r qs := by
      intro v hm
      cases v with
      | none => simp at hm
      | some qs =>
        dsimp only at hm
        by_cases hp : qs.map Summ.conc = r.premises
        · rw [if_pos hp] at hm
          injection hm with hm2
          exact ⟨qs, rfl, hp, hm2.symm⟩
        · rw [if_neg hp] at hm; simp at hm
    obtain ⟨qs, h1, hp, hq⟩ := key _ h
    exact ⟨qs, h1, hp, hq⟩
  · rintro ⟨qs, h1, hp, hq⟩
    rw [summarize_node_of h1 hp, hq]

/-- Head coherence: the summary's conclusion is the tree's root
conclusion. -/
theorem summarize_conc {A : Type} [DecidableEq A] (t : STree A) (q : Summ A)
    (h : summarize t = some q) : q.conc = headT t := by
  cases t with
  | sLeaf b a src =>
      cases b with
      | false =>
          simp only [summarize] at h
          injection h with hq
          rw [← hq]; rfl
      | true =>
          simp only [summarize] at h
          injection h with hq
          rw [← hq]; rfl
  | sNode r fs =>
      obtain ⟨qs, _, _, hq⟩ := (summarize_node_iff r fs q).mp h
      rw [hq]; rfl

/-! ## Delta readouts -/

theorem delta_last_defeasible {A : Type} (r : SRule A) (qs : List (Summ A))
    (hd : r.mode = .defeasible) (x : A) :
    x ∈ (deltaS r qs).lastI ↔ x = r.rid := by
  simp [deltaS, lastOfRule, hd]

theorem delta_last_strict {A : Type} (r : SRule A) (qs : List (Summ A))
    (hs : r.mode = .strictS) (x : A) :
    x ∈ (deltaS r qs).lastI ↔ ∃ q ∈ qs, x ∈ q.lastI := by
  simp [deltaS, lastOfRule, hs, List.mem_flatMap]

theorem delta_sites {A : Type} (r : SRule A) (qs : List (Summ A))
    (s : SiteSum A) :
    s ∈ (deltaS r qs).sites ↔
      s = ownSiteOf r qs ∨ ∃ q ∈ qs, s ∈ q.sites := by
  simp [deltaS]

theorem own_site_typed {A : Type} (r : SRule A) (qs : List (Summ A)) :
    ∃ la : List A,
      ownSiteOf r qs = SiteSum.ruleS r.head r.mode r.rid la r.guards :=
  ⟨lastOfRule r qs, rfl⟩

theorem delta_conc {A : Type} (r : SRule A) (qs : List (Summ A)) :
    (deltaS r qs).conc = r.head := rfl

theorem leaf_last_empty {A : Type} (a src : A) :
    (leafOrdSum a src).lastI = [] := rfl

theorem leaf_site_mem {A : Type} (a src : A) :
    SiteSum.leafS a ∈ (leafOrdSum a src).sites := by
  simp [leafOrdSum]

theorem exempt_site_free {A : Type} (a src : A) (s : SiteSum A) :
    s ∉ (leafExemptSum a src).sites := by
  simp [leafExemptSum]

/-! ## Saturation: height-indexed closure, witness soundness -/

/-- Height-indexed saturation: leaf seeds at any level; step children
live at level n, the composed summary at level n+1. -/
inductive SaturatedN {A : Type} (Γ : List (SRule A)) :
    ℕ → Summ A → Prop
  | leafOrd (n : ℕ) (a src : A) : SaturatedN Γ n (leafOrdSum a src)
  | leafExempt (n : ℕ) (a src : A) : SaturatedN Γ n (leafExemptSum a src)
  | step (n : ℕ) (r : SRule A) (hr : r ∈ Γ) (qs : List (Summ A))
      (hprem : qs.map Summ.conc = r.premises)
      (hch : ∀ q ∈ qs, SaturatedN Γ n q) :
      SaturatedN Γ (n + 1) (deltaS r qs)

/-- Unheighted saturation. -/
def Saturated {A : Type} (Γ : List (SRule A)) (q : Summ A) : Prop :=
  ∃ n, SaturatedN Γ n q

/-- Choice accumulation: if every summary in the list has a realizing
tree, some forest summarizes to exactly that list. -/
theorem summs_accumulate {A : Type} [DecidableEq A] :
    ∀ (qs : List (Summ A)), (∀ q ∈ qs, ∃ t, summarize t = some q) →
      ∃ fs, summs fs = some qs := by
  intro qs
  induction qs with
  | nil => intro _; exact ⟨.fNil, by simp [summs]⟩
  | cons q qs ih =>
      intro hall
      obtain ⟨t, ht⟩ := hall q (by simp)
      obtain ⟨fs, hfs⟩ := ih (fun q' hq' => hall q' (by simp [hq']))
      exact ⟨.fCons t fs, summs_cons_of ht hfs⟩

/-- Saturation witness soundness: every saturated summary has a
realizing tree - the saturated set contains no phantom summaries. -/
theorem saturatedN_witness {A : Type} [DecidableEq A] (Γ : List (SRule A)) :
    ∀ n q, SaturatedN Γ n q → ∃ t, summarize t = some q := by
  intro n
  induction n with
  | zero =>
      intro q h
      cases h with
      | leafOrd _ a src => exact ⟨.sLeaf true a src, summarize_leafOrd a src⟩
      | leafExempt _ a src =>
          exact ⟨.sLeaf false a src, summarize_leafExempt a src⟩
  | succ n ih =>
      intro q h
      cases h with
      | leafOrd _ a src => exact ⟨.sLeaf true a src, summarize_leafOrd a src⟩
      | leafExempt _ a src =>
          exact ⟨.sLeaf false a src, summarize_leafExempt a src⟩
      | step _ r _ qs hprem hch =>
          have hreal : ∀ q ∈ qs, ∃ t, summarize t = some q :=
            fun q hq => ih q (hch q hq)
          obtain ⟨fs, hfs⟩ := summs_accumulate qs hreal
          exact ⟨.sNode r fs, summarize_node_of hfs hprem⟩

theorem saturated_witness {A : Type} [DecidableEq A] (Γ : List (SRule A))
    {q : Summ A} (h : Saturated Γ q) : ∃ t, summarize t = some q := by
  obtain ⟨n, hn⟩ := h
  exact saturatedN_witness Γ n q hn

/-- Least closure: any set containing the leaf seeds and closed under
delta contains every saturated summary - Saturated is the least such
set, the least-fixed-point discipline of `saturate_summaries`. -/
theorem saturatedN_into_closed {A : Type} (Γ : List (SRule A))
    (S : List (Summ A))
    (hleavesOrd : ∀ a src, leafOrdSum a src ∈ S)
    (hleavesEx : ∀ a src, leafExemptSum a src ∈ S)
    (hstep : ∀ r ∈ Γ, ∀ qs : List (Summ A),
      qs.map Summ.conc = r.premises → (∀ q ∈ qs, q ∈ S) →
      deltaS r qs ∈ S) :
    ∀ n q, SaturatedN Γ n q → q ∈ S := by
  intro n
  induction n with
  | zero =>
      intro q h
      cases h with
      | leafOrd _ a src => exact hleavesOrd a src
      | leafExempt _ a src => exact hleavesEx a src
  | succ n ih =>
      intro q h
      cases h with
      | leafOrd _ a src => exact hleavesOrd a src
      | leafExempt _ a src => exact hleavesEx a src
      | step _ r hr qs hprem hch =>
          exact hstep r hr qs hprem (fun q hq => ih q (hch q hq))

end JurisLean.Seams.UnifiedSummary
