/-
Unified admission, layer D (plan §5.2–§5.4; I.4.6, U08–U10).

Basis-checked admission rounds, burden scoping, and stabilization.

Design (this fragment): facts of type `F`, issues of type `I`.  An
`AdmissionBasis` is a NAMED rule record — kind (ordinary support,
presumption, forensic exemption, judicial admission, final binding,
evidence obstruction), issue, premises, blocks, and the fact it grants
when valid.  A basis is valid under the currently admitted facts when
every premise is admitted and no block is admitted (an admitted block
is the revocation/defeat EVENT of §11.1).  The admission step admits
exactly the grants of valid bases — never a caller-fed verdict.

U08 `accepted_has_legal_basis`: every fact admitted after `n` rounds
either was admitted initially or is the grant of a basis VALID AT SOME
ROUND m ≤ n — the round at which its admission was licensed.
(Validity is NOT claimed to persist forward: a later-admitted block
can revoke a basis's validity at later rounds; the witness is anchored
to the licensing round.)

U09: burden scoping, two facts.  `burden_failure_issue_scoped`: the
notEstablished consequence of §5.2's final-burden rule lands ONLY on
the pending issue itself (exact membership condition — no propagation
to other issues by construction).  `burden_failure_not_ontic_negation`:
a burden failure is COMPATIBLE with the issue being actually true —
a two-branch witness in the spirit of plan §5.3.4: missing materials
leave the burden unmet while the world makes the issue true.

U10 `admission_reaches_fixed_point`: over a finite fact universe the
monotone admitted sequence reaches a fixed point within `card U` steps
(each strict growth strictly increases the cardinality; budget
induction on the remaining count).

STATUS: proved theorems pending their CI compile round (module check
then root then full release); no `sorry`/`admit`/custom `axiom`/
`: True :=`/`native_decide` appears here.
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

namespace JurisLean.Seams.UnifiedAdmission

/-- The six named admission channels (plan §5.2/§11.1).  Ordinary
support and presumption are the ordinary-path templates; the other four
are the special channels that never confer StrongBasis (that claim
lives in the standards layer, not here). -/
inductive BasisKind : Type
  | ordinarySupport | presumption | forensicExempt
  | judicialAdmission | finalBinding | evidenceObstruction

/-- A named admission basis: premises, blocking events, the issue it
belongs to, and the fact it grants when valid. -/
structure AdmissionBasis (F I : Type) where
  basisId : ℕ
  kind : BasisKind
  issue : I
  premises : Finset F
  blocks : Finset F
  grants : F

section Rounds
variable {F I : Type} [DecidableEq F]

/-- Basis validity under the admitted facts: every premise admitted,
no block admitted. -/
def BasisValid (admitted : Finset F) (b : AdmissionBasis F I) : Prop :=
  b.premises ⊆ admitted ∧ Disjoint b.blocks admitted

/-- Decidable version used by the step: the contract itself decided. -/
def basisValidB (admitted : Finset F) (b : AdmissionBasis F I) : Bool :=
  decide (b.premises ⊆ admitted ∧ Disjoint b.blocks admitted)

/-- The one-round admission step: newly admitted facts are exactly the
grants of valid bases. -/
def admittedStep (admitted : Finset F)
    (bases : Finset (AdmissionBasis F I)) : Finset F :=
  admitted ∪ (bases.filter (fun b => basisValidB admitted b)).image
    (fun b => b.grants)

/-- The n-round admission sequence. -/
def admittedRounds (admitted₀ : Finset F)
    (bases : Finset (AdmissionBasis F I)) : ℕ → Finset F
  | 0 => admitted₀
  | n + 1 => admittedStep (admittedRounds admitted₀ bases n) bases

/-- Reflection: the decided checker reads exactly the contract. -/
theorem basisValidB_iff (admitted : Finset F) (b : AdmissionBasis F I) :
    basisValidB admitted b = true ↔ BasisValid admitted b := by
  simp [basisValidB, BasisValid]

/-- Membership in the step's image part, decomposed once and reused:
a fact is granted by the step exactly when some basis of the table,
valid under `s`, grants it. -/
theorem mem_step_grants_iff (s : Finset F)
    (bases : Finset (AdmissionBasis F I)) (f : F) :
    f ∈ (bases.filter (fun b => basisValidB s b)).image
        (fun b => b.grants) ↔
    ∃ b ∈ bases, BasisValid s b ∧ b.grants = f := by
  constructor
  · intro h
    obtain ⟨b, hb, hgrant⟩ := Finset.mem_image.mp h
    obtain ⟨hb1, hb2⟩ := Finset.mem_filter.mp hb
    exact ⟨b, hb1, (basisValidB_iff s b).mp hb2, hgrant⟩
  · rintro ⟨b, hbmem, hval, rfl⟩
    exact Finset.mem_image.mpr
      ⟨b, Finset.mem_filter.mpr ⟨hbmem, (basisValidB_iff s b).mpr hval⟩,
       rfl⟩

/-- **U08** — every fact admitted after `n` rounds carries a legal
basis: it was admitted initially, or it is the grant of a basis valid
at some round m ≤ n (the round that licensed its admission). -/
theorem accepted_has_legal_basis (admitted₀ : Finset F)
    (bases : Finset (AdmissionBasis F I)) :
    ∀ (n : ℕ) (f : F), f ∈ admittedRounds admitted₀ bases n →
      f ∈ admitted₀ ∨ ∃ b ∈ bases, ∃ m, m ≤ n ∧
        BasisValid (admittedRounds admitted₀ bases m) b ∧ b.grants = f := by
  intro n
  induction n with
  | zero =>
      intro f hf
      exact Or.inl hf
  | succ n ih =>
      intro f hf
      rw [admittedRounds, admittedStep, Finset.mem_union] at hf
      rcases hf with hf | hf
      · rcases ih f hf with h0 | ⟨b, hbmem, m, hm, hval, hgrant⟩
        · exact Or.inl h0
        · exact Or.inr ⟨b, hbmem, m, Nat.le_succ_of_le hm, hval, hgrant⟩
      · rw [mem_step_grants_iff] at hf
        obtain ⟨b, hbmem, hval, hgrant⟩ := hf
        exact Or.inr ⟨b, hbmem, n, Nat.le_succ n, hval, hgrant⟩

/-- The step is monotone in the admitted set. -/
theorem admittedStep_mono (s : Finset F)
    (bases : Finset (AdmissionBasis F I)) :
    s ⊆ admittedStep s bases := by
  intro f hf
  rw [admittedStep, Finset.mem_union]
  exact Or.inl hf

/-- The step stays inside the universe. -/
theorem admittedStep_bounded (s U : Finset F)
    (bases : Finset (AdmissionBasis F I))
    (hs : s ⊆ U) (hgrant : ∀ b ∈ bases, b.grants ∈ U) :
    admittedStep s bases ⊆ U := by
  intro f hf
  rw [admittedStep, Finset.mem_union] at hf
  rcases hf with hf | hf
  · exact hs hf
  · rw [mem_step_grants_iff] at hf
    obtain ⟨b, hbmem, _, hgrant'⟩ := hf
    rw [← hgrant']
    exact hgrant b hbmem

/-- Every round is bounded by a universe containing the initial facts
and every grant. -/
theorem admittedRounds_bounded (admitted₀ U : Finset F)
    (bases : Finset (AdmissionBasis F I))
    (h₀ : admitted₀ ⊆ U) (hgrant : ∀ b ∈ bases, b.grants ∈ U) :
    ∀ n, admittedRounds admitted₀ bases n ⊆ U := by
  intro n
  induction n with
  | zero => exact h₀
  | succ n ih =>
      intro f hf
      rw [admittedRounds] at hf
      exact admittedStep_bounded _ U bases ih hgrant hf

/-- **U10** — the monotone bounded admission sequence reaches a fixed
point within the universe's cardinality budget: induction on the
budget (a strict step strictly increases the cardinality, consuming one
unit; at budget zero the set already fills the universe and the step
cannot add anything new). -/
theorem admission_reaches_fixed_point (admitted₀ U : Finset F)
    (bases : Finset (AdmissionBasis F I))
    (h₀ : admitted₀ ⊆ U) (hgrant : ∀ b ∈ bases, b.grants ∈ U) :
    ∃ m, m ≤ U.card ∧
      admittedStep (admittedRounds admitted₀ bases m) bases
        = admittedRounds admitted₀ bases m := by
  have key : ∀ (d : ℕ) (s : Finset F) (k : ℕ),
      s = admittedRounds admitted₀ bases k → s ⊆ U →
      U.card ≤ s.card + d →
      ∃ m, k ≤ m ∧ m ≤ k + d ∧
        admittedStep (admittedRounds admitted₀ bases m) bases
          = admittedRounds admitted₀ bases m := by
    intro d
    induction d with
    | zero =>
        intro s k hs hsub hcard
        have hsU : s = U :=
          Finset.eq_of_subset_of_card_le hsub (by omega)
        have hstepsub : admittedStep s bases ⊆ U :=
          admittedStep_bounded s U bases hsub hgrant
        have hfix : admittedStep s bases = s :=
          Finset.Subset.antisymm
            (by rw [← hsU]; exact hstepsub)
            (admittedStep_mono s bases)
        rw [hs] at hfix
        exact ⟨k, le_refl _, by omega, hfix⟩
    | succ d ih =>
        intro s k hs hsub hcard
        by_cases hfix : admittedStep s bases = s
        · rw [hs] at hfix
          exact ⟨k, le_refl _, by omega, hfix⟩
        · have hsub0 : s ⊆ admittedStep s bases :=
            admittedStep_mono s bases
          have hcard0 : s.card < (admittedStep s bases).card :=
            Finset.card_lt_card hsub0 (fun heq => hfix heq.symm)
          have hnext : admittedRounds admitted₀ bases (k + 1)
              = admittedStep s bases := by
            rw [hs]
            rfl
          have hsub1 : admittedRounds admitted₀ bases (k + 1) ⊆ U := by
            rw [hnext]
            exact admittedStep_bounded s U bases hsub hgrant
          have hcard1 : U.card ≤
              (admittedRounds admitted₀ bases (k + 1)).card + d := by
            rw [hnext]
            omega
          obtain ⟨m, hm1, hm2, hfixm⟩ :=
            ih (admittedStep s bases) (k + 1) hnext hsub1 hcard1
          exact ⟨m, by omega, by omega, hfixm⟩
  obtain ⟨m, _, hm2, hfix⟩ :=
    key U.card admitted₀ 0 rfl h₀ (by omega)
  exact ⟨m, hm2, hfix⟩

end Rounds

section Burden
variable {I : Type}

/-- The final-burden state of §5.2: the issues whose full evaluation
opportunity has closed without the fact being established. -/
structure BurdenCase (I : Type) where
  pendingIssues : Finset I

/-- Three-valued judgment status (§5.1). -/
inductive JudgmentStatus : Type
  | established | notEstablished | pending

/-- The burden rule's consequence: notEstablished lands exactly on the
pending issues. -/
def burdenStatus (c : BurdenCase I) (q : I) : JudgmentStatus :=
  if h : q ∈ c.pendingIssues then
    JudgmentStatus.notEstablished
  else
    JudgmentStatus.pending

/-- **U09 (a)** — issue scoping: the unilateral burden consequence
lands ONLY on the rule's own pending issue; an issue outside the case
never receives notEstablished from this rule. -/
theorem burden_failure_issue_scoped (c : BurdenCase I) (q : I)
    (h : burdenStatus c q = JudgmentStatus.notEstablished) :
    q ∈ c.pendingIssues := by
  by_contra hout
  rw [burdenStatus, dif_neg hout] at h
  cases h

/-- **U09 (b)** — a burden failure is compatible with the issue being
actually true: missing materials leave the burden unmet while the
actual world makes the issue true (plan §5.3.4's two-branch shape; the
ontic valuation is an independent assignment, never read by the burden
rule). -/
theorem burden_failure_not_ontic_negation (c : BurdenCase I) (q : I)
    (h : q ∈ c.pendingIssues) :
    ∃ w : I → Bool, w q = true ∧
      burdenStatus c q = JudgmentStatus.notEstablished := by
  refine ⟨fun _ => true, rfl, ?_⟩
  rw [burdenStatus, dif_pos h]

end Burden

end JurisLean.Seams.UnifiedAdmission
