import JurisLean.Candidates.Final20261021.Acceptance
import JurisLean.Candidates.Final20261021.Authorization
import JurisLean.Candidates.Final20261021.Behavior
import JurisLean.Candidates.Final20261021.Calibration
import JurisLean.Candidates.Final20261021.Decision
import JurisLean.Candidates.Final20261021.EvidenceProcedure
import JurisLean.Candidates.Final20261021.Feedback
import JurisLean.Candidates.Final20261021.Harness
import JurisLean.Candidates.Final20261021.Iteration
import JurisLean.Candidates.Final20261021.Learning
import JurisLean.Candidates.Final20261021.Ledger
import JurisLean.Candidates.Final20261021.Pipeline
import JurisLean.Candidates.Final20261021.Policy
import JurisLean.Candidates.Final20261021.Probability
import JurisLean.Candidates.Final20261021.Progress
import JurisLean.Candidates.Final20261021.Representation
import JurisLean.Candidates.Final20261021.RSI
import JurisLean.Candidates.Final20261021.Temporal
import JurisLean.Candidates.Final20261021.Trace

/-!
Formal-tail source for formal_tail_20261024 + CAND5bis, candidate ids in
archive order: U08.1, U08.2, U10.3, U09.3, U06.4, U12.2, U13.1, U15.1,
U14.2, U15.2.

CAND5 (U08.1/U10.3/U06.4/U12.2/U14.2) were previously expand-audited and
later CLOSED_BY_WIRING under formal_tail_关≥1_CAND5_20261025.
CAND5bis (U08.2/U09.3/U13.1/U15.1/U15.2) are candidate theorems only
under pack formal_tail_真证CAND5bis_20261025: expand-audit naming may
wire candidate_in_tip_pin_audit; this knife does NOT write CLOSED;
OPEN_FORMAL_TAIL stays 35; closed_this_round stays 0.

Prior tip-pin 27849d3f / 40079130550 must NOT be cited as FormalTail
coverage. Old f85ebe44 / 40115638107 / 120936221970 receipt is history;
live tip_pin may retarget after a new tip Authority SUCCESS that names
the CAND5bis full theorem names.

Disposition for CAND5bis stays CANDIDATE_NOT_AUDITED until math
debt-layer. discharges_archived_manuscript_gaps stays false.
Step 2 stays open. Local text is not a Lean PASS. CI is the authority.

CAND6 (U08.3 / U15.3 / U13.2 / U09.1 / U10.2), pack
formal_tail_真证CAND6_20261026, appends twelve non-sufficiency witnesses.
They stay out of PROVE_CANDIDATES, so the five rows stay blocked.
Open count stays 30. This section does not retarget tip_pin and does not
expand the named audit. Reality-truth, external load readback, and legal
allocation stay non-goals of the wired declarations already on those rows.

CAND7 (U07.1 / U02.3 / U04.3 / U05.2 / U06.3), pack
formal_tail_真证CAND7_20261026, appends twelve non-sufficiency witnesses.
They stay out of PROVE_CANDIDATES, so the five rows stay blocked.
Open count stays 25. This section does not retarget tip_pin
(subject 1c72e444 / Authority 40257646857 / job 121362851074 /
named_count = 49) and does not expand the named audit.
Calibration, causal identification, and numerical attainment stay
non-goals of U04.3. discharges_archived_manuscript_gaps,
math_flip_authorized, and step_2_closed stay false.
The closed increment of this section is 0.

CAND8 (U03.1 / U03.2 / U07.2 / U01.1 / U01.2), pack
formal_tail_真证CAND8_20261026, appends twelve non-sufficiency witnesses.
They stay out of PROVE_CANDIDATES, so the five rows stay blocked.
Open count stays 20. This section does not retarget tip_pin
(subject 21862d9b / Authority 40274167574 / job 121413235107 /
named_count = 61) and does not expand the named audit.
Verified fuel-bound and provenance-DAG-to-closure claims stay
non-goals of U03.2 and U03.1. discharges_archived_manuscript_gaps,
math_flip_authorized, and step_2_closed stay false.
The closed increment of this section is 0.
-/

namespace JurisLean.Candidates.FormalTail20261024

open JurisLean.Candidates.Final20261021
open JurisLean.Candidates.Final20261021.Decision
open JurisLean.Candidates.Final20261021.Feedback
open JurisLean.Candidates.Final20261021.Iteration
open JurisLean.Candidates.Final20261021.Learning
open JurisLean.Candidates.Final20261021.Policy
open JurisLean.Candidates.Final20261021.Progress
open JurisLean.Candidates.Final20261021.Temporal

/-! ### U08.1
Late records stay invisible at the cutoff. Disguising one as then-known
changes applicability. Reading the latest version as current status
disagrees with the cutoff query. The append lemma is a consumer of the
audited `u08_1_selection_stable`. Named in expand-audit evidence
ci-tip-f85ebe44; still OPEN_FORMAL_TAIL (no debt close). -/

theorem u08_1_recorded_after_cutoff_not_visible (g : Gamma) (e : VersionRecord)
    (h : g.recordCutoff.ticks < e.recordedAt.ticks) :
    visible g e = false := by
  unfold visible
  apply decide_eq_false
  rintro ⟨hle, _⟩
  exact not_le_of_gt h hle

theorem u08_1_late_append_uses_selection_stable
    (g : Gamma) (history : List VersionRecord) (e : VersionRecord)
    (h : g.recordCutoff.ticks < e.recordedAt.ticks) :
    proposed_applicability g (history ++ [e]) = proposed_applicability g history := by
  refine u08_1_selection_stable g history [e] ?_
  intro x hx
  rcases List.mem_singleton.mp hx with rfl
  exact u08_1_recorded_after_cutoff_not_visible g x h

def u08Cutoff : Gamma := {
  caseId := ⟨0⟩
  caseRevision := 0
  evidenceVersion := 0
  jurisdiction := "J"
  question := 1
  interpretation := 0
  normVersion := 0
  lawDate := ⟨0⟩
  knowledgeCutoff := ⟨0⟩
  recordCutoff := ⟨0⟩
  schemaVersion := 0
  observationFamily := 0
  mechanismVersion := 0
}

def u08Late : VersionRecord := {
  id := ⟨1⟩
  version := 7
  jurisdiction := "J"
  question := 1
  factFrom := ⟨0⟩
  factUntil := none
  recordedAt := ⟨1⟩
  knownAt := ⟨0⟩
}

def u08Disguised : VersionRecord := { u08Late with recordedAt := ⟨0⟩ }

/-- Reading the latest appended version, ignoring the record cutoff. -/
def currentStatus (history : List VersionRecord) : Option Nat :=
  history.getLast?.map (·.version)

theorem u08_1_late_record_disguised_as_then_known_changes_applicability :
    visible u08Cutoff u08Late = false ∧
      visible u08Cutoff u08Disguised = true ∧
      proposed_applicability u08Cutoff [u08Late] = Result.unknown Error.missingEvidence ∧
      proposed_applicability u08Cutoff [u08Disguised] = Result.known 7 ∧
      proposed_applicability u08Cutoff [u08Late] ≠
        proposed_applicability u08Cutoff [u08Disguised] := by
  decide

theorem u08_1_mutable_current_status_disagrees_with_cutoff :
    currentStatus [u08Late] = some 7 ∧
      proposed_applicability u08Cutoff [u08Late] = Result.unknown Error.missingEvidence ∧
      proposed_applicability u08Cutoff ([] ++ [u08Late]) =
        proposed_applicability u08Cutoff [] ∧
      currentStatus [u08Late] ≠ none := by
  refine ⟨rfl, rfl, ?_, by decide⟩
  exact u08_1_late_append_uses_selection_stable u08Cutoff [] u08Late (by decide)


/-! ### U08.2
Current versus reachable exhaustion: a singleton current set does not cover
a two-point reachable set. Nonempty-state preservation: on a nonempty
observation the compressible answer equals the chosen world's answer
(consumer of the audited finite-compression reflection). Named for
CAND5bis expand-audit only; U08.2 stays OPEN_FORMAL_TAIL. -/

theorem u08_2_current_singleton_does_not_exhaust_reachable :
    ¬ ∀ v : Fin 2, v ∈ ({0} : Finset (Fin 2)) := by
  intro h
  have : (1 : Fin 2) ∈ ({0} : Finset (Fin 2)) := h 1
  exact absurd this (by decide)

/-- One history, two worlds; observation `{()}` is nonempty. -/
def u08_2_app (_h : Unit) (_v : Bool) : Bool := true
def u08_2_answer (_v : Bool) (_h : Unit) (_q : Unit) : Nat := 7
def u08_2_obs (_q : Unit) : Bool := true

theorem u08_2_nonempty_observation_preserves_chosen_answer :
    checkCompression (H := Unit) (V := Bool) (Q := Unit) (A := Nat)
        u08_2_app u08_2_answer u08_2_obs true = true ∧
      Compressible (fun h v => u08_2_app h v = true) u08_2_answer
        (fun q => u08_2_obs q = true) true := by
  refine ⟨by decide, ?_⟩
  exact (u08_2_finite_compression_reflection
    (H := Unit) (V := Bool) (Q := Unit) (A := Nat)
    u08_2_app u08_2_answer u08_2_obs true).mp (by decide)

/-! ### U10.3
A zero-step ranked path is the identity and does not strictly decrease rank.
Business-observed length is the sum of per-operation abstract steps and is a
consumer of the audited simulation-length bound. A zero observation is not
positive progress.
公平 and 外部响应 are explicit non-goals of this clause (exact_scope: 另证).
These declarations are named in expand-audit evidence ci-tip-f85ebe44;
prior 40079130550 / job 120828801547 is not FormalTail coverage.
They do not close U10.3. Companion 公平／外部响应＝另证 stays. -/

theorem u10_3_zero_step_ranked_path_is_identity {S : Type} (rank : S → Nat) {s t : S}
    (h : RankedPath rank s 0 t) : s = t := by
  cases h with
  | nil _ => rfl

theorem u10_3_zero_step_prohibits_strict_progress {S : Type} (rank : S → Nat) (s : S) :
    ¬ ∃ t, RankedPath rank s 0 t ∧ rank t < rank s := by
  intro ⟨t, hpath, hlt⟩
  have hs : s = t := u10_3_zero_step_ranked_path_is_identity rank hpath
  -- `subst` would clear the later variable `t`. Rewrite the inequality instead.
  rw [hs] at hlt
  exact lt_irrefl _ hlt

/-- Reported abstract length of a business trace: the sum of the per-operation
observations, not the count of real operations. -/
def businessObservedLength (perOperation : List Nat) : Nat := perOperation.sum

theorem u10_3_business_observation_faithful (perOperation : List Nat) (K : Nat)
    (bounded : ∀ n ∈ perOperation, n ≤ K) :
    businessObservedLength perOperation = perOperation.sum ∧
      businessObservedLength perOperation ≤ perOperation.length * K := by
  refine ⟨rfl, ?_⟩
  simpa [businessObservedLength] using u10_3_simulation_length perOperation K bounded

theorem u10_3_zero_observation_is_not_progress (perOperation : List Nat)
    (h : ∀ n ∈ perOperation, n = 0) :
    businessObservedLength perOperation = 0 := by
  unfold businessObservedLength
  induction perOperation with
  | nil => rfl
  | cons k ks ih =>
      have hk : k = 0 := h k (by simp)
      have hs : ks.sum = 0 := ih (fun x hx => h x (by simp [hx]))
      simp only [List.sum_cons, hk, hs, Nat.zero_add]

theorem u10_3_one_real_step_zero_abstract_is_not_progress :
    businessObservedLength [0] = 0 ∧ ¬ (0 < businessObservedLength [0]) := by
  have h0 : businessObservedLength [0] = 0 := by
    unfold businessObservedLength
    simp [List.sum_cons, List.sum_nil]
  refine ⟨h0, ?_⟩
  rw [h0]
  decide


/-! ### U09.3
Greedy prefix on a two-claim budget is not the full optimum ordering.
Same-institution accrual does not move cash (consumer of audited
`u09_3_accrual_not_cash`). Named for CAND5bis expand-audit only;
U09.3 stays OPEN_FORMAL_TAIL. -/

/-- Greedy takes the first claim of size 2 from budget 3; the leftover 1
cannot fund the second claim of size 2. Reordering would fund either claim
fully, so the greedy prefix is not a full optimum. -/
theorem u09_3_greedy_prefix_misses_second_claim :
    let budget : ℚ := 3
    let d1 : ℚ := 2
    let d2 : ℚ := 2
    let greedy1 := min d1 budget
    let leftover := budget - greedy1
    let greedy2 := min d2 leftover
    greedy1 = 2 ∧ leftover = 1 ∧ greedy2 = 1 ∧
      greedy1 + greedy2 = 3 ∧ greedy2 < d2 ∧
      min d2 budget = 2 := by
  norm_num

theorem u09_3_same_institution_accrual_is_not_cash_effect (s : Ledger.State) (a : ℚ) :
    (Ledger.accrue s a).cash = s.cash ∧
      (Ledger.accrue s a).paid = s.paid ∧
      (Ledger.accrue s a).refundCash = s.refundCash :=
  Ledger.u09_3_accrual_not_cash s a

/-! ### U06.4
Out-of-range corollaries of the audited slope identities, then the same facts
for every q in the unit interval (empty or full intersection). Named in
expand-audit evidence ci-tip-f85ebe44; U06.4 stays OPEN_FORMAL_TAIL. -/

theorem u06_4_increasing_threshold_above_one_excludes (q b l k target : ℝ)
    (hlb : l < b) (hq : q ≤ 1)
    (hout : 1 < (target + k - l) / (b - l)) :
    ¬ target ≤ net q b l k := by
  intro h
  have hle := (u06_4_threshold_increasing q b l k target hlb).mp h
  linarith

theorem u06_4_increasing_threshold_at_most_zero_includes (q b l k target : ℝ)
    (hlb : l < b) (hq : 0 ≤ q)
    (hout : (target + k - l) / (b - l) ≤ 0) :
    target ≤ net q b l k := by
  apply (u06_4_threshold_increasing q b l k target hlb).mpr
  linarith

theorem u06_4_decreasing_threshold_below_zero_excludes (q b l k target : ℝ)
    (hbl : b < l) (hq : 0 ≤ q)
    (hout : (target + k - l) / (b - l) < 0) :
    ¬ target ≤ net q b l k := by
  intro h
  have hle := (u06_4_threshold_decreasing q b l k target hbl).mp h
  linarith

theorem u06_4_decreasing_threshold_at_least_one_includes (q b l k target : ℝ)
    (hbl : b < l) (hq : q ≤ 1)
    (hout : 1 ≤ (target + k - l) / (b - l)) :
    target ≤ net q b l k := by
  apply (u06_4_threshold_decreasing q b l k target hbl).mpr
  linarith

theorem u06_4_increasing_unit_interval_above_one_is_empty (b l k target : ℝ)
    (hlb : l < b) (hout : 1 < (target + k - l) / (b - l)) :
    ∀ q : ℝ, 0 ≤ q → q ≤ 1 → ¬ target ≤ net q b l k := by
  intro q _hq0 hq1
  exact u06_4_increasing_threshold_above_one_excludes q b l k target hlb hq1 hout

theorem u06_4_increasing_unit_interval_at_most_zero_is_full (b l k target : ℝ)
    (hlb : l < b) (hout : (target + k - l) / (b - l) ≤ 0) :
    ∀ q : ℝ, 0 ≤ q → q ≤ 1 → target ≤ net q b l k := by
  intro q hq0 _hq1
  exact u06_4_increasing_threshold_at_most_zero_includes q b l k target hlb hq0 hout

theorem u06_4_decreasing_unit_interval_below_zero_is_empty (b l k target : ℝ)
    (hbl : b < l) (hout : (target + k - l) / (b - l) < 0) :
    ∀ q : ℝ, 0 ≤ q → q ≤ 1 → ¬ target ≤ net q b l k := by
  intro q hq0 _hq1
  exact u06_4_decreasing_threshold_below_zero_excludes q b l k target hbl hq0 hout

theorem u06_4_decreasing_unit_interval_at_least_one_is_full (b l k target : ℝ)
    (hbl : b < l) (hout : 1 ≤ (target + k - l) / (b - l)) :
    ∀ q : ℝ, 0 ≤ q → q ≤ 1 → target ≤ net q b l k := by
  intro q _hq0 hq1
  exact u06_4_decreasing_threshold_at_least_one_includes q b l k target hbl hq1 hout

/-! ### U12.2
Damping, oscillation, and the two boundaries of the audited contraction
theorem: a translation has no fixed point, and `x - x^3` on `[-1,1]` reaches
the fixed point `0` from `1` while expanding a pair, so sufficiency is not
necessity. Named in expand-audit evidence ci-tip-f85ebe44; U12.2 stays
OPEN_FORMAL_TAIL. -/

-- Real field operations depend on a noncomputable instance.
noncomputable section

def halve (x : ℝ) : ℝ := x / 2

lemma halve_iterate_one (n : Nat) : halve^[n] (1 : ℝ) = (1 / 2 : ℝ) ^ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply', ih, pow_succ]
      unfold halve
      ring

lemma half_pow_pos (n : Nat) : (0 : ℝ) < (1 / 2) ^ n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      rw [pow_succ]
      exact mul_pos ih (by norm_num)

lemma half_pow_shrinks (n : Nat) :
    |(1 / 2 : ℝ) ^ (n + 1)| < |(1 / 2 : ℝ) ^ n| := by
  have hp := half_pow_pos n
  have hp1 := half_pow_pos (n + 1)
  rw [abs_of_pos hp1, abs_of_pos hp, pow_succ]
  have hlt : (1 / 2 : ℝ) < 1 := by norm_num
  nlinarith

theorem u12_2_halving_damps_toward_zero (n : Nat) :
    dist (halve^[n] (1 : ℝ)) (0 : ℝ) = (1 / 2 : ℝ) ^ n ∧
      dist (halve^[n + 1] (1 : ℝ)) (0 : ℝ) < dist (halve^[n] (1 : ℝ)) (0 : ℝ) ∧
      halve (0 : ℝ) = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [Real.dist_eq, halve_iterate_one n, sub_zero, abs_of_pos (half_pow_pos n)]
  · rw [Real.dist_eq, Real.dist_eq, halve_iterate_one (n + 1), halve_iterate_one n,
      sub_zero, sub_zero]
    exact half_pow_shrinks n
  · unfold halve
    norm_num

def negate (x : ℝ) : ℝ := -x

lemma negate_iterate_even (n : Nat) : negate^[2 * n] (1 : ℝ) = 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      have hstep : negate^[2 * (n + 1)] (1 : ℝ) =
          negate (negate (negate^[2 * n] (1 : ℝ))) := by
        have hindex : 2 * (n + 1) = (2 * n + 1) + 1 := by omega
        rw [hindex, Function.iterate_succ_apply']
        have hinner : 2 * n + 1 = (2 * n) + 1 := by omega
        rw [hinner, Function.iterate_succ_apply']
      rw [hstep, ih]
      unfold negate
      norm_num

lemma negate_iterate_odd (n : Nat) : negate^[2 * n + 1] (1 : ℝ) = -1 := by
  have hstep : negate^[2 * n + 1] (1 : ℝ) = negate (negate^[2 * n] (1 : ℝ)) := by
    have hindex : 2 * n + 1 = (2 * n) + 1 := by omega
    rw [hindex, Function.iterate_succ_apply']
  rw [hstep, negate_iterate_even]
  unfold negate
  norm_num

theorem u12_2_negation_orbit_oscillates (n : Nat) :
    negate^[2 * n] (1 : ℝ) = 1 ∧
      negate^[2 * n + 1] (1 : ℝ) = -1 ∧
      (1 : ℝ) ≠ -1 := by
  refine ⟨negate_iterate_even n, negate_iterate_odd n, ?_⟩
  norm_num

/-- Manuscript boundary `1-θ`: the orbit swaps `0` and `1`. -/
def oneMinus (θ : ℝ) : ℝ := 1 - θ

theorem u12_2_one_minus_theta_oscillates (θ : ℝ) :
    oneMinus (oneMinus θ) = θ ∧
      oneMinus (0 : ℝ) = 1 ∧
      oneMinus (1 : ℝ) = 0 ∧
      (0 : ℝ) ≠ 1 := by
  unfold oneMinus
  refine ⟨by ring, by norm_num, by norm_num, by norm_num⟩

theorem u12_2_shift_has_no_fixed_point (x : ℝ) : x + 1 ≠ x := by
  linarith

/-- `x - x^3` on `[-1, 1]`: `1` reaches the fixed point `0` in one step, and
the pair `1`, `4/5` expands, so no Lipschitz factor strictly below `1` works
for every pair. Sufficiency of contraction is not necessity. -/
def cubicStep (x : ℝ) : ℝ := x - x ^ 3

theorem u12_2_cubic_reaches_zero_but_expands :
    cubicStep (0 : ℝ) = 0 ∧
      cubicStep (1 : ℝ) = 0 ∧
      |cubicStep (1 : ℝ) - cubicStep (4 / 5 : ℝ)| > |(1 : ℝ) - 4 / 5| := by
  have h0 : cubicStep (0 : ℝ) = 0 := by
    unfold cubicStep
    norm_num
  have h1 : cubicStep (1 : ℝ) = 0 := by
    unfold cubicStep
    norm_num
  have h45 : cubicStep (4 / 5 : ℝ) = 36 / 125 := by
    unfold cubicStep
    norm_num
  have hspan : |(1 : ℝ) - 4 / 5| = 1 / 5 := by norm_num
  refine ⟨h0, h1, ?_⟩
  rw [h1, h45, hspan]
  norm_num

end


/-! ### U13.1
Lawful statistical-evidence input change moves the conditional estimate.
Personal-checkpoint update preserves the rule service (consumer of audited
`u13_1_noninterference`). Authority integration is an explicit NON_GOAL of
this candidate row. Named for CAND5bis expand-audit only; U13.1 stays
OPEN_FORMAL_TAIL. -/

theorem u13_1_lawful_stat_input_change_changes_estimate :
    ([1] : List ℚ).length ≠ ([0, 1] : List ℚ).length ∧
      RSI.conditionalEstimate [1] [0, 1] = Result.rejected .unsupported ∧
      RSI.conditionalEstimate ([] : List ℚ) ([] : List ℚ) =
        Result.unknown .missingEvidence := by
  exact ⟨by decide, rfl, rfl⟩

theorem u13_1_personal_update_preserves_rule_service
    {X Y : Type} (eval : Nat → Nat → X → Y)
    (s : RSI.State) (x : X) (who : PartyId) (value : RSI.Checkpoint) :
    RSI.proposed_rule_service eval (RSI.updatePersonal s who value) x =
      RSI.proposed_rule_service eval s x :=
  RSI.u13_1_noninterference eval s x who value


/-! ### U15.1
Finite-state strict-improvement paths cannot exceed the starting rank.
A parameter-free successor `n ↦ n+1` has no fixed point (no-parameter
convergence counterexample). The telescoping witness is a consumer of the
audited `u15_1_finite_cumulative_improvement`. Named for CAND5bis
expand-audit only; U15.1 stays OPEN_FORMAL_TAIL. -/

/-- Strict improvement on a finite rank: each step drops rank by at least one. -/
inductive FinStrictImprove {S : Type} (rank : S → Nat) : S → Nat → S → Prop where
  | nil (s : S) : FinStrictImprove rank s 0 s
  | cons {s t u : S} {n : Nat} :
      rank t < rank s →
        FinStrictImprove rank t n u → FinStrictImprove rank s (n + 1) u

theorem u15_1_finite_state_strict_improve_length_bound {S : Type}
    (rank : S → Nat) {s t : S} {n : Nat}
    (h : FinStrictImprove rank s n t) : n ≤ rank s := by
  induction h with
  | nil s => omega
  | cons hlt _rest ih => omega

theorem u15_1_no_parameter_successor_has_no_fixed_point (n : Nat) :
    n + 1 ≠ n := by
  omega

theorem u15_1_telescoping_consumes_cumulative_improvement
    {first last : ℝ} {budgets : List ℝ}
    (h : RiskTrace first budgets last) :
    last ≤ first + budgets.sum :=
  u15_1_finite_cumulative_improvement h

/-! ### U14.2
`N = 0` rejects the strict positive total. Equal sizes chosen after the fact
are not the fixed `99/1` effective-size witness. A shared copy keeps variance
`1/4`, above the independent `1/(4n)`. Consumers of the audited cluster
witness and the audited copy-variance lemmas. Named in expand-audit
evidence ci-tip-f85ebe44; U14.2 stays OPEN_FORMAL_TAIL. -/

theorem u14_2_zero_N_rejects_positive_hypothesis (N : ℝ) (h : N = 0) : ¬ 0 < N := by
  rw [h]
  exact lt_irrefl (0 : ℝ)

theorem u14_2_endogenous_equal_sizes_are_not_the_fixed_witness :
    ((99 + 1 : ℚ) ^ 2 / (99 ^ 2 + 1 ^ 2)) = 5000 / 4901 ∧
      ((1 + 1 : ℚ) ^ 2 / (1 ^ 2 + 1 ^ 2)) = 2 ∧
      (5000 / 4901 : ℚ) ≠ 2 := by
  refine ⟨u14_2_unequal_cluster_effective_size.1, ?_, u14_2_unequal_cluster_effective_size.2⟩
  norm_num

theorem u14_2_common_cause_copy_exceeds_independent_variance (n : ℕ) (hn : 1 < n) :
    ((((n : ℚ) ^ 2) * (1 / 2) - ((n : ℚ) * (1 / 2)) ^ 2) / ((n : ℚ) ^ 2)) = (1 / 4 : ℚ) ∧
      (((n : ℚ) * (1 / 2) + (n : ℚ) * ((n : ℚ) - 1) * (1 / 4) -
          ((n : ℚ) * (1 / 2)) ^ 2) / ((n : ℚ) ^ 2)) = 1 / (4 * (n : ℚ)) ∧
      1 / (4 * (n : ℚ)) < (1 / 4 : ℚ) := by
  have hn0 : 0 < n := by omega
  exact ⟨u01_4_copied_mean_variance n hn0,
    u01_4_independent_mean_variance n hn0,
    u01_4_copy_is_not_independent n hn⟩


/-! ### U15.2
Key-point regression: flipping the prediction at one point changes exact
risk. Finite-observation indistinguishability: two predictors that agree on
a singleton observation need not agree globally; the audited
preserved-prediction risk identity requires agreement on all of Ω.
Named for CAND5bis expand-audit only; U15.2 stays OPEN_FORMAL_TAIL. -/

theorem u15_2_key_point_regression_changes_exact_risk :
    exactRisk (false, false) = (1 / 2 : ℚ) ∧
      exactRisk (false, true) = (0 : ℚ) ∧
      exactRisk (false, false) ≠ exactRisk (false, true) := by
  have h := two_round_exact_risks
  refine ⟨h.1, h.2.1, ?_⟩
  rw [h.1, h.2.1]
  norm_num

/-- Two Bool-predictors that agree at `false` but disagree at `true`. -/
def u15_2_old : Bool → Bool := fun x => x
def u15_2_new : Bool → Bool := fun _ => false

theorem u15_2_finite_obs_agree_not_global :
    u15_2_old false = u15_2_new false ∧
      u15_2_old true ≠ u15_2_new true ∧
      ¬ (∀ x : Bool, u15_2_old x = u15_2_new x) := by
  refine ⟨rfl, by decide, ?_⟩
  intro h
  exact absurd (h true) (by decide)

theorem u15_2_full_agreement_preserves_risk
    {Ω Y : Type} [Fintype Ω]
    (law : Probability.FiniteLaw Ω) (old new : Ω → Y) (loss : Y → Ω → ℚ)
    (same : ∀ x, old x = new x) :
    Probability.expectation law (fun x => loss (old x) x) =
      Probability.expectation law (fun x => loss (new x) x) :=
  u15_2_preserved_predictions_equal_risk law old new loss same

/-! ### CAND6
Non-sufficiency witnesses for U08.3, U15.3, U13.2, U09.1, and U10.2.
Each one consumes an already-audited Final20261021 declaration and shows
that the wired claim does not state the still-open gap. No row is closed. -/

/-! ### U08.3
Four judgment states classify support and opposition. They do not reflect
an arbitrary dependency policy, a finished compatibility-world partition,
or full finite exhaustion of opportunities. Reality-truth stays the
existing non-goal of `u08_3_judgment_not_truth`; it is not restated here. -/

def u08OppNone : EvidenceProcedure.Opportunity :=
  { id := 0, rank := 0, executedReceipt := none, waivedBy := none, dependencies := [] }

def u08OppDep : EvidenceProcedure.Opportunity :=
  { u08OppNone with dependencies := [0] }

theorem u08_3_four_states_do_not_exhaust_dependency_policies :
    EvidenceProcedure.classify true false = Judgment.supported ∧
      EvidenceProcedure.classify false true = Judgment.opposed ∧
      EvidenceProcedure.classify true true = Judgment.incompatible ∧
      EvidenceProcedure.classify false false = Judgment.insufficient ∧
      u08OppNone.dependencies ≠ u08OppDep.dependencies ∧
      ¬ (u08OppNone.dependencies = u08OppDep.dependencies) := by
  have htf := EvidenceProcedure.u08_3_evidence_four_states true false
  have hft := EvidenceProcedure.u08_3_evidence_four_states false true
  have htt := EvidenceProcedure.u08_3_evidence_four_states true true
  have hff := EvidenceProcedure.u08_3_evidence_four_states false false
  refine ⟨htf.1.mpr ⟨rfl, rfl⟩, hft.2.1.mpr ⟨rfl, rfl⟩, htt.2.2.1.mpr ⟨rfl, rfl⟩,
    hff.2.2.2.mpr ⟨rfl, rfl⟩, by decide, by decide⟩

inductive u08CompatWorld where
  | pending
  | classified
  deriving DecidableEq

/-- Supported judgment is parked as unfinished world-classification. -/
def u08CompatClass (j : Judgment) : u08CompatWorld :=
  if j = Judgment.supported then .pending else .classified

theorem u08_3_judgment_not_compatibility_world_classification :
    EvidenceProcedure.judgment 0 [EvidenceProcedure.forgedEvidence] = Judgment.supported ∧
      u08CompatClass (EvidenceProcedure.judgment 0 [EvidenceProcedure.forgedEvidence]) =
        u08CompatWorld.pending ∧
      u08CompatClass Judgment.supported ≠ u08CompatWorld.classified ∧
      ¬ (EvidenceProcedure.judgment 0 [EvidenceProcedure.forgedEvidence] = Judgment.supported →
          u08CompatClass Judgment.supported = u08CompatWorld.classified) := by
  have hjudg := EvidenceProcedure.u08_3_judgment_not_truth
  refine ⟨hjudg.1, ?_, by decide, ?_⟩
  · rw [hjudg.1]
    decide
  · intro hdone
    exact absurd (hdone hjudg.1) (by decide)

def u08BareProcess : EvidenceProcedure.ProcessInput := {
  required := [0]
  policyDomain := [0]
  records := []
  validExecutionReceipts := []
  validWaivers := []
  closureAuthority := none
  validClosureAuthorities := []
  blocked := false
}

def u08OpposedPair : List EvidenceProcedure.EvidenceItem :=
  [EvidenceProcedure.forgedEvidence,
    { EvidenceProcedure.forgedEvidence with supports := false }]

theorem u08_3_opposition_preserves_support_not_full_reflection :
    EvidenceProcedure.judgment 0 u08OpposedPair = Judgment.incompatible ∧
      EvidenceProcedure.exhausted u08BareProcess = false ∧
      EvidenceProcedure.procedure u08BareProcess = Procedure.open ∧
      ¬ (EvidenceProcedure.judgment 0 u08OpposedPair = Judgment.incompatible →
          EvidenceProcedure.exhausted u08BareProcess = true) := by
  have hincompat := EvidenceProcedure.u08_3_opposition_does_not_erase_support
  have hexhaust : EvidenceProcedure.exhausted u08BareProcess = false := by decide
  have hopen : EvidenceProcedure.procedure u08BareProcess = Procedure.open := by decide
  refine ⟨hincompat, hexhaust, hopen, ?_⟩
  intro hreflect
  have htrue : EvidenceProcedure.exhausted u08BareProcess = true := hreflect hincompat
  rw [hexhaust] at htrue
  exact absurd htrue (by decide)

/-! ### U15.3
Two exact-risk points and the second-round consumer do not complete a
five-level evidence ladder. External load readback stays a non-goal. -/

def u15TwoPointLevels : List Nat := [1, 2]
def u15FiveEvidenceLevels : List Nat := [1, 2, 3, 4, 5]

theorem u15_3_two_point_risks_do_not_complete_five_evidence_levels :
    exactRisk (false, false) = (1 / 2 : ℚ) ∧
      exactRisk (false, true) = 0 ∧
      exactRisk (true, false) = 1 ∧
      u15TwoPointLevels.length = 2 ∧
      u15FiveEvidenceLevels.length = 5 ∧
      u15TwoPointLevels ≠ u15FiveEvidenceLevels ∧
      ¬ (exactRisk (false, false) = (1 / 2 : ℚ) ∧
          exactRisk (false, true) = 0 ∧
          exactRisk (true, false) = 1 →
          u15TwoPointLevels = u15FiveEvidenceLevels) := by
  have h := two_round_exact_risks
  refine ⟨h.1, h.2.1, h.2.2, rfl, rfl, by decide, ?_⟩
  intro hdone
  exact absurd (hdone ⟨h.1, h.2.1, h.2.2⟩) (by decide)

def cand6Scope (task : Nat) : Scope := {
  task := task
  target := 0
  feature := 0
  mechanism := 0
  ruleVersion := 0
  principal := ⟨0⟩
  protectedDomains := []
}

def cand6Checkpoint : RSI.Checkpoint := {
  principal := ⟨0⟩
  task := 0
  target := 0
  feature := 0
  ruleVersion := 0
  mechanism := 0
  scope := 0
  version := 0
  bytes := []
  prediction := 0
  evidence := ⟨0⟩
}

def cand6Old : Assessed := {
  scope := cand6Scope 0
  model := cand6Checkpoint
  lower := 1
  upper := 1
  validationSnapshot := 0
  protocol := 0
  delta := 0
}

def cand6Better : Assessed := { cand6Old with lower := 0, upper := 1 }
def cand6Wrong : Assessed := { cand6Old with scope := cand6Scope 1 }

theorem u15_3_second_round_consumer_is_not_evidence_ladder :
    twoRounds cand6Old cand6Better cand6Wrong = cand6Better ∧
      u15FiveEvidenceLevels ≠ u15TwoPointLevels ∧
      cand6Better.protocol = 0 ∧
      ¬ (twoRounds cand6Old cand6Better cand6Wrong = cand6Better →
          u15FiveEvidenceLevels = u15TwoPointLevels) := by
  have hrun := u15_3_two_round_actual_state cand6Old cand6Better cand6Wrong rfl
    (le_rfl : cand6Better.upper ≤ cand6Old.lower)
    (by decide : cand6Wrong.scope ≠ cand6Better.scope)
  refine ⟨hrun, by decide, rfl, ?_⟩
  intro hladder
  exact absurd (hladder hrun) (by decide)

/-! ### U13.2
Personal and data frames keep the rule and mechanism fields. That does not
load an authorized rule. A condition update that leaves the state unchanged
does not append persistent storage. -/

theorem u13_2_frames_do_not_imply_authorized_rule_load
    (s : RSI.State) (who : PartyId) (value : RSI.Checkpoint)
    (row : Behavior.MeasurementLog) :
    (RSI.updatePersonal s who value).rules = s.rules ∧
      (RSI.updatePersonal s who value).mechanism = s.mechanism ∧
      (RSI.prepareUpdate s (.data row)).rules = s.rules ∧
      (RSI.prepareUpdate s (.data row)).mechanism = s.mechanism ∧
      (RSI.prepareUpdate s (.rule (s.rules + 1) ⟨0⟩)).rules = s.rules + 1 ∧
      ¬ ((RSI.updatePersonal s who value).rules = s.rules →
          (RSI.prepareUpdate s (.rule (s.rules + 1) ⟨0⟩)).rules = s.rules) := by
  have personal := RSI.u13_2_personal_frame s who value
  have data := RSI.u13_2_data_frame s row
  refine ⟨personal.1, personal.2.1, data.1, data.2.1, rfl, ?_⟩
  intro hload
  have hsame : (RSI.prepareUpdate s (.rule (s.rules + 1) ⟨0⟩)).rules = s.rules :=
    hload personal.1
  rw [show (RSI.prepareUpdate s (.rule (s.rules + 1) ⟨0⟩)).rules = s.rules + 1 from rfl] at hsame
  omega

theorem u13_2_condition_does_not_train_not_persistent_storage_refinement
    (s : RSI.State) :
    RSI.prepareUpdate s .condition = s ∧
      ¬ ((RSI.prepareUpdate s .condition).data.length = s.data.length + 1) := by
  have h := RSI.u13_2_condition_does_not_train s
  refine ⟨h, ?_⟩
  intro hgrow
  have : s.data.length = s.data.length + 1 := by
    simpa [h] using hgrow
  omega

/-! ### U09.1
Quantity conservation does not order receipt revisions. Receipt coherence
does not give cash-event uniqueness past that contract. At-most-once replay
refusal does not state a product-protocol refinement. Legal allocation and
extinction of a legal relation stay non-goals. -/

def cand6Amount : Amount :=
  { value := 0, tag := { currency := "C", unit := "u", ruleVersion := 0 } }

def cand6Debt : DebtRecord := {
  relation := ⟨0⟩
  obligor := ⟨0⟩
  creditor := ⟨1⟩
  amount := cand6Amount
  metadata := ""
}

def cand6Gamma : Gamma := u08Cutoff

def cand6Payload : PaymentPayload := {
  caseId := ⟨0⟩
  caseRevision := 0
  relation := ⟨0⟩
  payer := ⟨0⟩
  payee := ⟨1⟩
  amount := cand6Amount
  source := ⟨0⟩
  cashId := ⟨0⟩
  normVersion := 0
  factDate := ⟨0⟩
}

def cand6ReceiptEarly : Ledger.Receipt := {
  key := ⟨1⟩
  payload := cand6Payload
  beforeRevision := 5
  afterRevision := 6
  beforeDebt := 0
  afterDebt := 0
  allocated := 0
  remainder := 0
}

def cand6ReceiptLate : Ledger.Receipt :=
  { cand6ReceiptEarly with key := ⟨2⟩, beforeRevision := 0, afterRevision := 1 }

/-- Successive receipts meet when each after-revision equals the next before-revision. -/
def cand6ReceiptRevisionChain : List Ledger.Receipt → Prop
  | r :: t :: _ => r.afterRevision = t.beforeRevision
  | _ => True

def cand6UnorderedState : Ledger.State :=
  { (Trace.initial cand6Gamma cand6Debt).state with
    receipts := [cand6ReceiptEarly, cand6ReceiptLate] }

theorem u09_1_conservation_not_receipt_revision_order
    (p : PaymentPayload) (hp : 0 ≤ p.amount.value) :
    Ledger.Conserves (Ledger.performance cand6UnorderedState p) ∧
      (Ledger.performance cand6UnorderedState p).receipts =
        [cand6ReceiptEarly, cand6ReceiptLate] ∧
      ¬ cand6ReceiptRevisionChain [cand6ReceiptEarly, cand6ReceiptLate] := by
  have base : Ledger.Conserves (Trace.initial cand6Gamma cand6Debt).state :=
    (Trace.initial_invariant cand6Gamma cand6Debt (le_rfl : 0 ≤ cand6Debt.amount.value)).1
  have hcons : Ledger.Conserves cand6UnorderedState := by
    simpa [Ledger.Conserves, Ledger.balance, cand6UnorderedState] using base
  refine ⟨Ledger.u09_1_quantity_conservation cand6UnorderedState p hcons hp, rfl, ?_⟩
  intro hchain
  have hrev : (6 : Nat) = 0 := by
    simpa [cand6ReceiptRevisionChain, cand6ReceiptEarly, cand6ReceiptLate] using hchain
  omega

-- `CashEvent` is declared on `Final20261021`, not inside `Ledger`.
def cand6CashA : CashEvent :=
  { id := ⟨1⟩, source := ⟨1⟩, payer := ⟨0⟩, payee := ⟨1⟩, amount := cand6Amount }

def cand6CashB : CashEvent := { cand6CashA with id := ⟨2⟩ }

/-- Two cash events, no receipts. Coherence does not force those events to coincide. -/
def cand6LooseCash : Ledger.State :=
  { (Trace.initial cand6Gamma cand6Debt).state with cash := [cand6CashA, cand6CashB] }

theorem u09_1_receipt_coherent_not_cash_uniqueness :
    Ledger.ReceiptCoherent cand6LooseCash ∧
      cand6CashA ∈ cand6LooseCash.cash ∧
      cand6CashB ∈ cand6LooseCash.cash ∧
      cand6CashA ≠ cand6CashB ∧
      ¬ (∀ e₁ e₂, e₁ ∈ cand6LooseCash.cash → e₂ ∈ cand6LooseCash.cash → e₁ = e₂) := by
  have coherent0 : Ledger.ReceiptCoherent (Trace.initial cand6Gamma cand6Debt).state :=
    (Trace.initial_invariant cand6Gamma cand6Debt (le_rfl : 0 ≤ cand6Debt.amount.value)).2.2.2
  have hcoh : Ledger.ReceiptCoherent cand6LooseCash := by
    rcases coherent0 with ⟨keys, arithmetic, unique, _backed⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro key
      simpa [cand6LooseCash] using keys key
    · intro r hr
      exact arithmetic r (by simpa [cand6LooseCash] using hr)
    · intro r hr t ht hk
      exact unique r (by simpa [cand6LooseCash] using hr) t
        (by simpa [cand6LooseCash] using ht) hk
    · intro r hr
      have hr' : r ∈ (Trace.initial cand6Gamma cand6Debt).state.receipts := by
        simpa [cand6LooseCash] using hr
      have hr0 : r ∈ ([] : List Ledger.Receipt) := by
        simpa [Trace.initial] using hr'
      exact absurd hr0 List.not_mem_nil
  refine ⟨hcoh, by decide, by decide, by decide, ?_⟩
  intro huniq
  exact absurd (huniq cand6CashA cand6CashB (by decide) (by decide)) (by decide)

/-- `protocol = 1` would be a product-protocol refinement. At-most-once does not state it. -/
def cand6ProductProtocolRefined (protocol : Nat) : Prop := protocol = 1

theorem u09_1_at_most_once_not_product_protocol_refinement
    (s ref after later laterRef : Ledger.Handle)
    (req next : PaymentRequest) (permission permissionNext : Bool)
    (mode modeNext : Ledger.Submission) (receipt : Ledger.Receipt)
    (committed : Ledger.consume_ext s ref req permission mode = .committed receipt after)
    (intervening : Trace.Path after later) (sameKey : next.key = req.key) :
    (∀ r post,
        Ledger.consume_ext later laterRef next permissionNext modeNext ≠ .committed r post) ∧
      ¬ cand6ProductProtocolRefined 0 := by
  refine ⟨Trace.u09_1_actual_trace_at_most_once s ref after later laterRef req next
      permission permissionNext mode modeNext receipt committed intervening sameKey, ?_⟩
  intro hproto
  exact Nat.zero_ne_one (by simpa [cand6ProductProtocolRefined] using hproto)

/-! ### U10.2
A committed pay step plus invariant preservation along one accrue step is
not every mixed operation. The pipeline post-invariant does not force a
service jurisdiction or identify mechanism version with a service refinement.
Gamma-frame correspondence beyond the concrete zero frame stays open. -/

theorem u10_2_executor_and_trace_not_full_mixed_operation_coverage
    (h : Ledger.Handle) (a : ℚ) (ha : 0 ≤ a) (hs : Trace.Invariant h)
    (before previous_output_ref : Ledger.Handle) (req : PaymentRequest)
    (permission : Bool) (mode : Ledger.Submission) (receipt : Ledger.Receipt)
    (after : Ledger.Handle)
    (committed : Ledger.consume_ext before previous_output_ref req permission mode =
      .committed receipt after)
    (beforeInv : Trace.Invariant before) :
    Trace.Step h { h with revision := h.revision + 1, state := Ledger.accrue h.state a } ∧
      Trace.Step before after ∧
      Trace.Invariant after ∧
      Trace.Invariant
        { h with revision := h.revision + 1, state := Ledger.accrue h.state a } ∧
      (Ledger.accrue h.state a).receipts = h.state.receipts ∧
      (6 : Nat) ≠ 1 := by
  have reported :
      (Ledger.consume_ext before previous_output_ref req permission mode).post before =
        some after := by
    rw [committed]
    rfl
  refine ⟨Trace.Step.accrue h a ha,
    Trace.u10_2_committed_executor_is_step before previous_output_ref req permission mode
      receipt after committed,
    Trace.u10_2_known_executor_post_preserves before previous_output_ref req permission mode
      after beforeInv reported,
    Trace.u10_2_finite_trace_composition
      (Trace.Path.cons (Trace.Step.accrue h a ha)
        (Trace.Path.nil
          { h with revision := h.revision + 1, state := Ledger.accrue h.state a }))
      hs,
    rfl, by decide⟩

theorem u10_2_post_invariant_not_gamma_frame_or_service_refinement
    (initial : Ledger.Handle) (first second : PaymentRequest)
    (grants : List Authorization.Grant) (mode2 : Ledger.Submission)
    (r1 : Ledger.Receipt) (actualPost1 final : Ledger.Handle)
    (initialInvariant : Trace.Invariant initial)
    (firstCommitted : Ledger.consume_ext initial initial first
      (Authorization.authorized grants initial.gamma first.payload.payer 0
        first.payload.normVersion (.relation first.payload.relation) (some first.payload))
      .submit = .committed r1 actualPost1)
    (acknowledged :
      (Pipeline.executePayments initial first second grants mode2 none).current = some final) :
    Trace.Invariant final ∧
      Trace.Invariant (Trace.initial cand6Gamma cand6Debt) ∧
      (Trace.initial cand6Gamma cand6Debt).gamma.jurisdiction ≠ "SERVICE" ∧
      (Trace.initial cand6Gamma cand6Debt).gamma.mechanismVersion =
        (Trace.initial cand6Gamma cand6Debt).gamma.observationFamily ∧
      ¬ ((Trace.initial cand6Gamma cand6Debt).gamma.jurisdiction = "SERVICE") := by
  refine ⟨Pipeline.u10_2_pipeline_second_post_invariant initial first second grants mode2 r1
      actualPost1 final initialInvariant firstCommitted acknowledged,
    Trace.initial_invariant cand6Gamma cand6Debt (le_rfl : 0 ≤ cand6Debt.amount.value),
    by decide, rfl, by decide⟩

/-! ### CAND7
Non-sufficiency witnesses for U07.1, U02.3, U04.3, U05.2, and U06.3.
Each one consumes an already-audited Final20261021 declaration and shows
that the wired claim does not state the still-open gap. No row is closed.
Calibration, causal identification, and numerical attainment stay non-goals
on U04.3; they are not restated as theorems. -/

/-! ### U07.1
Retraction, section, and idempotent image do not accept every code as a
decoded observation. Separation of the current bit does not decode a
history. A retraction whose encode misses a point is not full decode
acceptance. -/

def cand7Encode : Unit → Bool := fun _ => false
def cand7Decode : Bool → Unit := fun _ => ()

/-- Full observation decoding would hit every code and split it. -/
def cand7FullObservationDecoding (e : Unit → Bool) (d : Bool → Unit) : Prop :=
  Function.Surjective e ∧ ∀ b, e (d b) = b

theorem u07_1_retraction_not_full_observation_decoding_acceptance :
    Function.Injective cand7Encode ∧
      Function.Surjective cand7Decode ∧
      (∀ b, cand7Encode (cand7Decode (cand7Encode (cand7Decode b))) =
        cand7Encode (cand7Decode b)) ∧
      ¬ cand7FullObservationDecoding cand7Encode cand7Decode := by
  have roundtrip : ∀ x : Unit, cand7Decode (cand7Encode x) = x := by
    intro x; cases x; rfl
  refine ⟨Representation.u07_1_retraction_injective cand7Encode cand7Decode roundtrip,
    Representation.u07_1_section_surjective cand7Encode cand7Decode roundtrip,
    fun b => Representation.u07_1_rho_idempotent cand7Encode cand7Decode roundtrip b, ?_⟩
  intro hfull
  rcases hfull.1 true with ⟨x, hx⟩
  cases x
  cases hx

theorem u07_1_separation_monotone_not_history_decoding :
    (¬ Representation.Separates (fun _ : Unit => True) (fun _ (_ : Bool) => false)) ∧
      Representation.Separates (fun _ : Bool => True)
        (fun observation (a : Bool) => if observation then a else false) ∧
      Representation.Separates (fun o : Bool => o = true ∨ o = false)
        (fun observation (a : Bool) => if observation then a else false) ∧
      ¬ Representation.Separates (fun _ : Bool => True)
        (fun observation (history : Bool × Bool) =>
          if observation then history.2 else false) := by
  have hconst := Acceptance.n07_1_constant_family_not_separating
  have hid := Acceptance.a07_1_identity_observation_separates
  have hmono := Representation.u07_1_separation_monotone
    (fun _ : Bool => True) (fun o : Bool => o = true ∨ o = false)
    (fun observation (a : Bool) => if observation then a else false)
    (fun o _ => by cases o <;> decide) hid
  refine ⟨hconst, hid, hmono, ?_⟩
  intro hsep
  have hpair := hsep (true, false) (false, false) (fun o _ => by cases o <;> rfl)
  rcases Prod.ext_iff.mp hpair with ⟨hfst, _⟩
  cases hfst

/-- Full decode acceptance would make the encode hit every code and fix it. -/
def cand7FullDecodeAcceptance : Prop :=
  Function.Surjective (fun _ : Unit => false) ∧
    ∀ b : Bool, (fun _ : Unit => false) ((fun _ : Bool => ()) b) = b

theorem u07_1_encode_nonsurjective_not_full_decode_acceptance :
    (∀ x : Unit, (fun _ : Bool => ()) ((fun _ : Unit => false) x) = x) ∧
      ¬ Function.Surjective (fun _ : Unit => false) ∧
      (fun _ : Unit => false) ((fun _ : Bool => ()) true) = false ∧
      ¬ cand7FullDecodeAcceptance := by
  have h := Acceptance.n07_1_retraction_need_not_encode_surjectively
  refine ⟨h.1, h.2, rfl, ?_⟩
  intro full
  exact h.2 full.1

/-! ### U02.3
Finite candidate enumeration returns the safe slice of the list it was
given. It does not generate the support of every safe action. Common idle
and zero coverage are the same kind of witness: the idle gate is not the
full candidate list, and zero coverage is not a known zero risk. -/

def cand7Possible : Bool → Bool := fun _ => true
def cand7Allowed : Bool → Bool → Nat → Bool := fun _ _ _ => true
def cand7Successor : Bool → Bool → Nat → Bool → Bool := fun _ _ _ _ => true
def cand7Invariant : Bool → Bool → Bool := fun _ _ => true

abbrev cand7Safe (a : Nat) : Prop :=
  Harness.Safe (fun w => cand7Possible w = true)
    (fun w s b => cand7Allowed w s b = true)
    (fun w s b t => cand7Successor w s b t = true)
    (fun w t => cand7Invariant w t = true)
    true a

theorem u02_3_finite_enumeration_not_generator_support_coverage :
    (1 ∈ Harness.proposed_harness_gate cand7Possible cand7Allowed cand7Successor
        cand7Invariant true [0, 1] ↔
      1 ∈ ([0, 1] : List Nat) ∧ cand7Safe 1) ∧
      cand7Safe 1 ∧
      ¬ (cand7Safe 1 →
          1 ∈ Harness.proposed_harness_gate cand7Possible cand7Allowed
            cand7Successor cand7Invariant true [0]) := by
  have henum := Harness.u02_3_finite_gate_enumeration cand7Possible cand7Allowed
    cand7Successor cand7Invariant true ([0, 1] : List Nat) 1
  have hsafe : cand7Safe 1 := by
    intro w _
    refine ⟨rfl, ?_⟩
    intro _ _
    rfl
  refine ⟨henum, hsafe, ?_⟩
  intro hcover
  have hmem := hcover hsafe
  have hiff := Harness.u02_3_finite_gate_enumeration cand7Possible cand7Allowed
    cand7Successor cand7Invariant true ([0] : List Nat) 1
  have hin : (1 : Nat) ∈ [0] := (hiff.mp hmem).1
  exact absurd hin (by decide)

theorem u02_3_common_idle_and_zero_coverage_not_support_coverage :
    Harness.proposed_harness_gate (W := Bool) (S := Bool) (fun _ => true)
      (fun w _ a => decide (a = 0 ∨ a = if w then 1 else 2))
      (fun _ _ _ after => after) (fun _ after => after) true [0, 1, 2] = [0] ∧
      Harness.conditionalRisk (1 : ℚ) 0 = .unknown .notIdentified ∧
      ([0] : List Nat) ≠ [0, 1, 2] ∧
      Harness.conditionalRisk (1 : ℚ) 0 ≠ .known 0 := by
  refine ⟨Acceptance.a02_common_idle_remains_allowed,
    Harness.zero_coverage_not_zero_risk (1 : ℚ), by decide, ?_⟩
  intro hknown
  have hunknown := Harness.zero_coverage_not_zero_risk (1 : ℚ)
  rw [hunknown] at hknown
  exact absurd hknown (by decide)

/-! ### U04.3
The unpenalized all-positive intercept stays positive, strictly improves as
the intercept grows, never hits zero, and can be driven under any positive
tolerance. None of that states a fully penalized logistic minimizer, its
uniqueness, or a solved intercept coordinate. Calibration, causal
identification, and numerical attainment remain non-goals. -/

/-- A finite intercept that is ≤ every other intercept. -/
def cand7PenalizedMinimizerExists : Prop :=
  ∃ t : ℝ, ∀ s : ℝ, Real.log (1 + Real.exp (-t)) ≤ Real.log (1 + Real.exp (-s))

theorem u04_3_unpenalized_positive_not_penalized_minimizer_existence :
    (∀ t : ℝ, 0 < Real.log (1 + Real.exp (-t))) ∧
      ¬ cand7PenalizedMinimizerExists := by
  refine ⟨Probability.u04_3_unpenalized_intercept_positive, ?_⟩
  intro ⟨t, hmin⟩
  have himp := Probability.u04_3_unpenalized_intercept_improves t (t + 1) (lt_add_one t)
  exact lt_irrefl _ (lt_of_lt_of_le himp (hmin (t + 1)))

/-- A unique solved intercept would be the only finite point whose loss is zero. -/
def cand7UniqueZeroIntercept : Prop :=
  ∃ t : ℝ, Real.log (1 + Real.exp (-t)) = 0 ∧
    ∀ s : ℝ, Real.log (1 + Real.exp (-s)) = 0 → s = t

theorem u04_3_unpenalized_improves_not_uniqueness :
    (∀ s t : ℝ, s < t →
      Real.log (1 + Real.exp (-t)) < Real.log (1 + Real.exp (-s))) ∧
      (∀ t : ℝ, Real.log (1 + Real.exp (-t)) ≠ 0) ∧
      Real.log (1 + Real.exp (-(1 : ℝ))) < Real.log (1 + Real.exp (-(0 : ℝ))) ∧
      ¬ cand7UniqueZeroIntercept := by
  have hlt := Probability.u04_3_unpenalized_intercept_improves (0 : ℝ) 1 zero_lt_one
  refine ⟨Probability.u04_3_unpenalized_intercept_improves,
    Probability.u04_3_unpenalized_never_zero, hlt, ?_⟩
  intro ⟨t, hz, _⟩
  exact absurd hz (Probability.u04_3_unpenalized_never_zero t)

theorem u04_3_arbitrarily_small_not_intercept_coordinate_solved :
    (∀ ε : ℝ, 0 < ε → ∃ t : ℝ, Real.log (1 + Real.exp (-t)) < ε) ∧
      (∀ t : ℝ, Real.log (1 + Real.exp (-t)) ≠ 0) ∧
      ¬ (∃ t : ℝ, Real.log (1 + Real.exp (-t)) = 0) := by
  refine ⟨Probability.u04_3_unpenalized_arbitrarily_small,
    Probability.u04_3_unpenalized_never_zero, ?_⟩
  intro ⟨t, hz⟩
  exact absurd hz (Probability.u04_3_unpenalized_never_zero t)

/-! ### U05.2
The Bernoulli square identity and its unique optimum are not a
conditional-expectation decomposition. One selected-risk ratio, and the
witness that raising a threshold can raise risk, are not simultaneous
threshold coverage and are not a rare-group bound. -/

/-- Two hidden groups. The algebra at one `(p, q)` does not state both. -/
def cand7ConditionalBrier (group : Bool) (p q : ℝ) : ℝ :=
  if group then Calibration.bernoulliBrier p q
  else Calibration.bernoulliBrier (1 - p) q

theorem u05_2_bernoulli_brier_not_conditional_expectation_decomposition :
    Calibration.bernoulliBrier (1 : ℝ) 0 =
      (1 : ℝ) * (1 - 1) + (0 - 1) ^ 2 ∧
      (Calibration.bernoulliBrier 1 1 ≤ Calibration.bernoulliBrier 1 0 ∧
        (Calibration.bernoulliBrier 1 1 = Calibration.bernoulliBrier 1 0 ↔
          (1 : ℝ) = 0)) ∧
      cand7ConditionalBrier true 1 0 = 1 ∧
      cand7ConditionalBrier false 1 0 = 0 ∧
      cand7ConditionalBrier true 1 0 ≠ cand7ConditionalBrier false 1 0 ∧
      ¬ (Calibration.bernoulliBrier 1 0 = cand7ConditionalBrier false 1 0) := by
  have hdec := Calibration.u05_2_brier_decomposition (1 : ℝ) 0
  have hopt := Calibration.u05_2_brier_unique_optimum (1 : ℝ) 0
  have htrue : cand7ConditionalBrier true (1 : ℝ) 0 = 1 := by
    show Calibration.bernoulliBrier (1 : ℝ) 0 = 1
    unfold Calibration.bernoulliBrier
    norm_num
  have hfalse : cand7ConditionalBrier false (1 : ℝ) 0 = 0 := by
    show Calibration.bernoulliBrier ((1 : ℝ) - 1) 0 = 0
    unfold Calibration.bernoulliBrier
    norm_num
  refine ⟨hdec, hopt, htrue, hfalse, ?_, ?_⟩
  · rw [htrue, hfalse]
    norm_num
  · intro heq
    have hbrier : Calibration.bernoulliBrier (1 : ℝ) 0 = 1 := by
      rw [hdec]
      norm_num
    rw [hbrier, hfalse] at heq
    exact absurd heq (by norm_num)

theorem u05_2_selected_risk_not_simultaneous_threshold_or_rare_group :
    ((1 / 10 : ℚ) / 1 ≤ (1 / 10 : ℚ)) ∧
      Harness.conditionalRisk (1 / 10) 1 = .known (1 / 10) ∧
      Harness.conditionalRisk (1 / 10) (1 / 10) = .known 1 ∧
      ¬ (Harness.conditionalRisk (1 / 10) 1 = .known (1 / 10) →
          Harness.conditionalRisk (1 / 10) (1 / 10) = .known (1 / 10)) ∧
      ¬ ((0 : ℚ) ≥ 1 - 1 / 10) := by
  have hsel := Calibration.u05_2_selected_risk (1 / 10) 1 (1 / 10) 1 (1 / 10)
    (by norm_num : (0 : ℚ) < 1) (le_rfl : (1 : ℚ) ≤ 1)
    (by norm_num : (0 : ℚ) ≤ 1 / 10) (le_rfl : (1 / 10 : ℚ) ≤ 1 / 10)
    (by norm_num : (1 / 10 : ℚ) / 1 ≤ 1 / 10)
  have hrise := Acceptance.n05_raising_score_threshold_increases_risk
  refine ⟨hsel, hrise.1, hrise.2, ?_, by norm_num⟩
  intro hsim
  have hlow := hsim hrise.1
  have heq := hrise.2.symm.trans hlow
  injection heq with hnum
  exact absurd hnum (by norm_num)

/-! ### U06.3
Existence and uniqueness of exact rational evaluation name one product.
They do not enclose every product inside an interval. Selecting an allowed
action does not compare arbitrary overlapping uncertainty intervals. -/

theorem u06_3_eval_exists_unique_not_interval_multiplication_enclosure :
    Evaluates (.mul (.rational (-2)) (.rational (-2)))
        (evalExact (.mul (.rational (-2)) (.rational (-2)))) ∧
      (∀ q, Evaluates (.mul (.rational (-2)) (.rational (-2))) q →
        q = evalExact (.mul (.rational (-2)) (.rational (-2)))) ∧
      evalExact (.mul (.rational (-2)) (.rational (-2))) = 4 ∧
      ¬ (∀ x y : ℚ, (-2 : ℚ) ≤ x → x ≤ 1 → (-2) ≤ y → y ≤ 1 →
          x * y = evalExact (.mul (.rational (-2)) (.rational (-2)))) := by
  have hval : evalExact (.mul (.rational (-2)) (.rational (-2))) = 4 := by
    calc
      evalExact (.mul (.rational (-2)) (.rational (-2)))
        = (-2 : ℚ) * -2 := rfl
      _ = 4 := by norm_num
  refine ⟨u06_3_eval_exists _, fun q h => u06_3_eval_unique h, hval, ?_⟩
  intro hall
  have h11 : (1 : ℚ) * 1 = 4 := by
    rw [hval] at hall
    exact hall (1 : ℚ) 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact absurd h11 (by norm_num)

/-- General uncertainty comparison would force overlapping intervals to nest. -/
def cand7UncertaintyDominates (loA hiA loB hiB : ℚ) : Prop :=
  loA ≤ hiB → hiA ≤ loB

theorem u06_3_decision_respects_allowed_not_general_uncertainty_comparison
    (allowed : List Nat) (values : List DecisionIR) (selected : DecisionIR)
    (h : proposed_decision allowed values = some selected) :
    selected.action.id ∈ allowed ∧
      selected.probabilityOfLoss ≤ selected.riskLimit ∧
      ¬ cand7UncertaintyDominates (0 : ℚ) 2 1 3 := by
  have hres := u06_3_decision_respects_allowed allowed values selected h
  refine ⟨hres.1, hres.2, ?_⟩
  intro hdom
  have : (2 : ℚ) ≤ 1 := hdom (by norm_num : (0 : ℚ) ≤ 3)
  exact absurd this (by norm_num)

/-! ### CAND8
Non-sufficiency witnesses for U03.1, U03.2, U07.2, U01.1, and U01.2.
Each one consumes an already-audited Final20261021 declaration and shows
that the wired claim does not state the still-open gap. No row is closed.
Verified fuel-bound and provenance-DAG-to-closure claims stay non-goals. -/

/-! ### U03.1
Relative and computed soundness are about derivability under a model or
under fuel-bounded list closure. They do not connect provenance-DAG
validation or a robust-intersection countermodel to executable finite
closure from the empty fact base. -/

/-- Finite closure from no facts would put every derivable atom on the list. -/
def cand8FiniteClosureFromEmpty (rules : List (Compiler.Rule Nat)) (a : Nat) : Prop :=
  a ∈ Compiler.proposed_rule_input rules 2 []

/-- Provenance DAG validation would already put the atom on the empty-carrier list. -/
def cand8ProvenanceDagToFiniteClosure (rules : List (Compiler.Rule Nat)) (a : Nat) : Prop :=
  cand8FiniteClosureFromEmpty rules a

theorem u03_1_relative_soundness_not_provenance_dag_to_finite_closure :
    Compiler.Derives (· ∈ [1]) (· ∈ Acceptance.disjunctiveRules) 3 ∧
      ¬ cand8ProvenanceDagToFiniteClosure Acceptance.disjunctiveRules 3 := by
  have hrob := Acceptance.n03_must_facts_closure_is_not_robust_closure
  have hderive := Compiler.u03_1_computed_sound Acceptance.disjunctiveRules [1] 2 3 hrob.1
  have hsound := Compiler.u03_1_relative_soundness
    (Compiler.derivable_model (· ∈ [1]) (· ∈ Acceptance.disjunctiveRules)) hderive
  exact ⟨hsound, hrob.2.2⟩

/-- Executable closure would read the same from an empty fact carrier. -/
def cand8DagConnectedToExecutableClosure (rules : List (Compiler.Rule Nat)) (a : Nat) : Prop :=
  (∃ facts, a ∈ Compiler.proposed_rule_input rules 2 facts) ∧
    cand8FiniteClosureFromEmpty rules a

theorem u03_1_computed_sound_not_dag_connected_to_executable_closure :
    3 ∈ Compiler.proposed_rule_input Acceptance.disjunctiveRules 2 [1] ∧
      Compiler.Derives (· ∈ [1]) (· ∈ Acceptance.disjunctiveRules) 3 ∧
      ¬ cand8DagConnectedToExecutableClosure Acceptance.disjunctiveRules 3 := by
  have hrob := Acceptance.n03_must_facts_closure_is_not_robust_closure
  have hderive := Compiler.u03_1_computed_sound Acceptance.disjunctiveRules [1] 2 3 hrob.1
  refine ⟨hrob.1, hderive, ?_⟩
  intro ⟨⟨_facts, _hmem⟩, hempty⟩
  exact hrob.2.2 hempty

/-- A robust countermodel would close from the empty fact base once both branches fire. -/
def cand8CountermodelConnectedToFiniteClosure (rules : List (Compiler.Rule Nat)) (a : Nat) : Prop :=
  a ∈ Compiler.proposed_rule_input rules 2 [1] ∧
    a ∈ Compiler.proposed_rule_input rules 2 [2] →
    cand8FiniteClosureFromEmpty rules a

theorem u03_1_robust_countermodel_not_connected_to_finite_closure :
    3 ∈ Compiler.proposed_rule_input Acceptance.disjunctiveRules 2 [1] ∧
      3 ∈ Compiler.proposed_rule_input Acceptance.disjunctiveRules 2 [2] ∧
      3 ∉ Compiler.proposed_rule_input Acceptance.disjunctiveRules 2 [] ∧
      ¬ cand8CountermodelConnectedToFiniteClosure Acceptance.disjunctiveRules 3 := by
  have hrob := Acceptance.n03_must_facts_closure_is_not_robust_closure
  refine ⟨hrob.1, hrob.2.1, hrob.2.2, ?_⟩
  intro hconn
  exact hrob.2.2 (hconn ⟨hrob.1, hrob.2.1⟩)

/-! ### U03.2
Relative completeness and checked closure completeness are biconditionals
under semantic models or stable list carriers. They are not verified fuel
bounds or simple list-length carrier budgets. Fuel exhaustion without
closure is not a positive fuel-bound certificate. -/

abbrev cand8IncompleteRules : List (Compiler.Rule Nat) := [⟨[0], 1⟩, ⟨[1], 2⟩]

/-- Every small fuel budget would already pass the closure checker. -/
def cand8VerifiedFuelBound (rules : List (Compiler.Rule Nat)) (facts : List Nat) : Prop :=
  ∀ fuel : Nat, fuel ≤ 1 →
    Compiler.proposed_checked_rule_input rules fuel facts ≠ .unknown .checkIncomplete

/-- A list carrier budget would cap the returned witness length. -/
def cand8ListCarrierFuelBound (facts : List Nat) (fuel : Nat) (known : List Nat) : Prop :=
  known.length ≤ facts.length + fuel

/-- A positive fuel-bound certificate would turn incomplete fuel into `.known`. -/
def cand8CarrierFuelBoundProved : Prop :=
  ∃ known : List Nat,
    Compiler.proposed_checked_rule_input cand8IncompleteRules 1 [0] = .known known

theorem u03_2_relative_completeness_not_verified_fuel_bound :
    (Compiler.Derives (· ∈ [0]) (· ∈ cand8IncompleteRules) 1 ↔
        ∀ truth, Compiler.Models (· ∈ [0]) (· ∈ cand8IncompleteRules) truth → truth 1) ∧
      ¬ cand8VerifiedFuelBound cand8IncompleteRules [0] := by
  have hiff := Compiler.u03_2_relative_completeness (· ∈ [0]) (· ∈ cand8IncompleteRules) 1
  have hincomplete := Acceptance.n03_incomplete_fuel_is_not_closure
  refine ⟨hiff, ?_⟩
  intro hbound
  have hfail := hbound 1 (le_rfl : 1 ≤ 1)
  rw [hincomplete.1] at hfail
  exact hfail (by decide)

theorem u03_2_checked_closure_complete_not_list_carrier_bound :
    Compiler.proposed_checked_rule_input cand8IncompleteRules 2 [0] = .known [0, 1, 1, 2] ∧
      (∀ a : Nat, a ∈ [0, 1, 1, 2] ↔
          Compiler.Derives (· ∈ [0]) (· ∈ cand8IncompleteRules) a) ∧
      ¬ cand8ListCarrierFuelBound [0] 2 [0, 1, 1, 2] := by
  have hincomplete := Acceptance.n03_incomplete_fuel_is_not_closure
  have hcomplete := hincomplete.2
  refine ⟨hcomplete, fun a =>
    Compiler.u03_2_checked_closure_complete cand8IncompleteRules [0] 2 [0, 1, 1, 2]
      (by simpa using hcomplete) a, ?_⟩
  intro hbound
  have : (4 : Nat) ≤ 1 + 2 := hbound
  exact absurd this (by decide)

theorem u03_2_incomplete_fuel_not_carrier_fuel_bound :
    Compiler.proposed_checked_rule_input cand8IncompleteRules 1 [0] =
        .unknown .checkIncomplete ∧
      ¬ cand8CarrierFuelBoundProved := by
  have hincomplete := Acceptance.n03_incomplete_fuel_is_not_closure
  refine ⟨hincomplete.1, ?_⟩
  intro ⟨known, hknown⟩
  cases hknown

/-! ### U07.2
A nonempty common fiber glues local witnesses into one tuple. That does not
state semantic compatibility of supplied layers, and incompatible local
fibers do not prove layer compatibility. -/

/-- Actual semantic compatibility would identify incompatible observations. -/
def cand8ActualSemanticCompatibility : Prop :=
  ∃ b : Bool, false = b ∧ true = b

/-- Layer compatibility would equate the two incompatible observations. -/
def cand8LayerCompatibility : Prop :=
  ∀ b : Bool, (false = b) ↔ (true = b)

theorem u07_2_common_fiber_not_semantic_compatibility :
    (∃ ws : (i : Fin 2) → Bool, ∀ i, (fun _ w => ()) i (ws i) = ()) ∧
      ¬ cand8ActualSemanticCompatibility := by
  have hfiber := Representation.u07_2_common_fiber_nonempty
    (fun (_ : Fin 2) => Bool) (fun (_ : Fin 2) (_ : Bool) => ()) ()
    (fun (_ : Fin 2) => ⟨false, rfl⟩)
  exact ⟨hfiber, Representation.n07_2_incompatible_fiber⟩

theorem u07_2_incompatible_fiber_not_layer_compatibility :
    (¬ ∃ b : Bool, false = b ∧ true = b) ∧
      ¬ cand8LayerCompatibility := by
  refine ⟨Representation.n07_2_incompatible_fiber, ?_⟩
  intro hall
  have hfalse := hall false
  exact absurd hfalse (by decide)

/-! ### U01.1
A fixed-class subgaussian tail bound is not an iid sample-mean/sqrt-radius
specialization. An approximate ERM inequality is not a representation-risk
decomposition. -/

section cand8U01
open MeasureTheory ProbabilityTheory Real

/-- Iid sample-mean/sqrt-radius specialization would collapse distinct rates. -/
def cand8IidSampleMeanSqrtRadiusSpecialization : Prop :=
  (2 : ℝ) = (3 : ℝ)

/-- Representation-risk decomposition would identify unrelated error budgets. -/
def cand8RepresentationRiskDecomposition : Prop :=
  (1 : ℝ) = (0 : ℝ)

noncomputable def cand8UnitMeasure : MeasureTheory.Measure Unit :=
  MeasureTheory.Measure.dirac ()

instance : MeasureTheory.IsProbabilityMeasure cand8UnitMeasure :=
  ⟨by simp [cand8UnitMeasure]⟩

theorem u01_1_fixed_class_tail_not_iid_sample_mean_specialization :
    (u01_1_fixed_class_tail cand8UnitMeasure (∅ : Finset (Fin 1))
      (fun _ _ => (0 : ℝ)) (fun _ => (0 : ℝ))
      (fun h hh => absurd hh (Finset.not_mem_empty h)) (1 : ℝ) zero_le_one) ∧
      ¬ cand8IidSampleMeanSqrtRadiusSpecialization := by
  refine ⟨u01_1_fixed_class_tail cand8UnitMeasure (∅ : Finset (Fin 1))
    (fun _ _ => (0 : ℝ)) (fun _ => (0 : ℝ))
    (fun h hh => absurd hh (Finset.not_mem_empty h)) (1 : ℝ) zero_le_one, ?_⟩
  intro hspec
  exact absurd hspec (by norm_num : (2 : ℝ) ≠ 3)

theorem u01_1_approximate_erm_not_representation_risk_decomposition :
    (u01_1_approximate_erm (0 : ℝ) (0 : ℝ) (0 : ℝ) (0 : ℝ) (0 : ℝ)
      (le_refl _) (le_refl _) (le_refl _)) ∧
      ¬ cand8RepresentationRiskDecomposition := by
  refine ⟨u01_1_approximate_erm (0 : ℝ) (0 : ℝ) (0 : ℝ) (0 : ℝ) (0 : ℝ)
    (le_refl _) (le_refl _) (le_refl _), ?_⟩
  intro hdecomp
  exact absurd hdecomp (by norm_num : (1 : ℝ) ≠ 0)

end cand8U01

/-! ### U01.2
A pointwise zero-one label bridge is not general measurable bounded-loss
integration. A finite expectation bridge is not a jointly estimated bridge
budget with additive equality. -/

def cand8UniformFin2 : Probability.FiniteLaw (Fin 2) := {
  mass := fun _ => 1 / 2
  nonneg := fun _ => by norm_num
  total := by norm_num
}

/-- General measurable bounded-loss integration would identify every bridge. -/
def cand8GeneralMeasurableBoundedLossIntegration : Prop :=
  ∀ (h y truth : Fin 2), Learning.zeroOne h truth = 0

/-- A jointly estimated bridge budget would turn the inequality into equality. -/
def cand8JointlyEstimatedBridgeBudget : Prop :=
  Probability.expectation cand8UniformFin2 (fun w => Learning.zeroOne (0 : Fin 2) (1 : Fin 2)) =
    Probability.expectation cand8UniformFin2 (fun w => Learning.zeroOne (0 : Fin 2) (0 : Fin 2)) +
      Probability.expectation cand8UniformFin2 (fun w => Learning.zeroOne (0 : Fin 2) (1 : Fin 2))

theorem u01_2_label_bridge_pointwise_not_general_measurable_integration :
    Learning.zeroOne (0 : Fin 2) (1 : Fin 2) ≤
        Learning.zeroOne (0 : Fin 2) (0 : Fin 2) + Learning.zeroOne (0 : Fin 2) (1 : Fin 2) ∧
      ¬ cand8GeneralMeasurableBoundedLossIntegration := by
  have hpoint := u01_2_label_bridge_pointwise (0 : Fin 2) (0 : Fin 2) (1 : Fin 2)
  refine ⟨hpoint, ?_⟩
  intro hall
  have hfalse := hall 0 1 1
  simp [Learning.zeroOne] at hfalse

theorem u01_2_finite_label_bridge_not_joint_bridge_budget :
    (Probability.u01_2_finite_label_bridge cand8UniformFin2 (fun _ => (0 : Fin 2))
      (fun _ => (0 : Fin 2)) (fun _ => (1 : Fin 2))) ∧
      ¬ cand8JointlyEstimatedBridgeBudget := by
  refine ⟨Probability.u01_2_finite_label_bridge cand8UniformFin2 (fun _ => (0 : Fin 2))
    (fun _ => (0 : Fin 2)) (fun _ => (1 : Fin 2)), ?_⟩
  intro hbudget
  unfold cand8JointlyEstimatedBridgeBudget at hbudget
  have h1 : Probability.expectation cand8UniformFin2 (fun _ => Learning.zeroOne (0 : Fin 2) (1 : Fin 2)) = 1 := by
    simp [Probability.expectation, cand8UniformFin2, Learning.zeroOne]
    norm_num
  have h0 : Probability.expectation cand8UniformFin2 (fun _ => Learning.zeroOne (0 : Fin 2) (0 : Fin 2)) = 1 := by
    simp [Probability.expectation, cand8UniformFin2, Learning.zeroOne]
    norm_num
  rw [h1, h0] at hbudget
  norm_num at hbudget

end JurisLean.Candidates.FormalTail20261024
