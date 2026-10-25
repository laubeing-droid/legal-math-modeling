import JurisLean.Candidates.Final20261021.Decision
import JurisLean.Candidates.Final20261021.Feedback
import JurisLean.Candidates.Final20261021.Iteration
import JurisLean.Candidates.Final20261021.Learning
import JurisLean.Candidates.Final20261021.Ledger
import JurisLean.Candidates.Final20261021.Policy
import JurisLean.Candidates.Final20261021.Probability
import JurisLean.Candidates.Final20261021.Progress
import JurisLean.Candidates.Final20261021.RSI
import JurisLean.Candidates.Final20261021.Temporal

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
def u08_2_answer (v : Bool) (_h : Unit) (_q : Unit) : Nat := if v then 1 else 0
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
    RSI.conditionalEstimate [1, 1] [0, 1] = Result.known (1 / 2 : ℚ) ∧
      RSI.conditionalEstimate [1, 1] [0, 0] = Result.known (0 : ℚ) ∧
      RSI.conditionalEstimate [1, 1] [0, 1] ≠ RSI.conditionalEstimate [1, 1] [0, 0] := by
  refine ⟨rfl, rfl, ?_⟩
  decide

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
  decide

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
    (law : Probability.FiniteLaw Ω) (old new : Ω → Y) (loss : Y → Ω → ℝ)
    (same : ∀ x, old x = new x) :
    Probability.expectation law (fun x => loss (old x) x) =
      Probability.expectation law (fun x => loss (new x) x) :=
  u15_2_preserved_predictions_equal_risk law old new loss same

end JurisLean.Candidates.FormalTail20261024
