import JurisLean.Candidates.Final20261021.Decision
import JurisLean.Candidates.Final20261021.Feedback
import JurisLean.Candidates.Final20261021.Learning
import JurisLean.Candidates.Final20261021.Policy
import JurisLean.Candidates.Final20261021.Progress
import JurisLean.Candidates.Final20261021.Temporal

/-!
Formal-tail source for formal_tail_20261024, candidate ids
U08.1, U10.3, U06.4, U12.2, U14.2 (archive order).

These declarations are not in the live tip-pin axiom audit.
That audit's recorded commit is 27849d3f228ec3665da16a6aa0b801672421dca2,
its id is 40079130550, and its job id is 120828801547.
This header does not attest that audit. No landed axiom-audit text
names JurisLean.Candidates.FormalTail20261024.
They are not wired as tip-pin clause declarations.
A later gate SUCCESS on this file does not close an OPEN_FORMAL_TAIL row.
They do not set discharges_archived_manuscript_gaps.
They do not close step 2.
Local text is not a Lean PASS. CI is the authority.
-/

namespace JurisLean.Candidates.FormalTail20261024

open JurisLean.Candidates.Final20261021
open JurisLean.Candidates.Final20261021.Decision
open JurisLean.Candidates.Final20261021.Feedback
open JurisLean.Candidates.Final20261021.Learning
open JurisLean.Candidates.Final20261021.Policy
open JurisLean.Candidates.Final20261021.Progress
open JurisLean.Candidates.Final20261021.Temporal

/-! ### U08.1
Late records stay invisible at the cutoff. Disguising one as then-known
changes applicability. Reading the latest version as current status
disagrees with the cutoff query. The append lemma is a consumer of the
audited `u08_1_selection_stable`. None of this is in the tip-pin audit,
so U08.1 stays OPEN_FORMAL_TAIL. -/

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

/-! ### U10.3
A zero-step ranked path is the identity and does not strictly decrease rank.
Business-observed length is the sum of per-operation abstract steps and is a
consumer of the audited simulation-length bound. A zero observation is not
positive progress.
公平 and 外部响应 are explicit non-goals of this clause (exact_scope: 另证).
These declarations are not in tip-pin audit 40079130550 / job 120828801547.
They do not close U10.3. -/

theorem u10_3_zero_step_ranked_path_is_identity {S : Type} (rank : S → Nat) {s t : S}
    (h : RankedPath rank s 0 t) : s = t := by
  cases h with
  | nil _ => rfl

theorem u10_3_zero_step_prohibits_strict_progress {S : Type} (rank : S → Nat) (s : S) :
    ¬ ∃ t, RankedPath rank s 0 t ∧ rank t < rank s := by
  intro ⟨t, hpath, hlt⟩
  have hs : s = t := u10_3_zero_step_ranked_path_is_identity rank hpath
  subst hs
  exact lt_irrefl (rank t) hlt

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

/-! ### U06.4
Out-of-range corollaries of the audited slope identities, then the same facts
for every q in the unit interval (empty or full intersection). Still not in
the tip-pin audit, so U06.4 stays OPEN_FORMAL_TAIL. -/

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
necessity. Not in the tip-pin audit, so U12.2 stays OPEN_FORMAL_TAIL. -/

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

/-! ### U14.2
`N = 0` rejects the strict positive total. Equal sizes chosen after the fact
are not the fixed `99/1` effective-size witness. A shared copy keeps variance
`1/4`, above the independent `1/(4n)`. Consumers of the audited cluster
witness and the audited copy-variance lemmas. Not in the tip-pin audit, so
U14.2 stays OPEN_FORMAL_TAIL. -/

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

end JurisLean.Candidates.FormalTail20261024
