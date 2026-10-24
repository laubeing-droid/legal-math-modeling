import JurisLean.Candidates.Final20261021.Decision
import JurisLean.Candidates.Final20261021.Progress
import JurisLean.Candidates.Final20261021.Temporal

/-!
Formal-tail candidates for round formal_tail_20261024.

These declarations are not in the live tip-pin axiom audit
(commit e87543d836cd3cf83bbb5a65b74e47d9bfe31865, audit id 39933015422,
job 120345670150). They are not wired as clause declarations.
They do not set discharges_archived_manuscript_gaps.
They do not close an OPEN_FORMAL_TAIL row.
Local text is not a Lean PASS. CI is the authority.
-/

namespace JurisLean.Candidates.FormalTail20261024

open JurisLean.Candidates.Final20261021
open JurisLean.Candidates.Final20261021.Decision
open JurisLean.Candidates.Final20261021.Progress
open JurisLean.Candidates.Final20261021.Temporal

/-- U08.1 candidate. A record stamped strictly after the record cutoff is
not visible. This is not a mutable-current-status countermodel and it does
not close U08.1. -/
theorem u08_1_recorded_after_cutoff_not_visible (g : Gamma) (e : VersionRecord)
    (h : g.recordCutoff.ticks < e.recordedAt.ticks) :
    visible g e = false := by
  unfold visible
  apply decide_eq_false
  rintro ⟨hle, _⟩
  exact not_le_of_gt h hle

/-- U10.3 candidate. A zero-step ranked path does not change the state.
Business-observation faithfulness is not stated. Fairness and external
response remain non-goals of the clause. This does not close U10.3. -/
theorem u10_3_zero_step_ranked_path_is_identity {S : Type} (rank : S → Nat) {s t : S}
    (h : RankedPath rank s 0 t) : s = t := by
  induction h with
  | nil s => rfl
  | cons decrease rest ih => omega

/-- U06.4 candidate. Increasing net, threshold strictly above 1, q at most 1:
the target is not met. Not an audited declaration, so U06.4 stays open. -/
theorem u06_4_increasing_threshold_above_one_excludes (q b l k target : ℝ)
    (hlb : l < b) (hq : q ≤ 1)
    (hout : 1 < (target + k - l) / (b - l)) :
    ¬ target ≤ net q b l k := by
  intro h
  have hle := (u06_4_threshold_increasing q b l k target hlb).mp h
  linarith

/-- U06.4 candidate. Increasing net, threshold at most 0, q at least 0:
the target is met. Not an audited declaration, so U06.4 stays open. -/
theorem u06_4_increasing_threshold_at_most_zero_includes (q b l k target : ℝ)
    (hlb : l < b) (hq : 0 ≤ q)
    (hout : (target + k - l) / (b - l) ≤ 0) :
    target ≤ net q b l k := by
  apply (u06_4_threshold_increasing q b l k target hlb).mpr
  linarith

/-- U06.4 candidate. Decreasing net, threshold strictly below 0, q at least 0:
the target is not met. Not an audited declaration, so U06.4 stays open. -/
theorem u06_4_decreasing_threshold_below_zero_excludes (q b l k target : ℝ)
    (hbl : b < l) (hq : 0 ≤ q)
    (hout : (target + k - l) / (b - l) < 0) :
    ¬ target ≤ net q b l k := by
  intro h
  have hle := (u06_4_threshold_decreasing q b l k target hbl).mp h
  linarith

/-- U06.4 candidate. Decreasing net, threshold at least 1, q at most 1:
the target is met. Not an audited declaration, so U06.4 stays open. -/
theorem u06_4_decreasing_threshold_at_least_one_includes (q b l k target : ℝ)
    (hbl : b < l) (hq : q ≤ 1)
    (hout : 1 ≤ (target + k - l) / (b - l)) :
    target ≤ net q b l k := by
  apply (u06_4_threshold_decreasing q b l k target hbl).mpr
  linarith

/-- U12.2 candidate witness. Halving moves 1 closer to 0 and fixes 0.
Not a metric damping theorem and not a close of U12.2. -/
theorem u12_2_halving_damps_toward_zero :
    |(1 / 2 : ℝ)| < |(1 : ℝ)| ∧ (0 : ℝ) / 2 = 0 := by
  norm_num

/-- U12.2 candidate witness. Negation swaps 1 and -1 and returns.
Not a metric oscillation theorem and not a close of U12.2. -/
theorem u12_2_negation_orbit_oscillates :
    (fun x : ℝ => -x) (1 : ℝ) = -1 ∧
      (fun x : ℝ => -x) (-1) = (1 : ℝ) ∧
      (1 : ℝ) ≠ -1 := by
  norm_num

/-- U12.2 candidate witness. Translation by 1 has no fixed point.
Not a noncontraction-sufficiency theorem and not a close of U12.2. -/
theorem u12_2_shift_has_no_fixed_point (x : ℝ) : x + 1 ≠ x := by
  linarith

/-- U14.2 candidate. The strict positive-total hypothesis fails at zero.
Endogenous-size and common-cause counterexamples are not stated.
This does not close U14.2. -/
theorem u14_2_zero_N_rejects_positive_hypothesis (N : ℝ) (h : N = 0) : ¬ 0 < N := by
  rw [h]
  exact lt_irrefl (0 : ℝ)

end JurisLean.Candidates.FormalTail20261024
