import JurisLean.FiniteHorizonAdequacy
import JurisLean.UnifiedFeedbackBridge
import JurisLean.FeedbackHistoryBridge

/-!
A finite-horizon execution of the actual stochastic feedback model.
The same sampled Bool outcome is recorded in the full game history, replayed
through ClosedLoop.update, and used for the personal learning parameter.
The resulting numeric law is proved equal to the actual ClosedLoop.step
iteration, rather than postulated as a readout contract.
-/

namespace LegalMath20261109.FiniteGameFeedback

open MeasureTheory ProbabilityTheory
open LegalMath.FiniteHorizon
open LegalMath20261108
open scoped ENNReal ProbabilityTheory

noncomputable section

abbrev NumericState := UnifiedFeedbackBridge.State
abbrev BitHistory (T : Nat) := History T Unit Bool (fun _ => Bool)
abbrev BitPlan (T : Nat) := BehavioralPlan T Unit (fun _ => Bool) (fun _ => Bool)

local instance historyMeasurable (T : Nat) : MeasurableSpace (BitHistory T) := ⊤

/-- This is the original outcome measure, converted losslessly on finite Bool. -/
def coinPMF (s : NumericState) : PMF Bool :=
  (UnifiedFeedbackBridge.coin s).toPMF

@[simp] theorem coinPMF_toMeasure (s : NumericState) :
    (coinPMF s).toMeasure = UnifiedFeedbackBridge.coin s :=
  Measure.toPMF_toMeasure _

/-- Replay uses the actual update; it does not draw a second feedback variable. -/
def replay {T : Nat} (s₀ : NumericState) (h : BitHistory T) : NumericState :=
  h.val.foldl (fun s e => UnifiedFeedbackBridge.after s e.2) s₀

def game (T : Nat) (s₀ : NumericState) :
    Game T Unit Bool (fun _ => Bool) (fun _ => Bool) where
  initial := false
  signal := fun _ _ y => y
  transition := fun h _ => coinPMF (replay s₀ h)

@[simp] theorem replay_initial (T : Nat) (s₀ : NumericState) :
    replay s₀ (game T s₀).initialHistory = s₀ := rfl

theorem replay_advance {T : Nat} (s₀ : NumericState) (h : BitHistory T)
    (ht : h.val.length < T) (a : Unit → Bool) (y : Bool) :
    replay s₀ ((game T s₀).advance h ht a y) =
      ClosedLoop.update UnifiedFeedbackBridge.model (replay s₀ h, (a (), y)) := by
  simp only [replay, Game.advance, List.foldl_append, List.foldl]
  rfl

/-- The learning coordinate can be reconstructed from only the personal record. -/
def privateParameter {T : Nat} (q₀ : ℝ) (r : PersonalRecord T Bool Bool) : ℝ :=
  r.2.val.foldl
    (fun q e => SequentialFeedback.learnExample q (ClosedLoop.RepaymentExample.bit e.2)) q₀

theorem privateParameter_append {T : Nat} (q₀ : ℝ)
    (r : PersonalRecord T Bool Bool) (ht : stage r < T) (a y : Bool) :
    privateParameter q₀ (append r ht a y) =
      UnifiedFeedbackBridge.model.learn (privateParameter q₀ r)
        (ClosedLoop.RepaymentExample.bit y) := by
  simp only [privateParameter, append, List.foldl_append, List.foldl]
  rfl

private theorem localLog_eq_map (T : Nat) (s₀ : NumericState)
    (past xs : List ((Unit → Bool) × Bool)) :
    (game T s₀).localLog () past xs = xs.map (fun e => (e.1 (), e.2)) := by
  induction xs generalizing past with
  | nil => rfl
  | cons x xs ih => simp [Game.localLog, game, ih]

private theorem replay_snd (xs : List ((Unit → Bool) × Bool)) (s₀ : NumericState) :
    (xs.foldl (fun s e => UnifiedFeedbackBridge.after s e.2) s₀).2 =
      xs.foldl
        (fun q e => SequentialFeedback.learnExample q (ClosedLoop.RepaymentExample.bit e.2))
        s₀.2 := by
  induction xs generalizing s₀ with
  | nil => rfl
  | cons x xs ih =>
      simpa only [List.foldl, UnifiedFeedbackBridge.after_formula] using
        ih (UnifiedFeedbackBridge.after s₀ x.2)

theorem privateParameter_observe {T : Nat} (s₀ : NumericState) (h : BitHistory T) :
    privateParameter s₀.2 ((game T s₀).observe () h) = (replay s₀ h).2 := by
  simp only [privateParameter, Game.observe, localLog_eq_map, List.foldl_map]
  exact (replay_snd h.val s₀).symm

/-- An actual policy constructor reads the parameter obtained from the saved record.
The original model's fair policy is the constant-choice specialization below. -/
def parameterPolicy (T : Nat) (q₀ : ℝ) (choose : ℝ → PMF Bool) : BitPlan T :=
  fun _ r => if ht : stage r < T then
    (choose (privateParameter q₀ r)).map (ofAction r ht)
  else PMF.pure (by simpa [ActionAt, ht] using ())

def fairPolicy (T : Nat) (s₀ : NumericState) : BitPlan T :=
  parameterPolicy T s₀.2 (fun _ => ClosedLoop.RepaymentExample.fair.toPMF)

theorem parameterPolicy_raw {T : Nat} (q₀ : ℝ) (choose : ℝ → PMF Bool)
    (r : PersonalRecord T Bool Bool) (ht : stage r < T) :
    ((parameterPolicy T q₀ choose) () r).map (toAction r ht) =
      choose (privateParameter q₀ r) := by
  simp only [parameterPolicy, dif_pos ht, PMF.map_comp]
  simpa only [Function.comp_def, toAction_ofAction] using
    (PMF.map_id (choose (privateParameter q₀ r)))

/-- The original fair action kernel is preserved at each active personal record. -/
theorem fairPolicy_raw {T : Nat} (s₀ : NumericState)
    (r : PersonalRecord T Bool Bool) (ht : stage r < T) :
    (((fairPolicy T s₀) () r).map (toAction r ht)).toMeasure =
      UnifiedFeedbackBridge.model.policy s₀ := by
  rw [fairPolicy, parameterPolicy_raw, Measure.toPMF_toMeasure]
  rfl

private theorem after_measurable (s : NumericState) :
    Measurable (UnifiedFeedbackBridge.after s) := Measurable.of_discrete

/-- One original Bool draw followed by the actual update is exactly ClosedLoop.step. -/
theorem coin_update_step (s : NumericState) :
    ((coinPMF s).map (UnifiedFeedbackBridge.after s)).toMeasure =
      ClosedLoop.step UnifiedFeedbackBridge.model s := by
  ext B hB
  rw [PMF.toMeasure_map_apply _ _ _ (after_measurable s) hB, coinPMF_toMeasure,
    UnifiedFeedbackBridge.step_two_atoms]
  simp [UnifiedFeedbackBridge.coin, Measure.add_apply, smul_eq_mul,
    hB, (after_measurable s) hB]

/-- The full-history machine executes the same numeric update kernel.
Actions disappear from this projection only because the given model's outcome
and update are action-independent, not because feedback is resampled. -/
theorem nativeStep_replay {T : Nat} (s₀ : NumericState) (β : BitPlan T)
    (h : BitHistory T) (ht : h.val.length < T) :
    (((game T s₀).nativeStep β h).map (replay s₀)).toMeasure =
      ClosedLoop.step UnifiedFeedbackBridge.model (replay s₀ h) := by
  have hk (a : (game T s₀).core.JointActionAt h) :
      (((game T s₀).step h a).map (replay s₀)) =
        (coinPMF (replay s₀ h)).map (UnifiedFeedbackBridge.after (replay s₀ h)) := by
    simp only [Game.step, dif_pos ht, game, PMF.map_comp]
    congr 1
    funext y
    exact replay_advance s₀ h ht _ y
  unfold Game.nativeStep
  rw [PMF.map_bind]
  simp_rw [hk]
  rw [PMF.bind_const]
  exact coin_update_step _

/-- The direct game law has the same bounded clock as the core machine. -/
theorem nativeLaw_time {T : Nat} (s₀ : NumericState) (β : BitPlan T)
    (n : Nat) (h : BitHistory T)
    (hh : (game T s₀).nativeLaw β n h ≠ 0) :
    h.val.length = min n T := by
  induction n generalizing h with
  | zero =>
      have heq : h = (game T s₀).initialHistory := by
        by_contra hne
        exact hh (by simp [Game.nativeLaw, PMF.pure_apply, hne])
      subst h
      simp [Game.initialHistory]
  | succ n ih =>
      change h ∈ (((game T s₀).nativeLaw β n).bind
        ((game T s₀).nativeStep β)).support at hh
      obtain ⟨p, hp, ht⟩ := (PMF.mem_support_bind_iff h).mp hh
      change h ∈ ((Math.PMFProduct.pmfPi (fun i => β i ((game T s₀).observe i p))).bind
        ((game T s₀).step p)).support at ht
      obtain ⟨a, _, ha⟩ := (PMF.mem_support_bind_iff h).mp ht
      have htime := (game T s₀).step_time p h a ha
      have hprev := ih p hp
      rw [hprev] at htime
      omega

private theorem native_next_measure {T : Nat} (s₀ : NumericState) (β : BitPlan T)
    (p : PMF (BitHistory T)) (hp : ∀ h, p h ≠ 0 → h.val.length < T) :
    ((p.bind ((game T s₀).nativeStep β)).map (replay s₀)).toMeasure =
      ClosedLoop.step UnifiedFeedbackBridge.model ∘ₘ (p.map (replay s₀)).toMeasure := by
  ext B hB
  rw [PMF.map_bind, PMF.toMeasure_bind_apply _ _ hB,
    ← PMF.toMeasure_map p (show Measurable (replay s₀) from Measurable.of_discrete),
    Measure.bind_apply hB (ClosedLoop.step UnifiedFeedbackBridge.model).aemeasurable,
    lintegral_map (Kernel.measurable_coe _ hB) (show Measurable (replay s₀) from Measurable.of_discrete),
    lintegral_fintype, tsum_fintype]
  apply Finset.sum_congr rfl
  intro h _
  rw [PMF.toMeasure_apply_singleton p h (measurableSet_singleton h)]
  by_cases hh : p h = 0
  · simp [hh]
  · rw [nativeStep_replay s₀ β h (hp h hh)]
    exact mul_comm _ _

/-- Up to the chosen horizon, this is the actual ClosedLoop measure iteration,
including its learned parameter coordinate. -/
theorem nativeLaw_replay {T : Nat} (s₀ : NumericState) (β : BitPlan T)
    (n : Nat) : n ≤ T →
    (((game T s₀).nativeLaw β n).map (replay s₀)).toMeasure =
      UnifiedFeedbackBridge.law (Measure.dirac s₀) n := by
  induction n with
  | zero =>
      intro _
      simp [Game.nativeLaw, PMF.pure_map, PMF.toMeasure_pure,
        replay_initial, UnifiedFeedbackBridge.law]
  | succ n ih =>
      intro hn
      change ((((game T s₀).nativeLaw β n).bind ((game T s₀).nativeStep β)).map
        (replay s₀)).toMeasure =
          ClosedLoop.step UnifiedFeedbackBridge.model ∘ₘ
            UnifiedFeedbackBridge.law (Measure.dirac s₀) n
      rw [native_next_measure s₀ β _ (fun h hh => by
        have htime := nativeLaw_time s₀ β n h hh
        omega), ih (by omega)]

/-- Kuhn preserves the full recorded history together with the parameter actually
replayed from its outcomes. The preceding theorems bind this replay to step. -/
theorem kuhn_joint_history_learning (T : Nat) (s₀ : NumericState)
    (μ : (i : Unit) → PMF (LocalPlan T Bool Bool)) :
    ∃ β : BitPlan T, ∀ n,
      ((game T s₀).nativeLaw β n).map (fun h => (h, replay s₀ h)) =
        ((Math.PMFProduct.pmfPi μ).bind (fun π => (game T s₀).nativeLawPure π n)).map
          (fun h => (h, replay s₀ h)) := by
  obtain ⟨β, hβ⟩ := (game T s₀).native_mixed_to_behavioral μ
  exact ⟨β, fun n => congrArg (fun p => p.map (fun h => (h, replay s₀ h))) (hβ n)⟩

/-- The mixed strategy's actual numeric law is the same ClosedLoop iteration. -/
theorem mixedLaw_replay (T : Nat) (s₀ : NumericState)
    (μ : (i : Unit) → PMF (LocalPlan T Bool Bool)) (n : Nat) (hn : n ≤ T) :
    (((Math.PMFProduct.pmfPi μ).bind (fun π => (game T s₀).nativeLawPure π n)).map
      (replay s₀)).toMeasure = UnifiedFeedbackBridge.law (Measure.dirac s₀) n := by
  obtain ⟨β, hβ⟩ := (game T s₀).native_mixed_to_behavioral μ
  rw [← hβ n]
  exact nativeLaw_replay s₀ β n hn

/-- The pre-existing sequential mean theorem now applies to the same finite game. -/
theorem native_mean (T : Nat) (s₀ : NumericState) (hs₀ : s₀ ∈ UnifiedFeedbackBridge.square)
    (β : BitPlan T) (n : Nat) (hn : n ≤ T) :
    UnifiedFeedbackBridge.mean
      ((((game T s₀).nativeLaw β n).map (replay s₀)).toMeasure) =
        SequentialFeedback.iterateExample n s₀ := by
  rw [nativeLaw_replay s₀ β n hn,
    UnifiedFeedbackBridge.mean_law (Measure.dirac s₀) (by simpa using hs₀) n]
  simp [UnifiedFeedbackBridge.mean]

/-- The same finite-game law is the marginal of the original closed-loop path. -/
theorem native_path_marginal (T : Nat) (s₀ : NumericState) (β : BitPlan T)
    (n : Nat) (hn : n ≤ T) :
    (((game T s₀).nativeLaw β n).map (replay s₀)).toMeasure =
      (ClosedLoop.pathLaw UnifiedFeedbackBridge.model (Measure.dirac s₀)).map
        (fun x => x n) := by
  rw [nativeLaw_replay s₀ β n hn, UnifiedFeedbackBridge.path_marginal_eq_law]

/-- The proven gain bound controls expectations of this actual game process. -/
theorem native_mean_geometric_bound (T : Nat) (s₀ : NumericState)
    (hs₀ : s₀ ∈ UnifiedFeedbackBridge.square) (β : BitPlan T)
    (n : Nat) (hn : n ≤ T) :
    max |(UnifiedFeedbackBridge.mean
        ((((game T s₀).nativeLaw β n).map (replay s₀)).toMeasure)).1 - 1/2|
      |(UnifiedFeedbackBridge.mean
        ((((game T s₀).nativeLaw β n).map (replay s₀)).toMeasure)).2 - 1/2| ≤
      (3/4 : ℝ)^n * max |s₀.1 - 1/2| |s₀.2 - 1/2| := by
  rw [nativeLaw_replay s₀ β n hn]
  simpa [UnifiedFeedbackBridge.mean] using
    UnifiedFeedbackBridge.law_mean_geometric_bound (Measure.dirac s₀)
      (by simpa using hs₀) n

end
end LegalMath20261109.FiniteGameFeedback

#print axioms LegalMath20261109.FiniteGameFeedback.replay_advance
#print axioms LegalMath20261109.FiniteGameFeedback.privateParameter_observe
#print axioms LegalMath20261109.FiniteGameFeedback.nativeStep_replay
#print axioms LegalMath20261109.FiniteGameFeedback.nativeLaw_replay
#print axioms LegalMath20261109.FiniteGameFeedback.kuhn_joint_history_learning
#print axioms LegalMath20261109.FiniteGameFeedback.native_path_marginal
#print axioms LegalMath20261109.FiniteGameFeedback.native_mean_geometric_bound

