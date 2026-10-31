import JurisLean.Candidates.U06_1FiniteBellman20261030
import JurisLean.Candidates.U06_5OriginalModels20261031
import JurisLean.Candidates.U06_4ConditionalInformation20261031

noncomputable section

open scoped NNReal ENNReal BigOperators

namespace JurisLean.Candidates.U06_5FiniteObservationInstance20261031

open Math.Probability
open JurisLean.Candidates.U06_1FiniteBellman20261030


/-!
Original 06.5 L121: immediate action, acquisition and stopping share one
finite, nonanticipating model. The hidden state is not a policy input.
Observed information states use the actual posterior of JurisLean.Candidates.U06_5OriginalModels20261031.signalLaw.
A settled result is revealed only after the terminal action.
-/

inductive Visible where
  | prior
  | seen (signal : Bool)
  | settled (success : Bool)
  deriving DecidableEq, Fintype, Repr

inductive Choice where
  | guess (answer : Bool)
  | buy
  | stop
  deriving DecidableEq, Fintype, Repr

private lemma pair_univ :
    (Finset.univ : Finset (Bool × Bool)) =
      {(false, false), (false, true), (true, false), (true, true)} := by
  decide

private lemma source_point (z : Bool × Bool) :
    (JurisLean.Candidates.U06_5OriginalModels20261031.signalLaw z).toReal =
      if z.1 = z.2 then (2 / 5 : ℝ) else 1 / 10 := by
  rcases z with ⟨a, b⟩
  cases a <;> cases b
  · change (((2 / 5 : ℝ≥0) : ℝ≥0∞)).toReal = (2 / 5 : ℝ)
    norm_num
  · change (((1 / 10 : ℝ≥0) : ℝ≥0∞)).toReal = (1 / 10 : ℝ)
    norm_num
  · change (((1 / 10 : ℝ≥0) : ℝ≥0∞)).toReal = (1 / 10 : ℝ)
    norm_num
  · change (((2 / 5 : ℝ≥0) : ℝ≥0∞)).toReal = (2 / 5 : ℝ)
    norm_num

private lemma reachable (y : Bool) :
    ∃ z : Bool × Bool, z.2 = y ∧ z ∈ JurisLean.Candidates.U06_5OriginalModels20261031.signalLaw.support := by
  refine ⟨(y, y), rfl, (PMF.mem_support_iff _ _).mpr ?_⟩
  cases y
  · change ((2 / 5 : ℝ≥0) : ℝ≥0∞) ≠ 0
    norm_num
  · change ((2 / 5 : ℝ≥0) : ℝ≥0∞) ≠ 0
    norm_num

private def posterior (y : Bool) : PMF (Bool × Bool) := by
  classical
  exact JurisLean.Candidates.U06_5OriginalModels20261031.signalLaw.filter {z | z.2 = y} (reachable y)

private lemma fiber_mass (y : Bool) :
    (∑ z : Bool × Bool,
      ({v | v.2 = y}.indicator (fun v => JurisLean.Candidates.U06_5OriginalModels20261031.signalLaw v)) z).toReal =
        (1 / 2 : ℝ) := by
  classical
  rw [ENNReal.toReal_sum (s := Finset.univ)
    (f := fun z : Bool × Bool =>
      ({v | v.2 = y}.indicator (fun v => JurisLean.Candidates.U06_5OriginalModels20261031.signalLaw v)) z) (by
        intro z _
        by_cases same : z.2 = y <;>
          simp [Set.indicator, same, PMF.apply_ne_top])]
  cases y <;>
    norm_num [pair_univ, Set.indicator, source_point]

private lemma posterior_point (y : Bool) (z : Bool × Bool) :
    (posterior y z).toReal =
      if z.2 = y then
        2 * (if z.1 = z.2 then (2 / 5 : ℝ) else 1 / 10)
      else 0 := by
  classical
  calc
    (posterior y z).toReal =
        ((({v | v.2 = y}.indicator (fun v => JurisLean.Candidates.U06_5OriginalModels20261031.signalLaw v)) z) *
          (∑' v, ({u | u.2 = y}.indicator
            (fun u => JurisLean.Candidates.U06_5OriginalModels20261031.signalLaw u)) v)⁻¹).toReal := by
      exact congrArg (fun x : ℝ≥0∞ => x.toReal)
        (PMF.filter_apply (p := JurisLean.Candidates.U06_5OriginalModels20261031.signalLaw)
          (s := {v | v.2 = y}) (reachable y) z)
    _ = _ := by
      rw [ENNReal.toReal_mul, ENNReal.toReal_inv,
        tsum_fintype, fiber_mass]
      by_cases same : z.2 = y <;>
        simp [Set.indicator, same, source_point] <;> ring

private def win (answer : Bool) (z : Bool × Bool) : ℝ :=
  if answer = z.1 then 1 else 0

private lemma posterior_reward (y answer : Bool) :
    expect (posterior y) (win answer) =
      if answer = y then (4 / 5 : ℝ) else 1 / 5 := by
  rw [expect_eq_sum]
  cases y <;> cases answer <;>
    norm_num [pair_univ, posterior_point, win]

private def belief : Visible → PMF (Bool × Bool)
  | .prior => JurisLean.Candidates.U06_5OriginalModels20261031.signalLaw
  | .seen y => posterior y
  | .settled _ => PMF.pure (false, false)

private def nextLaw : Visible → Choice → PMF Visible
  | .prior, .buy =>
      PMF.map (fun z : Bool × Bool => Visible.seen z.2) JurisLean.Candidates.U06_5OriginalModels20261031.signalLaw
  | s, .guess answer =>
      PMF.map
        (fun z : Bool × Bool => Visible.settled (decide (answer = z.1)))
        (belief s)
  | _, _ => PMF.pure (.settled false)

private def legal (remaining : ℕ) : Visible → Finset Choice
  | .prior =>
      if 2 ≤ remaining then
        {.guess false, .guess true, .buy, .stop}
      else {.guess false, .guess true, .stop}
  | .seen _ => {.guess false, .guess true, .stop}
  | .settled _ => ∅

private def control : Control Visible Choice where
  legal := legal
  kernel := fun _ s a s' => (nextLaw s a s').toReal
  kernel_nonneg := by
    intro n s a permitted s'
    exact ENNReal.toReal_nonneg
  kernel_one := by
    intro n s a permitted
    exact pmf_toReal_sum_one (nextLaw s a)

private def terminal : Visible → ℝ
  | .settled true => 1
  | _ => 0

private def acquisition (k : ℝ) (_ : ℕ) (s : Visible) (a : Choice) : ℝ :=
  if s = .prior ∧ a = .buy then k else 0

private def netReward (k : ℝ) (t : ℕ) (s : Visible) (a : Choice) : ℝ :=
  0 - acquisition k t s a

private lemma prior_guess (answer : Bool) :
    expect (nextLaw .prior (.guess answer)) terminal = (1 / 2 : ℝ) := by
  change expect
    (PMF.map
      (fun z : Bool × Bool => Visible.settled (decide (answer = z.1)))
      JurisLean.Candidates.U06_5OriginalModels20261031.signalLaw) terminal = _
  rw [expect_map_fintype_target]
  simpa [JurisLean.Candidates.U06_5OriginalModels20261031.guessValue, terminal, win] using
    (JurisLean.Candidates.U06_5OriginalModels20261031.signal_information_values.1 (fun _ : Unit => answer))

private lemma seen_guess (y answer : Bool) :
    expect (nextLaw (.seen y) (.guess answer)) terminal =
      if answer = y then (4 / 5 : ℝ) else 1 / 5 := by
  change expect
    (PMF.map
      (fun z : Bool × Bool => Visible.settled (decide (answer = z.1)))
      (posterior y)) terminal = _
  rw [expect_map_fintype_target]
  simpa [terminal, win] using posterior_reward y answer

/-- Actual posterior and option semantics of this one finite observation model.
Acquisition is available only before observation with two decisions remaining;
all later decisions use the observed signal, not the hidden state. -/
theorem actual_information_states_and_options :
    (∀ y : Bool,
      JurisLean.Candidates.U06_4ConditionalInformation20261031.conditionalLaw JurisLean.Candidates.U06_5OriginalModels20261031.signalLaw Prod.snd y = some (posterior y)) ∧
    (∀ answer : Bool,
      expect (nextLaw .prior (.guess answer)) terminal = (1 / 2 : ℝ)) ∧
    (∀ y answer : Bool,
      expect (nextLaw (.seen y) (.guess answer)) terminal =
        if answer = y then (4 / 5 : ℝ) else 1 / 5) ∧
    nextLaw .prior .buy =
      PMF.map (fun z : Bool × Bool => Visible.seen z.2) JurisLean.Candidates.U06_5OriginalModels20261031.signalLaw ∧
    (∀ a : Choice, a ∈ control.legal 2 .prior) ∧
    (∀ y : Bool, Choice.buy ∉ control.legal 1 (.seen y)) ∧
    (∀ s : Visible, expect (nextLaw s .stop) terminal = 0) ∧
    (∀ s : Visible, terminal s ∈ Set.Icc (0 : ℝ) 1) := by
  refine ⟨?_, prior_guess, seen_guess, rfl, ?_, ?_, ?_, ?_⟩
  · intro y
    classical
    simp only [JurisLean.Candidates.U06_4ConditionalInformation20261031.conditionalLaw, dif_pos (reachable y)]
    rfl
  · intro a
    cases a with
    | guess answer => cases answer <;> simp [control, legal]
    | buy => simp [control, legal]
    | stop => simp [control, legal]
  · intro y
    simp [control, legal]
  · intro s
    cases s <;> simp [nextLaw, terminal]
  · intro s
    cases s with
    | prior => norm_num [terminal]
    | seen y => norm_num [terminal]
    | settled success => cases success <;> norm_num [terminal]

private def observeThenAct : Policy control := by
  intro n history s possible
  cases s with
  | prior =>
      by_cases enough : 2 ≤ n + 1
      · exact ⟨.buy, by simp [control, legal, enough]⟩
      · exact ⟨.guess false, by simp [control, legal, enough]⟩
  | seen y =>
      exact ⟨.guess y, by simp [control, legal]⟩
  | settled success =>
      simp [control, legal] at possible

private lemma seen_gross (y : Bool) (history : History Visible Choice) :
    policyValue control (fun _ _ _ => 0) terminal
      observeThenAct 1 history (.seen y) = (4 / 5 : ℝ) := by
  change (0 : ℝ) +
    (∑ s' : Visible, (nextLaw (.seen y) (.guess y) s').toReal *
      terminal s') = _
  rw [← expect_eq_sum]
  simpa using seen_guess y y

private lemma seen_cost (k : ℝ) (y : Bool)
    (history : History Visible Choice) :
    policyValue control (acquisition k) (fun _ => 0)
      observeThenAct 1 history (.seen y) = 0 := by
  change (0 : ℝ) +
    (∑ s' : Visible, (nextLaw (.seen y) (.guess y) s').toReal * 0) = 0
  simp

private lemma purchase_gross :
    trajectoryExpectation control (fun _ _ _ => 0) terminal
      observeThenAct 2 [] .prior = (4 / 5 : ℝ) := by
  rw [trajectory_expectation_eq_policy_value]
  change (0 : ℝ) +
    (∑ s' : Visible, (nextLaw .prior .buy s').toReal *
      policyValue control (fun _ _ _ => 0) terminal observeThenAct
        1 [(Visible.prior, Choice.buy)] s') = _
  rw [← expect_eq_sum]
  change (0 : ℝ) +
    expect (PMF.map (fun z : Bool × Bool => Visible.seen z.2) JurisLean.Candidates.U06_5OriginalModels20261031.signalLaw)
      (fun s' => policyValue control (fun _ _ _ => 0) terminal
        observeThenAct 1 [(Visible.prior, Choice.buy)] s') = _
  rw [expect_map_fintype_target]
  simp_rw [seen_gross]
  simp

private lemma purchase_cost (k : ℝ) :
    trajectoryExpectation control (acquisition k) (fun _ => 0)
      observeThenAct 2 [] .prior = k := by
  rw [trajectory_expectation_eq_policy_value]
  change k +
    (∑ s' : Visible, (nextLaw .prior .buy s').toReal *
      policyValue control (acquisition k) (fun _ => 0) observeThenAct
        1 [(Visible.prior, Choice.buy)] s') = k
  rw [← expect_eq_sum]
  change k +
    expect (PMF.map (fun z : Bool × Bool => Visible.seen z.2) JurisLean.Candidates.U06_5OriginalModels20261031.signalLaw)
      (fun s' => policyValue control (acquisition k) (fun _ => 0)
        observeThenAct 1 [(Visible.prior, Choice.buy)] s') = k
  rw [expect_map_fintype_target]
  simp_rw [seen_cost]
  simp

/-- The same actual trajectory law pays the real acquisition-plus-waiting
cost once, at purchase. Its net value is 4/5-k, with the old 3/10 cutoff. -/
theorem actual_purchase_trajectory_and_single_cost (k : ℝ) :
    trajectoryExpectation control (acquisition k) (fun _ => 0)
      observeThenAct 2 [] .prior = k ∧
    trajectoryExpectation control (netReward k) terminal
      observeThenAct 2 [] .prior = 4 / 5 - k ∧
    ((1 / 2 : ℝ) <
      trajectoryExpectation control (netReward k) terminal
        observeThenAct 2 [] .prior ↔ k < 3 / 10) := by
  have paid := purchase_cost k
  have accounted := cost_counted_once control (fun _ _ _ => 0)
    (acquisition k) terminal observeThenAct 2 [] .prior
  have net :
      trajectoryExpectation control (netReward k) terminal
        observeThenAct 2 [] .prior = 4 / 5 - k := by
    simpa only [netReward, purchase_gross, paid] using accounted
  refine ⟨paid, net, ?_⟩
  rw [net]
  constructor <;> intro h <;> linarith

/-- Original 06.5 finite-horizon optimum, directly instantiated from the
existing theorem. Every policy reads only time, visible past and visible state;
the expectation uses the actual normalized transition trajectory law. -/
theorem actual_nonanticipating_trajectory_optimum (k : ℝ) :
    ∃ optimal : Policy control,
      (∀ x : Trace Visible 2,
        0 ≤ trajectoryWeight control optimal 2 [] .prior x) ∧
      (∑ x : Trace Visible 2,
        trajectoryWeight control optimal 2 [] .prior x) = 1 ∧
      (∑ x : Trace Visible 2,
        (trajectoryLaw control optimal 2 [] .prior x).toReal *
          realizedReturn control (netReward k) terminal
            optimal 2 [] .prior x) =
        bellman control (netReward k) terminal 2 .prior ∧
      ∀ policy : Policy control,
        (∑ x : Trace Visible 2,
          (trajectoryLaw control policy 2 [] .prior x).toReal *
            realizedReturn control (netReward k) terminal
              policy 2 [] .prior x) ≤
        ∑ x : Trace Visible 2,
          (trajectoryLaw control optimal 2 [] .prior x).toReal *
            realizedReturn control (netReward k) terminal
              optimal 2 [] .prior x := by
  obtain ⟨optimal, certified⟩ :=
    bellman_optimum_of_actual_trajectory_expectation
      control (netReward k) terminal
  exact ⟨optimal, certified 2 [] .prior⟩

end JurisLean.Candidates.U06_5FiniteObservationInstance20261031
