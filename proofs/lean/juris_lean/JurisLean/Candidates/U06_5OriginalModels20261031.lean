import JurisLean.Candidates.LearningRisk20261027
import JurisLean.Candidates.U06_2EquilibriumTransfer20261030
import Mathlib.Probability.ConditionalProbability

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace JurisLean.Candidates.U06_5OriginalModels20261031

open JurisLean.Candidates.LearningRisk20261027
open JurisLean.Candidates.U06_2EquilibriumTransfer20261030

local instance : MeasurableSpace Bool := ⊤

/-!
CI_NOT_RUN.

Original U06.5 information toy: this section constructs one normalized
four-atom joint law, proves its actual state and conditional signal probabilities,
and connects all three information policies to expected utility under that law.
The existing finite Bayes theorem supplies the signal-policy optimum.
-/

private lemma bool_univ : (Finset.univ : Finset Bool) = {false, true} := by
  decide

private lemma pair_univ :
    (Finset.univ : Finset (Bool × Bool)) =
      {(false, false), (false, true), (true, false), (true, true)} := by
  decide

private def signalWeight (z : Bool × Bool) : ℝ≥0 :=
  if z.1 = z.2 then 2 / 5 else 1 / 10

private lemma signalWeight_sum :
    (∑ z : Bool × Bool, (signalWeight z : ℝ≥0∞)) = 1 := by
  have h : (∑ z : Bool × Bool, signalWeight z) = (1 : ℝ≥0) := by
    norm_num [signalWeight, pair_univ]
  exact_mod_cast h

/-- First coordinate is the state; second coordinate is the observed signal. -/
def signalLaw : PMF (Bool × Bool) :=
  PMF.ofFintype (fun z => (signalWeight z : ℝ≥0∞)) signalWeight_sum

def signalMeasure : Measure (Bool × Bool) := signalLaw.toMeasure

private lemma signal_event_mass (E : Set (Bool × Bool)) (hE : MeasurableSet E) :
    signalMeasure E =
      ∑ z : Bool × Bool, if z ∈ E then (signalWeight z : ℝ≥0∞) else 0 := by
  simpa [signalMeasure, signalLaw, Set.indicator, tsum_fintype] using
    (PMF.toMeasure_ofFintype_apply signalWeight_sum E hE)

private lemma signal_state_mass (ω : Bool) :
    signalMeasure {z | z.1 = ω} = (1 / 2 : ℝ≥0∞) := by
  rw [signal_event_mass _ (measurableSet_eq_fun measurable_fst measurable_const)]
  cases ω <;> norm_num [pair_univ, signalWeight]

private lemma signal_correct_mass :
    signalMeasure {z | z.2 = z.1} = (4 / 5 : ℝ≥0∞) := by
  rw [signal_event_mass _ (measurableSet_eq_fun measurable_snd measurable_fst)]
  norm_num [pair_univ, signalWeight]

private lemma signal_correct_given_state (ω : Bool) :
    ProbabilityTheory.cond signalMeasure {z | z.1 = ω} {z | z.2 = ω} =
      (4 / 5 : ℝ≥0∞) := by
  have hstate : MeasurableSet {z : Bool × Bool | z.1 = ω} :=
    measurableSet_eq_fun measurable_fst measurable_const
  have hsignal : MeasurableSet {z : Bool × Bool | z.2 = ω} :=
    measurableSet_eq_fun measurable_snd measurable_const
  rw [ProbabilityTheory.cond_apply hstate signalMeasure,
    signal_state_mass, signal_event_mass _ (hstate.inter hsignal)]
  cases ω <;> norm_num [pair_univ, signalWeight]

/-- Actual fair state prior and 4/5 signal accuracy, including given-state accuracy. -/
theorem signal_joint_law :
    (∀ ω : Bool, signalMeasure {z | z.1 = ω} = (1 / 2 : ℝ≥0∞)) ∧
      (∀ ω : Bool,
        ProbabilityTheory.cond signalMeasure {z | z.1 = ω} {z | z.2 = ω} =
          (4 / 5 : ℝ≥0∞)) ∧
      signalMeasure {z | z.2 = z.1} = (4 / 5 : ℝ≥0∞) :=
  ⟨signal_state_mass, signal_correct_given_state, signal_correct_mass⟩

/-- Every information policy is evaluated under the same normalized joint law. -/
def guessValue {Z : Type*} (observation : Bool × Bool → Z) (policy : Z → Bool) : ℝ :=
  Math.Probability.expect signalLaw
    (fun z => if policy (observation z) = z.1 then 1 else 0)

private lemma signal_risk_bridge (h : Bool → Bool) :
    1 - guessValue Prod.snd h =
      finiteBinaryRisk (fun _ : Bool => (1 / 2 : ℝ))
        (fun y => if y then 4 / 5 else 1 / 5) h := by
  cases hf : h false <;> cases ht : h true <;>
    norm_num [guessValue, Math.Probability.expect_eq_sum, signalLaw,
      signalWeight, pair_univ, finiteBinaryRisk, bool_univ, hf, ht]

private lemma no_signal_value (a : Unit → Bool) :
    guessValue (fun _ : Bool × Bool => ()) a = (1 / 2 : ℝ) := by
  cases ha : a () <;>
    norm_num [guessValue, Math.Probability.expect_eq_sum, signalLaw,
      signalWeight, pair_univ, ha]

private lemma signal_identity_value : guessValue Prod.snd id = (4 / 5 : ℝ) := by
  norm_num [guessValue, Math.Probability.expect_eq_sum, signalLaw,
    signalWeight, pair_univ]

private lemma signal_policy_optimal (h : Bool → Bool) :
    guessValue Prod.snd h ≤ (4 / 5 : ℝ) := by
  let q : Bool → ℝ := fun y => if y then 4 / 5 else 1 / 5
  have hb := fiberBayes_minimizes (fun _ : Bool => (1 / 2 : ℝ))
    (fun _ => by norm_num) id q h
  have hfb : fiberBayes q ∘ id = id := by
    funext y
    cases y <;> norm_num [fiberBayes, q, Function.comp_def]
  rw [hfb] at hb
  change finiteBinaryRisk (fun _ : Bool => (1 / 2 : ℝ)) q id ≤
    finiteBinaryRisk (fun _ : Bool => (1 / 2 : ℝ)) q h at hb
  have hi := signal_risk_bridge id
  have hh := signal_risk_bridge h
  change 1 - guessValue Prod.snd id =
    finiteBinaryRisk (fun _ : Bool => (1 / 2 : ℝ)) q id at hi
  change 1 - guessValue Prod.snd h =
    finiteBinaryRisk (fun _ : Bool => (1 / 2 : ℝ)) q h at hh
  rw [← hi, ← hh, signal_identity_value] at hb
  linarith

private lemma perfect_identity_value : guessValue Prod.fst id = (1 : ℝ) := by
  norm_num [guessValue, Math.Probability.expect_eq_sum, signalLaw,
    signalWeight, pair_univ]

private lemma perfect_policy_bound (h : Bool → Bool) :
    guessValue Prod.fst h ≤ (1 : ℝ) := by
  cases hf : h false <;> cases ht : h true <;>
    norm_num [guessValue, Math.Probability.expect_eq_sum, signalLaw,
      signalWeight, pair_univ, hf, ht]

/-- Original gross information values, all-policy optimality, and strict cost cutoff. -/
theorem signal_information_values :
    (∀ a : Unit → Bool,
      guessValue (fun _ : Bool × Bool => ()) a = (1 / 2 : ℝ)) ∧
      guessValue Prod.snd id = (4 / 5 : ℝ) ∧
      (∀ h : Bool → Bool, guessValue Prod.snd h ≤ (4 / 5 : ℝ)) ∧
      guessValue Prod.fst id = (1 : ℝ) ∧
      (∀ h : Bool → Bool, guessValue Prod.fst h ≤ (1 : ℝ)) ∧
      (∀ k : ℝ,
        guessValue Prod.snd id - k -
            guessValue (fun _ : Bool × Bool => ()) (fun _ => false) = 3 / 10 - k ∧
        (guessValue (fun _ : Bool × Bool => ()) (fun _ => false) <
          guessValue Prod.snd id - k ↔ k < 3 / 10)) := by
  refine ⟨no_signal_value, signal_identity_value, signal_policy_optimal,
    perfect_identity_value, perfect_policy_bound, ?_⟩
  intro k
  rw [signal_identity_value, no_signal_value]
  constructor
  · ring
  · constructor <;> intro h <;> linarith

/-!
Original U06.5 bargaining toy: the complete-strategy/history/run carrier is
reused, while terminal utility is newly defined for cake 10, delay loss 1 for
each player, and failure payoff -1 for each player. Every backward-induction
node is checked before the actual run and complete-strategy deviations.
-/

/-- false/true at the first offer gives B 4/6; at the second offer it gives A 4/6. -/
def originalTerminalPayoff : BargainTerminal → ℝ × ℝ
  | .accept0 q => if q then (4, 6) else (6, 4)
  | .accept1 _ r => if r then (5, 3) else (3, 5)
  | .failure _ _ => (-1, -1)

def originalUtility (z : BargainTerminal) (i : Bool) : ℝ :=
  if i then (originalTerminalPayoff z).2 else (originalTerminalPayoff z).1

/-- The root action is varied; all continuation actions are the computed BI actions. -/
def originalProfile (q : Bool) : BargainSourceProfile :=
  ((q, fun _ _ => true), (fun offered => offered, fun _ => false))

def originalBIProfile : BargainSourceProfile := originalProfile true

def originalPayoff (i : Bool) (s : BargainSourceProfile) : ℝ :=
  originalUtility (bargainRun s) i

noncomputable def originalGame : GameTheory.KernelGame Bool where
  Strategy := BargainStrategy
  Outcome := BargainTerminal
  utility := originalUtility
  outcomeKernel := fun σ => PMF.pure (bargainRun (σ false, σ true))

private lemma originalGame_profile_eu (s : BargainSourceProfile) (i : Bool) :
    originalGame.eu (bargainProfileEquiv s) i = originalPayoff i s := by
  change Math.Probability.expect (PMF.pure (bargainRun s))
    (fun z => originalUtility z i) = originalPayoff i s
  simp only [Math.Probability.expect_pure, originalPayoff]

private lemma original_all_deviations (i : Bool) (τ : BargainStrategy i) :
    originalPayoff i (bargainSourceUpdate originalBIProfile i τ) ≤
      originalPayoff i originalBIProfile := by
  cases i with
  | false =>
      cases hq : τ.1 <;> cases ha : τ.2 false false <;>
        norm_num [originalPayoff, bargainSourceUpdate, originalBIProfile,
          originalProfile, bargainRun, originalUtility, originalTerminalPayoff,
          hq, ha]
  | true =>
      cases ha : τ.1 true <;> cases hr : τ.2 true <;>
        norm_num [originalPayoff, bargainSourceUpdate, originalBIProfile,
          originalProfile, bargainRun, originalUtility, originalTerminalPayoff,
          ha, hr]

/-- Original node-by-node BI, realized (4,6), and all complete unilateral deviations. -/
theorem bargain_backward_induction :
    (∀ q r : Bool,
      originalUtility (.failure q r) false <
        originalUtility (.accept1 q r) false) ∧
      (∀ q : Bool,
        originalUtility (.accept1 q true) true <
          originalUtility (.accept1 q false) true) ∧
      originalUtility (.accept0 false) true <
        originalUtility (.accept1 false false) true ∧
      originalUtility (.accept1 true false) true <
        originalUtility (.accept0 true) true ∧
      originalPayoff false (originalProfile false) <
        originalPayoff false (originalProfile true) ∧
      bargainRun originalBIProfile = .accept0 true ∧
      (originalPayoff false originalBIProfile,
        originalPayoff true originalBIProfile) = (4, 6) ∧
      (∀ (i : Bool) (τ : BargainStrategy i),
        originalGame.eu
            (Function.update (bargainProfileEquiv originalBIProfile) i τ) i ≤
          originalGame.eu (bargainProfileEquiv originalBIProfile) i) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro q r
    cases r <;> norm_num [originalUtility, originalTerminalPayoff]
  · intro q
    norm_num [originalUtility, originalTerminalPayoff]
  · norm_num [originalUtility, originalTerminalPayoff]
  · norm_num [originalUtility, originalTerminalPayoff]
  · norm_num [originalPayoff, originalProfile, bargainRun,
      originalUtility, originalTerminalPayoff]
  · rfl
  · norm_num [originalPayoff, originalBIProfile, originalProfile, bargainRun,
      originalUtility, originalTerminalPayoff]
  · intro i τ
    calc
      originalGame.eu
          (Function.update (bargainProfileEquiv originalBIProfile) i τ) i =
          originalPayoff i (bargainSourceUpdate originalBIProfile i τ) := by
        rw [← bargainProfileEquiv_update]
        exact originalGame_profile_eu _ _
      _ ≤ originalPayoff i originalBIProfile := original_all_deviations i τ
      _ = originalGame.eu (bargainProfileEquiv originalBIProfile) i :=
        (originalGame_profile_eu _ _).symm

/- The already existing matching-pennies witness remains the cited result.
   Brouwer is background to the frozen exposition, not a new theorem here. -/
#check JurisLean.Candidates.Final20261021.Decision.u06_5_matching_pennies_no_pure

end JurisLean.Candidates.U06_5OriginalModels20261031

#print axioms JurisLean.Candidates.U06_5OriginalModels20261031.signal_joint_law
#print axioms JurisLean.Candidates.U06_5OriginalModels20261031.signal_information_values
#print axioms JurisLean.Candidates.U06_5OriginalModels20261031.bargain_backward_induction
