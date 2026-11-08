import JurisLean.PosteriorLawRealization
import JurisLean.Mandate.ReLUApprox
import JurisLean.Candidates.LearningERM20261027

/-! The original network and actual empirical fitter consume the same response
target as the feedback process. Brier excess is converted to prediction error,
then to every action's cash-flow value and the selected action's regret. -/

namespace LegalMath20261109.TrainedDecision

open MeasureTheory ProbabilityTheory
open LegalMath20261108.UnifiedFeedbackBridge
open LegalMath20261109.PosteriorLaw
open JurisLean.FullMath.Probability
open JurisLean.Seams.UnifiedPayoffChain JurisLean.Seams.PayoffEquilibrium
open JurisLean.Candidates.LearningERM20261027
open JurisLean.Candidates.LearningFiniteClass20261027

noncomputable section

def forecast (z : ℚ × ℚ) : ℚ :=
  max 0 (min 1 ((JurisLean.Mandate.ReLUApprox.out z - 3)/2))

theorem forecast_bounds (z : ℚ × ℚ) : 0 ≤ forecast z ∧ forecast z ≤ 1 :=
  ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩

def ideal (s : ℚ × ℚ) : ℚ × ℚ := (s.1/2+s.2-3/4, 0)

/-- Existing two-hidden-unit network, with explicit input encoding and readout. -/
theorem original_network_represents_response (s : ℚ × ℚ)
    (hs : 0 ≤ s.1 ∧ s.1 ≤ 1 ∧ 0 ≤ s.2 ∧ s.2 ≤ 1) :
    forecast (ideal s) = probabilityQ s := by
  have h1 : 0 ≤ (ideal s).1 - (ideal s).2 + 1 := by dsimp [ideal]; linarith
  have h2 : 0 ≤ -(ideal s).1 + 3*(ideal s).2 + 2 := by dsimp [ideal]; linarith
  have ho : JurisLean.Mandate.ReLUApprox.out (ideal s) = 2 * responseQ s + 3 := by
    unfold JurisLean.Mandate.ReLUApprox.out JurisLean.Mandate.ReLUApprox.h1
      JurisLean.Mandate.ReLUApprox.h2 JurisLean.Mandate.ReLUApprox.relu
    rw [max_eq_left h1, max_eq_left h2, max_eq_left (by linarith)]
    dsimp [ideal, responseQ]
    ring
  unfold forecast probabilityQ
  rw [ho]
  have eq : (2 * responseQ s + 3 - 3) / 2 = responseQ s := by ring
  rw [eq]

def loss (z : ℚ × ℚ) (y : Bool) : ℚ := (forecast z - if y then 1 else 0)^2

theorem loss_range (z : ℚ × ℚ) (y : Bool) : (loss z y : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by
  have h0 : (0 : ℝ) ≤ (forecast z : ℝ) := by exact_mod_cast (forecast_bounds z).1
  have h1 : (forecast z : ℝ) ≤ 1 := by exact_mod_cast (forecast_bounds z).2
  have product := mul_nonneg h0 (sub_nonneg.mpr h1)
  cases y
  · have eq : (loss z false : ℝ) = (forecast z : ℝ)^2 := by norm_num [loss]
    rw [eq]
    exact ⟨sq_nonneg _, by nlinarith⟩
  · have eq : (loss z true : ℝ) = ((forecast z : ℝ)-1)^2 := by norm_num [loss]
    rw [eq]
    exact ⟨sq_nonneg _, by nlinarith⟩

def risk (s : ℚ × ℚ) (z : ℚ × ℚ) : ℝ := ∫ y, (loss z y : ℝ) ∂coin (embed s)

theorem risk_excess (s : ℚ × ℚ) (z : ℚ × ℚ) :
    risk s z - expBern (probability (embed s))
      (fun y => (probability (embed s) - if y then 1 else 0)^2) =
        ((forecast z : ℝ) - probability (embed s))^2 := by
  unfold risk
  rw [integral_coin]
  have castLoss : (fun y => (loss z y : ℝ)) =
      (fun y => ((forecast z : ℝ) - if y then 1 else 0)^2) := by
    funext y; cases y <;> norm_num [loss]
  rw [castLoss]
  exact brier_excess_identity _ _

def fitted {n : Nat} (first : ℚ × ℚ) (rest : List (ℚ × ℚ)) (data : Fin n → Bool) : ℚ × ℚ :=
  fitNonempty loss first rest data

def realizedRadius {n : Nat} (s : ℚ × ℚ) (first : ℚ × ℚ) (rest : List (ℚ × ℚ))
    (data : Fin n → Bool) : ℝ :=
  (first :: rest).toFinset.sup' ⟨first, by simp⟩
    (fun z => |risk s z - (empiricalScore loss data z : ℝ)|)

theorem realizedRadius_uniform {n : Nat} (s : ℚ × ℚ) (first : ℚ × ℚ)
    (rest : List (ℚ × ℚ)) (data : Fin n → Bool) (z : ℚ × ℚ) (hz : z ∈ first :: rest) :
    |risk s z-(empiricalScore loss data z : ℝ)| ≤ realizedRadius s first rest data := by
  unfold realizedRadius
  exact Finset.le_sup' (fun z => |risk s z-(empiricalScore loss data z : ℝ)|)
    (List.mem_toFinset.mpr hz)

theorem realizedRadius_nonneg {n : Nat} (s : ℚ × ℚ) (first : ℚ × ℚ)
    (rest : List (ℚ × ℚ)) (data : Fin n → Bool) : 0 ≤ realizedRadius s first rest data :=
  le_trans (abs_nonneg _) (realizedRadius_uniform s first rest data first (by simp))

/-- The selected parameters really come from the original empirical fitter. -/
theorem actual_fit_prediction_bound {n : Nat} (hn : 0 < n) (s : ℚ × ℚ)
    (hs : 0 ≤ s.1 ∧ s.1 ≤ 1 ∧ 0 ≤ s.2 ∧ s.2 ≤ 1)
    (first : ℚ × ℚ) (rest : List (ℚ × ℚ)) (data : Fin n → Bool)
    (oracle : ideal s ∈ first :: rest) (r E : ℝ) (hE : 0 ≤ E) (radius : 2*r ≤ E^2)
    (uniform : ∀ z ∈ first :: rest,
      |risk s z - (empiricalScore loss data z : ℝ)| ≤ r) :
    proposed_empirical_fit loss (first :: rest) data = some (fitted first rest data) ∧
      |(forecast (fitted first rest data) : ℝ) - probability (embed s)| ≤ E := by
  have fit := u01_1_actual_empirical_fit_minimizes loss first rest data hn
  have hc := (abs_le.mp (uniform _ fit.2.1)).2
  have ho := (abs_le.mp (uniform _ oracle)).1
  have best : (empiricalScore loss data (fitted first rest data) : ℝ) ≤
      (empiricalScore loss data (ideal s) : ℝ) := by
    exact_mod_cast fit.2.2 _ oracle
  have oracleRisk := risk_excess s (ideal s)
  rw [original_network_represents_response s hs, probabilityQ_embed] at oracleRisk
  have chosenRisk := risk_excess s (fitted first rest data)
  have sq : ((forecast (fitted first rest data) : ℝ) - probability (embed s))^2 ≤ E^2 := by
    dsimp [fitted] at *
    nlinarith
  refine ⟨fit.1, abs_le.mpr ⟨?_, ?_⟩⟩ <;> nlinarith [sq_nonneg
    ((forecast (fitted first rest data) : ℝ) - probability (embed s) - E),
    sq_nonneg ((forecast (fitted first rest data) : ℝ) - probability (embed s) + E)]

def predictedValue (q : ℝ) (flows : Bool → Bool → PayFlow) (role : Role) (a : Bool) : ℝ :=
  expBern q (reward flows role a)

def greedy (q : ℝ) (flows : Bool → Bool → PayFlow) (role : Role) : Bool :=
  if predictedValue q flows role false ≤ predictedValue q flows role true then true else false

theorem greedy_maximizes (q : ℝ) (flows : Bool → Bool → PayFlow) (role : Role) (a : Bool) :
    predictedValue q flows role a ≤ predictedValue q flows role (greedy q flows role) := by
  unfold greedy
  split <;> cases a <;> simp_all <;> linarith

theorem actual_value_formula (s : State) (flows : Bool → Bool → PayFlow) (role : Role) (a : Bool) :
    value s flows role a = predictedValue (probability s) flows role a := by
  change (∫ y, reward flows role a y ∂coin s) = _
  exact integral_coin s _

theorem payoff_error (s : State) (q E C : ℝ) (hC : 0 ≤ C)
    (flows : Bool → Bool → PayFlow) (role : Role)
    (err : |q - probability s| ≤ E)
    (sensitivity : ∀ a, |reward flows role a true - reward flows role a false| ≤ C) (a : Bool) :
    |value s flows role a - predictedValue q flows role a| ≤ C*E := by
  rw [actual_value_formula]
  have identity : predictedValue (probability s) flows role a - predictedValue q flows role a =
      (probability s-q)*(reward flows role a true-reward flows role a false) := by
    unfold predictedValue expBern; ring
  rw [identity, abs_mul]
  have he : |probability s-q| ≤ E := by simpa [abs_sub_comm] using err
  calc
    _ ≤ E*C := mul_le_mul he (sensitivity a) (abs_nonneg _) (le_trans (abs_nonneg _) he)
    _ = C*E := by ring

/-- Regret is derived from two value errors of the same actual outcome law. -/
theorem decision_regret (s : State) (q E C : ℝ) (hC : 0 ≤ C)
    (flows : Bool → Bool → PayFlow) (role : Role) (err : |q-probability s| ≤ E)
    (sensitivity : ∀ a, |reward flows role a true-reward flows role a false| ≤ C) (a : Bool) :
    value s flows role a ≤ value s flows role (greedy q flows role) + 2*C*E := by
  have ha := (abs_le.mp (payoff_error s q E C hC flows role err sensitivity a)).2
  have hg := (abs_le.mp (payoff_error s q E C hC flows role err sensitivity
    (greedy q flows role))).1
  have opt := greedy_maximizes q flows role a
  linarith

/-- Complete sample -> actual fitted parameters -> actual legal-payoff bound. -/
theorem actual_training_to_legal_decision {n : Nat} (hn : 0 < n) (s : ℚ × ℚ)
    (hs : 0 ≤ s.1 ∧ s.1 ≤ 1 ∧ 0 ≤ s.2 ∧ s.2 ≤ 1)
    (first : ℚ × ℚ) (rest : List (ℚ × ℚ)) (data : Fin n → Bool)
    (oracle : ideal s ∈ first :: rest) (r E C : ℝ) (hE : 0 ≤ E) (hC : 0 ≤ C)
    (radius : 2*r ≤ E^2)
    (uniform : ∀ z ∈ first :: rest, |risk s z-(empiricalScore loss data z : ℝ)| ≤ r)
    (flows : Bool → Bool → PayFlow) (role : Role)
    (sensitivity : ∀ a, |reward flows role a true-reward flows role a false| ≤ C) :
    proposed_empirical_fit loss (first :: rest) data = some (fitted first rest data) ∧
      ∀ a, value (embed s) flows role a ≤ value (embed s) flows role
        (greedy (forecast (fitted first rest data)) flows role) + 2*C*E := by
  have bound := actual_fit_prediction_bound hn s hs first rest data oracle r E hE radius uniform
  exact ⟨bound.1, fun a => decision_regret _ _ E C hC flows role bound.2 sensitivity a⟩

/-- The uniform training event is supplied by the existing iid risk theorem
for this exact coin, network loss and parameter class. -/
theorem actual_iid_risk_event {Ω : Type*} [MeasurableSpace Ω] {n : Nat}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (hn : 0 < n) (s : ℚ × ℚ)
    (first : ℚ × ℚ) (rest : List (ℚ × ℚ))
    (sample : Fin n → Ω → Bool) (hsm : ∀ i, Measurable (sample i))
    (independent : iIndepFun sample μ)
    (law : ∀ i, IdentDistrib (sample i) id μ (coin (embed s)))
    (δ : ℝ) (hd0 : 0 < δ) (hd1 : δ < 1) :
    1-δ ≤ μ.real {w | ∀ z ∈ first :: rest,
      |risk s z - (empiricalScore loss (fun i => sample i w) z : ℝ)| ≤
        finiteRadius n (first :: rest).toFinset.card δ} := by
  have old := u01_1_iid_empirical_risk_uniform μ (coin (embed s)) hn
    (first :: rest).toFinset ⟨first, by simp⟩ sample hsm independent law
    (fun z y => (loss z y : ℝ)) (fun _ _ => Measurable.of_discrete)
    (fun z _ y => loss_range z y) δ hd0 hd1
  simpa only [List.mem_toFinset, risk, empiricalScore_cast, empiricalMean, abs_sub_comm] using old

/-- The statistical event is actually consumed by the decision theorem. -/
theorem actual_iid_training_to_legal_decision {Ω : Type*} [MeasurableSpace Ω] {n : Nat}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (hn : 0 < n) (s : ℚ × ℚ)
    (hs : 0 ≤ s.1 ∧ s.1 ≤ 1 ∧ 0 ≤ s.2 ∧ s.2 ≤ 1)
    (first : ℚ × ℚ) (rest : List (ℚ × ℚ)) (oracle : ideal s ∈ first :: rest)
    (sample : Fin n → Ω → Bool) (hsm : ∀ i, Measurable (sample i))
    (independent : iIndepFun sample μ)
    (law : ∀ i, IdentDistrib (sample i) id μ (coin (embed s)))
    (δ : ℝ) (hd0 : 0 < δ) (hd1 : δ < 1) (E C : ℝ) (hE : 0 ≤ E) (hC : 0 ≤ C)
    (radius : 2 * finiteRadius n (first :: rest).toFinset.card δ ≤ E^2)
    (flows : Bool → Bool → PayFlow) (role : Role)
    (sensitivity : ∀ a, |reward flows role a true-reward flows role a false| ≤ C) :
    1-δ ≤ μ.real {w | ∀ a, value (embed s) flows role a ≤ value (embed s) flows role
      (greedy (forecast (fitted first rest (fun i => sample i w))) flows role) + 2*C*E} := by
  apply le_trans (actual_iid_risk_event μ hn s first rest sample hsm independent law δ hd0 hd1)
  apply measureReal_mono (μ := μ) (h₂ := measure_ne_top μ _)
  intro w hw
  exact (actual_training_to_legal_decision hn s hs first rest (fun i => sample i w) oracle
    _ E C hE hC radius hw flows role sensitivity).2

def cashSensitivity (flows : Bool → Bool → PayFlow) (role : Role) : ℝ :=
  max |reward flows role false true-reward flows role false false|
    |reward flows role true true-reward flows role true false|

theorem cashSensitivity_nonneg (flows : Bool → Bool → PayFlow) (role : Role) :
    0 ≤ cashSensitivity flows role := le_trans (abs_nonneg _) (le_max_left _ _)

theorem cashSensitivity_bounds (flows : Bool → Bool → PayFlow) (role : Role) (a : Bool) :
    |reward flows role a true-reward flows role a false| ≤ cashSensitivity flows role := by
  cases a
  · exact le_max_left _ _
  · exact le_max_right _ _

/-- All error constants are now computed from sample size, confidence and the
same two action-dependent consequence flows. -/
theorem computed_iid_decision_bound {Ω : Type*} [MeasurableSpace Ω] {n : Nat}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (hn : 0 < n) (s : ℚ × ℚ)
    (hs : 0 ≤ s.1 ∧ s.1 ≤ 1 ∧ 0 ≤ s.2 ∧ s.2 ≤ 1)
    (first : ℚ × ℚ) (rest : List (ℚ × ℚ)) (oracle : ideal s ∈ first :: rest)
    (sample : Fin n → Ω → Bool) (hsm : ∀ i, Measurable (sample i))
    (independent : iIndepFun sample μ)
    (law : ∀ i, IdentDistrib (sample i) id μ (coin (embed s)))
    (δ : ℝ) (hd0 : 0 < δ) (hd1 : δ < 1)
    (flows : Bool → Bool → PayFlow) (role : Role) :
    1-δ ≤ μ.real {w | ∀ a, value (embed s) flows role a ≤ value (embed s) flows role
      (greedy (forecast (fitted first rest (fun i => sample i w))) flows role) +
        2*cashSensitivity flows role * Real.sqrt (2*finiteRadius n (first :: rest).toFinset.card δ)} := by
  apply actual_iid_training_to_legal_decision μ hn s hs first rest oracle sample hsm independent law
    δ hd0 hd1 _ _ (Real.sqrt_nonneg _) (cashSensitivity_nonneg flows role) _ flows role
    (cashSensitivity_bounds flows role)
  rw [Real.sq_sqrt (by unfold finiteRadius; positivity)]

#print axioms original_network_represents_response
#print axioms risk_excess
#print axioms actual_fit_prediction_bound
#print axioms payoff_error
#print axioms decision_regret
#print axioms actual_training_to_legal_decision
#print axioms actual_iid_risk_event
#print axioms actual_iid_training_to_legal_decision
#print axioms computed_iid_decision_bound
#print axioms realizedRadius_uniform

end
end LegalMath20261109.TrainedDecision
