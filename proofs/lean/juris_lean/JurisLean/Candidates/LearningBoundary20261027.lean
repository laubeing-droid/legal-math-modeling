import JurisLean.Candidates.LearningERM20261027

/-!
Original questions 01.1 and 01.5 / correction S01. These witnesses use
normalized finite populations and the actual empirical minimizer. A risk
about a declared label does not turn that label into a fact or authorization.
The two-world theorem quantifies over any deterministic learner using the
same visible sample; no unseen label is supplied to that learner.
-/

namespace JurisLean.Candidates.LearningBoundary20261027

open JurisLean.Candidates.LearningRisk20261027
open JurisLean.Candidates.LearningERM20261027

def pointWeight (visible : Bool) (x : Bool) : ℝ := if x = visible then 1 else 0

def pointPopulationRisk (visible : Bool) (target h : Bool → Bool) : ℝ :=
  finiteBinaryRisk (pointWeight visible) (fun x => if target x then 1 else 0) h

theorem pointWeight_is_probability (visible : Bool) :
    (∀ x, 0 ≤ pointWeight visible x) ∧ ∑ x, pointWeight visible x = 1 := by
  have univ : (Finset.univ : Finset Bool) = {false, true} := by decide
  constructor
  · intro x
    simp only [pointWeight]
    split <;> norm_num
  · cases visible <;> norm_num [pointWeight, univ]

theorem pointPopulationRisk_eq (visible : Bool) (target h : Bool → Bool) :
    pointPopulationRisk visible target h = if h visible = target visible then 0 else 1 := by
  have univ : (Finset.univ : Finset Bool) = {false, true} := by decide
  cases visible <;> cases hf : h false <;> cases ht : h true <;>
    cases tf : target false <;> cases tt : target true <;>
    norm_num [pointPopulationRisk, finiteBinaryRisk, pointWeight, univ, hf, ht, tf, tt]

def actualConstantFit (label : Bool) : Bool → Bool := fun _ =>
  fitNonempty (fun (h z : Bool) => if h = z then (0 : ℚ) else 1)
    false [true] (fun _ : Fin 2 => label)

theorem actualConstantFit_value (label x : Bool) : actualConstantFit label x = label := by
  cases label <;> norm_num [actualConstantFit, fitNonempty, selectMinimum, empiricalScore]

theorem u01_1_actual_fit_label_risk_not_truth_risk :
    pointPopulationRisk false (fun _ => true) (actualConstantFit true) = 0 ∧
      pointPopulationRisk false (fun _ => false) (actualConstantFit true) = 1 := by
  simp [pointPopulationRisk_eq, actualConstantFit_value]

theorem u01_3_actual_fit_zero_train_one_deploy :
    pointPopulationRisk false id (actualConstantFit false) = 0 ∧
      pointPopulationRisk true id (actualConstantFit false) = 1 := by
  simp [pointPopulationRisk_eq, actualConstantFit_value]

def worldTarget (hiddenLabel : Bool) (visible : Bool) : Bool :=
  if visible then hiddenLabel else false

def visibleTraining (n : ℕ) (hiddenLabel : Bool) : Fin n → Bool × Bool :=
  fun _ => (false, worldTarget hiddenLabel false)

theorem u01_3_two_worlds_same_training_uncontrolled_deployment
    (n : ℕ) (learner : (Fin n → Bool × Bool) → Bool → Bool) :
    visibleTraining n false = visibleTraining n true ∧
      worldTarget false ≠ worldTarget true ∧
      ∃ hiddenLabel, pointPopulationRisk true (worldTarget hiddenLabel)
        (learner (visibleTraining n false)) = 1 := by
  refine ⟨rfl, ?_, ?_⟩
  · intro same
    have atUnseen := congrFun same true
    simp [worldTarget] at atUnseen
  · cases chosen : learner (visibleTraining n false) true with
    | false =>
        refine ⟨true, ?_⟩
        simp [pointPopulationRisk_eq, worldTarget, chosen]
    | true =>
        refine ⟨false, ?_⟩
        simp [pointPopulationRisk_eq, worldTarget, chosen]

-- Authorization is an independent legal input. Even a perfect declared-label
-- fit has a nonempty context in which the predicted action is not authorized.
theorem u01_6_perfect_fit_does_not_supply_authorization :
    pointPopulationRisk false (fun _ => true) (actualConstantFit true) = 0 ∧
      let allowed : Bool → Prop := fun action => action = false
      ¬ allowed (actualConstantFit true false) := by
  simp [pointPopulationRisk_eq, actualConstantFit_value]

end JurisLean.Candidates.LearningBoundary20261027
