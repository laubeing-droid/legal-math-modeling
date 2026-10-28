import JurisLean.Candidates.Final20261021.RSI
import JurisLean.Candidates.LearningBoundary20261027
import JurisLean.Candidates.LearningBridge20261027

namespace JurisLean.Candidates.U13_3DebtClosureAudit20261028

open MeasureTheory

-- Frozen U13.3: the inverse is required only on represented inputs.
-- Equality substitution preserves the risk for the same law and loss.
-- This bridge does not assert that the loss integral exists as a finite expectation.
theorem same_loss_risk_under_used_inverse
    {Ω Z Z' Y : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (phi : Ω → Z) (b : Z → Z') (back : Z' → Z)
    (g : Z → Y) (inverse_on_used : ∀ ω, back (b (phi ω)) = phi ω)
    (loss : Y → Ω → ℝ) :
    (∫ ω, loss (g (back (b (phi ω)))) ω ∂μ) =
      (∫ ω, loss (g (phi ω)) ω ∂μ) := by
  exact congrArg (fun prediction : Ω → Y => ∫ ω, loss (prediction ω) ω ∂μ)
    (funext (fun ω => congrArg g (inverse_on_used ω)))

-- The accepted two-world theorem also applies to the empty sample.
example (learner : (Fin 0 → Bool × Bool) → Bool → Bool) :
    LearningBoundary20261027.visibleTraining 0 false =
        LearningBoundary20261027.visibleTraining 0 true ∧
      LearningBoundary20261027.worldTarget false ≠ LearningBoundary20261027.worldTarget true ∧
      ∃ hiddenLabel, LearningBoundary20261027.pointPopulationRisk true
        (LearningBoundary20261027.worldTarget hiddenLabel)
        (learner (LearningBoundary20261027.visibleTraining 0 false)) = 1 :=
  LearningBoundary20261027.u01_3_two_worlds_same_training_uncontrolled_deployment 0 learner

-- At the unobserved input the two normalized worlds have label 0 and label 1.
example : LearningBoundary20261027.worldTarget false true = false ∧
    LearningBoundary20261027.worldTarget true true = true := ⟨rfl, rfl⟩

end JurisLean.Candidates.U13_3DebtClosureAudit20261028

#check JurisLean.Candidates.Final20261021.RSI.u13_3_representation_transfer
#print axioms JurisLean.Candidates.Final20261021.RSI.u13_3_representation_transfer

#check JurisLean.Candidates.Final20261021.RSI.u13_1_noninterference
#print axioms JurisLean.Candidates.Final20261021.RSI.u13_1_noninterference

#check JurisLean.Candidates.LearningBoundary20261027.pointWeight_is_probability
#print axioms JurisLean.Candidates.LearningBoundary20261027.pointWeight_is_probability

#check JurisLean.Candidates.LearningBoundary20261027.u01_3_two_worlds_same_training_uncontrolled_deployment
#print axioms JurisLean.Candidates.LearningBoundary20261027.u01_3_two_worlds_same_training_uncontrolled_deployment

#check JurisLean.Candidates.U13_3DebtClosureAudit20261028.same_loss_risk_under_used_inverse
#print axioms JurisLean.Candidates.U13_3DebtClosureAudit20261028.same_loss_risk_under_used_inverse

#check JurisLean.Candidates.Final20261021.RSI.u13_4_missing_checkpoint_no_default
#print axioms JurisLean.Candidates.Final20261021.RSI.u13_4_missing_checkpoint_no_default
