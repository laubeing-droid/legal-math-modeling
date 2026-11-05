import JurisLean.Candidates.AdaptiveRoundLedger20261027
import JurisLean.Candidates.FeedbackLabelSemantics20261027

/-!
Original 14.4 L109 needs a finite witness connecting a change in the learner's
proposals to the fitter's returned proxy losses and the opposite target-risk
ordering. The two-point sample and risk computations are reused.
-/
namespace JurisLean.Candidates.U14_4LearnerProxyWitness20261106

open JurisLean.Candidates.AdaptiveRoundLedger20261027 (RoundLearner)
open JurisLean.Candidates.FeedbackLabelSemantics20261027
open JurisLean.Candidates.LearningConsumer20261027
open JurisLean.Candidates.LearningERM20261027

theorem learner_proxy_gain_worsens_target_risk :
    let before : RoundLearner := ⟨0, []⟩
    let after : RoundLearner := ⟨1, [[1, 0]]⟩
    let fit (learner : RoundLearner) :=
      fitTable twoPointProtocol binaryLoss ([0, 0] :: learner.proposals) pseudoData
    ∃ old next : FittedTable,
      fit before = .known old ∧ fit after = .known next ∧
      next.empiricalRisk < old.empiricalRisk ∧
      empiricalScore (tableLoss binaryLoss) trueData old.table <
        empiricalScore (tableLoss binaryLoss) trueData next.table := by
  have witness := suggestions_fit_better_but_true_risk_worsens
  refine ⟨⟨twoPointProtocol, [0, 0], 2, 1/2⟩, ⟨twoPointProtocol, [1, 0], 2, 0⟩,
    ?_, ?_, ?_, ?_⟩
  · norm_num [fitTable, twoPointProtocol, proposed_empirical_fit, fitNonempty,
      selectMinimum, empiricalScore, tableLoss, binaryLoss, pseudoData, Fin.sum_univ_two]
  · exact witness.1
  · norm_num
  · change empiricalScore (tableLoss binaryLoss) trueData [0, 0] <
      empiricalScore (tableLoss binaryLoss) trueData [1, 0]
    rw [witness.2.2.2.1, witness.2.2.2.2]
    norm_num

#check learner_proxy_gain_worsens_target_risk
#print axioms learner_proxy_gain_worsens_target_risk

end JurisLean.Candidates.U14_4LearnerProxyWitness20261106
