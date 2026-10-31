import JurisLean.Candidates.U06_OriginalFiniteExamples20261031
import JurisLean.Candidates.U09_2OriginalClosureAudit20261030
import JurisLean.Candidates.SourceRepresentationAudit20261027
import JurisLean.Candidates.IntervalDecisionConsumerAudit20261027
import JurisLean.Candidates.U06_2EquilibriumTransfer20261030
import JurisLean.Candidates.U11_1NamedCausalBridge20261030

open JurisLean.Candidates.U06_OriginalFiniteExamples20261031

#check adding_resolved_alias_preserves_cash
#print axioms adding_resolved_alias_preserves_cash

#check labels_and_actual_repayments_differ
#print axioms labels_and_actual_repayments_differ

#check higher_success_probability_can_have_lower_expected_cash
#print axioms higher_success_probability_can_have_lower_expected_cash

#check concaveUtility_strict_jensen
#print axioms concaveUtility_strict_jensen

#check same_expected_cash_different_concave_utility
#print axioms same_expected_cash_different_concave_utility

#check distinct_unique_branch_optima
#print axioms distinct_unique_branch_optima

#check unique_robust_policy_differs_from_both_branch_optima
#print axioms unique_robust_policy_differs_from_both_branch_optima

-- Direct library reuse, without new synonymous declarations.
#check Finset.sum_map
#check Finset.sum_union
#check Finset.exists_mem_eq_sup'

-- The fixed table has a deterministic terminal law for each branch.
-- There is no law on the branch carrier.
example (policy : Fin 3) (branch : Bool) :
    Math.Probability.expect (PMF.pure ())
      (fun _ : Unit => branchValue policy branch) =
        branchValue policy branch := by
  simp only [Math.Probability.expect_pure]

#check JurisLean.Candidates.Final20261021.Ledger.u09_2_cash_by_account
#check JurisLean.Candidates.SourceRepresentation20261027.semantic_key_exact
#check JurisLean.Candidates.SourceRepresentation20261027.copies_and_distinct_payments_are_separate

#check JurisLean.Candidates.IntervalDecisionConsumer20261027.binary_evaluation_uses_exact_amount_and_one_cost
#check JurisLean.Candidates.IntervalDecisionConsumer20261027.explicit_maximin_preserves_permission_and_risk
#check JurisLean.Candidates.IntervalDecisionConsumer20261027.maximin_none_exactly_when_infeasible
#check JurisLean.Candidates.IntervalDecisionConsumer20261027.missing_identification_cannot_succeed

#check JurisLean.Candidates.U06_2EquilibriumTransfer20261030.finite_expect_affine
#check JurisLean.Candidates.U06_2EquilibriumTransfer20261030.finite_expect_positiveAffine_preference
#check JurisLean.Candidates.Final20261021.Decision.u06_4_threshold_increasing
#check JurisLean.Candidates.U11_1NamedCausalBridge20261030.finite_g_formula_from_conditions
