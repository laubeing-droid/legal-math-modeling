import JurisLean.Candidates.U06_1OriginalCashIdentityInstances20261101

/-! Original 06.1: existing ledger identities and the concrete cash bridges. -/
open JurisLean.Candidates.Final20261021
open JurisLean.Candidates.U06_1OriginalCashIdentityInstances20261101

#check payloadCash
#check RealCashEvent
#check fromQCash
#check fromQPayload
#check cashFlow
#check netCash
#check labelCash
#check qCashFlow
#check qCashAccounts
#check realCashAccounts
#print axioms fromQPayload_preserves_fields
#print axioms performance_appends_payload_cash
#check commit_payment_appends_payload_cash
#print axioms commit_payment_appends_payload_cash
#check validated_commit_preserves_cash_ids
#print axioms validated_commit_preserves_cash_ids
#check cash_sum_reindexed_by_id
#print axioms cash_sum_reindexed_by_id
#check rename_preserves_cash
#print axioms rename_preserves_cash
#check event_id_renaming_preserves_cash
#print axioms event_id_renaming_preserves_cash
#check alias_preserves_cash
#print axioms alias_preserves_cash
#check disjoint_id_cash_additive
#print axioms disjoint_id_cash_additive
#check actual_cash_accounts_conserve
#print axioms actual_cash_accounts_conserve
#check q_ledger_cash_accounts_conserve
#print axioms q_ledger_cash_accounts_conserve
#check q_ledger_cash_vector_matches_real_cash
#print axioms q_ledger_cash_vector_matches_real_cash
#check three_labels_one_six
#print axioms three_labels_one_six
#check two_real_six_payments_keep_debt
#print axioms two_real_six_payments_keep_debt
#check two_real_six_payment_account_cash
#print axioms two_real_six_payment_account_cash

example (g : Gamma) (d : DebtRecord) :
    ((Trace.initial g d).state.cash.map CashEvent.id).Nodup := by
  simp [Trace.initial]

#print axioms Ledger.u09_2_cash_conservation
#print axioms Ledger.u09_2_cash_by_account
