import JurisLean.Candidates.SourceStages20261027

#check JurisLean.Candidates.SourceStages20261027.successful_binding_reads_actual_rows
#print axioms JurisLean.Candidates.SourceStages20261027.successful_binding_reads_actual_rows
#check JurisLean.Candidates.SourceStages20261027.deterministic_binding_data_unique
#print axioms JurisLean.Candidates.SourceStages20261027.deterministic_binding_data_unique
#check JurisLean.Candidates.SourceStages20261027.quantity_step_is_existing_ledger_step
#print axioms JurisLean.Candidates.SourceStages20261027.quantity_step_is_existing_ledger_step
#check JurisLean.Candidates.SourceStages20261027.payment_preserves_complete_nonquantity_fields
#print axioms JurisLean.Candidates.SourceStages20261027.payment_preserves_complete_nonquantity_fields
#check JurisLean.Candidates.SourceStages20261027.scalar_and_item_projections_commute
#print axioms JurisLean.Candidates.SourceStages20261027.scalar_and_item_projections_commute
#check JurisLean.Candidates.SourceStages20261027.four_stages_use_actual_previous_output
#print axioms JurisLean.Candidates.SourceStages20261027.four_stages_use_actual_previous_output
#check JurisLean.Candidates.SourceStages20261027.adjacent_formation_projection
#print axioms JurisLean.Candidates.SourceStages20261027.adjacent_formation_projection
#check JurisLean.Candidates.SourceStages20261027.two_payments_balance_and_cash
#print axioms JurisLean.Candidates.SourceStages20261027.two_payments_balance_and_cash
#check JurisLean.Candidates.SourceStages20261027.frame_contains_actual_computed_stages
#print axioms JurisLean.Candidates.SourceStages20261027.frame_contains_actual_computed_stages
#check JurisLean.Candidates.SourceStages20261027.accepted_view_binds_both_actual_payments
#print axioms JurisLean.Candidates.SourceStages20261027.accepted_view_binds_both_actual_payments
#check JurisLean.Candidates.SourceStages20261027.public_consumer_reads_actual_extraction
#print axioms JurisLean.Candidates.SourceStages20261027.public_consumer_reads_actual_extraction
#check JurisLean.Candidates.SourceStages20261027.independent_local_witnesses_iff_tuple
#print axioms JurisLean.Candidates.SourceStages20261027.independent_local_witnesses_iff_tuple
#check JurisLean.Candidates.SourceStages20261027.compatible_fibers_compose_local_contracts
#print axioms JurisLean.Candidates.SourceStages20261027.compatible_fibers_compose_local_contracts
#check JurisLean.Candidates.SourceStages20261027.nonempty_local_models_can_have_empty_common_fiber
#print axioms JurisLean.Candidates.SourceStages20261027.nonempty_local_models_can_have_empty_common_fiber
#check JurisLean.Candidates.SourceStages20261027.fixed_background_preserves_exact_old_contracts
#print axioms JurisLean.Candidates.SourceStages20261027.fixed_background_preserves_exact_old_contracts
#check JurisLean.Candidates.SourceStages20261027.exact_nat_bridge_is_unique
#print axioms JurisLean.Candidates.SourceStages20261027.exact_nat_bridge_is_unique
#check JurisLean.Candidates.SourceStages20261027.same_case_projection_transfers_local_contracts
#print axioms JurisLean.Candidates.SourceStages20261027.same_case_projection_transfers_local_contracts
#check JurisLean.Candidates.SourceStages20261027.static_source_semantic_and_quantity_bridge
#print axioms JurisLean.Candidates.SourceStages20261027.static_source_semantic_and_quantity_bridge

open JurisLean.Candidates.Final20261021
open JurisLean.Candidates.SourceCompilation20261027
open JurisLean.Candidates.SourceStages20261027

def stageGamma : Gamma := ⟨⟨1⟩, 1, 1, "synthetic", 3, 7, 8, ⟨10⟩, ⟨20⟩, ⟨20⟩, 1, 1, 1⟩
def stageTag : AmountTag := ⟨"CNY", "yuan", 8⟩
def stageMaterial : MaterialSnapshot :=
  ⟨stageGamma, 2, 3, [⟨⟨1⟩, 0, 0, "relation 9 formed; two distinct payments of 7 against debt 10"⟩]⟩
def stageQuote {A : Type} (value : A) : Quoted A := ⟨⟨⟨1⟩, 0, 2, 3⟩, value⟩
def stagePayment (key : Nat) : FullPayment :=
  ⟨⟨key⟩, 20, ⟨⟨1⟩, 1, ⟨9⟩, ⟨1⟩, ⟨2⟩, ⟨7, stageTag⟩, ⟨1⟩, ⟨key + 100⟩, 8, ⟨10⟩⟩⟩
def stageView : ConsumedView :=
  { record := stageQuote ⟨⟨0, 1, 2, 1, .normScope⟩, 3, true⟩
    relations := [stageQuote ⟨⟨9⟩, ⟨1⟩, ⟨2⟩, ⟨10, stageTag⟩, "all debt metadata retained"⟩]
    ledger := [stageQuote ⟨⟨20, .principal, .contractStip, 2, .supported, 10⟩, ⟨9⟩, ⟨1⟩, stageTag⟩]
    payments := [stageQuote (stagePayment 10), stageQuote (stagePayment 11)]
    initialHistory := []
    historyEvents := [stageQuote (.formation ⟨1⟩ ⟨9⟩),
      stageQuote (.payment ⟨1⟩ ⟨10⟩), stageQuote (.payment ⟨1⟩ ⟨11⟩)]
    objects := [stageQuote (⟨1⟩, .relation ⟨9⟩)]
    observed := stageQuote (⟨1⟩, ⟨9⟩), atoms := [stageQuote 1] }
def runStageView (view : ConsumedView) : Result SourceFrame :=
  sourceStages stageMaterial 0 [⟨stageMaterial, 0, view⟩]
def stageKnown (result : Result SourceFrame) : Bool :=
  match result with | .known _ => true | _ => false
def updateStagePayment (update : FullPayment → FullPayment) : ConsumedView :=
  { stageView with payments := [stageQuote (update (stagePayment 10)), stageQuote (stagePayment 11)] }

/-- info: true -/
#guard_msgs in
#eval match runStageView stageView with
  | .known out => decide (
      Ledger.balance out.stages.beforeFormation.state = 10 ∧
      Ledger.balance out.stages.afterFormation.state = 10 ∧
      Ledger.balance out.stages.afterFirst.state = 3 ∧ Ledger.balance out.stages.afterSecond.state = 0 ∧
      out.stages.afterFirst.state.allocated = 7 ∧ out.stages.afterSecond.state.allocated = 10 ∧
      out.stages.afterFirst.state.surplus = 0 ∧ out.stages.afterSecond.state.surplus = 4 ∧
      out.stages.afterSecond.state.paid = 14 ∧ out.stages.afterSecond.state.cash.length = 2 ∧
      out.stages.afterSecond.quantity.item.amount = 0)
  | _ => false

/-- info: true -/
#guard_msgs in
#eval match runStageView stageView with
  | .known out => decide (out.stages.beforeFormation.relations.length = 0 ∧
      out.stages.afterFormation.relations.length = 1 ∧ out.stages.afterSecond.relations.length = 1 ∧
      out.stages.afterFirst.state.formations = out.stages.afterSecond.state.formations ∧
      out.stages.afterFirst.state.debt.amount ≠ out.stages.afterSecond.state.debt.amount ∧
      out.stages.afterSecond.quantity.item.kind = .principal ∧
      out.stages.afterSecond.quantity.item.basis = .contractStip ∧
      out.stages.afterSecond.quantity.item.status = .supported ∧
      out.stages.afterSecond.state.debt.metadata = "all debt metadata retained")
  | _ => false

/-- info: true -/
#guard_msgs in
#eval !stageKnown (runStageView { stageView with payments := stageView.payments ++ [stageQuote (stagePayment 10)] })
/-- info: true -/
#guard_msgs in
#eval !stageKnown (runStageView { stageView with ledger := stageView.ledger ++ stageView.ledger })
/-- info: true -/
#guard_msgs in
#eval !stageKnown (runStageView { stageView with relations := stageView.relations ++ stageView.relations })
/-- info: true -/
#guard_msgs in
#eval !stageKnown (runStageView (updateStagePayment fun p => { p with targetDebt := 99 }))
/-- info: true -/
#guard_msgs in
#eval !stageKnown (runStageView (updateStagePayment fun p => { p with payload := { p.payload with payer := ⟨99⟩ } }))
/-- info: true -/
#guard_msgs in
#eval !stageKnown (runStageView (updateStagePayment fun p => { p with payload := { p.payload with payee := ⟨99⟩ } }))
/-- info: true -/
#guard_msgs in
#eval !stageKnown (runStageView (updateStagePayment fun p => { p with payload := { p.payload with
  amount := ⟨7, ⟨"USD", "yuan", 8⟩⟩ } }))
/-- info: true -/
#guard_msgs in
#eval !stageKnown (runStageView (updateStagePayment fun p => { p with payload := { p.payload with caseRevision := 99 } }))
/-- info: true -/
#guard_msgs in
#eval !stageKnown (runStageView (updateStagePayment fun p => { p with payload := { p.payload with normVersion := 99 } }))
/-- info: true -/
#guard_msgs in
#eval !stageKnown (runStageView (updateStagePayment fun p => { p with payload := { p.payload with factDate := ⟨11⟩ } }))
/-- info: true -/
#guard_msgs in
#eval !stageKnown (runStageView (updateStagePayment fun p => { p with payload := { p.payload with amount := ⟨-1, stageTag⟩ } }))
/-- info: true -/
#guard_msgs in
#eval !stageKnown (runStageView { stageView with historyEvents :=
  [stageQuote (.formation ⟨1⟩ ⟨9⟩), stageQuote (.payment ⟨99⟩ ⟨10⟩), stageQuote (.payment ⟨1⟩ ⟨11⟩)] })
/-- info: true -/
#guard_msgs in
#eval !stageKnown (runStageView { stageView with historyEvents :=
  [stageQuote (.formation ⟨1⟩ ⟨99⟩), stageQuote (.payment ⟨1⟩ ⟨10⟩), stageQuote (.payment ⟨1⟩ ⟨11⟩)] })
/-- info: true -/
#guard_msgs in
#eval !stageKnown (runStageView (updateStagePayment fun p => { p with payload := { p.payload with cashId := ⟨111⟩ } }))
/-- info: true -/
#guard_msgs in
#eval match bindPayment ⟨stageMaterial, 0, stageView⟩ 99 with
  | .unknown .missingEvidence => true | _ => false
/-- info: true -/
#guard_msgs in
#eval match bindPayment ⟨stageMaterial, 0, stageView⟩ 0 with
  | .unknown .missingEvidence => true | _ => false
/-- info: true -/
#guard_msgs in
#eval match runStageView (updateStagePayment fun p => { p with payload := { p.payload with amount := ⟨1/2, stageTag⟩ } }) with
  | .known out => decide (Ledger.balance out.stages.afterFirst.state = 19/2 ∧
      Ledger.balance out.stages.afterSecond.state = 5/2 ∧
      out.stages.afterSecond.quantity.item.amount = 5/2 ∧ (0 : ℚ) ≠ 1/2)
  | _ => false
/-- info: true -/
#guard_msgs in
#eval !stageKnown (sourceStages { stageMaterial with parseVersion := 99 } 0 [⟨stageMaterial, 0, stageView⟩])
