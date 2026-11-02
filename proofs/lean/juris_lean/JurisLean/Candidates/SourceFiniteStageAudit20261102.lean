import JurisLean.Candidates.SourceStagesAudit20261027

namespace JurisLean.Candidates.SourceStages20261027

theorem finite_stage_compatible_counterexample :
    ∃ out : SourceFrame,
      runStageView stageView = .known out ∧
      out.stages.beforeFormation.relations ≠ out.stages.afterFormation.relations ∧
      out.stages.afterFirst.relations = out.stages.afterSecond.relations ∧
      (∀ r, JurisLean.Seams.InstitutionalEffects.forms out.stages.afterFirst.relations r ↔
        JurisLean.Seams.InstitutionalEffects.forms out.stages.afterSecond.relations r) ∧
      out.stages.afterFirst.state.debt.amount.value = (3 : ℚ) ∧
      out.stages.afterSecond.state.debt.amount.value = (0 : ℚ) ∧
      out.stages.afterFirst.state ≠ out.stages.afterSecond.state := by
  obtain ⟨out, accepted⟩ := nonempty_source_stage_fixture
  have computed :
      (match runStageView stageView with
       | .known frame =>
           decide (frame.stages.beforeFormation.relations ≠
               frame.stages.afterFormation.relations ∧
             frame.stages.afterFirst.relations = frame.stages.afterSecond.relations ∧
             frame.stages.afterFirst.state.debt.amount.value = (3 : ℚ) ∧
             frame.stages.afterSecond.state.debt.amount.value = (0 : ℚ))
       | _ => false) = true := by decide +kernel
  have data :
      out.stages.beforeFormation.relations ≠ out.stages.afterFormation.relations ∧
      out.stages.afterFirst.relations = out.stages.afterSecond.relations ∧
      out.stages.afterFirst.state.debt.amount.value = (3 : ℚ) ∧
      out.stages.afterSecond.state.debt.amount.value = (0 : ℚ) :=
    of_decide_eq_true (by simpa only [accepted] using computed)
  obtain ⟨boundary_ne, relations_eq, first_amount, second_amount⟩ := data
  refine ⟨out, accepted, boundary_ne, relations_eq, ?_, first_amount, second_amount, ?_⟩
  · intro r
    rw [relations_eq]
  · intro states_eq
    have amounts_eq := congrArg
      (fun s : JurisLean.Candidates.Final20261021.Ledger.State => s.debt.amount.value) states_eq
    have impossible : (3 : ℚ) = 0 :=
      first_amount.symm.trans (amounts_eq.trans second_amount)
    exact (by decide : (3 : ℚ) ≠ 0) impossible

#check JurisLean.Candidates.SourceStages20261027.finite_stage_compatible_counterexample
#print axioms JurisLean.Candidates.SourceStages20261027.finite_stage_compatible_counterexample

end JurisLean.Candidates.SourceStages20261027
