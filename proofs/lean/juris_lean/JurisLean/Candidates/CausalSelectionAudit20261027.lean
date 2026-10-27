import JurisLean.Candidates.CausalSelection20261027

#check JurisLean.Candidates.CausalSelection20261027.full_selection_kernel_normalized
#print axioms JurisLean.Candidates.CausalSelection20261027.full_selection_kernel_normalized
#check JurisLean.Candidates.CausalSelection20261027.full_selection_kernel_nonnegative
#print axioms JurisLean.Candidates.CausalSelection20261027.full_selection_kernel_nonnegative
#check JurisLean.Candidates.CausalSelection20261027.selected_weight_recovery
#print axioms JurisLean.Candidates.CausalSelection20261027.selected_weight_recovery
#check JurisLean.Candidates.CausalSelection20261027.selected_database_requires_population_normalization
#print axioms JurisLean.Candidates.CausalSelection20261027.selected_database_requires_population_normalization
#check JurisLean.Candidates.CausalSelection20261027.selection_countermodels_have_identical_visible_law
#print axioms JurisLean.Candidates.CausalSelection20261027.selection_countermodels_have_identical_visible_law
#check JurisLean.Candidates.CausalSelection20261027.selected_association_is_not_population_effect
#print axioms JurisLean.Candidates.CausalSelection20261027.selected_association_is_not_population_effect
#check JurisLean.Candidates.CausalSelection20261027.no_visible_law_estimator_identifies_both
#print axioms JurisLean.Candidates.CausalSelection20261027.no_visible_law_estimator_identifies_both
#check JurisLean.Candidates.CausalSelection20261027.transport_requires_overlap_and_mean_stability
#print axioms JurisLean.Candidates.CausalSelection20261027.transport_requires_overlap_and_mean_stability
#check JurisLean.Candidates.CausalSelection20261027.actual_transport_reweights_the_target
#print axioms JurisLean.Candidates.CausalSelection20261027.actual_transport_reweights_the_target
#check JurisLean.Candidates.CausalSelection20261027.source_and_target_mix_do_not_identify_new_effect
#print axioms JurisLean.Candidates.CausalSelection20261027.source_and_target_mix_do_not_identify_new_effect

open JurisLean.Candidates.Final20261021
open JurisLean.Candidates.CausalSelection20261027

namespace CausalSelectionFixture
def mass (_x : Bool) : ℚ := 1/2
def latent (_x _u : Bool) : ℚ := 1/2
def assignment (_x : Bool) (a : Bool) : ℚ := if a then 1/4 else 3/4
def recording (_x _a : Bool) : ℚ := 1/2
def response (_x _u : Bool) (a : Bool) : ℚ := Behavior.indicator a

/-- info: true -/
#guard_msgs in
#eval decide ((∑ x : Bool, ∑ u : Bool, ∑ a : Bool, ∑ s : Bool,
  selectionJoint mass latent assignment recording x u a s) = 1 ∧
  selectionRecoveryValue mass latent assignment recording response true = 1 ∧
  interventionValue mass latent response true = 1)

/-- info: true -/
#guard_msgs in
#eval decide (selectionPopulationMass mass latent assignment recording = 1/2 ∧
  selectionRecoveryValue mass latent assignment recording response true /
    selectionPopulationMass mass latent assignment recording = 2)

/-- info: true -/
#guard_msgs in
#eval decide (∀ a s : Bool, ∀ y : Option Bool,
  visibleSelectionMass colliderVisible (a, s, y) = visibleSelectionMass directVisible (a, s, y))

/-- info: true -/
#guard_msgs in
#eval decide (selectedVisibleMean colliderVisible true = 1 ∧
  selectedVisibleMean colliderVisible false = 0 ∧ selectionEffect colliderPotential = 0 ∧
  selectedVisibleMean directVisible true = 1 ∧
  selectedVisibleMean directVisible false = 0 ∧ selectionEffect directPotential = 1)

/-- info: true -/
#guard_msgs in
#eval decide (Behavior.proposed_causal_evidence
  [selectionEffect colliderPotential, selectionEffect directPotential] = .unknown .notIdentified)

/-- info: true -/
#guard_msgs in
#eval decide (populationEffect sourceMix stableGroupEffect = 9/50 ∧
  transportedValue sourceMix targetMix stableGroupEffect = -9/50 ∧
  populationEffect changedScenario.targetDistribution changedScenario.targetEffects = 1 ∧
  targetMix false / sourceMix false = 1/4 ∧ targetMix true / sourceMix true = 4)

end CausalSelectionFixture

