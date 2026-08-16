import JurisLean.FiniteMonotoneIteration
import JurisLean.DungFixedPoint
import JurisLean.HornFixedPoint
import JurisLean.WeightedSupNorm

/-! Axiom audit for formal core release v1. -/

open FiniteMonotoneSystem
#print axioms exists_fixpoint_le_card
#print axioms fixed_at_card

open DungAAF
#print axioms grounded_is_least_fixed_point

open HornSystem
#print axioms horn_completeness
#print axioms horn_result_is_minimal_model

#print axioms weightedSupDist_complete
