import JurisLean.FiniteMonotoneIteration
import JurisLean.DungFixedPoint
import JurisLean.HornFixedPoint
import JurisLean.WeightedSupNorm

/-! Axiom audit for formal core release v1. -/

open FiniteMonotoneIteration
#print axioms exists_fixpoint_le_card
#print axioms fixed_at_card

open DungFixedPoint
#print axioms grounded_is_least_fixed_point

open HornFixedPoint
#print axioms horn_completeness
#print axioms horn_result_is_minimal_model

open WeightedSupNorm
#print axioms weightedSupDist_complete
