
import Mathlib.Data.Finset.Basic
import JurisLean.DungFixedPoint
import JurisLean.HornFixedPoint

/-! Axiom audit for formal core release. -/

-- AAF core
#print axioms DungAAF.F_monotone
#print axioms DungAAF.iteration_monotone
#print axioms DungAAF.groundedSpec_is_fixed_point
#print axioms DungAAF.groundedSpec_is_least_fixed_point
#print axioms DungAAF.groundedSpec_unique_least_fixed_point
#print axioms DungAAF.self_attack_precise_theorem
#print axioms DungAAF.finite_termination
#print axioms DungAAF.iteration_bound
#print axioms DungAAF.labelling_partition
#print axioms DungAAF.in_soundness
#print axioms DungAAF.out_soundness
#print axioms DungAAF.undecided_characterization

-- Horn core
#print axioms HornSystem.horn_result_fixed_point
#print axioms HornSystem.horn_result_least_fixed_point
#print axioms HornSystem.horn_result_is_minimal_model
#print axioms HornSystem.horn_finite_termination

-- FiniteMonotoneIteration
#print axioms FiniteMonotoneSystem.exists_fixpoint_le_card
#print axioms FiniteMonotoneSystem.fixed_at_card
