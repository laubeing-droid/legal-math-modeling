import JurisLean.FiniteMonotoneIteration
import JurisLean.DungFixedPoint
import JurisLean.HornFixedPoint
import JurisLean.WeightedSupNorm
import JurisLean.ULMAxiomAudit
import JurisLean.KernelV3
import JurisLean.Hohfeld
import JurisLean.BanachCertificate

/-! Axiom audit for formal core release v1. -/

open FiniteMonotoneSystem
#print axioms exists_fixpoint_le_card
#print axioms fixed_at_card

open DungAAF
#print axioms grounded_is_least_fixed_point

open HornSystem
#print axioms horn_completeness
#print axioms horn_result_unique_least_fixed_point

#print axioms weightedSupDist_separates_points

#print axioms JurisLean.KernelV3.mkEval_judgment
#print axioms JurisLean.KernelV3.mkEval_disposition
#print axioms JurisLean.KernelV3.judgment_notEstablished_does_not_force_truth_false
#print axioms JurisLean.KernelV3.transfer_confirmatory_identity
#print axioms JurisLean.KernelV3.transfer_performance_identity
#print axioms JurisLean.KernelV3.transfer_proceduralBinding_identity
#print axioms JurisLean.KernelV3.transfer_constitutive_updates_R
#print axioms JurisLean.KernelV3.transfer_constitutive_preserves_K
#print axioms JurisLean.KernelV3.narrowCandidates_preserves_R
#print axioms JurisLean.KernelV3.narrowCandidates_is_subset
#print axioms JurisLean.KernelV3.evalBatch_only_returns_asked_questions
#print axioms JurisLean.KernelV3.procedural_judgment_does_not_auto_create_substantive
#print axioms JurisLean.KernelV3.applicableNorm_t_not_independent
#print axioms JurisLean.KernelV3.applicableNorm_fails_closed_when_t_precedes_fact

#print axioms JurisLean.Hohfeld.opposite_involutive
#print axioms JurisLean.Hohfeld.correlative_involutive
#print axioms JurisLean.Hohfeld.opposite_ne_self
#print axioms JurisLean.Hohfeld.correlative_ne_self

#print axioms JurisLean.BanachCertificateV3.no_certificate_rejected
#print axioms JurisLean.BanachCertificateV3.certificate_has_q_lt_one_scaled
#print axioms JurisLean.BanachCertificateV3.certificate_error_within_tolerance
#print axioms JurisLean.BanachCertificateV3.certificate_has_nonempty_domain
#print axioms JurisLean.BanachCertificateV3.certificate_has_positive_iterations
