import JurisLean.Candidates.SourceRepresentation20261027

#check JurisLean.Candidates.SourceRepresentation20261027.resolved_identity_is_equivalence
#print axioms JurisLean.Candidates.SourceRepresentation20261027.resolved_identity_is_equivalence
#check JurisLean.Candidates.SourceRepresentation20261027.semantic_key_exact
#print axioms JurisLean.Candidates.SourceRepresentation20261027.semantic_key_exact
#check JurisLean.Candidates.SourceRepresentation20261027.resolution_uses_unique_matching_object
#print axioms JurisLean.Candidates.SourceRepresentation20261027.resolution_uses_unique_matching_object
#check JurisLean.Candidates.SourceRepresentation20261027.copies_and_distinct_payments_are_separate
#print axioms JurisLean.Candidates.SourceRepresentation20261027.copies_and_distinct_payments_are_separate
#check JurisLean.Candidates.SourceRepresentation20261027.reference_strings_can_split_copies
#print axioms JurisLean.Candidates.SourceRepresentation20261027.reference_strings_can_split_copies
#check JurisLean.Candidates.SourceRepresentation20261027.first_match_depends_on_order
#print axioms JurisLean.Candidates.SourceRepresentation20261027.first_match_depends_on_order
#check JurisLean.Candidates.SourceRepresentation20261027.adequate_representation_preserves_all_declared_observations
#print axioms JurisLean.Candidates.SourceRepresentation20261027.adequate_representation_preserves_all_declared_observations
#check JurisLean.Candidates.SourceRepresentation20261027.adequate_separating_representation_is_injective
#print axioms JurisLean.Candidates.SourceRepresentation20261027.adequate_separating_representation_is_injective
#check JurisLean.Candidates.SourceRepresentation20261027.same_balance_does_not_identify_history
#print axioms JurisLean.Candidates.SourceRepresentation20261027.same_balance_does_not_identify_history
#check JurisLean.Candidates.SourceRepresentation20261027.preservation_without_reflection
#print axioms JurisLean.Candidates.SourceRepresentation20261027.preservation_without_reflection
#check JurisLean.Candidates.SourceRepresentation20261027.all_rational_amounts_have_exact_tagged_encoding
#print axioms JurisLean.Candidates.SourceRepresentation20261027.all_rational_amounts_have_exact_tagged_encoding
#check JurisLean.Candidates.SourceRepresentation20261027.quantity_addition_preserves_full_tag
#print axioms JurisLean.Candidates.SourceRepresentation20261027.quantity_addition_preserves_full_tag
#check JurisLean.Candidates.SourceRepresentation20261027.quantity_addition_refuses_tag_mismatch
#print axioms JurisLean.Candidates.SourceRepresentation20261027.quantity_addition_refuses_tag_mismatch
#check JurisLean.Candidates.SourceRepresentation20261027.dimensionless_scaling_preserves_amount_tag
#print axioms JurisLean.Candidates.SourceRepresentation20261027.dimensionless_scaling_preserves_amount_tag
#check JurisLean.Candidates.SourceRepresentation20261027.old_division_free_syntax_cannot_represent_half
#print axioms JurisLean.Candidates.SourceRepresentation20261027.old_division_free_syntax_cannot_represent_half

open JurisLean.Candidates.Final20261021
open JurisLean.Candidates.SourceRepresentation20261027

def sourceIdentityTable : List (SourceRef × ObjectId) :=
  [(⟨0⟩, .payment ⟨1⟩), (⟨1⟩, .payment ⟨1⟩), (⟨2⟩, .payment ⟨2⟩)]

/-- info: true -/
#guard_msgs in
#eval decide (resolveObject sourceIdentityTable ⟨0⟩ = .known (.payment ⟨1⟩) ∧
  resolveObject sourceIdentityTable ⟨1⟩ = .known (.payment ⟨1⟩) ∧
  resolveObject sourceIdentityTable ⟨2⟩ = .known (.payment ⟨2⟩))

/-- info: true -/
#guard_msgs in
#eval decide (resolveObject sourceIdentityTable ⟨3⟩ = .unknown .identityUnknown)

/-- info: true -/
#guard_msgs in
#eval decide (resolveObject (sourceIdentityTable ++ [(⟨0⟩, .payment ⟨2⟩)]) ⟨0⟩ = .conflict 0 2)

/-- info: true -/
#guard_msgs in
#eval decide (resolveObject (sourceIdentityTable ++ [(⟨0⟩, .payment ⟨1⟩)]) ⟨0⟩ = .conflict 0 2)

/-- info: true -/
#guard_msgs in
#eval decide (firstAmount [(1, 7), (1, 9)] 1 = some 7 ∧ firstAmount [(1, 9), (1, 7)] 1 = some 9)

/-- info: true -/
#guard_msgs in
#eval decide (terminalBalance [10] = 0 ∧ terminalBalance [4, 3, 3] = 0)

def representationAmount : Amount := ⟨1/2, ⟨"CNY", "yuan", 3⟩⟩

/-- info: true -/
#guard_msgs in
#eval decide (quantityDenote (encodeQuantity representationAmount) = some representationAmount)

/-- info: true -/
#guard_msgs in
#eval decide (quantityDenote (.add (encodeQuantity representationAmount)
  (encodeQuantity representationAmount)) = some ⟨1, representationAmount.tag⟩)

/-- info: true -/
#guard_msgs in
#eval decide (quantityDenote (.scale (1/3) (encodeQuantity representationAmount)) =
  some ⟨1/6, representationAmount.tag⟩)

/-- info: true -/
#guard_msgs in
#eval decide (quantityDenote (.add (encodeQuantity representationAmount)
  (encodeQuantity {representationAmount with tag := ⟨"CNY", "yuan", 4⟩})) = none)

/-- info: true -/
#guard_msgs in
#eval decide (quantityDenote (.add (encodeQuantity representationAmount)
  (encodeQuantity {representationAmount with tag := ⟨"CNY", "fen", 3⟩})) = none)

/-- info: true -/
#guard_msgs in
#eval decide (quantityDenote (.add (encodeQuantity representationAmount)
  (encodeQuantity {representationAmount with tag := ⟨"USD", "yuan", 3⟩})) = none)
