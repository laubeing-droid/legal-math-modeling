import JurisLean.Candidates.Final20261021.Representation
import JurisLean.Seams.UnifiedNeedlesS3b

/-!
Original 07.1, 07.4 and the rational quantity bridge of 07.8.
Partial interpretation is fixed within its snapshot/context, not inferred from
strings, history positions or bare event IDs. The finite identity examples
separate duplicate references, distinct payments with one bare ID and an
ambiguous table key. This module does not certify real entity resolution.
The quantity extension is new syntax; the old integer-only result is reused.
-/

namespace JurisLean.Candidates.SourceRepresentation20261027

open JurisLean.Candidates.Final20261021
open JurisLean.Candidates.Final20261021.Representation

abbrev ResolvedReference (mu : SourceRef → Option ObjectId) :=
  {r : SourceRef // ∃ object, mu r = some object}

theorem interpreted_same_symmetric (mu : SourceRef → Option ObjectId)
    (a b : SourceRef) (same : InterpretedSame mu a b) : InterpretedSame mu b a := by
  obtain ⟨object, ha, hb⟩ := same
  exact ⟨object, hb, ha⟩

theorem interpreted_same_transitive (mu : SourceRef → Option ObjectId)
    (a b c : SourceRef) (ab : InterpretedSame mu a b) (bc : InterpretedSame mu b c) :
    InterpretedSame mu a c := by
  obtain ⟨left, ha, hb⟩ := ab
  obtain ⟨right, hb', hc⟩ := bc
  have same : left = right := Option.some.inj (hb.symm.trans hb')
  exact ⟨left, ha, by simpa only [same] using hc⟩

theorem resolved_identity_is_equivalence (mu : SourceRef → Option ObjectId) :
    Equivalence (fun a b : ResolvedReference mu => InterpretedSame mu a.val b.val) := by
  refine ⟨?_, ?_, ?_⟩
  · intro a
    obtain ⟨object, found⟩ := a.property
    exact ⟨object, found, found⟩
  · intro a b same
    exact interpreted_same_symmetric mu a b same
  · intro a b c ab bc
    exact interpreted_same_transitive mu a b c ab bc

noncomputable def semanticKey (mu : SourceRef → Option ObjectId)
    (r : ResolvedReference mu) : ObjectId := Classical.choose r.property

theorem semantic_key_exact (mu : SourceRef → Option ObjectId)
    (a b : ResolvedReference mu) :
    semanticKey mu a = semanticKey mu b ↔ InterpretedSame mu a.val b.val := by
  have ha : mu a = some (semanticKey mu a) := Classical.choose_spec a.property
  have hb : mu b = some (semanticKey mu b) := Classical.choose_spec b.property
  constructor
  · intro same
    exact ⟨semanticKey mu a, ha, by simpa only [same] using hb⟩
  · rintro ⟨object, left, right⟩
    exact (Option.some.inj (ha.symm.trans left)).trans
      (Option.some.inj (right.symm.trans hb))

def resolveObject (table : List (SourceRef × ObjectId)) (reference : SourceRef) : Result ObjectId :=
  match (table.filter fun row => decide (row.1 = reference)).map Prod.snd with
  | [object] => .known object
  | [] => .unknown .identityUnknown
  | _ => .conflict reference.value 2

theorem resolution_uses_unique_matching_object (table : List (SourceRef × ObjectId))
    (reference : SourceRef) (object : ObjectId)
    (accepted : resolveObject table reference = .known object) :
    (table.filter fun row => decide (row.1 = reference)).map Prod.snd = [object] := by
  unfold resolveObject at accepted
  split at accepted
  · rename_i found
    cases accepted
    exact found
  · cases accepted
  · cases accepted

def identityExample : SourceRef → Option ObjectId
  | ⟨0⟩ => some (.payment ⟨1⟩)
  | ⟨1⟩ => some (.payment ⟨1⟩)
  | ⟨2⟩ => some (.payment ⟨2⟩)
  | _ => none

def bareEventExample (_ : SourceRef) : EventId := ⟨9⟩

theorem copies_and_distinct_payments_are_separate :
    InterpretedSame identityExample ⟨0⟩ ⟨1⟩ ∧
    ¬ InterpretedSame identityExample ⟨0⟩ ⟨2⟩ ∧
    bareEventExample ⟨0⟩ = bareEventExample ⟨2⟩ ∧
    ¬ InterpretedSame identityExample ⟨3⟩ ⟨3⟩ := by
  refine ⟨⟨.payment ⟨1⟩, rfl, rfl⟩, ?_, rfl, ?_⟩
  · rintro ⟨object, left, right⟩
    have impossible : identityExample ⟨0⟩ = identityExample ⟨2⟩ := left.trans right.symm
    cases impossible
  · exact unknown_not_an_identity identityExample ⟨3⟩ ⟨3⟩ rfl

theorem reference_strings_can_split_copies :
    (0 : Nat) ≠ 1 ∧ InterpretedSame identityExample ⟨0⟩ ⟨1⟩ :=
  ⟨by decide, ⟨.payment ⟨1⟩, rfl, rfl⟩⟩

-- The original two rows share a table key, not an established object identity.
def firstAmount (rows : List (Nat × ℚ)) (key : Nat) : Option ℚ :=
  (rows.find? fun row => decide (row.1 = key)).map Prod.snd

theorem first_match_depends_on_order :
    firstAmount [(1, 7), (1, 9)] 1 = some 7 ∧
    firstAmount [(1, 9), (1, 7)] 1 = some 9 ∧
    firstAmount [(1, 7), (1, 9)] 1 ≠ firstAmount [(1, 9), (1, 7)] 1 := by decide

def ObservationAdequate {R M O V : Type*} (encode : R → M) (read : O → R → V) : Prop :=
  ∀ o, ∃ decode : M → V, ∀ r, decode (encode r) = read o r

theorem adequate_representation_preserves_all_declared_observations
    {R M O V : Type*} (encode : R → M) (read : O → R → V)
    (adequate : ObservationAdequate encode read) (a b : R) (same : encode a = encode b) :
    ∀ o, read o a = read o b := by
  intro o
  obtain ⟨decode, preserves⟩ := adequate o
  rw [← preserves a, ← preserves b, same]

theorem adequate_separating_representation_is_injective
    {R M O V : Type*} (encode : R → M) (read : O → R → V)
    (adequate : ObservationAdequate encode read)
    (separating : ∀ a b, (∀ o, read o a = read o b) → a = b) :
    Function.Injective encode := by
  intro a b same
  exact separating a b
    (adequate_representation_preserves_all_declared_observations encode read adequate a b same)

def terminalBalance (payments : List ℚ) : ℚ := max (10 - payments.sum) 0

theorem same_balance_does_not_identify_history :
    terminalBalance [10] = terminalBalance [4, 3, 3] ∧
    ([10] : List ℚ) ≠ [4, 3, 3] := by decide

-- Literal preservation on an image says nothing about points outside that image.
theorem preservation_without_reflection :
    (∀ r : Unit, (fun _ : Unit => false) r = (fun x : Bool => x) false) ∧
    (fun x : Bool => x) true = true ∧ ¬ ∃ r : Unit, (fun _ : Unit => false) r = true := by
  constructor
  · intro r; rfl
  · exact ⟨rfl, by simp⟩

inductive RationalQty where
  | rational (amount : Amount)
  | add (left right : RationalQty)
  | scale (dimensionless : ℚ) (amount : RationalQty)
  deriving DecidableEq, Repr

def quantityDenote : RationalQty → Option Amount
  | .rational amount => some amount
  | .add left right =>
      match quantityDenote left, quantityDenote right with
      | some a, some b =>
          if a.tag = b.tag then some ⟨a.value + b.value, a.tag⟩ else none
      | _, _ => none
  | .scale scalar expression =>
      (quantityDenote expression).map fun amount => ⟨scalar * amount.value, amount.tag⟩

def encodeQuantity (amount : Amount) : RationalQty := .rational amount

theorem all_rational_amounts_have_exact_tagged_encoding (amount : Amount) :
    quantityDenote (encodeQuantity amount) = some amount := rfl

theorem quantity_addition_preserves_full_tag (a b : Amount) (same : a.tag = b.tag) :
    quantityDenote (.add (encodeQuantity a) (encodeQuantity b)) =
      some ⟨a.value + b.value, a.tag⟩ := by
  simp [quantityDenote, encodeQuantity, same]

theorem quantity_addition_refuses_tag_mismatch (a b : Amount) (different : a.tag ≠ b.tag) :
    quantityDenote (.add (encodeQuantity a) (encodeQuantity b)) = none := by
  simp [quantityDenote, encodeQuantity, different]

theorem dimensionless_scaling_preserves_amount_tag (scalar : ℚ) (amount : Amount) :
    quantityDenote (.scale scalar (encodeQuantity amount)) =
      some ⟨scalar * amount.value, amount.tag⟩ := rfl

theorem old_division_free_syntax_cannot_represent_half
    (expression : JurisLean.Seams.UnifiedNeedlesS3b.QtyAst)
    (unit : String)
    (free : JurisLean.Seams.UnifiedNeedlesS3b.divFree expression = true) :
    JurisLean.Seams.UnifiedNeedlesS3b.qtyDenote expression ≠ some ⟨1/2, unit⟩ := by
  intro represented
  obtain ⟨integer, integerValue⟩ :=
    JurisLean.Seams.UnifiedNeedlesS3b.qtyDenote_divFree_int_valued expression free _ represented
  have lowerQ : (0 : ℚ) < (integer : ℚ) := by
    rw [← integerValue]
    norm_num
  have upperQ : (integer : ℚ) < 1 := by
    rw [← integerValue]
    norm_num
  have lower : (0 : ℤ) < integer := by exact_mod_cast lowerQ
  have upper : integer < (1 : ℤ) := by exact_mod_cast upperQ
  omega

end JurisLean.Candidates.SourceRepresentation20261027
