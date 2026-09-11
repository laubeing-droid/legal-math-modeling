-- Frozen-sample classification; not a categorical impossibility theorem.
import Mathlib.Data.Fintype.Basic

/-!
The 44 encoded statuses contain CN_ONLY labels. This is a property of this
encoding, not proof that a foreign institution or a semantics-preserving map
does not exist. Source CSV correspondence and legal interpretations are
separate obligations. No majority threshold is required for the theorem.
-/

/-- Mapping status from claim_mapping.csv -/
inductive MappingStatus : Type
  | CN_ONLY
  | COLLISION
  | ASYMMETRY
  | CN_US_PARTIAL
  | CN_HK_PARTIAL
  | TRI_JURISDICTION_PARTIAL
  | TRI_JURISDICTION_MAPPED
  deriving DecidableEq, Repr

/-- mapping_status function for the 44 entries (0-indexed).
    Source: data/category_rosetta/claim_mapping.csv -/
def mappingStatus (i : Nat) : MappingStatus :=
  if i < 30 then .CN_ONLY           -- FP-CN-001 through FP-CN-030
  else if i < 32 then .CN_US_PARTIAL -- FP-CNUS-001, FP-CNUS-002
  else if i < 36 then .COLLISION     -- FP-CNUS-003, FP-CNUS-004, FP-COLL-001, FP-COLL-002
  else if i < 39 then .ASYMMETRY     -- FP-CNUS-005, FP-ASYM-001, FP-ASYM-002
  else if i < 42 then .CN_HK_PARTIAL -- FP-CNHk-001, FP-CNHK-002, FP-CNHK-003
  else if i < 43 then .TRI_JURISDICTION_PARTIAL -- FP-TRI-001
  else .TRI_JURISDICTION_MAPPED                  -- FP-TRI-002

/-- CN_ONLY count: entries labelled CN_ONLY in the encoded sample -/
def cnOnlyCount : Nat :=
  (List.range 44).filter (fun i => mappingStatus i == .CN_ONLY) |>.length

/-- COLLISION count: entries with direct cross-jurisdiction conflict -/
def collisionCount : Nat :=
  (List.range 44).filter (fun i => mappingStatus i == .COLLISION) |>.length

/-- ASYMMETRY count: entries with asymmetric mapping -/
def asymmetryCount : Nat :=
  (List.range 44).filter (fun i => mappingStatus i == .ASYMMETRY) |>.length

/-- Total obstruction count: CN_ONLY + COLLISION + ASYMMETRY -/
def obstructionCount : Nat := cnOnlyCount + collisionCount + asymmetryCount

-- Verification: CN_ONLY = 30
theorem cnOnly_eq_30 : cnOnlyCount = 30 := rfl

-- Verification: COLLISION = 4
theorem collision_eq_4 : collisionCount = 4 := rfl

-- Verification: ASYMMETRY = 3
theorem asymmetry_eq_3 : asymmetryCount = 3 := rfl

-- Verification: Total obstructions = 37
theorem obstruction_eq_37 : obstructionCount = 37 := rfl

/-- The majority of encoded entries carry CN_ONLY (30 > 44/2 = 22). -/
theorem cnOnly_exceeds_half : cnOnlyCount > 44 / 2 := by decide

/-- The obstruction count exceeds the majority (37 > 44/2 = 22). -/
theorem obstruction_exceeds_half : obstructionCount > 44 / 2 := by decide

/-- At least one entry of the encoded sample has the CN_ONLY label.
No claim about the existence of general or semantics-preserving functors. -/
theorem sample_mapping_not_total :
    ¬ (∀ i : Fin 44, mappingStatus i.val ≠ .CN_ONLY) := by
  intro h
  have := h ⟨0, by decide⟩
  simp [mappingStatus] at this

/-- The obstruction density exceeds 2/3 (37/44 ≈ 84%). -/
theorem obstruction_density_gt_two_thirds :
    obstructionCount * 3 > 44 * 2 := by decide

/-- Even excluding partial mappings, pure obstructions (CN_ONLY + COLLISION + ASYMMETRY)
    still exceed the majority. -/
theorem pure_obstruction_majority :
    (cnOnlyCount + collisionCount + asymmetryCount) > 44 / 2 := by decide
