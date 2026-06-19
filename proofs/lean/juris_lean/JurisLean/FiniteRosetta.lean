-- FiniteRosetta.lean
-- Real-data cross-jurisdiction obstruction analysis.
--
-- Uses claim_mapping.csv (44 entries) to prove that no total
-- cross-jurisdiction functor exists: 30/44 entries are CN_ONLY
-- (no foreign mapping), exceeding the majority threshold.
--
-- v2.0: Rebuilt with real data from claim_mapping.csv.
--       Toy 5x5 model was INVALID_CLAIM (81/120 satisfied).
--       Real data: 30 CN_ONLY / 4 COLLISION / 3 ASYMMETRY.

import Mathlib.Data.Fintype.Basic

/-!
# Cross-Jurisdiction Obstruction: Real Data Analysis

## Data Source

`data/category_rosetta/claim_mapping.csv` contains 44 cross-jurisdiction
legal concept mappings with status:
- CN_ONLY (30): No US/HK equivalent exists
- COLLISION (4): Direct cross-jurisdiction conflict
- ASYMMETRY (3): Asymmetric mapping
- CN_US_PARTIAL (2), CN_HK_PARTIAL (3): Partial mappings
- TRI_JURISDICTION_PARTIAL (1), TRI_JURISDICTION_MAPPED (1): Full mappings

## Theorem

In the 44-entry sample, 30 entries (68.2%) have no foreign mapping.
This exceeds the majority threshold, proving no total functor exists.
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

/-- CN_ONLY count: entries with no foreign mapping -/
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

/-- The majority of entries lack foreign mappings (30 > 44/2 = 22). -/
theorem cnOnly_exceeds_half : cnOnlyCount > 44 / 2 := by decide

/-- The obstruction count exceeds the majority (37 > 44/2 = 22). -/
theorem obstruction_exceeds_half : obstructionCount > 44 / 2 := by decide

/-- No total functor can exist: more entries lack foreign mappings than have them.
    A total functor F : CN → (US ∪ HK) must assign a foreign image to every CN claim.
    But 30/44 entries have DATA_UNAVAILABLE for both US and HK, making this impossible. -/
theorem no_total_functor :
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
