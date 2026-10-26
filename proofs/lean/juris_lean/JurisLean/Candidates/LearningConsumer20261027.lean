import JurisLean.Candidates.LearningERM20261027
import JurisLean.Candidates.Final20261021.Calibration

/-!
Original S01 output contract and edge 01 -> 04/05, for finite tabular predictors.
A score is evaluated from the table actually selected from the supplied sample.
Calibration records bind that full table as well as the complete declared scope;
a version label alone cannot substitute for equality of predictor contents.

The calibration confidence event, source/label interpretation, population and
sampling design still require their stated external or mathematical evidence.
This computable consumer checks bindings and the existing calibration gate; it
does not manufacture those premises or any legal authorization.
-/

namespace JurisLean.Candidates.LearningConsumer20261027

open JurisLean.Candidates.Final20261021
open JurisLean.Candidates.LearningERM20261027

structure LearningProtocol where
  fit : Learning.FitContract
  labelVersion : Nat
  lossVersion : Nat
  population : Nat
  samplingDesign : Nat
  groupingVersion : Nat
  selectionProtocol : Nat
  effectiveDomain : Nat
  failureBudget : ℚ
  deriving DecidableEq, Repr

structure FittedTable where
  protocol : LearningProtocol
  table : List ℚ
  sampleSize : Nat
  empiricalRisk : ℚ
  deriving DecidableEq, Repr

structure TableCalibration where
  protocol : LearningProtocol
  table : List ℚ
  bounds : Calibration.BoundPrediction
  deriving DecidableEq, Repr

structure TaskScore where
  protocol : LearningProtocol
  value : ℚ
  bounds : Calibration.BoundPrediction
  deriving DecidableEq, Repr

def tableLoss {m : Nat} {Y : Type} (loss : ℚ → Y → ℚ)
    (table : List ℚ) (row : Fin m × Y) : ℚ :=
  loss (table.getD row.1.val 0) row.2

def fitTable {m n : Nat} {Y : Type} (protocol : LearningProtocol)
    (loss : ℚ → Y → ℚ) (models : List (List ℚ))
    (data : Fin n → Fin m × Y) : Result FittedTable :=
  if ¬ (0 < protocol.failureBudget ∧ protocol.failureBudget < 1) then
    .unknown .unsupported
  else if ¬ models.all (fun table => decide (table.length = m)) then
    .unknown .unsupported
  else
    match proposed_empirical_fit (tableLoss loss) models data with
    | none => .unknown .missingEvidence
    | some table => .known
        { protocol := protocol, table := table, sampleSize := n
          empiricalRisk := empiricalScore (tableLoss loss) data table }

def consumeCalibration {m : Nat} (expected : LearningProtocol) (fitted : FittedTable)
    (query : Fin m) (certificate : TableCalibration) (riskLimit : ℚ)
    (supported : Bool) : Result TaskScore :=
  if fitted.protocol ≠ expected ∨ certificate.protocol ≠ expected ∨
      certificate.table ≠ fitted.table then
    .unknown .targetMismatch
  else if fitted.table.length ≠ m then .unknown .scopeMismatch
  else
    match Calibration.proposed_calibration_support_gate fitted.protocol.fit
      certificate.bounds riskLimit supported with
    | .known bounds => .known
        { protocol := fitted.protocol, value := fitted.table.getD query.val 0, bounds := bounds }
    | .unknown e => .unknown e
    | .rejected e => .rejected e
    | .conflict a b => .conflict a b

def fitThenCalibrationGate {m n : Nat} {Y : Type}
    (protocol expected : LearningProtocol) (loss : ℚ → Y → ℚ)
    (models : List (List ℚ)) (data : Fin n → Fin m × Y)
    (query : Fin m) (certificate : TableCalibration) (riskLimit : ℚ)
    (supported : Bool) : Result TaskScore :=
  match fitTable protocol loss models data with
  | .known fitted => consumeCalibration expected fitted query certificate riskLimit supported
  | .unknown e => .unknown e
  | .rejected e => .rejected e
  | .conflict a b => .conflict a b

theorem u01_6_fit_card_minimizes_actual_sample {m n : Nat} {Y : Type}
    (protocol : LearningProtocol) (loss : ℚ → Y → ℚ)
    (models : List (List ℚ)) (data : Fin n → Fin m × Y)
    (out : FittedTable) (accepted : fitTable protocol loss models data = .known out) :
    out.protocol = protocol ∧ out.sampleSize = n ∧ out.table.length = m ∧ out.table ∈ models ∧
      out.empiricalRisk = empiricalScore (tableLoss loss) data out.table ∧
      ∀ table ∈ models,
        empiricalScore (tableLoss loss) data out.table ≤ empiricalScore (tableLoss loss) data table := by
  unfold fitTable at accepted
  split at accepted
  · cases accepted
  · split at accepted
    · cases accepted
    · rename_i widths
      have allWidths : models.all (fun table => decide (table.length = m)) = true := by
        simpa using widths
      cases models with
      | nil => simp [proposed_empirical_fit] at accepted
      | cons first rest =>
          by_cases hn : n = 0
          · simp [proposed_empirical_fit, hn] at accepted
          · simp only [proposed_empirical_fit, hn, if_false] at accepted
            cases accepted
            have best := selectMinimum_spec (empiricalScore (tableLoss loss) data) first rest
            have selectedWidth :
                (selectMinimum (empiricalScore (tableLoss loss) data) first rest).length = m := by
              simpa using (List.all_eq_true.mp allWidths _ best.1)
            exact ⟨rfl, rfl, selectedWidth, best.1, rfl, best.2⟩

theorem u01_6_reject_changed_model_contents {m : Nat}
    (expected : LearningProtocol) (fitted : FittedTable) (query : Fin m)
    (certificate : TableCalibration) (riskLimit : ℚ) (supported : Bool)
    (changed : certificate.table ≠ fitted.table) :
    consumeCalibration expected fitted query certificate riskLimit supported =
      .unknown .targetMismatch := by
  simp [consumeCalibration, changed]

theorem u01_6_reject_changed_fit_scope {m : Nat}
    (expected : LearningProtocol) (fitted : FittedTable) (query : Fin m)
    (certificate : TableCalibration) (riskLimit : ℚ) (supported : Bool)
    (changed : fitted.protocol ≠ expected ∨ certificate.protocol ≠ expected) :
    consumeCalibration expected fitted query certificate riskLimit supported =
      .unknown .targetMismatch := by
  rcases changed with changed | changed <;> simp [consumeCalibration, changed]

theorem u01_6_reject_wrong_feature_width {m n : Nat} {Y : Type}
    (protocol : LearningProtocol) (loss : ℚ → Y → ℚ)
    (models : List (List ℚ)) (data : Fin n → Fin m × Y)
    (wrong : models.all (fun table => decide (table.length = m)) = false) :
    fitTable protocol loss models data = .unknown .unsupported := by
  simp [fitTable, wrong]

theorem u01_6_reject_invalid_failure_budget {m n : Nat} {Y : Type}
    (protocol : LearningProtocol) (loss : ℚ → Y → ℚ)
    (models : List (List ℚ)) (data : Fin n → Fin m × Y)
    (invalid : ¬ (0 < protocol.failureBudget ∧ protocol.failureBudget < 1)) :
    fitTable protocol loss models data = .unknown .unsupported := by
  simp [fitTable, invalid]

theorem u01_6_actual_fit_output_is_consumed {m n : Nat} {Y : Type}
    (protocol expected : LearningProtocol) (loss : ℚ → Y → ℚ)
    (models : List (List ℚ)) (data : Fin n → Fin m × Y)
    (query : Fin m) (certificate : TableCalibration) (riskLimit : ℚ) (supported : Bool)
    (out : FittedTable) (accepted : fitTable protocol loss models data = .known out) :
    fitThenCalibrationGate protocol expected loss models data query certificate riskLimit supported =
      consumeCalibration expected out query certificate riskLimit supported := by
  simp [fitThenCalibrationGate, accepted]

theorem u01_6_matching_calibration_reads_selected_table {m : Nat}
    (fitted : FittedTable) (query : Fin m) (certificate : TableCalibration) (riskLimit : ℚ)
    (scope : certificate.protocol = fitted.protocol) (sameTable : certificate.table = fitted.table)
    (width : fitted.table.length = m)
    (boundScope : certificate.bounds.contract = fitted.protocol.fit)
    (coverage : 0 < certificate.bounds.lowerCoverage)
    (nonnegative : 0 ≤ certificate.bounds.upperRisk)
    (acceptable : certificate.bounds.upperRisk ≤ riskLimit) :
    consumeCalibration fitted.protocol fitted query certificate riskLimit true =
      .known { protocol := fitted.protocol, value := fitted.table.getD query.val 0, bounds := certificate.bounds } := by
  simp [consumeCalibration, scope, sameTable, width,
    Calibration.proposed_calibration_support_gate, boundScope, coverage, nonnegative, acceptable]

theorem u01_6_successful_pipeline_uses_actual_empirical_minimizer {m n : Nat} {Y : Type}
    (protocol : LearningProtocol) (loss : ℚ → Y → ℚ)
    (models : List (List ℚ)) (data : Fin n → Fin m × Y)
    (query : Fin m) (certificate : TableCalibration) (riskLimit : ℚ)
    (out : FittedTable) (accepted : fitTable protocol loss models data = .known out)
    (scope : certificate.protocol = protocol) (sameTable : certificate.table = out.table)
    (boundScope : certificate.bounds.contract = protocol.fit)
    (coverage : 0 < certificate.bounds.lowerCoverage)
    (nonnegative : 0 ≤ certificate.bounds.upperRisk)
    (acceptable : certificate.bounds.upperRisk ≤ riskLimit) :
    fitThenCalibrationGate protocol protocol loss models data query certificate riskLimit true =
      .known { protocol := protocol, value := out.table.getD query.val 0, bounds := certificate.bounds } ∧
      out.table ∈ models ∧
      ∀ table ∈ models,
        empiricalScore (tableLoss loss) data out.table ≤ empiricalScore (tableLoss loss) data table := by
  have best := u01_6_fit_card_minimizes_actual_sample protocol loss models data out accepted
  have consumed := u01_6_actual_fit_output_is_consumed protocol protocol loss models data
    query certificate riskLimit true out accepted
  have checked := u01_6_matching_calibration_reads_selected_table out query certificate riskLimit
    (scope.trans best.1.symm) sameTable best.2.2.1 (boundScope.trans (congrArg LearningProtocol.fit best.1).symm)
    coverage nonnegative acceptable
  refine ⟨?_, best.2.2.2.1, best.2.2.2.2.2⟩
  simpa only [best.1] using consumed.trans (by simpa only [best.1] using checked)

end JurisLean.Candidates.LearningConsumer20261027
