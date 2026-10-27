import JurisLean.Candidates.DecisionTrajectoryConsumer20261027

/-!
Original 11.1, S11, E11 and original 04 edge 10. Three measurement rules read
procedure choices, full filing instants, or actual ledger allocation receipts.
An externally bound finding of a procedural defect is a separate construct;
revocation is not silently recoded as defect. The dictionary fixes case/stage/
opportunity, outcome-event identity, observation window and versioned context.

The external observation and complete-window catalogs below are inputs, not
proofs of source truth, identity, completeness, iid sampling or legal meaning.
Payment timestamps are external evidence: a ledger commit has no real-world
clock. Known negative observations require a closed, independently attested
complete window. Unknown commits provide no poststate for this consumer.
-/

namespace JurisLean.Candidates.BusinessMeasurement20261027

open JurisLean.Candidates.Final20261021
open JurisLean.Candidates.DecisionTrajectoryConsumer20261027

inductive BehaviorConstruct where
  | procedureChoice (actor : PartyId) (action : Nat)
  | timelyFiling (actor : PartyId)
  | timelyPerformance (relation : RelationId) (payer payee : PartyId) (required : Amount)
  | reviewedDefect
  deriving DecidableEq, Repr

structure MeasurementDictionary where
  context : Gamma
  stage : Nat
  opportunity : Nat
  event : EventId
  unit : MeasurementId
  resultRecord : RecordId
  targetVersion : Nat
  windowStart : Instant
  windowEnd : Instant
  timezone : String
  clockVersion : Nat
  construct : BehaviorConstruct
  deriving DecidableEq, Repr

inductive BehaviorRecord where
  | procedureChoice (actor : PartyId) (action : Nat)
  | filing (actor : PartyId)
  | payment (key : PaymentId)
  | reviewedFinding (defect : Bool) (reviewEvidence : SourceRef)
  | revocation
  deriving DecidableEq, Repr

structure MeasurementRow where
  dictionary : MeasurementDictionary
  event : EventId
  record : RecordId
  occurredAt : Instant
  recordedAt : Instant
  source : SourceRef
  body : BehaviorRecord
  deriving DecidableEq, Repr

structure ObservationAttestation where
  row : MeasurementRow
  witness : SourceRef
  deriving DecidableEq, Repr

-- Completeness is a statement about this exact dictionary and visible rows.
-- It cannot be inferred from the absence of a row in a queried database.
structure WindowClosure where
  dictionary : MeasurementDictionary
  rows : List MeasurementRow
  witnessedAt : Instant
  source : SourceRef
  deriving DecidableEq, Repr

inductive MeasurementFailure where
  | scopeMismatch | measurementBridgeMissing | incompleteWindow | unknownCommit
  deriving DecidableEq, Repr

structure BehaviorMeasurement where
  actualPost : Ledger.Handle
  dictionary : MeasurementDictionary
  rows : List MeasurementRow
  observedAt : Instant
  measuredTotal : ℚ
  label : Bool
  deriving DecidableEq

inductive MeasurementResult where
  | measured (receipt : BehaviorMeasurement)
  | unknown (reason : MeasurementFailure)
  deriving DecidableEq

def measurementThreshold (d : MeasurementDictionary) : ℚ :=
  match d.construct with
  | .timelyPerformance _ _ _ required => required.value
  | _ => 1

-- A receipt is looked up in the actual poststate, not accepted as a parallel
-- caller-supplied allocation. The external row supplies only identity/time.
def rowMagnitude (post : Ledger.Handle) (d : MeasurementDictionary)
    (row : MeasurementRow) : Option ℚ :=
  match d.construct, row.body with
  | .procedureChoice actor action, .procedureChoice observed choice =>
      if actor = observed then some (if action = choice then 1 else 0) else none
  | .timelyFiling actor, .filing observed =>
      if actor = observed then some 1 else none
  | .timelyPerformance relation payer payee required, .payment key =>
      match Ledger.lookupReceipt post.state key with
      | none => none
      | some receipt =>
          if receipt.payload.caseId = d.context.caseId ∧
              receipt.payload.relation = relation ∧ receipt.payload.payer = payer ∧
              receipt.payload.payee = payee ∧ receipt.payload.amount.tag = required.tag ∧
              receipt.payload.normVersion = d.context.normVersion ∧
              receipt.payload.cashId = row.event ∧ receipt.payload.source = row.source ∧
              0 ≤ receipt.allocated ∧
              (⟨receipt.payload.cashId, receipt.payload.source, payer, payee,
                receipt.payload.amount⟩ : CashEvent) ∈ post.state.cash then
            some receipt.allocated
          else none
  | .reviewedDefect, .reviewedFinding defect _ => some (Behavior.indicator defect)
  | _, _ => none

def rowContribution (post : Ledger.Handle) (d : MeasurementDictionary)
    (row : MeasurementRow) : Option ℚ :=
  (rowMagnitude post d row).map fun amount =>
    if d.windowStart.ticks ≤ row.occurredAt.ticks ∧
        row.occurredAt.ticks ≤ d.windowEnd.ticks then amount else 0

def measuredTotal (post : Ledger.Handle) (d : MeasurementDictionary) :
    List MeasurementRow → Option ℚ
  | [] => some 0
  | row :: rest => do
      let value ← rowContribution post d row
      let tail ← measuredTotal post d rest
      pure (value + tail)

def measurementInputsValid (post : Ledger.Handle) (d : MeasurementDictionary)
    (now : Instant) (catalog : List ObservationAttestation) (rows : List MeasurementRow) : Bool :=
  decide (d.context = post.gamma ∧ d.windowStart.ticks ≤ d.windowEnd.ticks ∧
    0 < measurementThreshold d ∧ rows.Pairwise (fun a b => a.event ≠ b.event)) &&
  rows.all (fun row => decide (row.dictionary = d ∧ row.occurredAt.ticks ≤ row.recordedAt.ticks ∧
      row.recordedAt.ticks ≤ now.ticks) &&
    catalog.any (fun entry => decide (entry.row = row)))

def windowComplete (d : MeasurementDictionary) (now : Instant)
    (rows : List MeasurementRow) (closures : List WindowClosure) : Bool :=
  closures.any fun c => decide (c.dictionary = d ∧ c.rows = rows ∧
    d.windowEnd.ticks ≤ c.witnessedAt.ticks ∧ c.witnessedAt.ticks ≤ now.ticks)

def measureBusiness (post : Ledger.Handle) (d : MeasurementDictionary) (now : Instant)
    (catalog : List ObservationAttestation) (closures : List WindowClosure)
    (rows : List MeasurementRow) : MeasurementResult :=
  if measurementInputsValid post d now catalog rows = false then .unknown .scopeMismatch
  else match measuredTotal post d rows with
  | none => .unknown .measurementBridgeMissing
  | some total =>
      if measurementThreshold d ≤ total then
        .measured ⟨post, d, rows, now, total, true⟩
      else if windowComplete d now rows closures then
        .measured ⟨post, d, rows, now, total, false⟩
      else .unknown .incompleteWindow

theorem measurement_reads_actual_state_and_rows (post : Ledger.Handle)
    (d : MeasurementDictionary) (now : Instant) (catalog : List ObservationAttestation)
    (closures : List WindowClosure) (rows : List MeasurementRow) (out : BehaviorMeasurement)
    (accepted : measureBusiness post d now catalog closures rows = .measured out) :
    out.actualPost = post ∧ out.dictionary = d ∧ out.rows = rows ∧ out.observedAt = now ∧
    measuredTotal post d rows = some out.measuredTotal ∧
    measurementInputsValid post d now catalog rows = true := by
  unfold measureBusiness at accepted
  split at accepted
  · simp at accepted
  · rename_i valid
    have hv : measurementInputsValid post d now catalog rows = true := by
      cases hb : measurementInputsValid post d now catalog rows <;> simp_all
    cases sumEq : measuredTotal post d rows with
    | none => simp [sumEq] at accepted
    | some total =>
        simp only [sumEq] at accepted
        split at accepted
        · cases accepted
          exact ⟨rfl, rfl, rfl, rfl, rfl, hv⟩
        · split at accepted
          · cases accepted
            exact ⟨rfl, rfl, rfl, rfl, rfl, hv⟩
          · simp at accepted

theorem negative_requires_complete_closed_window (post : Ledger.Handle)
    (d : MeasurementDictionary) (now : Instant) (catalog : List ObservationAttestation)
    (closures : List WindowClosure) (rows : List MeasurementRow) (out : BehaviorMeasurement)
    (accepted : measureBusiness post d now catalog closures rows = .measured out)
    (negative : out.label = false) :
    windowComplete d now rows closures = true ∧ d.windowEnd.ticks ≤ now.ticks ∧
    out.measuredTotal < measurementThreshold d := by
  unfold measureBusiness at accepted
  split at accepted
  · simp at accepted
  · cases sumEq : measuredTotal post d rows with
    | none => simp [sumEq] at accepted
    | some total =>
        simp only [sumEq] at accepted
        split at accepted
        · cases accepted
          simp at negative
        · rename_i below
          split at accepted
          · rename_i complete
            cases accepted
            obtain ⟨c, _, hc⟩ := List.any_eq_true.mp complete
            have facts := of_decide_eq_true hc
            exact ⟨complete, le_trans facts.2.2.1 facts.2.2.2, lt_of_not_ge below⟩
          · simp at accepted

theorem duplicate_events_refused (post : Ledger.Handle) (d : MeasurementDictionary)
    (now : Instant) (catalog : List ObservationAttestation) (closures : List WindowClosure)
    (rows : List MeasurementRow) (duplicate : ¬ rows.Pairwise (fun a b => a.event ≠ b.event)) :
    measureBusiness post d now catalog closures rows = .unknown .scopeMismatch := by
  simp [measureBusiness, measurementInputsValid, duplicate]

theorem accepted_rows_are_external_and_current (post : Ledger.Handle)
    (d : MeasurementDictionary) (now : Instant) (catalog : List ObservationAttestation)
    (closures : List WindowClosure) (rows : List MeasurementRow) (out : BehaviorMeasurement)
    (accepted : measureBusiness post d now catalog closures rows = .measured out) :
    d.context = post.gamma ∧ ∀ row ∈ rows, row.dictionary = d ∧
      row.occurredAt.ticks ≤ row.recordedAt.ticks ∧ row.recordedAt.ticks ≤ now.ticks ∧
      ∃ entry ∈ catalog, entry.row = row := by
  have valid := (measurement_reads_actual_state_and_rows post d now catalog closures rows out accepted).2.2.2.2.2
  simp only [measurementInputsValid, Bool.and_eq_true, decide_eq_true_eq] at valid
  refine ⟨valid.1.1, ?_⟩
  intro row member
  have rowValid := List.all_eq_true.mp valid.2 row member
  simp only [Bool.and_eq_true, decide_eq_true_eq] at rowValid
  have times := rowValid.1
  obtain ⟨entry, included, same⟩ := List.any_eq_true.mp rowValid.2
  exact ⟨times.1, times.2.1, times.2.2, entry, included, of_decide_eq_true same⟩

theorem positive_means_actual_total_reaches_threshold (post : Ledger.Handle)
    (d : MeasurementDictionary) (now : Instant) (catalog : List ObservationAttestation)
    (closures : List WindowClosure) (rows : List MeasurementRow) (out : BehaviorMeasurement)
    (accepted : measureBusiness post d now catalog closures rows = .measured out)
    (positive : out.label = true) : measurementThreshold d ≤ out.measuredTotal := by
  unfold measureBusiness at accepted
  split at accepted
  · simp at accepted
  · cases sumEq : measuredTotal post d rows with
    | none => simp [sumEq] at accepted
    | some total =>
        simp only [sumEq] at accepted
        split at accepted
        · rename_i enough
          cases accepted
          exact enough
        · split at accepted
          · cases accepted
            simp at positive
          · simp at accepted

theorem revocation_does_not_supply_defect_measurement (post : Ledger.Handle)
    (d : MeasurementDictionary) (row : MeasurementRow)
    (construct : d.construct = .reviewedDefect) (observed : row.body = .revocation) :
    rowContribution post d row = none := by
  simp [rowContribution, rowMagnitude, construct, observed]

theorem missing_payment_receipt_cannot_measure_performance (post : Ledger.Handle)
    (d : MeasurementDictionary) (row : MeasurementRow) (relation : RelationId)
    (payer payee : PartyId) (required : Amount) (key : PaymentId)
    (construct : d.construct = .timelyPerformance relation payer payee required)
    (recorded : row.body = .payment key) (missing : Ledger.lookupReceipt post.state key = none) :
    rowContribution post d row = none := by
  simp [rowContribution, rowMagnitude, construct, recorded, missing]

theorem performance_magnitude_is_actual_allocation (post : Ledger.Handle)
    (d : MeasurementDictionary) (row : MeasurementRow) (relation : RelationId)
    (payer payee : PartyId) (required : Amount) (key : PaymentId) (value : ℚ)
    (construct : d.construct = .timelyPerformance relation payer payee required)
    (recorded : row.body = .payment key) (measured : rowMagnitude post d row = some value) :
    ∃ receipt, Ledger.lookupReceipt post.state key = some receipt ∧
      value = receipt.allocated ∧ receipt.payload.cashId = row.event ∧
      receipt.payload.amount.tag = required.tag := by
  simp only [rowMagnitude, construct, recorded] at measured
  cases found : Ledger.lookupReceipt post.state key with
  | none => simp [found] at measured
  | some receipt =>
      simp only [found] at measured
      split at measured
      · rename_i checked
        simp only [Option.some.injEq] at measured
        exact ⟨receipt, rfl, measured.symm, checked.2.2.2.2.2.2.1,
          checked.2.2.2.2.1⟩
      · simp at measured

structure MeasuredTrajectory where
  trajectory : Pipeline.PaymentRun
  measurement : MeasurementResult
  deriving DecidableEq

def measureTrajectory (grants : List Authorization.Grant) (initial : Ledger.Handle)
    (steps : List Instruction) (d : MeasurementDictionary) (now : Instant)
    (catalog : List ObservationAttestation) (closures : List WindowClosure)
    (rows : List MeasurementRow) : MeasuredTrajectory :=
  let actual := runTrajectory grants initial steps
  ⟨actual, match actual.current with
    | none => .unknown .unknownCommit
    | some post => measureBusiness post d now catalog closures rows⟩

theorem trajectory_measurement_uses_reported_post (grants : List Authorization.Grant)
    (initial post : Ledger.Handle) (steps : List Instruction) (d : MeasurementDictionary)
    (now : Instant) (catalog : List ObservationAttestation) (closures : List WindowClosure)
    (rows : List MeasurementRow) (reported : (runTrajectory grants initial steps).current = some post) :
    (measureTrajectory grants initial steps d now catalog closures rows).measurement =
      measureBusiness post d now catalog closures rows := by
  simp [measureTrajectory, reported]

theorem unknown_commit_has_no_behavior_label (grants : List Authorization.Grant)
    (initial : Ledger.Handle) (steps : List Instruction) (d : MeasurementDictionary)
    (now : Instant) (catalog : List ObservationAttestation) (closures : List WindowClosure)
    (rows : List MeasurementRow) (unknown : (runTrajectory grants initial steps).current = none) :
    (measureTrajectory grants initial steps d now catalog closures rows).measurement =
      .unknown .unknownCommit := by
  simp [measureTrajectory, unknown]

theorem accepted_measurement_keeps_actual_trace_invariant (grants : List Authorization.Grant)
    (initial : Ledger.Handle) (steps : List Instruction) (d : MeasurementDictionary)
    (now : Instant) (catalog : List ObservationAttestation) (closures : List WindowClosure)
    (rows : List MeasurementRow) (out : BehaviorMeasurement) (valid : Trace.Invariant initial)
    (accepted : (measureTrajectory grants initial steps d now catalog closures rows).measurement =
      .measured out) :
    Trace.Invariant out.actualPost ∧ initial.state.used ⊆ out.actualPost.state.used := by
  cases reported : (runTrajectory grants initial steps).current with
  | none => simp [measureTrajectory, reported] at accepted
  | some post =>
      have hm : measureBusiness post d now catalog closures rows = .measured out := by
        simpa [measureTrajectory, reported] using accepted
      have bound := measurement_reads_actual_state_and_rows post d now catalog closures rows out hm
      rw [bound.1]
      exact finite_interpreter_preserves_full_invariant grants steps initial post valid reported

def appealCompletionRate (unreviewedDefects : Nat) : ℚ := (8 + unreviewedDefects) / 100

theorem original_appeal_frequencies :
    appealCompletionRate 2 = 1/10 ∧ (8/20 : ℚ) = 2/5 ∧ (8/100 : ℚ) = 2/25 := by
  norm_num [appealCompletionRate]

theorem unknown_appeal_labels_have_sharp_bounds (n : Nat) (hn : n ≤ 80) :
    2/25 ≤ appealCompletionRate n ∧ appealCompletionRate n ≤ 22/25 ∧
    appealCompletionRate 0 = 2/25 ∧ appealCompletionRate 80 = 22/25 := by
  have h : (n : ℚ) ≤ 80 := by exact_mod_cast hn
  have h0 : (0 : ℚ) ≤ n := Nat.cast_nonneg n
  norm_num [appealCompletionRate]
  constructor <;> linarith

theorem appeal_observations_cannot_identify_population_rate (estimator : (Nat × Nat) → ℚ) :
    ¬ (estimator (20, 8) = appealCompletionRate 0 ∧
       estimator (20, 8) = appealCompletionRate 80) := by
  rintro ⟨a, b⟩
  norm_num [appealCompletionRate] at a b
  linarith

end JurisLean.Candidates.BusinessMeasurement20261027
