import JurisLean.Candidates.BusinessFeedbackLoop20261027
import Mathlib.Data.List.OfFn

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal BigOperators

namespace JurisLean.Candidates.U00ActualStatisticalJoin20261031

open JurisLean.Candidates.Final20261021
open JurisLean.Candidates.LearningERM20261027
open JurisLean.Candidates.LearningConsumer20261027
open JurisLean.Candidates.SampleCalibrationConsumer20261027
open JurisLean.Candidates.ProbabilityIntervalConsumer20261027
open JurisLean.Candidates.IntervalDecisionConsumer20261027
open JurisLean.Candidates.EventFeedbackConsumer20261027
open JurisLean.Candidates.ProtectedFeedback20261027
open JurisLean.Candidates.ValidatedFeedbackLoad20261027
open JurisLean.Candidates.AdaptiveRoundLedger20261027
open JurisLean.Candidates.LegalActionDomain20261027
open JurisLean.Candidates.LoadedLegalConsumer20261027

/-!
Actual finite observations are passed to the existing calibration and validation
consumers. Both confidence events use the same declared validation law QΓ.
The law concerns statistical validation; legal branches are not assigned a law.
No independence between the calibration and validation streams is assumed.
-/

def samplePacket {m n : Nat} (template : CalibrationPacket m)
    (models : List (List ℚ)) (events : Fin n → EventId)
    (data : Fin n → Fin m × Bool) : CalibrationPacket m :=
  { template with
    models := models
    rows := List.ofFn (fun i => ⟨events i, (data i).1, (data i).2⟩) }

/-- This retains every row, its multiplicity and its original finite index. -/
theorem sample_packet_reads_actual_column {m n : Nat}
    (template : CalibrationPacket m) (models : List (List ℚ))
    (events : Fin n → EventId) (data : Fin n → Fin m × Bool) :
    ∃ size : (samplePacket template models events data).rows.length = n,
      ∀ i : Fin n,
        calibrationData (samplePacket template models events data)
          (Fin.cast size.symm i) = data i := by
  refine ⟨by simp [samplePacket], ?_⟩
  intro i
  simp [calibrationData, samplePacket, List.get_ofFn]

private theorem packet_empirical_score {m n : Nat} {H : Type}
    (template : CalibrationPacket m) (models : List (List ℚ))
    (events : Fin n → EventId) (data : Fin n → Fin m × Bool)
    (loss : H → Fin m × Bool → ℚ) (h : H) :
    empiricalScore loss (calibrationData (samplePacket template models events data)) h =
      empiricalScore loss data h := by
  simp [empiricalScore, calibrationData, samplePacket]
  congr 1
  exact Fintype.sum_equiv
    (finCongr (List.length_ofFn (f := fun i =>
      SampleObservation.mk (events i) (data i).1 (data i).2))) _ _ (fun _ => rfl)

private theorem packet_produce_interval {m n : Nat}
    (protocol : LearningProtocol) (fitted : FittedTable)
    (models : List (List ℚ)) (template : CalibrationPacket m)
    (events : Fin n → EventId) (data : Fin n → Fin m × Bool)
    (query : Fin m) (radius : ℚ) (exponent : Nat) :
    produceInterval protocol fitted models
        (calibrationData (samplePacket template models events data))
        query radius exponent template.snapshot template.supported =
      produceInterval protocol fitted models data
        query radius exponent template.snapshot template.supported := by
  simp only [produceInterval, packet_empirical_score]
  simp only [samplePacket, List.length_ofFn]

def sampledRequest {m G : Nat} (base : RoundRequest m)
    (plan : ValidationPlan) (n : Fin G → Nat)
    (domain snapshot : Fin G → Nat) (delta radius : Fin G → ℚ)
    (exponent : Fin G → Nat) (tolerance : Fin G → ℚ)
    (events : (g : Fin G) → Fin (n g) → EventId)
    (data : (g : Fin G) → Fin (n g) → Fin m × Bool) : RoundRequest m :=
  { base with blocks := List.ofFn (fun g =>
      sampledBlock plan (domain g) (snapshot g) (delta g) (radius g)
        (exponent g) (tolerance g) (events g) (data g)) }

/-- The actual request reads these blocks; its external receipts are not replaced. -/
theorem sampled_request_reads_actual_blocks {m G : Nat}
    (base : RoundRequest m) (plan : ValidationPlan) (n : Fin G → Nat)
    (domain snapshot : Fin G → Nat) (delta radius : Fin G → ℚ)
    (exponent : Fin G → Nat) (tolerance : Fin G → ℚ)
    (events : (g : Fin G) → Fin (n g) → EventId)
    (data : (g : Fin G) → Fin (n g) → Fin m × Bool) :
    (sampledRequest base plan n domain snapshot delta radius exponent tolerance events data).blocks =
      List.ofFn (fun g => sampledBlock plan (domain g) (snapshot g) (delta g) (radius g)
        (exponent g) (tolerance g) (events g) (data g)) ∧
    (sampledRequest base plan n domain snapshot delta radius exponent tolerance events data).sampling =
      base.sampling ∧
    (sampledRequest base plan n domain snapshot delta radius exponent tolerance events data).permit =
      base.permit := ⟨rfl, rfl, rfl⟩

def activatedRound {m : Nat} (state : RoundState m) (evaluation : Evaluation m)
    (samples : List (SamplingReceipt m)) (receipt : SamplingReceipt m)
    (permits : List (LoadPermit m)) (permit : LoadPermit m) : RoundState m :=
  { state with service := (activate state.service evaluation samples receipt permits permit).post }

/-- On one actual joint event, computed validation bounds apply to the model
actually loaded, and the actual downstream chosen decision carries the interval
computed from the actual calibration column. All success and permission checks
remain the checks of the existing consumers. -/
theorem actual_chosen_and_loaded_joint_confidence
    {Ω : Type*} {m nc G : Nat} [MeasurableSpace Ω]
    [MeasurableSpace (Fin m × Bool)] [MeasurableSingletonClass (Fin m × Bool)]
    (QΓ : Measure Ω) [IsProbabilityMeasure QΓ]
    (Pc : Measure (Fin m × Bool)) [IsProbabilityMeasure Pc]
    (Pv : Fin G → Measure (Fin m × Bool)) [∀ g, IsProbabilityMeasure (Pv g)]
    (hm : 0 < m) (hnc : 0 < nc)
    (protocol : LearningProtocol) (first : List ℚ) (rest : List (List ℚ))
    (calSample : Fin nc → Ω → Fin m × Bool)
    (calMeasurable : ∀ i, Measurable (calSample i))
    (calIndependent : iIndepFun calSample QΓ)
    (calLaw : ∀ i, IdentDistrib (calSample i) id QΓ Pc)
    (calDeltaPositive : 0 < protocol.failureBudget)
    (calDeltaBelowOne : protocol.failureBudget < 1)
    (plan : ValidationPlan) (planNonempty : plan.models.toFinset.Nonempty)
    (nv : Fin G → Nat) (nvPositive : ∀ g, 0 < nv g)
    (valSample : (g : Fin G) → Fin (nv g) → Ω → Fin m × Bool)
    (valMeasurable : ∀ g i, Measurable (valSample g i))
    (valIndependent : ∀ g, iIndepFun (valSample g) QΓ)
    (valLaw : ∀ g i, IdentDistrib (valSample g i) id QΓ (Pv g))
    (bounded : ∀ table ∈ plan.models, ∀ z : Fin m × Bool,
      (tableLoss binaryLoss table z : ℝ) ∈ Set.Icc (0 : ℝ) 1)
    (delta : Fin G → ℚ) (deltaPositive : ∀ g, 0 < delta g)
    (deltaBelowOne : ∀ g, delta g < 1)
    (budget : (∑ g, delta g) ≤ plan.failureBudget) :
    ∃ good : Set Ω, MeasurableSet good ∧
      1 - ((protocol.failureBudget : ℝ) + (plan.failureBudget : ℝ)) ≤ QΓ.real good ∧
      ∀ w ∈ good, ∀ (state : RoundState m) (base : RoundRequest m)
        (candidate : TrainingCandidate m)
        (domain snapshot : Fin G → Nat) (radius tolerance : Fin G → ℚ)
        (exponent : Fin G → Nat) (events : (g : Fin G) → Fin (nv g) → EventId)
        (evaluation : Evaluation m)
        (samples : List (SamplingReceipt m)) (permits : List (LoadPermit m)),
        evaluate plan (readLoaded state.service) candidate binaryLoss
          (sampledRequest base plan nv domain snapshot delta radius exponent tolerance events
            (fun g i => valSample g i w)).blocks = .known evaluation →
        (activate state.service evaluation samples base.sampling permits base.permit).status = .loaded →
        ∀ (template : CalibrationPacket m) (calEvents : Fin nc → EventId)
          (request : DecisionRequest m), request.protocol = protocol →
          ∀ (W : Type) (legal : LegalInput W) (model : ActionModel W Ledger.Handle)
            (proposals : List Proposal) (catalog : List (CalibrationPacket m))
            (calRadius : ℚ) (calExponent : Nat) (utility : ℚ → ℚ)
            (grants : List Authorization.Grant) (initial : Ledger.Handle)
            (selected : IntervalDecision m),
          (runLoaded legal model proposals
            (activatedRound state evaluation samples base.sampling permits base.permit)
            request (samplePacket template (first :: rest) calEvents (fun i => calSample i w))
            catalog calRadius calExponent utility grants initial).decision = .known selected →
          selected.probability.fitted =
            (readLoaded (activatedRound state evaluation samples base.sampling permits base.permit).service).fitted ∧
          (0 < Pc.real {z | scoreBin (selected.probability.fitted.table, selected.probability.query) z = true} ∧
            (selected.probability.lower : ℝ) ≤
              Pc.real {z | scoreBin (selected.probability.fitted.table, selected.probability.query) z = true ∧ z.2 = true} /
                Pc.real {z | scoreBin (selected.probability.fitted.table, selected.probability.query) z = true} ∧
            Pc.real {z | scoreBin (selected.probability.fitted.table, selected.probability.query) z = true ∧ z.2 = true} /
                Pc.real {z | scoreBin (selected.probability.fitted.table, selected.probability.query) z = true} ≤
              (selected.probability.upper : ℝ)) ∧
          ∀ g, (∫ z, (tableLoss binaryLoss
              (readLoaded (activatedRound state evaluation samples base.sampling permits base.permit).service).fitted.table z : ℝ) ∂Pv g) ≤
            (∫ z, (tableLoss binaryLoss (readLoaded state.service).fitted.table z : ℝ) ∂Pv g) +
              (tolerance g : ℝ) := by
  obtain ⟨C, hmC, massC, confidenceC⟩ :=
    frozen_family_probability_confidence QΓ Pc hm hnc protocol first rest
      calSample calMeasurable calIndependent calLaw calDeltaPositive calDeltaBelowOne
  obtain ⟨V, hmV, massV, confidenceV⟩ :=
    actual_protected_evaluation_confidence QΓ Pv plan planNonempty nv nvPositive
      valSample valMeasurable valIndependent valLaw binaryLoss bounded
      delta deltaPositive deltaBelowOne budget
  have total : QΓ.real Set.univ = 1 := by simp
  have badC : QΓ.real Cᶜ ≤ (protocol.failureBudget : ℝ) := by
    rw [measureReal_compl hmC, total]
    linarith
  have badV : QΓ.real Vᶜ ≤ (plan.failureBudget : ℝ) := by
    rw [measureReal_compl hmV, total]
    linarith
  have bad : QΓ.real (C ∩ V)ᶜ ≤
      (protocol.failureBudget : ℝ) + (plan.failureBudget : ℝ) := by
    have complement : (C ∩ V)ᶜ = Cᶜ ∪ Vᶜ := by
      classical
      ext w
      by_cases hw : w ∈ C <;> simp [hw]
    rw [complement]
    exact (measureReal_union_le _ _).trans (add_le_add badC badV)
  have mass : 1 - ((protocol.failureBudget : ℝ) + (plan.failureBudget : ℝ)) ≤
      QΓ.real (C ∩ V) := by
    rw [measureReal_compl (hmC.inter hmV), total] at bad
    linarith
  refine ⟨C ∩ V, hmC.inter hmV, mass, ?_⟩
  intro w hw state base candidate domain snapshot radius tolerance exponent events
    evaluation samples permits evaluated loaded template calEvents request protocolSame
    W legal model proposals catalog calRadius calExponent utility grants initial selected chosen
  let next := activatedRound state evaluation samples base.sampling permits base.permit
  have computed :
      evaluate plan (readLoaded state.service) candidate binaryLoss
        (List.ofFn (fun g => sampledBlock plan (domain g) (snapshot g) (delta g) (radius g)
          (exponent g) (tolerance g) (events g) (fun i => valSample g i w))) = .known evaluation := by
    simpa only [sampledRequest] using evaluated
  have assembledActual := (evaluation_is_actual_input_and_computation plan
    (readLoaded state.service) candidate binaryLoss _ evaluation computed).2.2.2
  obtain ⟨_, _, _, passed, _, _, actualRead, _⟩ :=
    loaded_package_is_actual_written_readback state.service evaluation samples base.sampling
      permits base.permit loaded
  have actualCandidate : readLoaded next.service = candidate := by
    change readLoaded (activate state.service evaluation samples base.sampling permits base.permit).post =
      candidate
    rw [actualRead, assembledActual]
    rfl
  have validationRisk := confidenceV w hw.2 (readLoaded state.service) candidate
    domain snapshot radius tolerance exponent events evaluation computed passed
  have sameModel := (loaded_run_choice_uses_current_model legal model proposals next request
    (samplePacket template (first :: rest) calEvents (fun i => calSample i w))
    catalog calRadius calExponent utility grants initial selected chosen).1
  have chooseActual :
      chooseLoaded request utility (review legal model initial proposals).allowed
        (loadedProbability next request
          (samplePacket template (first :: rest) calEvents (fun i => calSample i w))
          catalog calRadius calExponent) = .known selected := by
    change (if _ then Result.rejected .scopeMismatch else _) = .known selected at chosen
    split at chosen
    · cases chosen
    · exact chosen
  obtain ⟨p, quote, produced, _, _, sameProbability, _, _⟩ :=
    selected_decision_reads_same_probability_and_quote request utility
      (review legal model initial proposals).allowed _ selected chooseActual
  have producedPacket := (known_probability_binds_actual_loaded_and_sample next request
    (samplePacket template (first :: rest) calEvents (fun i => calSample i w))
    catalog calRadius calExponent p produced).2.1
  have producedColumn :
      produceInterval protocol (readLoaded next.service).fitted (first :: rest)
        (fun i => calSample i w) request.query calRadius calExponent
        template.snapshot template.supported = .known p := by
    change produceInterval request.protocol (readLoaded next.service).fitted (first :: rest)
      (calibrationData (samplePacket template (first :: rest) calEvents (fun i => calSample i w)))
      request.query calRadius calExponent template.snapshot template.supported = .known p at producedPacket
    rw [packet_produce_interval, protocolSame] at producedPacket
    exact producedPacket
  have calibrationInterval := confidenceC w hw.1 (readLoaded next.service).fitted request.query
    calRadius calExponent template.snapshot template.supported p producedColumn
  refine ⟨sameModel, ?_, ?_⟩
  · rw [sameProbability]
    exact calibrationInterval
  · intro g
    have risk := validationRisk g
    rw [← actualCandidate] at risk
    simpa only [next] using risk

end JurisLean.Candidates.U00ActualStatisticalJoin20261031