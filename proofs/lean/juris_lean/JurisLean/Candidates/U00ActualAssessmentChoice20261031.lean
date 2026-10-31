import JurisLean.Candidates.U00ActualStatisticalJoin20261031
import JurisLean.Candidates.U00RoundPostBridge20261031
import JurisLean.Candidates.U00RSICandidateBridge20261031

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace JurisLean.Candidates.U00ActualAssessmentChoice20261031

open JurisLean.Candidates.Final20261021
open JurisLean.Candidates.LearningERM20261027
open JurisLean.Candidates.LearningConsumer20261027
open JurisLean.Candidates.EventFeedbackConsumer20261027
open JurisLean.Candidates.ProtectedFeedback20261027
open JurisLean.Candidates.ValidatedFeedbackLoad20261027
open JurisLean.Candidates.AdaptiveRoundLedger20261027
open JurisLean.Candidates.LoadedLegalConsumer20261027
open JurisLean.Candidates.IntervalDecisionConsumer20261027
open JurisLean.Candidates.BusinessFeedbackLoop20261027
open JurisLean.Candidates.U00ActualStatisticalJoin20261031
open JurisLean.Candidates.U00RoundPostBridge20261031
open JurisLean.Candidates.U00RSICandidateBridge20261031

/-!
U00 section 13: B's same-law event reaches the actual fresh assessment and
next act through C's one-way successful-choice transport. No probability
theorem or state induction is repeated.
-/

/-- The actual personal producer supplies B's parent, not an arbitrary typed
pending declaration. E's successful-entry theorem supplies this native call. -/
private theorem native_assessment_reads_actual_loaded_parent {m : Nat}
    (exchange : PersonalExchange m) (personalRequest : RSI.PredictionRequest)
    (now : Instant) (meanings : List (LogMeaning m)) (nativePlan : ValidationPlan)
    (native : RoundState m)
    (started : startPersonalRound exchange personalRequest now meanings nativePlan = .known native)
    (declaration : RoundDeclaration m) (pending : native.pending = some declaration)
    (request : RoundRequest m) (samples : List (SamplingReceipt m))
    (permits : List (LoadPermit m)) (evaluation : Evaluation m)
    (actual : (assessAdaptiveRound native declaration request samples permits).evaluation =
      some (.known evaluation)) :
    ∃ candidate : TrainingCandidate m,
      declaration.prepared.candidate = .known candidate ∧
      evaluate declaration.plan (readLoaded native.service) candidate binaryLoss request.blocks =
        .known evaluation ∧ declaration.plan = request.sampling.plan := by
  have receiptPlan : declaration.plan = request.sampling.plan := by
    by_contra different
    have opposite : request.sampling.plan ≠ declaration.plan := Ne.symm different
    unfold assessAdaptiveRound at actual
    split_ifs at actual <;> simp_all [emptyRoundRecord]
  obtain ⟨generated, generatedPending, parent, _⟩ :=
    native_pending_binds_actual_parent_and_sample exchange personalRequest now meanings
      nativePlan native started
  have sameDeclaration : generated = declaration :=
    Option.some.inj (generatedPending.symm.trans pending)
  subst generated
  have keepsLoaded : readLoaded native.service = readLoaded exchange.round.service := by
    obtain ⟨input, _, _, _, nativeSame, _⟩ :=
      actual_personal_round_uses_native_entry exchange personalRequest now meanings
        nativePlan native started
    rw [nativeSame]
    dsimp only [nativeBegin]
    unfold beginAdaptiveRound
    split <;> rfl
  have sameParent : declaration.prepared.parent = readLoaded native.service :=
    parent.trans keepsLoaded.symm
  unfold assessAdaptiveRound at actual
  split_ifs at actual <;> try simp_all [emptyRoundRecord]
  cases candidateKnown : declaration.prepared.candidate with
  | unknown e => simp [candidateKnown, emptyRoundRecord] at actual
  | rejected e => simp [candidateKnown, emptyRoundRecord] at actual
  | conflict a b => simp [candidateKnown, emptyRoundRecord] at actual
  | known candidate =>
      cases computed : evaluate declaration.plan declaration.prepared.parent
          candidate binaryLoss request.blocks with
      | unknown e => simp [candidateKnown, computed, emptyRoundRecord] at actual
      | rejected e => simp [candidateKnown, computed, emptyRoundRecord] at actual
      | conflict a b => simp [candidateKnown, computed, emptyRoundRecord] at actual
      | known value =>
          have same : value = evaluation := by
            simpa [candidateKnown, computed] using actual
          subst value
          refine ⟨candidate, rfl, ?_, receiptPlan⟩
          simpa only [sameParent] using computed

/-- Actual computed evaluate/load branches and original fresh guards remain
explicit. The good event, its mass and both risk conclusions are derived. -/
theorem actual_assessment_and_next_action_joint_confidence
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
      ∀ w ∈ good, ∀ (state : State m) (declaration : RoundDeclaration m)
        (base : RoundRequest m) (exchange : PersonalExchange m)
        (personalRequest : RSI.PredictionRequest) (nativeNow : Instant)
        (meanings : List (LogMeaning m)) (nativePlan : ValidationPlan)
        (domain snapshot : Fin G → Nat) (radius tolerance : Fin G → ℚ)
        (exponent : Fin G → Nat) (events : (g : Fin G) → Fin (nv g) → EventId)
        (evaluation : Evaluation m) (loaded : LoadOutcome m)
        (samples : List (SamplingReceipt m)) (permits : List (LoadPermit m)),
        let request := sampledRequest base plan nv domain snapshot delta radius exponent
          tolerance events (fun g i => valSample g i w)
        startPersonalRound exchange personalRequest nativeNow meanings nativePlan =
          .known state.learning →
        base.sampling.plan = plan →
        state.learning.records.find? (fun entry => entry.request.round == request.round) = none →
        request.round = state.learning.records.length →
        state.learning.records.length < state.learning.horizon →
        state.learning.pending = some declaration →
        (assessAdaptiveRound state.learning declaration request samples permits).evaluation =
          some (.known evaluation) →
        (assessAdaptiveRound state.learning declaration request samples permits).load =
          some loaded →
        loaded.status = .loaded →
        ∀ (template : CalibrationPacket m) (calEvents : Fin nc → EventId)
          (W : Type) (input : ActionInput W m),
          input.request.protocol = protocol →
          let actualInput : ActionInput W m :=
            { input with calibration :=
                samplePacket template (first :: rest) calEvents (fun i => calSample i w) }
          ∀ (actual : LoadedRun W m) (selected : IntervalDecision m),
            (act (assess state request samples permits) actualInput).run = some actual →
            actual.decision = .known selected →
            selected.probability.fitted =
              (readLoaded (finishAdaptiveRound state.learning request samples permits).post.service).fitted ∧
            (0 < Pc.real {z | scoreBin (selected.probability.fitted.table,
                selected.probability.query) z = true} ∧
              (selected.probability.lower : ℝ) ≤
                Pc.real {z | scoreBin (selected.probability.fitted.table,
                    selected.probability.query) z = true ∧ z.2 = true} /
                  Pc.real {z | scoreBin (selected.probability.fitted.table,
                    selected.probability.query) z = true} ∧
              Pc.real {z | scoreBin (selected.probability.fitted.table,
                    selected.probability.query) z = true ∧ z.2 = true} /
                  Pc.real {z | scoreBin (selected.probability.fitted.table,
                    selected.probability.query) z = true} ≤ (selected.probability.upper : ℝ)) ∧
            ∀ g, (∫ z, (tableLoss binaryLoss
                (readLoaded (finishAdaptiveRound state.learning request samples permits).post.service).fitted.table
                  z : ℝ) ∂Pv g) ≤
              (∫ z, (tableLoss binaryLoss (readLoaded state.learning.service).fitted.table z : ℝ) ∂Pv g) +
                (tolerance g : ℝ) := by
  obtain ⟨good, measurable, mass, onGood⟩ :=
    actual_chosen_and_loaded_joint_confidence QΓ Pc Pv hm hnc protocol first rest
      calSample calMeasurable calIndependent calLaw calDeltaPositive calDeltaBelowOne
      plan planNonempty nv nvPositive valSample valMeasurable valIndependent valLaw
      bounded delta deltaPositive deltaBelowOne budget
  refine ⟨good, measurable, mass, ?_⟩
  intro w hw state declaration base exchange personalRequest nativeNow meanings nativePlan
    domain snapshot radius tolerance exponent events evaluation loaded samples permits
  dsimp only
  intro started receiptPlan fresh round room pending actualEvaluation actualLoad loadedStatus
    template calEvents W input protocolSame
  dsimp only
  intro actual selected called chosen
  let request := sampledRequest base plan nv domain snapshot delta radius exponent tolerance
    events (fun g i => valSample g i w)
  let packet := samplePacket template (first :: rest) calEvents (fun i => calSample i w)
  let actualInput : ActionInput W m := { input with calibration := packet }
  obtain ⟨candidate, candidateKnown, nativeComputed, planFromReceipt⟩ :=
    native_assessment_reads_actual_loaded_parent exchange personalRequest nativeNow meanings nativePlan
      state.learning started declaration pending request samples permits evaluation actualEvaluation
  have samePlan : declaration.plan = plan := planFromReceipt.trans receiptPlan
  have computed : evaluate plan (readLoaded state.learning.service) candidate binaryLoss
      request.blocks = .known evaluation := by
    simpa only [samePlan] using nativeComputed
  obtain ⟨initial, reported, exactRun, payment⟩ :=
    actual_action_reads_current_handle_and_loaded_state
      (assess state request samples permits) actualInput actual called
  rw [exactRun] at chosen
  have transported := actual_round_choice_transports_to_activation_projection
    state.learning declaration request samples permits evaluation loaded fresh round room pending
    actualEvaluation actualLoad input.legal input.model input.proposals input.request packet
    input.calibrationCatalog input.radius input.exponent input.utility input.grants initial selected chosen
  have fromActivation := assessed_load_comes_from_actual_activation state.learning declaration
    request samples permits evaluation loaded actualEvaluation actualLoad
  have activated : (activate state.learning.service evaluation samples request.sampling
      permits request.permit).status = .loaded := by
    rw [← fromActivation]
    exact loadedStatus
  have result := onGood w hw state.learning base candidate domain snapshot radius tolerance
    exponent events evaluation samples permits computed activated template calEvents input.request
    protocolSame W input.legal input.model input.proposals input.calibrationCatalog
    input.radius input.exponent input.utility input.grants initial selected transported
  have serviceSame :
      (finishAdaptiveRound state.learning request samples permits).post.service =
        (activatedRound state.learning evaluation samples request.sampling permits request.permit).service :=
    fresh_round_post_service_is_actual_activation state.learning declaration request samples permits
      evaluation loaded fresh round room pending actualEvaluation actualLoad
  rw [← serviceSame] at result
  exact result

end JurisLean.Candidates.U00ActualAssessmentChoice20261031
