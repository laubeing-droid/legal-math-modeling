import JurisLean.Candidates.AdaptiveRoundLedger20261027
import JurisLean.Candidates.LoadedLegalConsumer20261027

noncomputable section

namespace JurisLean.Candidates.U00RoundPostBridge20261031

open JurisLean.Candidates.Final20261021
open JurisLean.Candidates.EventFeedbackConsumer20261027
open JurisLean.Candidates.ProtectedFeedback20261027
open JurisLean.Candidates.ValidatedFeedbackLoad20261027
open JurisLean.Candidates.AdaptiveRoundLedger20261027
open JurisLean.Candidates.DecisionTrajectoryConsumer20261027
open JurisLean.Candidates.IntervalDecisionConsumer20261027
open JurisLean.Candidates.LegalActionDomain20261027
open JurisLean.Candidates.LoadedLegalConsumer20261027

/-- U00 L741/L744 and edges 14--15: the fresh round's actual post service
is the post of its actual activation, including refusal outcomes. -/
theorem fresh_round_post_service_is_actual_activation {m : Nat}
    (s : RoundState m) (d : RoundDeclaration m) (r : RoundRequest m)
    (samples : List (SamplingReceipt m)) (permits : List (LoadPermit m))
    (evaluation : Evaluation m) (loaded : LoadOutcome m)
    (fresh : s.records.find? (fun entry => entry.request.round == r.round) = none)
    (round : r.round = s.records.length)
    (room : s.records.length < s.horizon)
    (pending : s.pending = some d)
    (actualEvaluation :
      (assessAdaptiveRound s d r samples permits).evaluation = some (.known evaluation))
    (actualLoad : (assessAdaptiveRound s d r samples permits).load = some loaded) :
    (finishAdaptiveRound s r samples permits).post.service =
      (activate s.service evaluation samples r.sampling permits r.permit).post := by
  have fromActivation :=
    assessed_load_comes_from_actual_activation s d r samples permits evaluation loaded
      actualEvaluation actualLoad
  calc
    (finishAdaptiveRound s r samples permits).post.service =
        (appendRoundRecord s (assessAdaptiveRound s d r samples permits)).service := by
      simp only [finishAdaptiveRound, fresh]
      simp [round, Nat.not_le_of_lt room, pending]
    _ = loaded.post :=
      recorded_load_is_actual_next_service s
        (assessAdaptiveRound s d r samples permits) loaded actualLoad
    _ = (activate s.service evaluation samples r.sampling permits r.permit).post :=
      congrArg (fun outcome : LoadOutcome m => outcome.post) fromActivation

/- U00 edges 14--15: a successful actual probability call transports to the
same service with fewer exposed events. The success gate supplies non-reuse. -/
private theorem known_probability_with_less_exposure {m : Nat}
    (older newer : RoundState m)
    (sameService : older.service = newer.service)
    (lessExposure : ∀ event ∈ exposedRoundEvents older,
      event ∈ exposedRoundEvents newer)
    (request : DecisionRequest m) (packet : CalibrationPacket m)
    (catalog : List (CalibrationPacket m)) (radius : ℚ) (exponent : Nat)
    (p : ProbabilityIntervalConsumer20261027.SampleProbability m)
    (known : loadedProbability newer request packet catalog radius exponent = .known p) :
    loadedProbability older request packet catalog radius exponent = .known p := by
  have bound := known_probability_binds_actual_loaded_and_sample
    newer request packet catalog radius exponent p known
  have readyNew := bound.1
  have readyOld : calibrationReady older request packet catalog = true := by
    simp only [calibrationReady, decide_eq_true_eq] at readyNew ⊢
    simp only [sameService]
    rcases readyNew with
      ⟨member, loadedBinding, packetContext, requestContext, protocolBinding,
        snapshotBinding, scopeBinding, protocolValid, lossVersion, ruleVersion,
        mechanismVersion, declaredBefore, timeReady, modelLengths, distinctRows, rowsNew⟩
    have rowsOld : ∀ row ∈ packet.rows,
        row.event ∉ trainingEvents newer.service.journal ∧
        row.event ∉ trainingEvents (readLoaded newer.service).snapshot ∧
        row.event ∉ exposedRoundEvents older := by
      intro row member
      have h := rowsNew row member
      exact ⟨h.1, h.2.1, fun exposed => h.2.2 (lessExposure row.event exposed)⟩
    exact ⟨member, loadedBinding, packetContext, requestContext, protocolBinding,
      snapshotBinding, scopeBinding, protocolValid, lossVersion, ruleVersion,
      mechanismVersion, declaredBefore, timeReady, modelLengths, distinctRows, rowsOld⟩
  simpa [loadedProbability, readyOld, sameService] using bound.2.1

/- U00 edges 14--15: transport only a known decision, not arbitrary calls.
All legal review, context, utility, permission and execution inputs stay actual. -/
private theorem known_run_with_less_exposure {W : Type} {m : Nat}
    (older newer : RoundState m)
    (sameService : older.service = newer.service)
    (lessExposure : ∀ event ∈ exposedRoundEvents older,
      event ∈ exposedRoundEvents newer)
    (input : LegalInput W) (model : ActionModel W Ledger.Handle)
    (proposals : List Proposal) (request : DecisionRequest m)
    (packet : CalibrationPacket m) (catalog : List (CalibrationPacket m))
    (radius : ℚ) (exponent : Nat) (utility : ℚ → ℚ)
    (grants : List Authorization.Grant) (initial : Ledger.Handle)
    (selected : IntervalDecision m)
    (chosen : (runLoaded input model proposals newer request packet catalog radius exponent
      utility grants initial).decision = .known selected) :
    (runLoaded input model proposals older request packet catalog radius exponent
      utility grants initial).decision = .known selected := by
  have actualChosen := chosen
  change (if input.anchor.gamma ≠ request.gamma ∨ initial.gamma ≠ request.gamma then
      Result.rejected .scopeMismatch
    else chooseLoaded request utility (review input model initial proposals).allowed
      (loadedProbability newer request packet catalog radius exponent)) = .known selected at chosen
  split at chosen
  · cases chosen
  · obtain ⟨p, quote, known, _, _, _, _, _⟩ :=
      selected_decision_reads_same_probability_and_quote request utility
        (review input model initial proposals).allowed
        (loadedProbability newer request packet catalog radius exponent) selected chosen
    have oldKnown := known_probability_with_less_exposure older newer sameService lessExposure
      request packet catalog radius exponent p known
    have sameProbability :
        loadedProbability older request packet catalog radius exponent =
          loadedProbability newer request packet catalog radius exponent :=
      oldKnown.trans known.symm
    have sameDecision :
        (runLoaded input model proposals older request packet catalog radius exponent
          utility grants initial).decision =
        (runLoaded input model proposals newer request packet catalog radius exponent
          utility grants initial).decision := by
      simp only [runLoaded, sameProbability]
    exact sameDecision.trans actualChosen

/-- U00 L741/L744 and edges 14--15: a decision actually chosen after the fresh
round is also chosen in the activation-service projection. The new record's
exposure check is retained and success implies the weaker old-history check. -/
theorem actual_round_choice_transports_to_activation_projection {W : Type} {m : Nat}
    (s : RoundState m) (d : RoundDeclaration m) (r : RoundRequest m)
    (samples : List (SamplingReceipt m)) (permits : List (LoadPermit m))
    (evaluation : Evaluation m) (loaded : LoadOutcome m)
    (fresh : s.records.find? (fun entry => entry.request.round == r.round) = none)
    (round : r.round = s.records.length)
    (room : s.records.length < s.horizon)
    (pending : s.pending = some d)
    (actualEvaluation :
      (assessAdaptiveRound s d r samples permits).evaluation = some (.known evaluation))
    (actualLoad : (assessAdaptiveRound s d r samples permits).load = some loaded)
    (input : LegalInput W) (model : ActionModel W Ledger.Handle)
    (proposals : List Proposal) (request : DecisionRequest m)
    (packet : CalibrationPacket m) (catalog : List (CalibrationPacket m))
    (radius : ℚ) (exponent : Nat) (utility : ℚ → ℚ)
    (grants : List Authorization.Grant) (initial : Ledger.Handle)
    (selected : IntervalDecision m)
    (chosen : (runLoaded input model proposals
      (finishAdaptiveRound s r samples permits).post request packet catalog radius exponent
      utility grants initial).decision = .known selected) :
    (runLoaded input model proposals
      { s with service := (activate s.service evaluation samples r.sampling permits r.permit).post }
      request packet catalog radius exponent utility grants initial).decision = .known selected := by
  have finished :
      (finishAdaptiveRound s r samples permits).post =
        appendRoundRecord s (assessAdaptiveRound s d r samples permits) := by
    simp only [finishAdaptiveRound, fresh]
    simp [round, Nat.not_le_of_lt room, pending]
  have serviceSame :=
    fresh_round_post_service_is_actual_activation s d r samples permits evaluation loaded
      fresh round room pending actualEvaluation actualLoad
  apply known_run_with_less_exposure
    ({ s with service := (activate s.service evaluation samples r.sampling permits r.permit).post })
    ((finishAdaptiveRound s r samples permits).post)
    serviceSame.symm ?_ input model proposals request packet catalog radius exponent
    utility grants initial selected chosen
  intro event exposed
  have oldExposure : event ∈ exposedRoundEvents s := exposed
  rw [finished]
  have appended :
      exposedRoundEvents (appendRoundRecord s (assessAdaptiveRound s d r samples permits)) =
        exposedRoundEvents s ++
          requestedEvents (assessAdaptiveRound s d r samples permits).request := by
    simp [exposedRoundEvents, appendRoundRecord]
  rw [appended]
  exact List.mem_append.mpr (Or.inl oldExposure)

end JurisLean.Candidates.U00RoundPostBridge20261031
