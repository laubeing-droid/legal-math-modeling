import JurisLean.CN.Revision20261101.World
import JurisLean.Candidates.LearningConsumer20261027
import JurisLean.Candidates.CausalSelection20261027
import JurisLean.Candidates.Final20261021.Decision
import JurisLean.Candidates.Final20261021.Ledger
import JurisLean.Candidates.PolicyResponse20261027
import JurisLean.Candidates.AdaptiveRoundLedger20261027

/- Native source types, before legal state. No second state or semantics. -/
namespace JurisLean.CN.Completion20261105
open JurisLean.CN.Revision20261101
namespace Native
export JurisLean.Candidates.Final20261021
  (Result Error PaymentPayload AmountTag PartyId)
namespace Fit
export JurisLean.Candidates.LearningConsumer20261027
  (LearningProtocol FittedTable fitTable u01_6_fit_card_minimizes_actual_sample tableLoss)
end Fit
namespace Prob
export JurisLean.Candidates.Final20261021.Probability
  (FiniteLaw proposed_probability_model posterior_mass expectation)
end Prob
namespace Causal
export JurisLean.Candidates.CausalSelection20261027
  (selectionRecoveryValue interventionValue selected_weight_recovery)
end Causal
namespace Decision
export JurisLean.Candidates.Final20261021.Decision
  (best best_mem best_dominates legalBest legal_best_sound TypedValue addValues evalExact
    Evaluates u06_3_eval_exists u06_3_eval_unique)
end Decision
namespace Cash
export JurisLean.Candidates.Final20261021.Ledger
  (State Conserves CashConsistent performance balance u09_1_quantity_conservation
    performance_cash_consistent)
end Cash
namespace Response
export JurisLean.Candidates.PolicyResponse20261027 (preparationUtility finite_response_payoffs)
end Response
namespace RSI
export JurisLean.Candidates.AdaptiveRoundLedger20261027
  (RoundState RoundRequest RoundOutcome finishAdaptiveRound roundSpent
    finish_round_preserves_budget assessed_load_comes_from_actual_activation
    recorded_load_is_actual_next_service)
export JurisLean.Candidates.ValidatedFeedbackLoad20261027 (SamplingReceipt LoadPermit)
end RSI
end Native


structure CausalInput (n k : Nat) where
  mass : Native.Prob.FiniteLaw (Fin n)
  latent : Fin n → Native.Prob.FiniteLaw (Fin k)
  assignment : Fin n → Native.Prob.FiniteLaw Bool
  recording : Fin n → Bool → ℚ
  response : Fin n → Fin k → Bool → ℚ


inductive EngineCall
  | fit (m n : Nat) (protocol : Native.Fit.LearningProtocol)
      (loss : ℚ → Bool → ℚ) (models : List (List ℚ)) (data : Fin n → Fin m × Bool)
  | prob (n : Nat) (prior : Native.Prob.FiniteLaw (Fin n))
      (likelihood : Fin n → ℚ) (event : Fin n → Ref .event)
  | causal (n k : Nat) (model : CausalInput n k) (permit : Option CausalPermit)
  | bargain (n : Nat) (score : Fin n → ℚ) (permitted : Fin n → Bool)
      (options : List (Fin n)) (offers : Fin n → List (Ref .actor × Quantity .money))
  | cash (before : Native.Cash.State) (payment : Native.PaymentPayload)
  | exact (unit : UnitKind) (left right : Native.Decision.TypedValue)
  | behavior (threshold : ℚ) (actor : Ref .actor) (action : Fin 3 → Ref .query)
  | rsi (m : Nat) (before : Native.RSI.RoundState m) (request : Native.RSI.RoundRequest m)
      (samples : List (Native.RSI.SamplingReceipt m)) (permits : List (Native.RSI.LoadPermit m))
      (proposal : Ref .model)

def EngineCall.NativeType : EngineCall → Type
  | .fit _ _ _ _ _ _ => Native.Result Native.Fit.FittedTable
  | .prob n _ _ _ => Native.Result (Native.Prob.FiniteLaw (Fin n))
  | .causal _ _ _ _ => Native.Result ℚ
  | .bargain n _ _ _ _ => Native.Result (Fin n)
  | .cash _ _ => Native.Result Native.Cash.State
  | .exact _ _ _ => Native.Result Native.Decision.TypedValue
  | .behavior _ _ _ => Native.Result (Fin 3)
  | .rsi m _ _ _ _ _ => Native.RSI.RoundOutcome m


structure EngineMaterial where
  id : Ref .material
  scope : Scope
  target : Ref .query
  source : Ref .document
  version : Nat
  input : EngineCall

end JurisLean.CN.Completion20261105
