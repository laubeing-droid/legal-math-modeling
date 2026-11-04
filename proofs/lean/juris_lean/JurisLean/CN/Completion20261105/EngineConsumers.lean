import JurisLean.CN.Completion20261105.Operators
import JurisLean.CN.Completion20261105.Payloads
import JurisLean.Candidates.LearningConsumer20261027
import JurisLean.Candidates.CausalSelection20261027
import JurisLean.Candidates.Final20261021.Decision
import JurisLean.Candidates.Final20261021.Ledger
import JurisLean.Candidates.PolicyResponse20261027
import JurisLean.Candidates.AdaptiveRoundLedger20261027

/-!
V4 7.2 / audit A08: calls to accepted source functions, not engine-name aliases.
Source snapshot: main b3bdaed60c59907260b74fbf9d5aea01ab4c7854.
Native replies retain the complete actual source result as well as the legal
candidate projection. Numerical source results never directly update F/N/L.
The connection theorems invoke accepted declarations without reproving U.
-/
namespace JurisLean.CN.Completion20261105
open JurisLean.CN.Revision20261101

structure EngineContext where
  scope : Scope
  target : Ref .query

structure NativeReply (α : Type) where
  legal : Reply EngineOutput
  native : α

def engineOutput (s : Situation) (c : EngineContext) (kind : UEng)
    (theoremName : String) (payload : EngineValue kind) : EngineOutput :=
  ⟨kind, c.scope, c.target, s.core.state.F.map (fun e => e.id),
    theoremName, [], payload⟩

def sourceUnknown : Native.Error → UnknownKind
  | .notIdentified | .unsupported | .authorityUnresolved | .incompatibleFiber => .systemNotJudge
  | _ => .inputUnchecked

def relayNative {α : Type} (s : Situation) (result : Native.Result α)
    (pack : α → EngineOutput) : NativeReply (Native.Result α) :=
  ⟨match result with
    | .known value =>
      let output := pack value
      ⟨(Law.proposeEngine s output).after, .success output⟩
    | .unknown reason => quiet s (.unknown (sourceUnknown reason))
    | .rejected _ => quiet s (.rejected .unsupported)
    | .conflict _ _ => quiet s (.conflict .competentReview),
   result⟩

/- Universal boundary for the actual consumers below: all native result
   branches retain legal facts, norms, relations and bindings. -/
theorem relay_is_candidate_only {α : Type} (s : Situation) (result : Native.Result α)
    (pack : α → EngineOutput) :
    (relayNative s result pack).legal.after.core.state.F = s.core.state.F ∧
    (relayNative s result pack).legal.after.core.state.N = s.core.state.N ∧
    (relayNative s result pack).legal.after.core.state.L = s.core.state.L ∧
    (relayNative s result pack).legal.after.core.state.bindings = s.core.state.bindings := by
  cases result <;> exact ⟨rfl, rfl, rfl, rfl⟩

def consumeFit {m n : Nat} {Y : Type} (s : Situation) (c : EngineContext)
    (protocol : Native.Fit.LearningProtocol) (loss : ℚ → Y → ℚ)
    (models : List (List ℚ)) (data : Fin n → Fin m × Y) :
    NativeReply (Native.Result Native.Fit.FittedTable) :=
  relayNative s (Native.Fit.fitTable protocol loss models data) (fun out =>
    engineOutput s c .fit
      "JurisLean.Candidates.LearningConsumer20261027.u01_6_fit_card_minimizes_actual_sample"
      (⟨out.empiricalRisk⟩, ⟨protocol.failureBudget⟩))

def probabilitySource {n : Nat} (prior : Native.Prob.FiniteLaw (Fin n))
    (likelihood : Fin n → ℚ) : Native.Result (Native.Prob.FiniteLaw (Fin n)) :=
  match Native.Prob.proposed_probability_model prior likelihood with
  | none => .unknown .notIdentified
  | some post => .known post

def consumeProb {n : Nat} (s : Situation) (c : EngineContext)
    (prior : Native.Prob.FiniteLaw (Fin n)) (likelihood : Fin n → ℚ)
    (event : Fin n → Ref .event) :
    NativeReply (Native.Result (Native.Prob.FiniteLaw (Fin n))) :=
  if decide (Function.Injective event) then
    relayNative s (probabilitySource prior likelihood) (fun post =>
      engineOutput s c .prob
      "JurisLean.Candidates.Final20261021.Probability.posterior_mass"
        (List.ofFn (fun w : Fin n => (event w, ⟨post.mass w⟩))))
  else ⟨quiet s (.rejected .unsupported), probabilitySource prior likelihood⟩


def CausalInput.supported {n k : Nat} (x : CausalInput n k) : Bool :=
  decide (∀ i, x.mass.mass i ≠ 0 →
    ∀ a, (x.assignment i).mass a ≠ 0 ∧ x.recording i a ≠ 0)

def CausalInput.recovered {n k : Nat} (x : CausalInput n k) (a : Bool) : ℚ :=
  Native.Causal.selectionRecoveryValue x.mass.mass (fun i => (x.latent i).mass)
    (fun i => (x.assignment i).mass) x.recording x.response a

def causalSource {n k : Nat} (x : CausalInput n k) : Native.Result ℚ :=
  if x.supported then .known (x.recovered true - x.recovered false)
  else .unknown .notIdentified

def containsAtom (target : Atom) : Formula → Bool
  | .atom a => a == target
  | .both a b | .either a b => containsAtom target a || containsAtom target b
  | .neg a => containsAtom target a

def causalClauseAllowed (s : Situation) (p : CausalPermit) : Bool :=
  s.causalClauses.any (fun clause =>
    clause.source.id == p.source.id && clause.source.version == p.source.version &&
    clause.scope == p.scope && clause.statistic == p.statistic && clause.element.scope == p.scope &&
    s.core.state.N.rules.any (fun law => law.source.id == clause.source.id &&
      law.source.version == clause.source.version && law.scope == clause.scope &&
      containsAtom clause.element law.guard))

def consumeCausal {n k : Nat} (s : Situation) (c : EngineContext)
    (x : CausalInput n k) (permit : Option CausalPermit) :
    NativeReply (Native.Result ℚ) :=
  let actual := causalSource x
  match permit with
  | none => ⟨quiet s (.unknown .inputUnchecked), actual⟩
  | some p =>
    if p.scope == c.scope && p.statistic == c.target && registeredNorm s p.source && causalClauseAllowed s p then
      relayNative s actual (fun value =>
        engineOutput s c .causal
          "JurisLean.Candidates.CausalSelection20261027.selected_weight_recovery"
          (⟨value⟩, ⟨value⟩))
    else ⟨quiet s (.unknown .inputUnchecked), actual⟩

def bargainSource {n : Nat} (score : Fin n → ℚ) (permitted : Fin n → Bool)
    (options : List (Fin n)) : Native.Result (Fin n) :=
  match Native.Decision.legalBest score permitted options with
  | none => .unknown .unsupported
  | some selected => .known selected

def consumeBargain {n : Nat} (s : Situation) (c : EngineContext)
    (score : Fin n → ℚ) (permitted : Fin n → Bool) (options : List (Fin n))
    (offer : Fin n → List (Ref .actor × Quantity .money)) :
    NativeReply (Native.Result (Fin n)) :=
  relayNative s (bargainSource score permitted options) (fun selected =>
    engineOutput s c .bargain
      "JurisLean.Candidates.Final20261021.Decision.legal_best_sound" (offer selected))

private instance (s : Native.Cash.State) : Decidable (Native.Cash.Conserves s) := by
  unfold JurisLean.Candidates.Final20261021.Ledger.Conserves
  infer_instance

private instance (s : Native.Cash.State) : Decidable (Native.Cash.CashConsistent s) := by
  unfold JurisLean.Candidates.Final20261021.Ledger.CashConsistent
  infer_instance

def cashSource (before : Native.Cash.State) (payment : Native.PaymentPayload) :
    Native.Result Native.Cash.State :=
  if Native.Cash.Conserves before ∧ Native.Cash.CashConsistent before ∧
      0 ≤ payment.amount.value ∧ payment.amount.tag = before.debt.amount.tag then
    .known (Native.Cash.performance before payment)
  else .rejected .stateConservationMismatch

def consumeCash (s : Situation) (c : EngineContext) (before : Native.Cash.State)
    (payment : Native.PaymentPayload) : NativeReply (Native.Result Native.Cash.State) :=
  relayNative s (cashSource before payment) (fun after =>
    engineOutput s c .cash
      "JurisLean.Candidates.Final20261021.Ledger.u09_1_quantity_conservation"
      [(⟨before.debt.relation.value⟩, ⟨after.allocated - before.allocated⟩)])

/- Native retains the actual typed expression and its currency/unit metadata;
   the legal view only adds a declared quantity-unit projection. -/
def exactUnitMatches (unit : UnitKind) : Option Native.AmountTag → Bool
  | none => unit == .scalar
  | some tag =>
    match unit with
    | .money => !tag.currency.isEmpty && (tag.unit == "yuan" || tag.unit == "money")
    | .day => tag.currency.isEmpty && tag.unit == "day"
    | .count => tag.currency.isEmpty && tag.unit == "count"
    | .information => tag.currency.isEmpty && tag.unit == "bit"
    | .scalar => tag.currency.isEmpty && tag.unit == "scalar"

def consumeExact (s : Situation) (c : EngineContext) (unit : UnitKind)
    (left right : Native.Decision.TypedValue) :
    NativeReply (Native.Result Native.Decision.TypedValue) :=
  if exactUnitMatches unit left.dimension then
    relayNative s (Native.Decision.addValues left right) (fun actual =>
      engineOutput s c .exact
      "JurisLean.Candidates.Final20261021.Decision.u06_3_eval_unique"
        ⟨unit, ⟨Native.Decision.evalExact actual.expr⟩⟩)
  else ⟨quiet s (.rejected .unsupported), Native.Decision.addValues left right⟩

def behaviorSource (threshold : ℚ) : Native.Result (Fin 3) :=
  if 0 < threshold ∧ threshold ≤ 1 then
    match Native.Decision.best (Native.Response.preparationUtility threshold) [0, 1, 2] with
    | none => .unknown .unsupported
    | some a => .known a
  else .rejected .unsupported

def consumeBehavior (s : Situation) (c : EngineContext) (threshold : ℚ)
    (actor : Ref .actor) (actionQuery : Fin 3 → Ref .query) :
    NativeReply (Native.Result (Fin 3)) :=
  relayNative s (behaviorSource threshold) (fun selected =>
    engineOutput s c .behave
      "JurisLean.Candidates.PolicyResponse20261027.finite_response_payoffs"
      [(actor, actionQuery selected)])

/- The complete adaptive outcome (assessment, load, actual post, replay/key
   conflict) is retained. References here name the proposal; they are never used
   as proofs that tables or actual Loaded objects are equal. -/
def consumeRSI {m : Nat} (s : Situation) (c : EngineContext)
    (before : Native.RSI.RoundState m) (request : Native.RSI.RoundRequest m)
    (samples : List (Native.RSI.SamplingReceipt m)) (permits : List (Native.RSI.LoadPermit m))
    (proposal : Ref .model) : NativeReply (Native.RSI.RoundOutcome m) :=
  let actual := Native.RSI.finishAdaptiveRound before request samples permits
  let legal :=
    match actual.status with
    | .evaluated | .replayed =>
      let output := engineOutput s c .rsi
        "JurisLean.Candidates.AdaptiveRoundLedger20261027.finish_round_preserves_budget"
        (s.core.state.A.model, proposal)
      ⟨(Law.proposeEngine s output).after, .success output⟩
    | .keyConflict => quiet s (.conflict .competentReview)
    | _ => quiet s (.unknown .inputUnchecked)
  ⟨legal, actual⟩

/- Connection obligations: the predicates below concern the native value
   returned by the actual consumer, and reuse the accepted source theorem. -/
theorem fit_uses_actual_sample {m n : Nat} {Y : Type} (s : Situation) (c : EngineContext)
    (protocol : Native.Fit.LearningProtocol) (loss : ℚ → Y → ℚ)
    (models : List (List ℚ)) (data : Fin n → Fin m × Y)
    (out : Native.Fit.FittedTable)
    (h : (consumeFit s c protocol loss models data).native = .known out) :
    out.protocol = protocol ∧ out.sampleSize = n ∧ out.table.length = m ∧ out.table ∈ models ∧
      out.empiricalRisk = JurisLean.Candidates.LearningERM20261027.empiricalScore
        (Native.Fit.tableLoss loss) data out.table ∧
      ∀ table ∈ models,
        JurisLean.Candidates.LearningERM20261027.empiricalScore
          (Native.Fit.tableLoss loss) data out.table ≤
        JurisLean.Candidates.LearningERM20261027.empiricalScore
          (Native.Fit.tableLoss loss) data table :=
  Native.Fit.u01_6_fit_card_minimizes_actual_sample protocol loss models data out h

theorem probability_uses_actual_posterior {n : Nat} (s : Situation) (c : EngineContext)
    (prior : Native.Prob.FiniteLaw (Fin n)) (likelihood : Fin n → ℚ)
    (event : Fin n → Ref .event) (post : Native.Prob.FiniteLaw (Fin n))
    (h : (consumeProb s c prior likelihood event).native = .known post) :
    ∀ w, post.mass w = prior.mass w * likelihood w / Native.Prob.expectation prior likelihood := by
  have hn : (consumeProb s c prior likelihood event).native = probabilitySource prior likelihood := by
    unfold consumeProb
    split <;> rfl
  rw [hn] at h
  unfold probabilitySource at h
  cases hs : Native.Prob.proposed_probability_model prior likelihood with
  | none => simp [hs] at h
  | some out =>
    rw [hs] at h
    cases h
    exact Native.Prob.posterior_mass prior likelihood post hs

theorem causal_actual_identified_value {n k : Nat} (x : CausalInput n k)
    (h : x.supported = true) :
    x.recovered true - x.recovered false =
      Native.Causal.interventionValue x.mass.mass (fun i => (x.latent i).mass) x.response true -
      Native.Causal.interventionValue x.mass.mass (fun i => (x.latent i).mass) x.response false := by
  have hs : ∀ i, x.mass.mass i ≠ 0 →
      ∀ a, (x.assignment i).mass a ≠ 0 ∧ x.recording i a ≠ 0 := by
    simpa [CausalInput.supported] using h
  unfold CausalInput.recovered
  rw [Native.Causal.selected_weight_recovery _ _ _ _ _ true (fun i hi => hs i hi true),
    Native.Causal.selected_weight_recovery _ _ _ _ _ false (fun i hi => hs i hi false)]

theorem causal_no_legal_permit {n k : Nat} (s : Situation) (c : EngineContext)
    (x : CausalInput n k) :
    (consumeCausal s c x none).legal.answer = .unknown .inputUnchecked := rfl

theorem bargain_actual_allowed_maximum {n : Nat} (s : Situation) (c : EngineContext)
    (score : Fin n → ℚ) (permitted : Fin n → Bool) (options : List (Fin n))
    (offer : Fin n → List (Ref .actor × Quantity .money)) (a : Fin n)
    (h : (consumeBargain s c score permitted options offer).native = .known a) :
    a ∈ options ∧ permitted a = true ∧
      ∀ b ∈ options, permitted b = true → score b ≤ score a := by
  change bargainSource score permitted options = .known a at h
  unfold bargainSource at h
  cases hs : Native.Decision.legalBest score permitted options with
  | none => simp [hs] at h
  | some out =>
    rw [hs] at h
    cases h
    exact Native.Decision.legal_best_sound score permitted options a hs

theorem cash_actual_post_conserves (s : Situation) (c : EngineContext)
    (before : Native.Cash.State) (payment : Native.PaymentPayload) (out : Native.Cash.State)
    (h : (consumeCash s c before payment).native = .known out) :
    Native.Cash.Conserves out ∧ Native.Cash.CashConsistent out := by
  change cashSource before payment = .known out at h
  unfold cashSource at h
  split at h
  · rename_i valid
    cases h
    exact ⟨Native.Cash.u09_1_quantity_conservation before payment valid.1 valid.2.2.1,
      Native.Cash.performance_cash_consistent before payment valid.2.1⟩
  · cases h

theorem exact_native_meaning (out : Native.Decision.TypedValue) :
    Native.Decision.Evaluates out.expr (Native.Decision.evalExact out.expr) :=
  Native.Decision.u06_3_eval_exists out.expr

theorem behavior_model_does_not_filter_illegal_action (threshold : ℚ)
    (h0 : 0 < threshold) (h1 : threshold ≤ 1) :
    ∀ b : Fin 3, b ≠ 2 →
      Native.Response.preparationUtility threshold b <
        Native.Response.preparationUtility threshold 2 :=
  (Native.Response.finite_response_payoffs threshold h0 h1).2.2.2

theorem rsi_actual_post_budget {m : Nat} (s : Situation) (c : EngineContext)
    (before : Native.RSI.RoundState m) (request : Native.RSI.RoundRequest m)
    (samples : List (Native.RSI.SamplingReceipt m)) (permits : List (Native.RSI.LoadPermit m))
    (proposal : Ref .model) (h : Native.RSI.roundSpent before ≤ before.limit) :
    Native.RSI.roundSpent (consumeRSI s c before request samples permits proposal).native.post ≤
      before.limit :=
  Native.RSI.finish_round_preserves_budget before request samples permits h

#print axioms relay_is_candidate_only
#print axioms fit_uses_actual_sample
#print axioms probability_uses_actual_posterior
#print axioms causal_actual_identified_value
#print axioms causal_no_legal_permit
#print axioms bargain_actual_allowed_maximum
#print axioms cash_actual_post_conserves
#print axioms exact_native_meaning
#print axioms behavior_model_does_not_filter_illegal_action
#print axioms rsi_actual_post_budget
end JurisLean.CN.Completion20261105

