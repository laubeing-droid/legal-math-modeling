import JurisLean.Candidates.SourceAction20261027
import JurisLean.Candidates.U00MeasuredRSIEntry20261031

noncomputable section

namespace JurisLean.Candidates.U00SourcePersonalEpisode20261031

open JurisLean.Candidates.Final20261021
open JurisLean.Candidates.SourceCompilation20261027
open JurisLean.Candidates.SourceOpening20261027
open JurisLean.Candidates.SourceAction20261027
open JurisLean.Candidates.LearningConsumer20261027
open JurisLean.Candidates.EventFeedbackConsumer20261027
open JurisLean.Candidates.ProtectedFeedback20261027
open JurisLean.Candidates.AdaptiveRoundLedger20261027
open JurisLean.Candidates.LoadedLegalConsumer20261027
open JurisLean.Candidates.LegalActionDomain20261027
open JurisLean.Candidates.IntervalDecisionConsumer20261027
open JurisLean.Candidates.BusinessFeedbackLoop20261027
open JurisLean.Candidates.U00RSICandidateBridge20261031
open JurisLean.Candidates.U00MeasuredRSIEntry20261031

/-!
U00 section 13: a common financial opening need not give equal decoded
features. All retained branches must pass the actual common-query gate.
The fixed versioned extraction is a declared external task interpretation;
feature equality is not asserted to establish complete semantic compatibility.
-/

def commonQuery {W : Type} {m : Nat} (version : Nat)
    (encode : ConsumedView → Fin m) (opening : SharedOpening W)
    (protocol : LearningProtocol) : Result (Fin m) :=
  if version ≠ protocol.fit.featureVersion then .unknown .targetMismatch
  else
    let query := encode opening.anchor.frame.source.decoded
    if opening.branches.all
        (fun branch => decide (encode branch.frame.source.decoded = query)) then
      .known query
    else .unknown .incompatibleFiber

/-- The query is accepted only after every retained branch has been checked,
rather than choosing one interpretation or assuming their features agree. -/
theorem accepted_query_checks_every_retained_branch {W : Type} {m : Nat}
    (version : Nat) (encode : ConsumedView → Fin m) (opening : SharedOpening W)
    (protocol : LearningProtocol) (query : Fin m)
    (known : commonQuery version encode opening protocol = .known query) :
    version = protocol.fit.featureVersion ∧
      query = encode opening.anchor.frame.source.decoded ∧
      ∀ branch ∈ opening.branches, encode branch.frame.source.decoded = query := by
  unfold commonQuery at known
  split at known
  · cases known
  · rename_i matchingVersion
    dsimp only at known
    split at known
    · rename_i common
      cases known
      refine ⟨?_, rfl, ?_⟩
      · simpa only [not_not] using matchingVersion
      · intro branch member
        exact of_decide_eq_true (List.all_eq_true.mp common branch member)
    · cases known

def querySettings {W : Type} {m : Nat} (settings : ActionSettings W m)
    (query : Fin m) : ActionSettings W m :=
  { settings with request := { settings.request with query := query } }

def queryMeasurement {m : Nat} (measurement : MeasurementInput m)
    (query : Fin m) : MeasurementInput m :=
  { measurement with treatment := { measurement.treatment with feature := query } }

structure PersonalSourceEpisode (W : Type) (m : Nat) where
  opening : SharedOpening W
  query : Fin m
  initial : State m
  action : ActionOutput W m
  continuation : PersonalContinuation m

/-- No old episode continuation is executed. The catalogs are retained exactly;
the old consumers refuse a feature-adjusted treatment absent from its catalog. -/
def runPersonalSource {W : Type} {m : Nat}
    (legal : LegalInput W) (learning : RoundState m)
    (version : Nat) (encode : ConsumedView → Fin m) (settings : ActionSettings W m)
    (measurement : MeasurementInput m) (policy : PolicyInput m) (before : RSI.State)
    (evidence : SourceRef) (request : RSI.PredictionRequest) (now : Instant)
    (meanings : List (LogMeaning m)) (plan : ValidationPlan) :
    Result (PersonalSourceEpisode W m) :=
  match openingFor legal with
  | .known opening =>
      match commonQuery version encode opening settings.request.protocol with
      | .known query =>
          let rows := planResults opening settings.plans
          match initialState opening learning with
          | .known initial =>
              let action := act initial (actionInput legal (querySettings settings query) rows)
              .known ⟨opening, query, initial, action,
                continuePersonalBusiness action.post before query evidence
                  (queryMeasurement measurement query) policy request now meanings plan⟩
          | .unknown e => .unknown e
          | .rejected e => .rejected e
          | .conflict a b => .conflict a b
      | .unknown e => .unknown e
      | .rejected e => .rejected e
      | .conflict a b => .conflict a b
  | .unknown e => .unknown e
  | .rejected e => .rejected e
  | .conflict a b => .conflict a b

/-- The actual wrapper consumes the real common opening, executes act once,
and passes that act's actual post to the personal continuation with one query.
No catalog is rewritten to make a changed feature acceptable. -/
theorem actual_source_head_enters_personal_continuation {W : Type} {m : Nat}
    (legal : LegalInput W) (learning : RoundState m)
    (version : Nat) (encode : ConsumedView → Fin m) (settings : ActionSettings W m)
    (measurement : MeasurementInput m) (policy : PolicyInput m) (before : RSI.State)
    (evidence : SourceRef) (request : RSI.PredictionRequest) (now : Instant)
    (meanings : List (LogMeaning m)) (plan : ValidationPlan)
    (out : PersonalSourceEpisode W m)
    (known : runPersonalSource legal learning version encode settings measurement policy before
      evidence request now meanings plan = .known out) :
    openingFor legal = .known out.opening ∧
      commonQuery version encode out.opening settings.request.protocol = .known out.query ∧
      initialState out.opening learning = .known out.initial ∧
      out.action = act out.initial
        (actionInput legal (querySettings settings out.query)
          (planResults out.opening settings.plans)) ∧
      out.continuation = continuePersonalBusiness out.action.post before out.query evidence
        (queryMeasurement measurement out.query) policy request now meanings plan ∧
      (queryMeasurement measurement out.query).treatment.feature = out.query ∧
      (queryMeasurement measurement out.query).treatments = measurement.treatments ∧
      (queryMeasurement measurement out.query).sources = measurement.sources := by
  cases opened : openingFor legal with
  | unknown e => simp [runPersonalSource, opened] at known
  | rejected e => simp [runPersonalSource, opened] at known
  | conflict a b => simp [runPersonalSource, opened] at known
  | known opening =>
      cases queried : commonQuery version encode opening settings.request.protocol with
      | unknown e => simp [runPersonalSource, opened, queried] at known
      | rejected e => simp [runPersonalSource, opened, queried] at known
      | conflict a b => simp [runPersonalSource, opened, queried] at known
      | known query =>
          cases initialized : initialState opening learning with
          | unknown e => simp [runPersonalSource, opened, queried, initialized] at known
          | rejected e => simp [runPersonalSource, opened, queried, initialized] at known
          | conflict a b => simp [runPersonalSource, opened, queried, initialized] at known
          | known initial =>
              simp only [runPersonalSource, opened, queried, initialized,
                Result.known.injEq] at known
              subst out
              exact ⟨rfl, queried, initialized, rfl, rfl, rfl, rfl, rfl⟩

/-- The first chosen payment plan reuses the old source/quote/legal-validation
proof. The old episode occurs only in this proof reference, not in the wrapper.
Its action projection is definitionally the one actual act above. -/
theorem selected_personal_source_plan_reuses_actual_source_validation
    {W : Type} {m : Nat} (legal : LegalInput W) (learning : RoundState m)
    (version : Nat) (encode : ConsumedView → Fin m) (settings : ActionSettings W m)
    (measurement : MeasurementInput m) (policy : PolicyInput m) (before : RSI.State)
    (evidence : SourceRef) (request : RSI.PredictionRequest) (now : Instant)
    (meanings : List (LogMeaning m)) (plan : ValidationPlan)
    (out : PersonalSourceEpisode W m) (actual : LoadedRun W m) (proposal : Proposal)
    (feedback : FeedbackInput m)
    (known : runPersonalSource legal learning version encode settings measurement policy before
      evidence request now meanings plan = .known out)
    (called : out.action.run = some actual)
    (chosen : actual.execution.proposal = some proposal) :
    ∃ spec ∈ settings.plans, bindPlan out.opening spec = .known proposal ∧
      ∃ branches, legal.inspect = .known branches ∧
        accepts settings.model legal.truth out.opening.handle legal.anchor.gamma
          branches proposal = true := by
  have connected := actual_source_head_enters_personal_continuation legal learning version
    encode settings measurement policy before evidence request now meanings plan out known
  let reference : SourceAction20261027.Completed W m :=
    ⟨out.opening, planResults out.opening settings.plans, out.initial,
      episode out.initial
        (actionInput legal (querySettings settings out.query)
          (planResults out.opening settings.plans))
        (queryMeasurement measurement out.query) policy feedback⟩
  have completed :
      (SourceAction20261027.run legal learning (querySettings settings out.query)
        (queryMeasurement measurement out.query) policy feedback).outcome = .known reference := by
    simp only [SourceAction20261027.run, connected.1, connected.2.2.1,
      querySettings, reference]
  have referenceCalled : reference.episode.action.run = some actual := by
    change (act out.initial
      (actionInput legal (querySettings settings out.query)
        (planResults out.opening settings.plans))).run = some actual
    rw [← connected.2.2.2.1]
    exact called
  simpa only [querySettings, reference] using
    (selected_source_plan_has_actual_spec_and_legal_validation legal learning
      (querySettings settings out.query) (queryMeasurement measurement out.query)
      policy feedback reference actual proposal completed referenceCalled chosen)

end JurisLean.Candidates.U00SourcePersonalEpisode20261031
