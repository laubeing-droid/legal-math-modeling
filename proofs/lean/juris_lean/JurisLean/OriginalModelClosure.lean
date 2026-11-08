import JurisLean.BusinessProcessRealization
import JurisLean.TrainedDecisionRealization

/-! A single consumer of the four seams. Its numerical snapshot reads the
actual observed label and the currently loaded model. Its training sample is
the original observation history; its chosen finite command still executes
the original business step and retains the original legal invariant. -/

namespace LegalMath20261109.OriginalModel

open MeasureTheory ProbabilityTheory
open LegalMath20261109.BusinessProcess LegalMath20261109.PosteriorLaw
open LegalMath20261109.TrainedDecision
open LegalMath20261108.ClosedLoop
open JurisLean.Candidates.Final20261021
open JurisLean.Candidates.AdaptiveRoundLedger20261027
open JurisLean.Candidates.MeasuredPolicy20261027
open JurisLean.Candidates.ValidatedFeedbackLoad20261027
open JurisLean.Seams.UnifiedPayoffChain JurisLean.Seams.PayoffEquilibrium

noncomputable section

local instance {m : Nat} : MeasurableSpace (JurisLean.Candidates.BusinessFeedbackLoop20261027.State m) := ⊤
local instance {m : Nat} : MeasurableSpace (RoundState m) := ⊤
local instance : MeasurableSpace (Fin 2) := ⊤
local instance : MeasurableSpace (List (Fin 2)) := ⊤


def snapshot {m : Nat} (s : JurisLean.Candidates.BusinessFeedbackLoop20261027.State m)
    (row : PolicyObservation m) (query : Fin m) : ℚ × ℚ :=
  (if row.measured.label then 1 else 0, max 0 (min 1 (predictLoaded s.learning.service query)))

theorem snapshot_bounds {m : Nat} (s : JurisLean.Candidates.BusinessFeedbackLoop20261027.State m)
    (row : PolicyObservation m) (query : Fin m) :
    0 ≤ (snapshot s row query).1 ∧ (snapshot s row query).1 ≤ 1 ∧
      0 ≤ (snapshot s row query).2 ∧ (snapshot s row query).2 ≤ 1 := by
  have hp : 0 ≤ max 0 (min 1 (predictLoaded s.learning.service query)) ∧
      max 0 (min 1 (predictLoaded s.learning.service query)) ≤ (1 : ℚ) :=
    ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩
  cases row.measured.label <;> simp [snapshot, hp]

def recordedData {m : Nat} (s : JurisLean.Candidates.BusinessFeedbackLoop20261027.State m) :
    Fin s.observationHistory.length → Bool :=
  fun i => (s.observationHistory.get i).measured.label

def actionIndex (a : Bool) : Fin 2 := if a then 1 else 0

/-- Closed composition: actual past -> actual fitter -> same-world decision
value -> the chosen original command -> the original legal invariant. -/
theorem joint_realization {W : Type} {m : Nat}
    (initial : JurisLean.Candidates.BusinessFeedbackLoop20261027.State m)
    (catalog : Fin 2 → JurisLean.Candidates.BusinessFeedbackLoop20261027.Command W m)
    (h : List (Fin 2)) (row : PolicyObservation m) (query : Fin m)
    (observed : (replay initial catalog h).lastObservation = .known row)
    (valid : JurisLean.Candidates.BusinessFeedbackLoop20261027.KnownBusinessInvariant initial)
    (bounded : roundSpent initial.learning ≤ initial.learning.limit)
    (hn : 0 < (replay initial catalog h).observationHistory.length)
    (first : ℚ × ℚ) (rest : List (ℚ × ℚ))
    (oracle : ideal (snapshot (replay initial catalog h) row query) ∈ first :: rest)
    (flows : Bool → Bool → PayFlow) (role : Role) :
    let current := replay initial catalog h
    let numeric := snapshot current row query
    let q := forecast (fitted first rest (recordedData current))
    let chosen := greedy q flows role
    let E := Real.sqrt (2*realizedRadius numeric first rest (recordedData current))
    let C := cashSensitivity flows role
    let pick := fun _ : List (Fin 2) => actionIndex chosen
    current.lastObservation = .known row ∧
    (∀ a,
      (∑ y : Bool, reward flows role a y * ((∑ w, ∑ mt, xi numeric (w, mt, y) : ℚ) : ℝ)) ≤
      (∑ y : Bool, reward flows role chosen y * ((∑ w, ∑ mt, xi numeric (w, mt, y) : ℚ) : ℝ)) + 2*C*E) ∧
    step (BusinessProcess.model initial catalog pick) (encode initial catalog h) =
      Measure.dirac (encode initial catalog (h ++ [actionIndex chosen])) ∧
    legalInvariant initial catalog (encode initial catalog (h ++ [actionIndex chosen])) := by
  dsimp only
  let numeric := snapshot (replay initial catalog h) row query
  let data := recordedData (replay initial catalog h)
  let r := realizedRadius numeric first rest data
  let E := Real.sqrt (2*r)
  have nonneg : 0 ≤ r := realizedRadius_nonneg numeric first rest data
  have radius : 2*r ≤ E^2 := by
    dsimp [E]
    rw [Real.sq_sqrt (by positivity)]
  have decision := actual_training_to_legal_decision hn numeric (snapshot_bounds _ row query)
    first rest data oracle r E (cashSensitivity flows role) (Real.sqrt_nonneg _)
    (cashSensitivity_nonneg flows role) radius
    (realizedRadius_uniform numeric first rest data) flows role (cashSensitivity_bounds flows role)
  refine ⟨observed, ?_, actual_step_law _ _ _ _, replay_invariant _ _ valid bounded _⟩
  intro a
  simpa only [actual_payoff_from_same_xi] using decision.2 a

#print axioms snapshot_bounds
#print axioms joint_realization

end
end LegalMath20261109.OriginalModel
