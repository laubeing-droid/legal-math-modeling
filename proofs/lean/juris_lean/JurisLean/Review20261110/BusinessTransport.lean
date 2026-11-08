import JurisLean.OriginalModelClosure
import JurisLean.Review20261110.OccurrenceHistory
import JurisLean.Review20261110.ObservationBridge
import JurisLean.Review20261110.InvariantClosure

namespace LegalMath20261110.BusinessTransport

open MeasureTheory ProbabilityTheory

noncomputable section

/-- A concrete command update, a faithful state encoding, and its independently
specified represented update. Random command laws must also be shared. -/
structure TransportData (B C S : Type*) [MeasurableSpace B] [MeasurableSpace C]
    [MeasurableSpace S] where
  sourceStep : B → C → B
  targetStep : S → C → S
  enc : B → S
  decode : S → B
  decode_enc : ∀ b, decode (enc b) = b
  measurable_enc : Measurable enc
  measurable_sourceStep : ∀ b, Measurable (sourceStep b)
  commute : ∀ b c, enc (sourceStep b c) = targetStep (enc b) c

variable {B C S : Type*} [MeasurableSpace B] [MeasurableSpace C] [MeasurableSpace S]

theorem run_transport (D : TransportData B C S) (commands : List C) (b : B) :
    D.enc (commands.foldl D.sourceStep b) = commands.foldl D.targetStep (D.enc b) := by
  induction commands generalizing b with
  | nil => rfl
  | cons c cs ih =>
      simp only [List.foldl_cons]
      rw [ih, D.commute]

theorem invariant_transport (D : TransportData B C S) (I : B → Prop)
    (closed : ∀ b c, I b → I (D.sourceStep b c)) (commands : List C) (b : B) (initial : I b) :
    I (D.decode (commands.foldl D.targetStep (D.enc b))) := by
  rw [← run_transport, D.decode_enc]
  induction commands generalizing b with
  | nil => exact initial
  | cons c cs ih => exact ih (D.sourceStep b c) (closed b c initial)

theorem readout_transport (D : TransportData B C S) {R : Type*}
    (sourceRead : B → R) (targetRead : S → R) (compatible : ∀ b, targetRead (D.enc b) = sourceRead b)
    (commands : List C) (b : B) :
    targetRead (commands.foldl D.targetStep (D.enc b)) = sourceRead (commands.foldl D.sourceStep b) := by
  rw [← run_transport]
  exact compatible _

/-- The same input law is explicit; a pointwise update square alone does not
identify two separately chosen policies. -/
theorem kernel_transport (D : TransportData B C S) (κ : Kernel B C) (b : B) :
    ((κ b).map (D.sourceStep b)).map D.enc =
      (κ (D.decode (D.enc b))).map (D.targetStep (D.enc b)) := by
  rw [D.decode_enc, Measure.map_map D.measurable_enc (D.measurable_sourceStep b)]
  congr 1
  funext c
  exact D.commute b c

theorem transport_theorem (D : TransportData B C S) (κ : Kernel B C) (I : B → Prop)
    (closed : ∀ b c, I b → I (D.sourceStep b c)) (commands : List C) (b : B) (initial : I b) :
    D.enc (commands.foldl D.sourceStep b) = commands.foldl D.targetStep (D.enc b) ∧
    I (D.decode (commands.foldl D.targetStep (D.enc b))) ∧
    ((κ b).map (D.sourceStep b)).map D.enc =
      (κ (D.decode (D.enc b))).map (D.targetStep (D.enc b)) :=
  ⟨run_transport D commands b, invariant_transport D I closed commands b initial, kernel_transport D κ b⟩

open LegalMath20261108.ClosedLoop
open LegalMath20261109.BusinessProcess
open LegalMath20261110.InvariantClosure
open JurisLean.Candidates.Final20261021
open JurisLean.Candidates.AdaptiveRoundLedger20261027
open JurisLean.Candidates.MeasuredPolicy20261027

variable {W : Type} {m k : Nat}

local instance : MeasurableSpace (JurisLean.Candidates.BusinessFeedbackLoop20261027.State m) := ⊤
local instance : MeasurableSpace (RoundState m) := ⊤
local instance : MeasurableSpace (Fin k) := ⊤
local instance : MeasurableSpace (List (Fin k)) := ⊤

/-- The five targets are about the specific full-history lift, not a claim that
arbitrary numeric summaries encode every business invariant. -/
def O1 (initial : JurisLean.Candidates.BusinessFeedbackLoop20261027.State m)
    (catalog : Fin k → JurisLean.Candidates.BusinessFeedbackLoop20261027.Command W m) : Prop :=
  ∀ h, (encode initial catalog h).1 = h ∧
    (encode initial catalog h).2 = (replay initial catalog h).learning

def O2 (initial : JurisLean.Candidates.BusinessFeedbackLoop20261027.State m)
    (catalog : Fin k → JurisLean.Candidates.BusinessFeedbackLoop20261027.Command W m) : Prop :=
  ∀ h a, response initial catalog (encode initial catalog h, a) =
    JurisLean.Candidates.BusinessFeedbackLoop20261027.step (replay initial catalog h) (catalog a)

def O3 (commands : List (JurisLean.Candidates.BusinessFeedbackLoop20261027.Command W m)) : Prop :=
  ∀ initial, replay initial (fun i : Fin commands.length => commands.get i)
    (List.finRange commands.length) = commands.foldl JurisLean.Candidates.BusinessFeedbackLoop20261027.step initial

def O4 (initial : JurisLean.Candidates.BusinessFeedbackLoop20261027.State m)
    (catalog : Fin k → JurisLean.Candidates.BusinessFeedbackLoop20261027.Command W m)
    (pick : List (Fin k) → Fin k) : Prop :=
  ∀ h a, update (model initial catalog pick)
    (encode initial catalog h, (a, JurisLean.Candidates.BusinessFeedbackLoop20261027.step
      (replay initial catalog h) (catalog a))) = encode initial catalog (h ++ [a])

def O5 (initial : JurisLean.Candidates.BusinessFeedbackLoop20261027.State m)
    (catalog : Fin k → JurisLean.Candidates.BusinessFeedbackLoop20261027.Command W m)
    (pick : List (Fin k) → Fin k) : Prop :=
  ∀ h, step (model initial catalog pick) (encode initial catalog h) =
    Measure.dirac (encode initial catalog (h ++ [pick h]))

theorem O1_proved (initial : JurisLean.Candidates.BusinessFeedbackLoop20261027.State m)
    (catalog : Fin k → JurisLean.Candidates.BusinessFeedbackLoop20261027.Command W m) : O1 initial catalog :=
  fun _ => ⟨rfl, rfl⟩

theorem O2_proved (initial : JurisLean.Candidates.BusinessFeedbackLoop20261027.State m)
    (catalog : Fin k → JurisLean.Candidates.BusinessFeedbackLoop20261027.Command W m) : O2 initial catalog :=
  fun _ _ => rfl

theorem O3_proved (commands : List (JurisLean.Candidates.BusinessFeedbackLoop20261027.Command W m)) :
    O3 commands := fun initial => finite_sequence_catalog commands initial

theorem O4_proved (initial : JurisLean.Candidates.BusinessFeedbackLoop20261027.State m)
    (catalog : Fin k → JurisLean.Candidates.BusinessFeedbackLoop20261027.Command W m)
    (pick : List (Fin k) → Fin k) : O4 initial catalog pick := actual_post_commutes initial catalog pick

theorem O5_proved (initial : JurisLean.Candidates.BusinessFeedbackLoop20261027.State m)
    (catalog : Fin k → JurisLean.Candidates.BusinessFeedbackLoop20261027.Command W m)
    (pick : List (Fin k) → Fin k) : O5 initial catalog pick := actual_step_law initial catalog pick

/-- Original observation records, including multiple records for one event,
use their original event identity for counting. -/
theorem original_record_count_once (records : Finset (PolicyObservation m)) (row : PolicyObservation m)
    (seen : row.measured.dictionary.event ∈ records.image (fun r => r.measured.dictionary.event)) :
    OccurrenceHistory.recordCount (fun r : PolicyObservation m => r.measured.dictionary.event) (insert row records) =
      OccurrenceHistory.recordCount (fun r : PolicyObservation m => r.measured.dictionary.event) records :=
  OccurrenceHistory.record_count_once _ records row seen

/-- The observation theorem is consumed by the original prepared-feedback
update, with the actual private learner and actually available observation. -/
theorem original_feedback_no_leak
    (input : JurisLean.Candidates.BusinessFeedbackLoop20261027.FeedbackInput m)
    (x x' : JurisLean.Candidates.BusinessFeedbackLoop20261027.State m × Result (PolicyObservation m))
    (same : (x.1.learning,x.2) = (x'.1.learning,x'.2)) :
    JurisLean.Candidates.BusinessFeedbackLoop20261027.preparedState x.1.learning
      (JurisLean.Candidates.BusinessFeedbackLoop20261027.prepareObserved x.1.learning input x.2) =
    JurisLean.Candidates.BusinessFeedbackLoop20261027.preparedState x'.1.learning
      (JurisLean.Candidates.BusinessFeedbackLoop20261027.prepareObserved x'.1.learning input x'.2) :=
  ObservationBridge.factored_no_leak
    (fun z : JurisLean.Candidates.BusinessFeedbackLoop20261027.State m × Result (PolicyObservation m) => (z.1.learning,z.2))
    (fun z : RoundState m × Result (PolicyObservation m) => JurisLean.Candidates.BusinessFeedbackLoop20261027.preparedState z.1
      (JurisLean.Candidates.BusinessFeedbackLoop20261027.prepareObserved z.1 input z.2)) x x' same

/-- The general path theorem is consumed by the actual original business lift. -/
theorem original_business_legal_path
    (initial : JurisLean.Candidates.BusinessFeedbackLoop20261027.State m)
    (catalog : Fin k → JurisLean.Candidates.BusinessFeedbackLoop20261027.Command W m)
    (pick : List (Fin k) → Fin k)
    (valid : JurisLean.Candidates.BusinessFeedbackLoop20261027.KnownBusinessInvariant initial)
    (bounded : roundSpent initial.learning ≤ initial.learning.limit) :
    ∀ᵐ path ∂pathLaw (model initial catalog pick) (Measure.dirac (encode initial catalog [])),
      ∀ n, legalInvariant initial catalog (path n) := by
  let I : Set (List (Fin k) × RoundState m) := {s | legalInvariant initial catalog s}
  have included : I ⊆ Set.range (encode initial catalog) := by
    intro s hs
    refine ⟨s.1, Prod.ext rfl ?_⟩
    exact hs.2.1.symm
  have hI : MeasurableSet I :=
    ((Set.countable_range (encode initial catalog)).mono included).measurableSet
  have first : Measure.dirac (encode initial catalog []) I = 1 := by
    have good : encode initial catalog [] ∈ I := replay_invariant initial catalog valid bounded []
    simp [Measure.dirac_apply' _ hI, good]
  apply ae_invariant_path (model initial catalog pick) _ I hI first
  intro s hs
  have same : s = encode initial catalog s.1 := Prod.ext rfl hs.2.1
  rw [same]
  have good := actual_law_preserves_invariant initial catalog pick valid bounded s.1
  have zero : step (model initial catalog pick) (encode initial catalog s.1) Iᶜ = 0 :=
    ae_iff.mp good
  have eq := measure_add_measure_compl (μ := step (model initial catalog pick)
    (encode initial catalog s.1)) hI
  simpa only [zero, add_zero, measure_univ] using eq

#print axioms run_transport
#print axioms invariant_transport
#print axioms readout_transport
#print axioms kernel_transport
#print axioms transport_theorem
#print axioms O1_proved
#print axioms O2_proved
#print axioms O3_proved
#print axioms O4_proved
#print axioms O5_proved
#print axioms original_feedback_no_leak
#print axioms original_record_count_once
#print axioms original_business_legal_path

end
end LegalMath20261110.BusinessTransport
