import JurisLean.Candidates.PolicyEvaluation20261027
import JurisLean.External.GameTheory.Math.Probability
import Mathlib.Probability.ProbabilityMassFunction.Integrals

open scoped BigOperators

namespace JurisLean.Candidates.U12_3MARSequential20261030

open MeasureTheory
open JurisLean.Candidates.Final20261021
open JurisLean.Candidates.PolicyEvaluation20261027

/-! CI_NOT_RUN. Finite MAR and finite-horizon sequential bridges only.
The conditional kernels and recording probabilities must describe the actual
frozen data-generating mechanism; SourceRef agreement does not prove this.
-/

/-- The finite probability adapter is used to construct the actual kernels;
normalization is proved before any IPW conclusion is used. -/
private noncomputable def rationalFinitePMF
    {B : Type*} [Fintype B] (w : B → ℚ)
    (nonnegative : ∀ b, 0 ≤ w b) (normalized : ∑ b, w b = 1) : PMF B := by
  have realNonnegative (b : B) : (0 : ℝ) ≤ (w b : ℝ) := by
    exact_mod_cast nonnegative b
  have realNormalized : (∑ b, (w b : ℝ)) = 1 := by
    exact_mod_cast normalized
  exact PMF.ofFintype (fun b => ENNReal.ofReal (w b : ℝ)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun b _ => realNonnegative b),
      realNormalized]
    exact ENNReal.ofReal_one)

private theorem rationalFinitePMF_mass
    {B : Type*} [Fintype B] (w : B → ℚ)
    (nonnegative : ∀ b, 0 ≤ w b) (normalized : ∑ b, w b = 1) (b : B) :
    ((rationalFinitePMF w nonnegative normalized) b).toReal = (w b : ℝ) := by
  change (ENNReal.ofReal (w b : ℝ)).toReal = _
  exact ENNReal.toReal_ofReal (by exact_mod_cast nonnegative b)

private theorem rationalFinitePMF_expect
    {B : Type*} [Fintype B] (w : B → ℚ)
    (nonnegative : ∀ b, 0 ≤ w b) (normalized : ∑ b, w b = 1) (f : B → ℚ) :
    Math.Probability.expect (rationalFinitePMF w nonnegative normalized)
        (fun b => (f b : ℝ)) = ((∑ b, w b * f b : ℚ) : ℝ) := by
  rw [Math.Probability.expect_eq_sum]
  simp only [rationalFinitePMF_mass]
  push_cast <;> rfl

/-- U12.3 MAR blocker: R has its own actual conditional probability kernel. -/
def recordingMass (p : ℚ) (r : Bool) : ℚ := if r then p else 1 - p

private noncomputable def recordingPMF (p : ℚ) (hp : 0 ≤ p) (hp1 : p ≤ 1) : PMF Bool :=
  rationalFinitePMF (recordingMass p)
    (by
      intro r
      cases r
      · simpa [recordingMass] using sub_nonneg.mpr hp1
      · simpa [recordingMass] using hp)
    (by simp [recordingMass, Fintype.sum_bool] <;> ring)

/-- U12.3 MAR blocker: for a normalized conditional atom table given X,A,
this is the finite factorization definition of independence of outcome and R.
It is not the weighted moment identity to be proved. -/
def finiteMARRow {Y : Type*} [Fintype Y] (joint : Y → Bool → ℚ) : Prop :=
  ∀ y r, joint y r = (∑ r', joint y r') * (∑ y', joint y' r)

/-- U12.3 MAR blocker: the original conditional independence premise identifies
the recording kernel through its marginal, rather than assuming a corrected mean. -/
theorem finiteMARRow_factorization
    {Y : Type*} [Fintype Y] (joint : Y → Bool → ℚ)
    (normalized : (∑ y, ∑ r, joint y r) = 1)
    (independent : finiteMARRow joint) (y : Y) (r : Bool) :
    joint y r = (∑ r', joint y r') * recordingMass (∑ y', joint y' true) r := by
  have recordingTotal : (∑ y', joint y' false) + (∑ y', joint y' true) = 1 := by
    simpa only [Fintype.sum_bool, Finset.sum_add_distrib, add_comm]
      using normalized
  rw [independent y r]
  cases r
  · simp only [recordingMass, Bool.false_eq_true, ↓reduceIte]
    congr 1
    linarith
  · rfl

abbrev MARWorld (X A Y : Type*) := X × A × Y × Bool
abbrev MARVisible (X A Y : Type*) := X × A × Option Y

/-- U12.3 MAR blocker: the observable report keeps R=false as None;
it never reads an unrecorded outcome or silently drops that case. -/
def marReport {X A Y : Type*} (z : MARWorld X A Y) : MARVisible X A Y :=
  (z.1, z.2.1, if z.2.2.2 then some z.2.2.1 else none)

noncomputable def marVisibleLaw {X A Y : Type*}
    (joint : PMF (MARWorld X A Y)) : PMF (MARVisible X A Y) :=
  joint.bind (fun z => PMF.pure (marReport z))

/-- U12.3 MAR blocker: the corrected score is a function of X,A,Option Y,
with the joint assignment/recording weight; None contributes zero. -/
def marVisibleScore {X A Y : Type*}
    (logging target recording : X → A → ℚ) (reward : Y → ℚ)
    (z : MARVisible X A Y) : ℚ :=
  (target z.1 z.2.1 / logging z.1 z.2.1) *
    match z.2.2 with
    | none => 0
    | some y => reward y / recording z.1 z.2.1

/-- U12.3 MAR blocker: eliminate the actual recording draw under positive
recording probability on target-supported actions. -/
theorem recording_weight_elimination (mu pi rho value : ℚ)
    (support : pi ≠ 0 → mu ≠ 0)
    (recordingSupport : pi ≠ 0 → rho ≠ 0) :
    (∑ r : Bool, recordingMass rho r *
      ((pi / mu) * (if r then value / rho else 0))) = (pi / mu) * value := by
  by_cases zero : pi = 0
  · simp [zero]
  · have hm := support zero
    have hr := recordingSupport zero
    simp [recordingMass, Fintype.sum_bool]
    field_simp [hm, hr] <;> ring

section MARModel

variable {X A Y : Type} [Fintype X] [Fintype A] [Fintype Y]
variable (mass : X → ℚ) (massNonnegative : ∀ x, 0 ≤ mass x)
  (massNormalized : ∑ x, mass x = 1)
variable (logging : X → A → ℚ) (loggingNonnegative : ∀ x a, 0 ≤ logging x a)
  (loggingNormalized : ∀ x, ∑ a, logging x a = 1)
variable (response : X → A → Y → ℚ)
  (responseNonnegative : ∀ x a y, 0 ≤ response x a y)
  (responseNormalized : ∀ x a, ∑ y, response x a y = 1)
variable (recording : X → A → ℚ) (recordingNonnegative : ∀ x a, 0 ≤ recording x a)
  (recordingBelowOne : ∀ x a, recording x a ≤ 1)

/-- U12.3 MAR blocker: generate a real full-data PMF from the frozen context,
assignment, response and recording kernels. The R kernel does not read Y,
which realizes the conditional independence premise. -/
noncomputable def marWorldLaw : PMF (MARWorld X A Y) :=
  (rationalFinitePMF mass massNonnegative massNormalized).bind (fun x =>
    (rationalFinitePMF (logging x) (loggingNonnegative x)
      (loggingNormalized x)).bind (fun a =>
      (rationalFinitePMF (response x a) (responseNonnegative x a)
        (responseNormalized x a)).bind (fun y =>
        (recordingPMF (recording x a) (recordingNonnegative x a)
          (recordingBelowOne x a)).bind (fun r => PMF.pure (x, a, y, r)))))

include responseNormalized in
/-- U12.3 MAR blocker: verify the generated conditional row really satisfies
finite conditional independence, rather than relabeling a desired weighted mean. -/
theorem mar_generated_row_independent (x : X) (a : A) :
    finiteMARRow (fun y r => response x a y * recordingMass (recording x a) r) := by
  have recordingTotal : (∑ r : Bool, recordingMass (recording x a) r) = 1 := by
    simp [recordingMass, Fintype.sum_bool] <;> ring
  intro y r
  have marginalY : (∑ r', response x a y * recordingMass (recording x a) r') =
      response x a y := by
    rw [← Finset.mul_sum, recordingTotal, mul_one]
  have marginalR : (∑ y', response x a y' * recordingMass (recording x a) r) =
      recordingMass (recording x a) r := by
    rw [← Finset.sum_mul, responseNormalized x a, one_mul]
  rw [marginalY, marginalR]

/-- U12.3 MAR blocker: after recording cancellation, use the already-proved
finite assignment IPW identity; do not reprove assignment-weight cancellation. -/
theorem mar_weighted_sum
    (target : X → A → ℚ) (reward : Y → ℚ)
    (support : ∀ x a, target x a ≠ 0 → logging x a ≠ 0)
    (recordingSupport : ∀ x a, target x a ≠ 0 → recording x a ≠ 0) :
    (∑ x, mass x * ∑ a, logging x a * ∑ y, response x a y *
      ∑ r : Bool, recordingMass (recording x a) r *
        marVisibleScore logging target recording reward (marReport (x, a, y, r))) =
      policyValue mass target (fun x a => ∑ y, response x a y * reward y) := by
  have eliminate (x : X) (a : A) (y : Y) :
      (∑ r : Bool, recordingMass (recording x a) r *
        marVisibleScore logging target recording reward (marReport (x, a, y, r))) =
      (target x a / logging x a) * reward y := by
    simpa [marVisibleScore, marReport, Fintype.sum_bool] using
      recording_weight_elimination (logging x a) (target x a)
        (recording x a) (reward y) (support x a) (recordingSupport x a)
  calc
    _ = importanceValue mass logging target (fun x a => ∑ y, response x a y * reward y) := by
      simp_rw [eliminate]
      unfold importanceValue
      apply Finset.sum_congr rfl
      intro x _
      congr 1
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro y _
      ring
    _ = _ := finite_policy_ipw mass logging target
      (fun x a => ∑ y, response x a y * reward y) support

/-- U12.3 MAR blocker: the exact corrected mean is computed under the real
visible law induced by the generated full-data law, including None records. -/
theorem mar_visible_score_expectation
    (target : X → A → ℚ) (reward : Y → ℚ)
    (support : ∀ x a, target x a ≠ 0 → logging x a ≠ 0)
    (recordingSupport : ∀ x a, target x a ≠ 0 → recording x a ≠ 0) :
    Math.Probability.expect
      (marVisibleLaw (marWorldLaw mass massNonnegative massNormalized
        logging loggingNonnegative loggingNormalized response responseNonnegative
        responseNormalized recording recordingNonnegative recordingBelowOne))
      (fun z => (marVisibleScore logging target recording reward z : ℝ)) =
      (policyValue mass target (fun x a => ∑ y, response x a y * reward y) : ℝ) := by
  simp only [marVisibleLaw, marWorldLaw, recordingPMF,
    Math.Probability.expect_bind, Math.Probability.expect_pure]
  simp_rw [rationalFinitePMF_expect]
  exact congrArg (fun q : ℚ => (q : ℝ))
    (mar_weighted_sum mass logging response recording target reward support recordingSupport)

/-- U12.3 MAR blocker: expose integrability and the measure-integral form
needed by policy-value statements, without assuming a corrected expectation. -/
theorem mar_visible_score_integral
    [MeasurableSpace (MARVisible X A Y)]
    [MeasurableSingletonClass (MARVisible X A Y)]
    (target : X → A → ℚ) (reward : Y → ℚ)
    (support : ∀ x a, target x a ≠ 0 → logging x a ≠ 0)
    (recordingSupport : ∀ x a, target x a ≠ 0 → recording x a ≠ 0) :
    let visible := marVisibleLaw (marWorldLaw mass massNonnegative massNormalized
      logging loggingNonnegative loggingNormalized response responseNonnegative
      responseNormalized recording recordingNonnegative recordingBelowOne)
    Integrable (fun z => (marVisibleScore logging target recording reward z : ℝ))
        visible.toMeasure ∧
      (∫ z, (marVisibleScore logging target recording reward z : ℝ) ∂visible.toMeasure) =
        (policyValue mass target (fun x a => ∑ y, response x a y * reward y) : ℝ) := by
  refine ⟨.of_finite, ?_⟩
  rw [PMF.integral_eq_sum]
  have mean := mar_visible_score_expectation mass massNonnegative massNormalized
    logging loggingNonnegative loggingNormalized response responseNonnegative
    responseNormalized recording recordingNonnegative recordingBelowOne
    target reward support recordingSupport
  rw [Math.Probability.expect_eq_sum] at mean
  simpa only [smul_eq_mul] using mean

end MARModel

/-- U12.3 MAR blocker: connect the observable Option score to the original
joint assignment/recording weight pi * R * Y / (mu * rho), including R=false. -/
theorem mar_reported_score_joint_weight
    {X A Y : Type*} (logging target recording : X → A → ℚ)
    (reward : Y → ℚ) (x : X) (a : A) (y : Y) (r : Bool) :
    marVisibleScore logging target recording reward (marReport (x, a, y, r)) =
      target x a * Behavior.indicator r * reward y /
        (logging x a * recording x a) := by
  cases r <;>
    by_cases hmu : logging x a = 0 <;>
    by_cases hrho : recording x a = 0 <;>
    simp [marVisibleScore, marReport, Behavior.indicator, hmu, hrho] <;>
    field_simp [hmu, hrho] <;> ring

end JurisLean.Candidates.U12_3MARSequential20261030
