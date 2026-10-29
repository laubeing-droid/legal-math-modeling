import JurisLean.External.GameTheory.Math.Probability
import Mathlib.Probability.ProbabilityMassFunction.Integrals

open scoped BigOperators

namespace JurisLean.Candidates.U12_3SequentialFinite20261030

open MeasureTheory

/-- U12.3 sequential blocker: generate a dependent pair from a genuine
conditional PMF, retaining the sampled prefix in the resulting outcome. -/
private noncomputable def dependentPairPMF
    {B C : Type*} (p : PMF B) (q : B → PMF C) : PMF (B × C) :=
  p.bind (fun b => (q b).bind (fun c => PMF.pure (b, c)))

private theorem dependentPairPMF_apply
    {B C : Type*} (p : PMF B) (q : B → PMF C) (b : B) (c : C) :
    dependentPairPMF p q (b, c) = p b * q b c := by
  classical
  simp only [dependentPairPMF, PMF.bind_apply, PMF.pure_apply, Prod.mk.injEq]
  rw [tsum_eq_single b]
  · simp [mul_ite]
    rw [tsum_eq_single c]
    · simp
    · intro c' different
      simp [Ne.symm different]
  · intro b' different
    simp [Ne.symm different]

/-- U12.3 sequential blocker: a history contains the initial state and every
past action/next-state pair, so policies cannot read a future suffix. -/
def SequentialHistory (S A : Type) : ℕ → Type
  | 0 => S
  | n + 1 => SequentialHistory S A n × A × S

instance sequentialHistoryFintype
    {S A : Type} [Fintype S] [Fintype A] (n : ℕ) :
    Fintype (SequentialHistory S A n) := by
  induction n with
  | zero =>
      change Fintype S
      infer_instance
  | succ n ih =>
      change Fintype (SequentialHistory S A n × A × S)
      letI := ih
      infer_instance

/-- Exactly n conditional action kernels, one for each full prefix length. -/
def SequentialPolicy (S A : Type) : ℕ → Type
  | 0 => PUnit
  | n + 1 => SequentialPolicy S A n × (SequentialHistory S A n → PMF A)

/-- Exactly n shared conditional environment kernels. They may read the full
history; no unproved Markov reduction or stationarity assumption is imposed. -/
def SequentialKernel (S A : Type) : ℕ → Type
  | 0 => PUnit
  | n + 1 => SequentialKernel S A n × (SequentialHistory S A n → A → PMF S)

/-- U12.3 sequential blocker: this is the actual finite trajectory law generated
by initial state, conditional action draws, and conditional next-state draws.
Every extension keeps its whole prefix rather than projecting to the last state. -/
noncomputable def sequentialLaw {S A : Type}
    (initial : PMF S) : (n : ℕ) → SequentialPolicy S A n →
      SequentialKernel S A n → PMF (SequentialHistory S A n)
  | 0, _, _ => initial
  | n + 1, policy, kernel =>
      dependentPairPMF (sequentialLaw initial n policy.1 kernel.1)
        (fun h => dependentPairPMF (policy.2 h) (kernel.2 h))

/-- U12.3 sequential blocker: the generated trajectory mass really factors
through its conditional kernels; this is not an assumed likelihood identity. -/
theorem sequentialLaw_step_mass {S A : Type}
    (initial : PMF S) (n : ℕ) (policy : SequentialPolicy S A (n + 1))
    (kernel : SequentialKernel S A (n + 1))
    (h : SequentialHistory S A n) (a : A) (s : S) :
    ((sequentialLaw initial (n + 1) policy kernel) (h, a, s)).toReal =
      ((sequentialLaw initial n policy.1 kernel.1) h).toReal *
        (policy.2 h a).toReal * (kernel.2 h a s).toReal := by
  change ((dependentPairPMF (sequentialLaw initial n policy.1 kernel.1)
    (fun h => dependentPairPMF (policy.2 h) (kernel.2 h))) (h, (a, s))).toReal = _
  rw [dependentPairPMF_apply, dependentPairPMF_apply,
    ENNReal.toReal_mul, ENNReal.toReal_mul]
  ring

/-- U12.3 sequential blocker: this recursion is the finite product of the
conditional pi/mu ratios along the retained full history, with empty product 1. -/
noncomputable def sequentialRatio {S A : Type} :
    (n : ℕ) → SequentialPolicy S A n → SequentialPolicy S A n →
      SequentialHistory S A n → ℝ
  | 0, _, _, _ => 1
  | n + 1, logging, target, h =>
      sequentialRatio n logging.1 target.1 h.1 *
        ((target.2 h.1 h.2.1).toReal / (logging.2 h.1 h.2.1).toReal)

/-- U12.3 sequential blocker: coverage is checked at every target-reachable
history and every target-positive action, not merely on realized log rows. -/
def sequentialSupported {S A : Type} (initial : PMF S) :
    (n : ℕ) → SequentialPolicy S A n → SequentialPolicy S A n →
      SequentialKernel S A n → Prop
  | 0, _, _, _ => True
  | n + 1, logging, target, kernel =>
      sequentialSupported initial n logging.1 target.1 kernel.1 ∧
      ∀ (h : SequentialHistory S A n) (a : A),
        0 < ((sequentialLaw initial n target.1 kernel.1) h).toReal →
        0 < (target.2 h a).toReal →
        0 < (logging.2 h a).toReal

/-- U12.3 sequential blocker: prove the change of measure for every finite
horizon from the generated laws, shared environment, and conditional coverage. -/
theorem sequential_mass_transport {S A : Type}
    (initial : PMF S) (n : ℕ) :
    ∀ (logging target : SequentialPolicy S A n) (kernel : SequentialKernel S A n),
      sequentialSupported initial n logging target kernel →
      ∀ h : SequentialHistory S A n,
        ((sequentialLaw initial n target kernel) h).toReal =
          sequentialRatio n logging target h *
            ((sequentialLaw initial n logging kernel) h).toReal := by
  induction n with
  | zero =>
      intro logging target kernel supported h
      simp [sequentialLaw, sequentialRatio]
  | succ n ih =>
      intro logging target kernel supported h
      rcases h with ⟨past, action, state⟩
      have previous := ih logging.1 target.1 kernel.1 supported.1 past
      rw [sequentialLaw_step_mass, sequentialLaw_step_mass]
      let p : ℝ := ((sequentialLaw initial n target.1 kernel.1) past).toReal
      let l : ℝ := ((sequentialLaw initial n logging.1 kernel.1) past).toReal
      let r : ℝ := sequentialRatio n logging.1 target.1 past
      let pi : ℝ := (target.2 past action).toReal
      let mu : ℝ := (logging.2 past action).toReal
      let k : ℝ := (kernel.2 past action state).toReal
      change p * pi * k = (r * (pi / mu)) * (l * mu * k)
      have prefixIdentity : p = r * l := previous
      by_cases zeroPrefix : p = 0
      · have weightedZero : r * l = 0 := prefixIdentity.symm.trans zeroPrefix
        calc
          p * pi * k = 0 := by rw [zeroPrefix]; ring
          _ = (r * l) * (pi / mu) * mu * k := by rw [weightedZero]; ring
          _ = (r * (pi / mu)) * (l * mu * k) := by ring
      · by_cases zeroAction : pi = 0
        · simp [zeroAction]
        · have prefixPositive : 0 < p :=
            lt_of_le_of_ne (show 0 ≤ p from ENNReal.toReal_nonneg)
              (Ne.symm zeroPrefix)
          have actionPositive : 0 < pi :=
            lt_of_le_of_ne (show 0 ≤ pi from ENNReal.toReal_nonneg)
              (Ne.symm zeroAction)
          have loggingPositive : 0 < mu :=
            supported.2 past action prefixPositive actionPositive
          have loggingNonzero : mu ≠ 0 := ne_of_gt loggingPositive
          rw [prefixIdentity]
          field_simp [loggingNonzero] <;> ring

/-- U12.3 sequential blocker: transport expected terminal or cumulative return
using the proved density relation. Finiteness, not an infinite-horizon bound,
provides the finite expectation here. -/
theorem sequential_expectation_transport
    {S A : Type} [Fintype S] [Fintype A]
    (initial : PMF S) (n : ℕ)
    (logging target : SequentialPolicy S A n) (kernel : SequentialKernel S A n)
    (supported : sequentialSupported initial n logging target kernel)
    (returnValue : SequentialHistory S A n → ℝ) :
    Math.Probability.expect (sequentialLaw initial n logging kernel)
        (fun h => sequentialRatio n logging target h * returnValue h) =
      Math.Probability.expect (sequentialLaw initial n target kernel) returnValue := by
  rw [Math.Probability.expect_eq_sum, Math.Probability.expect_eq_sum]
  apply Finset.sum_congr rfl
  intro h _
  rw [sequential_mass_transport initial n logging target kernel supported h]
  ring

/-- U12.3 sequential blocker: expose the actual trajectory-measure integral
identity and both integrability facts, rather than stop at formal ratio algebra. -/
theorem sequential_integral_transport
    {S A : Type} [Fintype S] [Fintype A]
    (initial : PMF S) (n : ℕ)
    [MeasurableSpace (SequentialHistory S A n)]
    [MeasurableSingletonClass (SequentialHistory S A n)]
    (logging target : SequentialPolicy S A n) (kernel : SequentialKernel S A n)
    (supported : sequentialSupported initial n logging target kernel)
    (returnValue : SequentialHistory S A n → ℝ) :
    Integrable returnValue (sequentialLaw initial n target kernel).toMeasure ∧
      Integrable (fun h => sequentialRatio n logging target h * returnValue h)
        (sequentialLaw initial n logging kernel).toMeasure ∧
      (∫ h, sequentialRatio n logging target h * returnValue h
        ∂(sequentialLaw initial n logging kernel).toMeasure) =
        ∫ h, returnValue h ∂(sequentialLaw initial n target kernel).toMeasure := by
  refine ⟨.of_finite, .of_finite, ?_⟩
  rw [PMF.integral_eq_sum, PMF.integral_eq_sum]
  have mean := sequential_expectation_transport
    initial n logging target kernel supported returnValue
  rw [Math.Probability.expect_eq_sum, Math.Probability.expect_eq_sum] at mean
  simpa only [smul_eq_mul] using mean

end JurisLean.Candidates.U12_3SequentialFinite20261030