import JurisLean.Seams.UniformContinuous
import JurisLean.Candidates.U11_1OriginalInstances20261030
import JurisLean.Candidates.U04_2OriginalObservationInstances20261101

/-! Frozen04.6 L129/L131 only.
Uses the existing Function.FactorsThrough psi Obs definition of identification.
The missingness counterexample reuses original04.4; unknown mechanisms may vary.
The L133 six-question/premise register stays in the existing original97 record. -/

noncomputable section
open MeasureTheory Set
open JurisLean.Candidates.BernoulliMeanInstance20261031
open JurisLean.Candidates.U04_2OriginalObservationInstances20261101

namespace JurisLean.Candidates.U04_6OriginalIdentificationInstances20261101
open JurisLean.Seams.UniformContinuous
open JurisLean.Candidates.U11_1OriginalInstances20261030

theorem uniform_knowledge_comparison :
    uniform01 (Icc (0 : ℝ) 1) = 1 ∧
    uniform01 (Ioc (0 : ℝ) 1) = 1 ∧
    (¬ ∀ x ∈ Icc (0 : ℝ) 1, x ≠ 0) ∧
    (∀ x ∈ Ioc (0 : ℝ) 1, x ≠ 0) := by
  have hc : uniform01 (Icc (0 : ℝ) 1) = 1 := by
    rw [uniform01, Measure.restrict_apply measurableSet_Icc, Set.inter_self]
    exact volume_unit_interval
  have ho := uniform01_truth_event
  rw [truth_event_eq_Ioc] at ho
  refine ⟨hc, ho, ?_, ?_⟩
  · intro h
    have hz := h 0 (by constructor <;> norm_num)
    exact hz rfl
  · intro x hx
    exact ne_of_gt hx.1

theorem identical_reports_do_not_identify_missing_mean :
    ¬ Function.FactorsThrough originalMissingMean originalMissingReport := by
  intro identified
  have endpoints := original04_4_two_feasible_endpoints
  have hObs : originalMissingReport false = originalMissingReport true := by
    funext m report
    exact endpoints.1 m report
  have hTarget := identified hObs
  rw [endpoints.2.1, endpoints.2.2.1] at hTarget
  norm_num at hTarget

local instance : MeasurableSpace Bool := ⊤

def quarterParameter (b : Bool) : ℝ := if b then 3 / 4 else 1 / 4

private theorem quarter_nonneg (b : Bool) : 0 ≤ quarterParameter b := by
  cases b <;> norm_num [quarterParameter]

private theorem quarter_le_one (b : Bool) : quarterParameter b ≤ 1 := by
  cases b <;> norm_num [quarterParameter]

def quarterObservationLaw (b : Bool) : Measure Bool :=
  bernoulliMeasure (quarterParameter b) (quarter_nonneg b) (quarter_le_one b)

private theorem quarter_true_mass (b : Bool) :
    (quarterObservationLaw b).real {true} = quarterParameter b := by
  change ((bernoulliMeasure (quarterParameter b)
    (quarter_nonneg b) (quarter_le_one b)) {true}).toReal = quarterParameter b
  rw [fixed_bernoulli_true_mass, ENNReal.toReal_ofReal (quarter_nonneg b)]

theorem quarter_parameter_identified :
    Function.FactorsThrough quarterParameter quarterObservationLaw := by
  intro b c h
  have hm := congrArg (fun mu : Measure Bool => (mu {true}).toReal) h
  change (quarterObservationLaw b).real {true} =
    (quarterObservationLaw c).real {true} at hm
  rw [quarter_true_mass, quarter_true_mass] at hm
  exact hm

theorem identifiable_target_with_nonzero_sample_error :
    Function.FactorsThrough quarterParameter quarterObservationLaw ∧
    (quarterObservationLaw false).real {true} = 1 / 4 ∧
    ∀ y : Bool, 0 < |(if y then (1 : ℝ) else 0) - quarterParameter false| := by
  refine ⟨quarter_parameter_identified, ?_, ?_⟩
  · simpa [quarterParameter] using quarter_true_mass false
  · intro y
    cases y <;> norm_num [quarterParameter]

end JurisLean.Candidates.U04_6OriginalIdentificationInstances20261101
