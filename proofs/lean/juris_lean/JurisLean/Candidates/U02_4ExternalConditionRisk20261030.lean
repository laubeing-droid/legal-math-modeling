/-
CI_NOT_RUN.

Blocks frozen master U02.4 L297--299: the existing adaptive risk theorem is
instantiated in the actual conditional probability measure P_H = P(. | H),
its expected cumulative budget is bounded by the original pathwise budget,
and the outer alpha + epsilon step uses the actual H/B measure partition.

Fin T denotes exactly rounds 0,...,T-1. The finite result requires only that
prefix's cumulative bound. In the countable result the cumulative-budget
contract is the bound on every finite prefix, all under the same P_H. For the
original nonnegative budgets this is the usual monotone partial-sum meaning
of cumulative nonnegative spending (and follows from a bounded nonnegative
series). Predictability may be retained by the original process; no extra
independence, finite sample space, or finite partition is required here.

No Integrable delta premise is added: the existing theorem receives the
actual conditional risks r_t = E_{P_H}[1_(B_t) | past t], which are integrable
by the library. The original r_t <= delta_t and cumulative-spending premises
then bound their finite sums. No new tower theorem is proved. The original
17-target risk package and the H=B conditioning counterexample are unchanged.
-/

import JurisLean.Candidates.HarnessRisk20261027
import Mathlib.Probability.ConditionalProbability
import Mathlib.MeasureTheory.Measure.Real

open scoped BigOperators
open MeasureTheory ProbabilityTheory

namespace JurisLean.Candidates.U02_4ExternalConditionRisk20261030

private theorem finite_prefix_budget {Ω : Type} [m₀ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (T : Nat)
    (past : Fin T → MeasurableSpace Ω) (information : ∀ t, past t ≤ m₀)
    (bad : Fin T → Set Ω) (measurable : ∀ t, MeasurableSet (bad t))
    (budget : Fin T → Ω → ℝ) (ε : ℝ)
    (conditional : ∀ t, ∀ᵐ w ∂μ,
      (μ[(bad t).indicator (fun _ => (1 : ℝ)) | past t]) w ≤ budget t w)
    (spent : ∀ᵐ w ∂μ, (∑ t : Fin T, budget t w) ≤ ε) :
    μ.real (⋃ t : Fin T, bad t) ≤ ε := by
  classical
  let risk : Fin T → Ω → ℝ := fun t =>
    μ[(bad t).indicator (fun _ => (1 : ℝ)) | past t]
  have riskIntegrable (t : Fin T) : Integrable (risk t) μ := integrable_condExp
  have simultaneous : ∀ᵐ w ∂μ, ∀ t : Fin T, risk t w ≤ budget t w :=
    ae_all_iff.mpr conditional
  have riskSpent : ∀ᵐ w ∂μ, (∑ t : Fin T, risk t w) ≤ ε := by
    filter_upwards [simultaneous, spent] with w hw cumulative
    exact (Finset.sum_le_sum (fun t _ => hw t)).trans cumulative
  have sumIntegrable : Integrable (fun w => ∑ t : Fin T, risk t w) μ :=
    integrable_finsetSum Finset.univ (fun t _ => riskIntegrable t)
  have expected : (∫ w, ∑ t : Fin T, risk t w ∂μ) ≤ ε := by
    calc
      (∫ w, ∑ t : Fin T, risk t w ∂μ) ≤ ∫ _ : Ω, ε ∂μ :=
        integral_mono_ae sumIntegrable (integrable_const ε) riskSpent
      _ = ε := by simp [integral_const]
  have unionBound : μ.real (⋃ t : Fin T, bad t) ≤
      ∫ w, ∑ t : Fin T, risk t w ∂μ := by
    simpa using
      (JurisLean.Candidates.HarnessRisk20261027.finite_adaptive_union_bound
        μ (Finset.univ : Finset (Fin T)) past information bad measurable risk riskIntegrable
        (by intro t _; exact ae_of_all μ (fun _ => le_rfl)))
  exact unionBound.trans expected

/-- Only an internal connector: the conditional bound is derived by the public
results below, and this lemma supplies the actual partition, not a free one. -/
private theorem actual_partition_to_global {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (H : Set Ω)
    (measurableH : MeasurableSet H) (positive : 0 < P H)
    (B : Set Ω) (α ε : ℝ)
    (conditional : (ProbabilityTheory.cond P H).real B ≤ ε)
    (outside : P.real Hᶜ ≤ α) : P.real B ≤ α + ε := by
  have massPositive : 0 < P.real H :=
    ENNReal.toReal_pos (ne_of_gt positive) (measure_ne_top P H)
  have massLeOne : P.real H ≤ 1 := by
    simpa using
      (measureReal_mono (μ := P) (h₂ := measure_ne_top P Set.univ) (Set.subset_univ H))
  have epsNonnegative : 0 ≤ ε :=
    (show 0 ≤ (ProbabilityTheory.cond P H).real B from ENNReal.toReal_nonneg).trans conditional
  have realProduct :
      (ProbabilityTheory.cond P H).real B * P.real H = P.real (H ∩ B) := by
    have product := congrArg ENNReal.toReal
      (ProbabilityTheory.cond_mul_eq_inter measurableH B P)
    simpa only [ENNReal.toReal_mul, measureReal_def] using product
  have ratio : P.real (H ∩ B) / P.real H = (ProbabilityTheory.cond P H).real B := by
    rw [← realProduct]
    field_simp [ne_of_gt massPositive]
  have partition : P.real B = P.real (H ∩ B) + P.real (B \ H) := by
    simpa only [Set.inter_comm B H] using
      (measureReal_inter_add_diff (μ := P) (s := B) measurableH).symm
  have outsideBound : P.real (B \ H) ≤ α := by
    apply le_trans (measureReal_mono (μ := P) (h₂ := measure_ne_top P Hᶜ) ?_) outside
    intro w belongs
    exact belongs.2
  exact JurisLean.Candidates.Final20261021.Harness.u02_4_unconditional_budget
    (P.real B) (P.real (H ∩ B)) (P.real (B \ H)) (P.real H) α ε
    massPositive massLeOne epsNonnegative partition
    (by rw [ratio]; exact conditional) outsideBound

/-- Master U02.4 L297--299 for one fixed prefix: actual conditional risks and
that prefix's pathwise spending bound yield both conditional and global risk. -/
theorem finite_prefix_external_condition_bound {Ω : Type} [m₀ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (H : Set Ω)
    (measurableH : MeasurableSet H) (positive : 0 < P H) (T : Nat)
    (past : Fin T → MeasurableSpace Ω) (information : ∀ t, past t ≤ m₀)
    (bad : Fin T → Set Ω) (measurable : ∀ t, MeasurableSet (bad t))
    (budget : Fin T → Ω → ℝ) (α ε : ℝ)
    (conditional : ∀ t, ∀ᵐ w ∂ProbabilityTheory.cond P H,
      ((ProbabilityTheory.cond P H)[(bad t).indicator (fun _ => (1 : ℝ)) | past t]) w ≤
        budget t w)
    (spent : ∀ᵐ w ∂ProbabilityTheory.cond P H, (∑ t : Fin T, budget t w) ≤ ε)
    (outside : P.real Hᶜ ≤ α) :
    (ProbabilityTheory.cond P H).real (⋃ t : Fin T, bad t) ≤ ε ∧
      P.real (⋃ t : Fin T, bad t) ≤ α + ε := by
  let μH : Measure Ω := ProbabilityTheory.cond P H
  letI : IsProbabilityMeasure μH := ProbabilityTheory.cond_isProbabilityMeasure (ne_of_gt positive)
  have bound : μH.real (⋃ t : Fin T, bad t) ≤ ε :=
    finite_prefix_budget μH T past information bad measurable budget ε conditional spent
  exact ⟨bound, actual_partition_to_global P H measurableH positive _ α ε bound outside⟩

/-- Master U02.4 L297--299 for countably many rounds. Every finite prefix has
the original pathwise budget bound under the same actual conditional measure;
continuity from below is the sole passage from finite prefixes to all rounds. -/
theorem countable_prefix_external_condition_bound {Ω : Type} [m₀ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (H : Set Ω)
    (measurableH : MeasurableSet H) (positive : 0 < P H)
    (past : Nat → MeasurableSpace Ω) (information : ∀ t, past t ≤ m₀)
    (bad : Nat → Set Ω) (measurable : ∀ t, MeasurableSet (bad t))
    (budget : Nat → Ω → ℝ) (α ε : ℝ)
    (conditional : ∀ t, ∀ᵐ w ∂ProbabilityTheory.cond P H,
      ((ProbabilityTheory.cond P H)[(bad t).indicator (fun _ => (1 : ℝ)) | past t]) w ≤
        budget t w)
    (spent : ∀ n, ∀ᵐ w ∂ProbabilityTheory.cond P H,
      (∑ t : Fin n, budget t.val w) ≤ ε)
    (outside : P.real Hᶜ ≤ α) :
    (ProbabilityTheory.cond P H).real (⋃ t : Nat, bad t) ≤ ε ∧
      P.real (⋃ t : Nat, bad t) ≤ α + ε := by
  let μH : Measure Ω := ProbabilityTheory.cond P H
  letI : IsProbabilityMeasure μH := ProbabilityTheory.cond_isProbabilityMeasure (ne_of_gt positive)
  let prefixEvents : Nat → Set Ω := fun n => ⋃ t : Fin n, bad t.val
  have prefixBound (n : Nat) : μH.real (prefixEvents n) ≤ ε :=
    finite_prefix_budget μH n (fun t => past t.val) (fun t => information t.val)
      (fun t => bad t.val) (fun t => measurable t.val)
      (fun t => budget t.val) ε (fun t => conditional t.val) (spent n)
  have epsNonnegative : 0 ≤ ε :=
    (show 0 ≤ μH.real (prefixEvents 0) from ENNReal.toReal_nonneg).trans (prefixBound 0)
  have increasing : Monotone prefixEvents := by
    intro n m ordered w belongs
    obtain ⟨t, member⟩ := Set.mem_iUnion.mp belongs
    exact Set.mem_iUnion.mpr ⟨⟨t.val, lt_of_lt_of_le t.isLt ordered⟩, member⟩
  have unionPrefixes : (⋃ n : Nat, prefixEvents n) = ⋃ t : Nat, bad t := by
    ext w
    constructor
    · intro belongs
      obtain ⟨n, member⟩ := Set.mem_iUnion.mp belongs
      obtain ⟨t, badMember⟩ := Set.mem_iUnion.mp member
      exact Set.mem_iUnion.mpr ⟨t.val, badMember⟩
    · intro belongs
      obtain ⟨t, badMember⟩ := Set.mem_iUnion.mp belongs
      exact Set.mem_iUnion.mpr ⟨t + 1,
        Set.mem_iUnion.mpr ⟨⟨t, Nat.lt_succ_self t⟩, badMember⟩⟩
  have ennBound : μH (⋃ t : Nat, bad t) ≤ ENNReal.ofReal ε := by
    rw [← unionPrefixes, increasing.measure_iUnion]
    exact iSup_le (fun n =>
      (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top μH (prefixEvents n)) epsNonnegative).mpr
        (prefixBound n))
  have bound : μH.real (⋃ t : Nat, bad t) ≤ ε :=
    ENNReal.toReal_le_of_le_ofReal epsNonnegative ennBound
  exact ⟨bound, actual_partition_to_global P H measurableH positive _ α ε bound outside⟩

end JurisLean.Candidates.U02_4ExternalConditionRisk20261030
