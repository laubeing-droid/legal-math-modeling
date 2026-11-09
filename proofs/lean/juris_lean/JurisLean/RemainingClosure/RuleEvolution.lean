import JurisLean.Review20261110.InvariantClosure
import JurisLean.Candidates.U10_1RefreshRuleProtocol20261030
import Mathlib.Topology.MetricSpace.Contracting

/-!
Nonautonomous laws with changing invariant sets, actual authorized refreshes,
and a sufficient convergence theorem for commuting strict contractions. A
switch of individually contracting maps can still oscillate. Source only;
CI_NOT_RUN until the exact subject build and axiom artifact are recorded.
-/
set_option autoImplicit false

namespace LegalMath20261110.RemainingClosure.RuleEvolution

open MeasureTheory ProbabilityTheory Filter
open LegalMath20261108.ClosedLoop
open LegalMath20261110.InvariantClosure
open scoped ENNReal NNReal Topology

noncomputable section

variable {S : Type*} [MeasurableSpace S]

/-- A countable time index gives joint measurability from kernel measurability. -/
def indexedKernel (K : Nat → Kernel S S) : Kernel (Nat × S) S where
  toFun z := K z.1 z.2
  measurable' := measurable_from_prod_countable_right (fun n => (K n).measurable)

instance (K : Nat → Kernel S S) [∀ n, IsMarkovKernel (K n)] :
    IsMarkovKernel (indexedKernel K) where
  isProbabilityMeasure z := by change IsProbabilityMeasure (K z.1 z.2); infer_instance

/-- The time coordinate belongs to the common history; it is not a fresh
worst-case model chosen separately for each term in a long-horizon value. -/
def clockedDynamics (K : Nat → Kernel S S) : Dynamics (Nat × S) Unit Unit S Unit where
  policy := Kernel.const ((Nat × S) × Unit) (Measure.dirac ())
  outcome := (indexedKernel K).comap (fun z => z.1.1) measurable_fst.fst
  append := fun h _ next => (h.1+1,next)
  measure := fun _ _ _ => ()
  learn := fun _ _ => ()
  measurable_append := by fun_prop
  measurable_measure := measurable_const
  measurable_learn := measurable_const

instance (K : Nat → Kernel S S) : IsMarkovKernel (clockedDynamics K).policy := by
  dsimp [clockedDynamics]
  infer_instance

instance (K : Nat → Kernel S S) [∀ n, IsMarkovKernel (K n)] :
    IsMarkovKernel (clockedDynamics K).outcome := by
  dsimp [clockedDynamics]
  infer_instance

theorem nonautonomous_markov (K : Nat → Kernel S S) [∀ n, IsMarkovKernel (K n)] :
    IsMarkovKernel (step (clockedDynamics K)) := inferInstance

lemma clock_step_apply (K : Nat → Kernel S S) [∀ n, IsMarkovKernel (K n)]
    (n : Nat) (s : S) (B : Set ((Nat × S) × Unit)) (hB : MeasurableSet B) :
    step (clockedDynamics K) ((n,s),()) B = K n s {t | ((n+1,t),()) ∈ B} := by
  rw [step_apply _ _ hB, joint, Kernel.compProd_apply]
  · simp [clockedDynamics, indexedKernel, Kernel.const_apply, Kernel.comap_apply,
      update, historyOut, parameterOut, feedback]
    rfl
  · exact ((measurable_update (clockedDynamics K)).comp
      (measurable_const.prodMk measurable_id)) hB

def clockInvariant (I : Nat → Set S) : Set ((Nat × S) × Unit) :=
  {z | z.1.2 ∈ I z.1.1}

lemma measurable_clockInvariant (I : Nat → Set S) (hI : ∀ n, MeasurableSet (I n)) :
    MeasurableSet (clockInvariant I) := by
  have equality : clockInvariant I =
      ⋃ n : Nat, {z : (Nat × S) × Unit | z.1.1 = n} ∩ {z | z.1.2 ∈ I n} := by
    ext z
    simp only [clockInvariant, Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_inter_iff]
    constructor
    · intro hz
      exact ⟨z.1.1,rfl,hz⟩
    · rintro ⟨n,hn,hi⟩
      simpa [hn] using hi
  rw [equality]
  exact MeasurableSet.iUnion (fun n =>
    (measurable_fst.fst (measurableSet_singleton n)).inter
      ((hI n).preimage measurable_fst.snd))

lemma clock_step_closed (K : Nat → Kernel S S) [∀ n, IsMarkovKernel (K n)]
    (I : Nat → Set S) (hI : ∀ n, MeasurableSet (I n))
    (closed : ∀ n s, s ∈ I n → K n s (I (n+1)) = 1)
    (z : (Nat × S) × Unit) (hz : z ∈ clockInvariant I) :
    step (clockedDynamics K) z (clockInvariant I) = 1 := by
  rcases z with ⟨⟨n,s⟩,⟨⟩⟩
  rw [clock_step_apply _ _ _ _ (measurable_clockInvariant I hI)]
  exact closed n s hz

/-- A changing legal invariant is transported at each actual time. This uses
the previously proved path law, rather than postulating a separate trajectory. -/
theorem clocked_path_invariant (K : Nat → Kernel S S) [∀ n, IsMarkovKernel (K n)]
    (I : Nat → Set S) (hI : ∀ n, MeasurableSet (I n)) (s₀ : S) (initial : s₀ ∈ I 0)
    (closed : ∀ n s, s ∈ I n → K n s (I (n+1)) = 1) :
    ∀ᵐ path ∂pathLaw (clockedDynamics K) (Measure.dirac ((0,s₀),())),
      ∀ n, (path n).1.2 ∈ I (path n).1.1 := by
  exact ae_invariant_path (clockedDynamics K) (Measure.dirac ((0,s₀),()))
    (clockInvariant I) (measurable_clockInvariant I hI)
    (by simp [clockInvariant, initial]) (clock_step_closed K I hI closed)

lemma clock_time_iterations (K : Nat → Kernel S S) [∀ n, IsMarkovKernel (K n)]
    (s₀ : S) (n : Nat) :
    ∀ᵐ z ∂iterationLaw (clockedDynamics K) (Measure.dirac ((0,s₀),())) n,
      z.1.1 = n := by
  have timeMeasurable (m : Nat) : MeasurableSet {z : (Nat × S) × Unit | z.1.1 = m} :=
    measurable_fst.fst (measurableSet_singleton m)
  induction n with
  | zero =>
      change ∀ᵐ z ∂(Measure.dirac ((0,s₀),())), z.1.1 = 0
      apply ae_of_mass_one _ _ (timeMeasurable 0)
      rw [Measure.dirac_apply' _ (timeMeasurable 0)]
      simp
  | succ n ih =>
      change ∀ᵐ z ∂(step (clockedDynamics K) ∘ₘ
        iterationLaw (clockedDynamics K) (Measure.dirac ((0,s₀),())) n), z.1.1 = n+1
      apply Measure.ae_comp_of_ae_ae (timeMeasurable (n+1))
      filter_upwards [ih] with z hz
      rcases z with ⟨⟨m,x⟩,⟨⟩⟩
      change m = n at hz
      subst m
      apply ae_of_mass_one _ _ (timeMeasurable (n+1))
      rw [clock_step_apply _ _ _ _ (timeMeasurable (n+1))]
      simpa using (measure_univ (μ := K n x))

/-- The clock equals the actual transition index almost surely, so the
changing invariant below is indexed by n itself, not an arbitrary state clock. -/
theorem nonautonomous_path_invariant (K : Nat → Kernel S S) [∀ n, IsMarkovKernel (K n)]
    (I : Nat → Set S) (hI : ∀ n, MeasurableSet (I n)) (s₀ : S) (initial : s₀ ∈ I 0)
    (closed : ∀ n s, s ∈ I n → K n s (I (n+1)) = 1) :
    ∀ᵐ path ∂pathLaw (clockedDynamics K) (Measure.dirac ((0,s₀),())),
      ∀ n, (path n).1.1 = n ∧ (path n).1.2 ∈ I n := by
  have clock : ∀ᵐ path ∂pathLaw (clockedDynamics K) (Measure.dirac ((0,s₀),())),
      ∀ n, (path n).1.1 = n := by
    apply ae_all_iff.mpr
    intro n
    have marginal : ∀ᵐ z ∂(pathLaw (clockedDynamics K)
        (Measure.dirac ((0,s₀),()))).map (fun path => path n), z.1.1 = n := by
      rw [pathLaw_marginal]
      exact clock_time_iterations K s₀ n
    exact ae_of_ae_map (μ := pathLaw (clockedDynamics K) (Measure.dirac ((0,s₀),())))
      (f := fun path : Nat → (Nat × S) × Unit => path n)
      (measurable_pi_apply n).aemeasurable marginal
  filter_upwards [clock, clocked_path_invariant K I hI s₀ initial closed] with path ht hi
  intro n
  exact ⟨ht n, by simpa [ht n] using hi n⟩

section Contractions
variable {X : Type*} [MetricSpace X]

def evolve (F : Nat → X → X) (x : X) : Nat → X
  | 0 => x
  | n+1 => F n (evolve F x n)

theorem nonautonomous_forgetting (F : Nat → X → X) (q : ℝ≥0)
    (contract : ∀ n, ContractingWith q (F n)) (x y : X) (n : Nat) :
    dist (evolve F x n) (evolve F y n) ≤ (q:ℝ)^n * dist x y := by
  induction n with
  | zero => simp [evolve]
  | succ n ih =>
      calc
        dist (evolve F x (n+1)) (evolve F y (n+1)) ≤
            (q:ℝ) * dist (evolve F x n) (evolve F y n) := (contract n).dist_le_mul _ _
        _ ≤ (q:ℝ) * ((q:ℝ)^n * dist x y) := mul_le_mul_of_nonneg_left ih q.property
        _ = (q:ℝ)^(n+1) * dist x y := by rw [pow_succ]; ring

lemma evolve_fixed (F : Nat → X → X) (z : X) (fixed : ∀ n, F n z = z) (n : Nat) :
    evolve F z n = z := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [evolve, ih] using fixed n

/-- Commutation supplies a common invariant point from the existing Banach
existence theorem; existence is not inserted as a premise. -/
theorem commuting_changes_have_unique_attractor [Nonempty X] [CompleteSpace X]
    (F : Nat → X → X) (q : ℝ≥0) (contract : ∀ n, ContractingWith q (F n))
    (commute : ∀ n x, F 0 (F n x) = F n (F 0 x)) :
    ∃! z : X, (∀ n, F n z = z) ∧
      ∀ x, Tendsto (evolve F x) atTop (𝓝 z) := by
  let z := ContractingWith.fixedPoint (F 0) (contract 0)
  have h0 : F 0 z = z := (contract 0).fixedPoint_isFixedPt.eq
  have fixed : ∀ n, F n z = z := by
    intro n
    apply (contract 0).fixedPoint_unique
    change F 0 (F n z) = F n z
    rw [commute n z,h0]
  refine ⟨z, ⟨fixed, ?_⟩, ?_⟩
  · intro x
    apply tendsto_iff_dist_tendsto_zero.mpr
    have hq : (q:ℝ) < 1 := by exact_mod_cast (contract 0).1
    have hp := tendsto_pow_atTop_nhds_zero_of_lt_one q.property hq
    have limit : Tendsto (fun n : Nat => (q:ℝ)^n * dist x z) atTop (𝓝 0) := by
      simpa using hp.mul_const (dist x z)
    apply squeeze_zero (fun _ => dist_nonneg) (fun n => ?_) limit
    simpa [evolve_fixed F z fixed n] using nonautonomous_forgetting F q contract x z n
  · intro y hy
    exact (contract 0).fixedPoint_unique (hy.1 0)

end Contractions

def alternating (n : Nat) : ℝ := if n % 2 = 0 then 0 else 1

def alternatingChange (n : Nat) (_ : ℝ) : ℝ := alternating (n+1)

theorem every_alternating_change_is_strictly_contracting (n : Nat) :
    ContractingWith 0 (alternatingChange n) := by
  refine ⟨by norm_num, LipschitzWith.of_dist_le_mul ?_⟩
  intro x y
  simp [alternatingChange]

theorem arbitrary_switching_need_not_converge : ¬ CauchySeq alternating := by
  intro hc
  obtain ⟨N,hN⟩ := Metric.cauchySeq_iff.mp hc (1/2) (by norm_num)
  have bad := hN (2*N) (by omega) (2*N+1) (by omega)
  norm_num [alternating, Nat.add_mod, Nat.mul_mod] at bad

section ActualRefresh
open JurisLean.Candidates.Final20261021
open JurisLean.Candidates.TemporalInterpretation20261027
open JurisLean.Candidates.U10_1RefreshRuleProtocol20261030

theorem actual_refresh_keeps_authority_and_history (grants : List Authorization.Grant)
    (before after : Ledger.Handle) (change : Pipeline.RefreshInput)
    (published : Pipeline.refresh grants before change = .known after) :
    Authorization.authorized grants before.gamma change.actor 1 change.event.version
      (.document change.event.version) none (some change.gamma) = true ∧
    after.gamma = change.gamma ∧ after.state.normHistory = before.state.normHistory ++ [change.event] ∧
    after.state.cash = before.state.cash ∧ after.state.used = before.state.used := by
  by_cases same : change.gamma.caseId = before.gamma.caseId
  · cases auth : Authorization.authorized grants before.gamma change.actor 1 change.event.version
        (.document change.event.version) none (some change.gamma) with
    | false => simp [Pipeline.refresh, same, auth] at published
    | true =>
        simp [Pipeline.refresh, same, auth] at published
        cases published
        exact ⟨rfl,rfl,rfl,rfl,rfl⟩
  · simp [Pipeline.refresh, same] at published

/-- A successful rule refresh consumes the original authorization theorem and
its original conserved ledger, rather than treating model learning as authority. -/
theorem actual_refresh_transports_invariant (grants : List Authorization.Grant)
    (before after : Ledger.Handle) (change : Pipeline.RefreshInput)
    (published : Pipeline.refresh grants before change = .known after)
    (valid : Trace.Invariant before) : Trace.Invariant after :=
  Trace.step_preserves (Pipeline.u10_1_authorized_refresh_is_step grants before after change published) valid

theorem old_cutoff_survives_later_refresh (grants : List Authorization.Grant)
    (before after : Ledger.Handle) (change : Pipeline.RefreshInput)
    (published : Pipeline.refresh grants before change = .known after)
    (old : Gamma) (versions : List Nat) (app : App)
    (invisible : Temporal.visible old change.event = false) :
    selectVersion old after.state.normHistory versions app =
      selectVersion old before.state.normHistory versions app := by
  rw [(actual_refresh_keeps_authority_and_history grants before after change published).2.2.1]
  apply selection_stable_after_invisible_append
  intro event member
  have same : event = change.event := by simpa using member
  simpa [same] using invisible

/-- Today's re-evaluation reads the actual refreshed environment. The old
cutoff theorem above is about a different query, not a frozen current answer. -/
theorem current_evaluation_uses_actual_refreshed_environment {W : Type}
    (current : Ledger.Handle) (input : JurisLean.Candidates.LegalActionDomain20261027.LegalInput W)
    (branch : Nat) (bound : JurisLean.Candidates.FiniteLegalValidation20261027.BoundData)
    (out : JurisLean.Candidates.FiniteLegalValidation20261027.HornReport)
    (accepted : evaluateCurrentRules current input branch = .known (bound,out)) :
    current.state.env = .known out.selectedVersion ∧ out.selectedVersion = current.gamma.normVersion := by
  have actual := evaluated_rules_use_actual_environment current input branch bound out accepted
  exact ⟨actual.2.2.2.2.2.1,actual.2.2.2.2.2.2.1⟩

end ActualRefresh

#print axioms nonautonomous_markov
#print axioms nonautonomous_path_invariant
#print axioms nonautonomous_forgetting
#print axioms commuting_changes_have_unique_attractor
#print axioms arbitrary_switching_need_not_converge
#print axioms actual_refresh_transports_invariant
#print axioms old_cutoff_survives_later_refresh
#print axioms current_evaluation_uses_actual_refreshed_environment

end
end LegalMath20261110.RemainingClosure.RuleEvolution
