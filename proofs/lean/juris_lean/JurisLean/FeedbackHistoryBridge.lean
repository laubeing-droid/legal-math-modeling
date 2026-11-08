import JurisLean.UnifiedFeedbackBridge

/-!
The closed-loop path, its directly iterated marginal, and a full event-log lift.
The log lift samples exactly the original action/outcome pair and records it.
All projection equalities are derived from that construction. For a general
event alphabet the chosen list encoding must have measurable append; the Bool
instance at the end supplies this condition with the discrete sigma algebra.
-/

namespace LegalMath20261108.ClosedLoop

open MeasureTheory ProbabilityTheory Preorder
open scoped ENNReal ProbabilityTheory

noncomputable section

variable {H Θ A O M : Type*}
  [MeasurableSpace H] [MeasurableSpace Θ] [MeasurableSpace A]
  [MeasurableSpace O] [MeasurableSpace M]

/-- Pulling a kernel back and then composing is the same as pushing its input law forward. -/
theorem comap_comp_map {S U V : Type*} [MeasurableSpace S]
    [MeasurableSpace U] [MeasurableSpace V]
    (κ : Kernel U V) (f : S → U) (hf : Measurable f) (μ : Measure S) :
    κ.comap f hf ∘ₘ μ = κ ∘ₘ μ.map f := by
  ext B hB
  rw [Measure.bind_apply hB (Kernel.aemeasurable _),
    Measure.bind_apply hB (Kernel.aemeasurable _),
    lintegral_map (κ.measurable_coe hB) hf]
  rfl

variable (D : Dynamics H Θ A O M)

/-- Direct iteration of the actual closed-loop transition measure. -/
def iterationLaw (D : Dynamics H Θ A O M) (μ₀ : Measure (H × Θ)) :
    ℕ → Measure (H × Θ)
  | 0 => μ₀
  | n + 1 => step D ∘ₘ iterationLaw D μ₀ n

variable [IsMarkovKernel D.policy] [IsMarkovKernel D.outcome]

instance iterationLaw_probability (μ₀ : Measure (H × Θ)) [IsProbabilityMeasure μ₀]
    (n : ℕ) : IsProbabilityMeasure (iterationLaw D μ₀ n) := by
  induction n with
  | zero => exact inferInstanceAs (IsProbabilityMeasure μ₀)
  | succ n ih =>
      letI := ih
      change IsProbabilityMeasure (step D ∘ₘ iterationLaw D μ₀ n)
      infer_instance

theorem pathLaw_initial (μ₀ : Measure (H × Θ)) :
    (pathLaw D μ₀).map (fun x => x 0) = μ₀ := by
  have hzero : (pathLaw D μ₀).map (frestrictLe 0) =
      μ₀.map (MeasurableEquiv.piUnique (fun _ : Finset.Iic 0 => H × Θ)).symm := by
    rw [pathLaw, Kernel.trajMeasure, Measure.map_comp _ _ (by fun_prop),
      Kernel.traj_map_frestrictLe, Kernel.partialTraj_self, Measure.id_comp]
  have h := congrArg (fun ν : Measure (Prefix H Θ 0) =>
    ν.map (fun x => x ⟨0, Finset.mem_Iic.mpr le_rfl⟩)) hzero
  dsimp only at h
  rw [Measure.map_map (by fun_prop) (by fun_prop),
    Measure.map_map (by fun_prop) (by fun_prop)] at h
  change (pathLaw D μ₀).map (fun x => x 0) = μ₀.map id at h
  simpa only [Measure.map_id] using h

theorem pathLaw_next (μ₀ : Measure (H × Θ)) [IsProbabilityMeasure μ₀] (n : ℕ) :
    (pathLaw D μ₀).map (fun x => x (n + 1)) =
      step D ∘ₘ (pathLaw D μ₀).map (fun x => x n) := by
  have h := congrArg (fun ν : Measure (Prefix H Θ n × (H × Θ)) => ν.map Prod.snd)
    (complete_prefix_joint D μ₀ n)
  dsimp only at h
  change ((pathLaw D μ₀).map (frestrictLe n) ⊗ₘ chain D n).snd = _ at h
  rw [Measure.snd_compProd, Measure.map_map measurable_snd (by fun_prop)] at h
  have hk : chain D n ∘ₘ (pathLaw D μ₀).map (frestrictLe n) =
      step D ∘ₘ (pathLaw D μ₀).map (fun x => x n) := by
    rw [chain, comap_comp_map,
      Measure.map_map (by fun_prop) (by fun_prop)]
    rfl
  rw [hk] at h
  exact h.symm

/-- The infinite path and direct state recursion describe the same n-th state. -/
theorem pathLaw_marginal (μ₀ : Measure (H × Θ)) [IsProbabilityMeasure μ₀] (n : ℕ) :
    (pathLaw D μ₀).map (fun x => x n) = iterationLaw D μ₀ n := by
  induction n with
  | zero => exact pathLaw_initial D μ₀
  | succ n ih => rw [pathLaw_next D μ₀ n, ih]; rfl

section EventHistory

variable [MeasurableSpace (List (A × O))]

def forgetLog (s : (List (A × O) × H) × Θ) : H × Θ := (s.1.2, s.2)

lemma measurable_forgetLog : Measurable (forgetLog (H := H) (Θ := Θ) (A := A) (O := O)) :=
  measurable_fst.snd.prodMk measurable_snd

variable (hlog : Measurable (fun z : List (A × O) × (A × O) => z.1 ++ [z.2]))

/-- Store every actual action and outcome while keeping the original transition semantics. -/
def withEventHistory : Dynamics (List (A × O) × H) Θ A O M where
  policy := D.policy.comap forgetLog measurable_forgetLog
  outcome := D.outcome.comap (fun z => (forgetLog z.1, z.2))
    ((measurable_forgetLog.comp measurable_fst).prodMk measurable_snd)
  append := fun h a o => (h.1 ++ [(a, o)], D.append h.2 a o)
  measure := fun h a o => D.measure h.2 a o
  learn := D.learn
  measurable_append :=
    (hlog.comp (measurable_fst.fst.prodMk measurable_snd)).prodMk
      (D.measurable_append.comp (measurable_fst.snd.prodMk measurable_snd))
  measurable_measure := D.measurable_measure.comp (measurable_fst.snd.prodMk measurable_snd)
  measurable_learn := D.measurable_learn

instance history_policy_markov : IsMarkovKernel (withEventHistory D hlog).policy := by
  change IsMarkovKernel (D.policy.comap forgetLog measurable_forgetLog)
  infer_instance

instance history_outcome_markov : IsMarkovKernel (withEventHistory D hlog).outcome := by
  change IsMarkovKernel (D.outcome.comap
    (fun z : ((List (A × O) × H) × Θ) × A => (forgetLog z.1, z.2))
    ((measurable_forgetLog.comp measurable_fst).prodMk measurable_snd))
  infer_instance

theorem history_update_projection (s : (List (A × O) × H) × Θ) (z : A × O) :
    forgetLog (update (withEventHistory D hlog) (s, z)) = update D (forgetLog s, z) := rfl

theorem history_update_log (s : (List (A × O) × H) × Θ) (a : A) (o : O) :
    (update (withEventHistory D hlog) (s, (a, o))).1.1 = s.1.1 ++ [(a, o)] := rfl

theorem history_keeps_past (s : (List (A × O) × H) × Θ) (a : A) (o : O) :
    s.1.1 <+: (update (withEventHistory D hlog) (s, (a, o))).1.1 :=
  append_event_prefix s.1.1 a o

theorem history_joint (s : (List (A × O) × H) × Θ) :
    joint (withEventHistory D hlog) s = joint D (forgetLog s) := by
  ext B hB
  rw [joint, Kernel.compProd_apply hB, joint, Kernel.compProd_apply hB]
  rfl

/-- One projection of the same joint draw, with no independent resampling. -/
theorem history_step_projection (s : (List (A × O) × H) × Θ) :
    (step (withEventHistory D hlog) s).map forgetLog = step D (forgetLog s) := by
  ext B hB
  rw [Measure.map_apply measurable_forgetLog hB,
    step_apply (withEventHistory D hlog) s (measurable_forgetLog hB),
    step_apply D (forgetLog s) hB, history_joint]
  rfl

theorem history_step_kernel :
    (step (withEventHistory D hlog)).map forgetLog =
      (step D).comap forgetLog measurable_forgetLog := by
  ext s : 1
  rw [Kernel.map_apply _ measurable_forgetLog, Kernel.comap_apply]
  exact history_step_projection D hlog s

theorem history_iteration_projection (μ₀ : Measure ((List (A × O) × H) × Θ)) (n : ℕ) :
    (iterationLaw (withEventHistory D hlog) μ₀ n).map forgetLog =
      iterationLaw D (μ₀.map forgetLog) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change (step (withEventHistory D hlog) ∘ₘ
        iterationLaw (withEventHistory D hlog) μ₀ n).map forgetLog =
          step D ∘ₘ iterationLaw D (μ₀.map forgetLog) n
      rw [Measure.map_comp _ _ measurable_forgetLog, history_step_kernel,
        comap_comp_map, ih]

/-- The complete logged process projects at every time to the original process. -/
theorem history_path_marginal (μ₀ : Measure ((List (A × O) × H) × Θ))
    [IsProbabilityMeasure μ₀] (n : ℕ) :
    (pathLaw (withEventHistory D hlog) μ₀).map (fun x => forgetLog (x n)) =
      iterationLaw D (μ₀.map forgetLog) n := by
  calc
    _ = ((pathLaw (withEventHistory D hlog) μ₀).map (fun x => x n)).map forgetLog :=
      (Measure.map_map measurable_forgetLog (measurable_pi_apply n)).symm
    _ = iterationLaw D (μ₀.map forgetLog) n := by
      rw [pathLaw_marginal, history_iteration_projection]

end EventHistory
end
end LegalMath20261108.ClosedLoop

namespace LegalMath20261108.UnifiedFeedbackBridge

open MeasureTheory ProbabilityTheory ClosedLoop
open scoped ProbabilityTheory

noncomputable section

theorem law_eq_iterationLaw (μ₀ : Measure State) (n : ℕ) :
    law μ₀ n = iterationLaw model μ₀ n := by
  induction n with
  | zero => rfl
  | succ n ih => change step model ∘ₘ law μ₀ n = step model ∘ₘ iterationLaw model μ₀ n; rw [ih]

theorem path_marginal_eq_law (μ₀ : Measure State) [IsProbabilityMeasure μ₀] (n : ℕ) :
    (pathLaw model μ₀).map (fun x => x n) = law μ₀ n := by
  rw [pathLaw_marginal, law_eq_iterationLaw]

local instance boolLogMeasurableSpace : MeasurableSpace (List (Bool × Bool)) := ⊤

lemma measurable_bool_log_append :
    Measurable (fun z : List (Bool × Bool) × (Bool × Bool) => z.1 ++ [z.2]) :=
  Measurable.of_discrete

def historyModel := withEventHistory model measurable_bool_log_append

instance historyModel_policy_markov : IsMarkovKernel historyModel.policy :=
  history_policy_markov model measurable_bool_log_append

instance historyModel_outcome_markov : IsMarkovKernel historyModel.outcome :=
  history_outcome_markov model measurable_bool_log_append

/-- The response example now retains every actual sampled action and response. -/
theorem response_history_appends (s : (List (Bool × Bool) × ℝ) × ℝ) (a y : Bool) :
    (update historyModel (s, (a, y))).1.1 = s.1.1 ++ [(a, y)] := rfl

theorem full_history_numeric_law
    (μ₀ : Measure ((List (Bool × Bool) × ℝ) × ℝ)) [IsProbabilityMeasure μ₀] (n : ℕ) :
    (pathLaw historyModel μ₀).map (fun x => forgetLog (x n)) =
      law (μ₀.map forgetLog) n := by
  rw [law_eq_iterationLaw]
  exact history_path_marginal model measurable_bool_log_append μ₀ n

/-- The geometric bound is a readout of the full action/outcome-history process. -/
theorem full_history_mean_geometric_bound
    (μ₀ : Measure ((List (Bool × Bool) × ℝ) × ℝ)) [IsProbabilityMeasure μ₀]
    (h₀ : ∀ᵐ s ∂μ₀.map forgetLog, s ∈ square) (n : ℕ) :
    max |(mean ((pathLaw historyModel μ₀).map (fun x => forgetLog (x n)))).1 - 1/2|
        |(mean ((pathLaw historyModel μ₀).map (fun x => forgetLog (x n)))).2 - 1/2| ≤
      (3/4 : ℝ)^n * max |(mean (μ₀.map forgetLog)).1 - 1/2|
        |(mean (μ₀.map forgetLog)).2 - 1/2| := by
  letI : IsProbabilityMeasure (μ₀.map forgetLog) :=
    Measure.isProbabilityMeasure_map measurable_forgetLog.aemeasurable
  rw [full_history_numeric_law]
  exact law_mean_geometric_bound (μ₀.map forgetLog) h₀ n

end
end LegalMath20261108.UnifiedFeedbackBridge

#print axioms LegalMath20261108.ClosedLoop.pathLaw_marginal
#print axioms LegalMath20261108.ClosedLoop.history_step_projection
#print axioms LegalMath20261108.ClosedLoop.history_iteration_projection
#print axioms LegalMath20261108.ClosedLoop.history_path_marginal
#print axioms LegalMath20261108.UnifiedFeedbackBridge.full_history_mean_geometric_bound
