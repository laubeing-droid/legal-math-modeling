import Mathlib

/-!
# A joint law for action, actual feedback, history and personal learning

Pinned Mathlib: c5ea00351c28e24afc9f0f84379aa41082b1188f.
Static source/API review only; Lean/Lake/Elan have NOT been run for this file.

The outcome kernel may depend on BOTH the current state and the sampled action.
The same outcome updates history and personal parameters. `retained` pairs the
current deterministic input with this joint draw; it does not independently
resample feedback. The next policy consumes the updated pair.

This supplies a general mathematical connection, not all jurisdiction-specific
instances. Legality and actual-event contracts enter as local support hypotheses;
normalization, joint marginals and trajectory consistency are derived.
-/

namespace LegalMath20261108.ClosedLoop

open MeasureTheory ProbabilityTheory Preorder
open scoped ENNReal ProbabilityTheory

noncomputable section

variable {H Θ A O M : Type*}
  [MeasurableSpace H] [MeasurableSpace Θ] [MeasurableSpace A]
  [MeasurableSpace O] [MeasurableSpace M]

/-- Existing history, private parameters, actions, actual outcomes and measurements. -/
structure Dynamics (H Θ A O M : Type*)
    [MeasurableSpace H] [MeasurableSpace Θ] [MeasurableSpace A]
    [MeasurableSpace O] [MeasurableSpace M] where
  policy : Kernel (H × Θ) A
  outcome : Kernel ((H × Θ) × A) O
  append : H → A → O → H
  measure : H → A → O → M
  learn : Θ → M → Θ
  measurable_append : Measurable (fun z : H × (A × O) => append z.1 z.2.1 z.2.2)
  measurable_measure : Measurable (fun z : H × (A × O) => measure z.1 z.2.1 z.2.2)
  measurable_learn : Measurable (fun z : Θ × M => learn z.1 z.2)

variable (D : Dynamics H Θ A O M)

def historyOut (z : (H × Θ) × (A × O)) : H := D.append z.1.1 z.2.1 z.2.2

def feedback (z : (H × Θ) × (A × O)) : M :=
  D.measure (historyOut D z) z.2.1 z.2.2

def parameterOut (z : (H × Θ) × (A × O)) : Θ := D.learn z.1.2 (feedback D z)

def update (z : (H × Θ) × (A × O)) : H × Θ := (historyOut D z, parameterOut D z)

lemma measurable_historyOut : Measurable (historyOut D) :=
  D.measurable_append.comp (measurable_fst.fst.prodMk measurable_snd)

lemma measurable_feedback : Measurable (feedback D) :=
  D.measurable_measure.comp ((measurable_historyOut D).prodMk measurable_snd)

lemma measurable_parameterOut : Measurable (parameterOut D) :=
  D.measurable_learn.comp (measurable_fst.snd.prodMk (measurable_feedback D))

lemma measurable_update : Measurable (update D) :=
  (measurable_historyOut D).prodMk (measurable_parameterOut D)

/-- Learning reads the actual post-history; replacing the private input cannot
rewrite that post-history or any projection of it. This says nothing about the
next policy being unchanged. Legal events themselves may alter the history. -/
theorem history_projection_frame {V : Type*} (view : H → V)
    (h : H) (θ θ' : Θ) (a : A) (o : O) :
    view (update D ((h, θ), (a, o))).1 =
      view (update D ((h, θ'), (a, o))).1 := rfl

/-- Transport of an existing append contract, not a new proof of that contract. -/
theorem past_preserved (Past : H → H → Prop)
    (happend : ∀ h a o, Past h (D.append h a o)) (s : H × Θ) (z : A × O) :
    Past s.1 (update D (s, z)).1 := happend s.1 z.1 z.2

/-- A concrete full event history really retains every past event, in order. -/
theorem append_event_prefix (h : List (A × O)) (a : A) (o : O) :
    h <+: h ++ [(a, o)] := List.prefix_append h [(a, o)]

def joint : Kernel (H × Θ) (A × O) := D.policy ⊗ₖ D.outcome

def retained : Kernel (H × Θ) ((H × Θ) × (A × O)) := Kernel.id ×ₖ joint D

def step : Kernel (H × Θ) (H × Θ) := (retained D).map (update D)

variable [IsMarkovKernel D.policy] [IsMarkovKernel D.outcome]

instance joint_markov : IsMarkovKernel (joint D) := by unfold joint; infer_instance

instance retained_markov : IsMarkovKernel (retained D) := by unfold retained; infer_instance

instance step_markov : IsMarkovKernel (step D) :=
  Kernel.IsMarkovKernel.map (retained D) (measurable_update D)

theorem step_normalized (s : H × Θ) : step D s Set.univ = 1 := measure_univ

/-- One pushforward of one joint draw, rather than a product of two marginals. -/
theorem step_apply (s : H × Θ) {B : Set (H × Θ)} (hB : MeasurableSet B) :
    step D s B = joint D s ((fun z => update D (s, z)) ⁻¹' B) := by
  calc
    step D s B = retained D s ((update D) ⁻¹' B) :=
      Kernel.map_apply' _ (measurable_update D) s hB
    _ = joint D s (Prod.mk s ⁻¹' ((update D) ⁻¹' B)) :=
      Kernel.id_prod_apply' _ s ((measurable_update D) hB)
    _ = joint D s ((fun z => update D (s, z)) ⁻¹' B) := rfl

theorem step_lintegral (s : H × Θ) (f : H × Θ → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ t, f t ∂step D s =
      ∫⁻ a, ∫⁻ o, f (update D (s, (a, o))) ∂D.outcome (s, a) ∂D.policy s := by
  rw [step, Kernel.lintegral_map _ (measurable_update D) s hf, retained,
    Kernel.lintegral_id_prod (hf.comp (measurable_update D)) (joint D) s]
  exact Kernel.lintegral_compProd' D.policy D.outcome s
    (hf.comp ((measurable_update D).comp (measurable_const.prodMk measurable_id)))

/-- Both marginal equalities retain the SAME `retained D`; no independence is asserted. -/
theorem history_marginal :
    (step D).map Prod.fst = (retained D).map (historyOut D) := by
  exact (Kernel.map_comp_right (retained D) (measurable_update D) measurable_fst).symm

theorem learning_marginal :
    (step D).map Prod.snd = (retained D).map (parameterOut D) := by
  exact (Kernel.map_comp_right (retained D) (measurable_update D) measurable_snd).symm

/-- Local action permission and the action-dependent actual-event contract are
lifted together. The event contract may include adverse or erroneous outcomes;
it is not silently replaced by the set of normatively allowed judgments. -/
theorem joint_support (s : H × Θ) (Allowed : A → Prop) (Event : A → O → Prop)
    (hm : MeasurableSet {z : A × O | Allowed z.1 ∧ Event z.1 z.2})
    (hp : ∀ᵐ a ∂D.policy s, Allowed a)
    (he : ∀ a, Allowed a → ∀ᵐ o ∂D.outcome (s, a), Event a o) :
    ∀ᵐ z ∂joint D s, Allowed z.1 ∧ Event z.1 z.2 := by
  apply Kernel.ae_compProd_of_ae_ae hm
  filter_upwards [hp] with a ha
  filter_upwards [he a ha] with o ho
  exact ⟨ha, ho⟩

def nextAction : Kernel (H × Θ) A := D.policy ∘ₖ step D

/-- The second action reads the new history AND the newly learned parameters. -/
theorem nextAction_apply (s : H × Θ) {B : Set A} (hB : MeasurableSet B) :
    nextAction D s B =
      ∫⁻ a, ∫⁻ o, D.policy
        (D.append s.1 a o, D.learn s.2 (D.measure (D.append s.1 a o) a o)) B
        ∂D.outcome (s, a) ∂D.policy s := by
  rw [nextAction, Kernel.comp_apply' _ _ _ hB]
  exact step_lintegral D s (fun t => D.policy t B) (Kernel.measurable_coe D.policy hB)

/-! Complete state prefixes. When H is the full legal history, that entire
coordinate is retained. The theorem does not turn an arbitrary H into a full
history: the list append lemma above supplies one concrete history contract.
No global finiteness of histories or private parameters is required. -/

abbrev Prefix (H Θ : Type*) (n : ℕ) := Π _i : Finset.Iic n, H × Θ

def chain (n : ℕ) : Kernel (Prefix H Θ n) (H × Θ) :=
  (step D).comap (fun h => h ⟨n, Finset.mem_Iic.mpr le_rfl⟩)
    (measurable_pi_apply ⟨n, Finset.mem_Iic.mpr le_rfl⟩)

instance chain_markov (n : ℕ) : IsMarkovKernel (chain D n) := by
  unfold chain
  infer_instance

theorem chain_reads_current (n : ℕ) (h : Prefix H Θ n) :
    chain D n h = step D (h ⟨n, Finset.mem_Iic.mpr le_rfl⟩) := rfl

/-- Finite composition retains the whole prefix, not only the latest state. -/
theorem finite_prefix_compose (a b c : ℕ) (hab : a ≤ b) (hbc : b ≤ c) :
    Kernel.partialTraj (chain D) b c ∘ₖ Kernel.partialTraj (chain D) a b =
      Kernel.partialTraj (chain D) a c :=
  Kernel.partialTraj_comp_partialTraj (κ := chain D) hab hbc

instance finite_prefix_markov (a b : ℕ) :
    IsMarkovKernel (Kernel.partialTraj (chain D) a b) := inferInstance

theorem full_path_prefix (a b : ℕ) :
    (Kernel.traj (chain D) a).map (frestrictLe b) = Kernel.partialTraj (chain D) a b :=
  Kernel.traj_map_frestrictLe (κ := chain D) a b

theorem full_path_unique (a : ℕ) (η : Kernel (Prefix H Θ a) (ℕ → H × Θ))
    (hη : ∀ b, η.map (frestrictLe b) = Kernel.partialTraj (chain D) a b) :
    η = Kernel.traj (chain D) a := Kernel.eq_traj (κ := chain D) η hη

def pathLaw (μ₀ : Measure (H × Θ)) : Measure (ℕ → H × Θ) :=
  Kernel.trajMeasure μ₀ (chain D)

instance pathLaw_probability (μ₀ : Measure (H × Θ)) [IsProbabilityMeasure μ₀] :
    IsProbabilityMeasure (pathLaw D μ₀) := by unfold pathLaw; infer_instance

theorem complete_prefix_joint (μ₀ : Measure (H × Θ)) [IsProbabilityMeasure μ₀] (n : ℕ) :
    (pathLaw D μ₀).map (frestrictLe n) ⊗ₘ chain D n =
      (pathLaw D μ₀).map (fun x => (frestrictLe n x, x (n + 1))) :=
  Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure
    (κ := chain D) (μ₀ := μ₀) (a := n)

theorem complete_prefix_projection (μ₀ : Measure (H × Θ))
    [IsProbabilityMeasure μ₀] (n : ℕ) :
    ((pathLaw D μ₀).map (frestrictLe n) ⊗ₘ chain D n).fst =
      (pathLaw D μ₀).map (frestrictLe n) := by
  exact Measure.fst_compProd _ _

/-! A nonempty, genuinely random SINGLE-STEP NUMERIC PROJECTION instance.
Here H=ℝ stores only a balance, not a complete legal history. Repeated subtraction
is not a multi-round payment model (it could make the balance negative).
Fixed repayment interpretation: principal 10, payment 7·1_Y, score (q+1_Y)/2. A gift
interpretation would keep balance 10 while keeping the same actual payment;
interpretation labels are not automatically supplied with a prior here. -/

namespace RepaymentExample

def bit (y : Bool) : ℝ := if y then 1 else 0

lemma measurable_bit : Measurable bit := Measurable.of_discrete

def fair : Measure Bool :=
  (1 / 2 : ℝ≥0∞) • Measure.dirac false + (1 / 2 : ℝ≥0∞) • Measure.dirac true

instance fair_probability : IsProbabilityMeasure fair where
  measure_univ := by
    simpa [fair, Measure.add_apply, smul_eq_mul] using ENNReal.add_halves (1 : ℝ≥0∞)

theorem fair_atoms : fair {false} = 1 / 2 ∧ fair {true} = 1 / 2 := by
  simp [fair, Measure.add_apply, smul_eq_mul]

def choose (s : ℝ × ℝ) : Bool := if (1 / 2 : ℝ) ≤ s.2 then true else false

lemma measurable_choose : Measurable choose :=
  Measurable.ite (measurableSet_le measurable_const measurable_snd)
    measurable_const measurable_const

def model : Dynamics ℝ ℝ Bool Bool ℝ where
  policy := Kernel.deterministic choose measurable_choose
  outcome := Kernel.const ((ℝ × ℝ) × Bool) fair
  append := fun balance _ y => balance - 7 * bit y
  measure := fun _ _ y => bit y
  learn := fun q observation => q / 2 + observation / 2
  measurable_append := measurable_fst.sub
    (measurable_const.mul (measurable_bit.comp measurable_snd.snd))
  measurable_measure := measurable_bit.comp measurable_snd.snd
  measurable_learn := by fun_prop

instance model_policy_markov : IsMarkovKernel model.policy := by
  change IsMarkovKernel (Kernel.deterministic choose measurable_choose)
  infer_instance

instance model_outcome_markov : IsMarkovKernel model.outcome := by
  change IsMarkovKernel (Kernel.const ((ℝ × ℝ) × Bool) fair)
  infer_instance

def initial : ℝ × ℝ := (10, 1 / 5)

theorem two_outputs (a y : Bool) :
    update model (initial, (a, y)) = (10, 1 / 10) ∨
      update model (initial, (a, y)) = (3, 3 / 5) := by
  cases y <;> norm_num [update, historyOut, parameterOut, feedback, model, initial, bit]

theorem no_crossed_feedback (a y : Bool) :
    update model (initial, (a, y)) ≠ (10, 3 / 5) := by
  cases y <;> norm_num [update, historyOut, parameterOut, feedback, model, initial, bit]

/-- Both coordinates arise from the same Y: the crossed pair has zero probability. -/
theorem crossed_pair_mass_zero : step model initial {(10, 3 / 5)} = 0 := by
  rw [step_apply model initial (measurableSet_singleton _)]
  have hempty : (fun z : Bool × Bool => update model (initial, z)) ⁻¹'
      {(10, 3 / 5)} = ∅ := by
    ext z
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false]
    exact no_crossed_feedback z.1 z.2
  rw [hempty, measure_empty]

theorem joint_two_point_support :
    step model initial ({(10, 1 / 10)} ∪ {(3, 3 / 5)}) = 1 := by
  rw [step_apply model initial
    ((measurableSet_singleton _).union (measurableSet_singleton _))]
  have hall : (fun z : Bool × Bool => update model (initial, z)) ⁻¹'
      ({(10, 1 / 10)} ∪ {(3, 3 / 5)}) = Set.univ := by
    ext z
    simp only [Set.mem_preimage, Set.mem_union, Set.mem_singleton_iff, Set.mem_univ, iff_true]
    exact two_outputs z.1 z.2
  rw [hall, measure_univ]

/-- The rule/principal is fixed, but feedback changes the next selected action. -/
theorem next_choice_changes :
    choose initial = false ∧ choose (update model (initial, (false, true))) = true := by
  norm_num [choose, update, historyOut, parameterOut, feedback, model, initial, bit]

/-- The change is in the actual policy kernel, not just an unused score. -/
theorem next_policy_values :
    model.policy initial = Measure.dirac false ∧
      model.policy (update model (initial, (false, true))) = Measure.dirac true := by
  constructor
  · change Kernel.deterministic choose measurable_choose initial = _
    rw [Kernel.deterministic_apply]
    exact congrArg Measure.dirac next_choice_changes.1
  · change Kernel.deterministic choose measurable_choose
      (update model (initial, (false, true))) = _
    rw [Kernel.deterministic_apply]
    exact congrArg Measure.dirac next_choice_changes.2

end RepaymentExample
end
end LegalMath20261108.ClosedLoop
