import JurisLean.FeedbackHistoryBridge

/-!
Whole-path transport of the original closed-loop laws. The hypothesis is a
one-step semiconjugacy, not equality of the desired path measures. We first
transport complete finite-prefix joint laws, then use projective uniqueness.
The final consumers use the original event-log lift and its actual joint draw.
Source only; authoritative CI evidence is maintained in the engineering appendix.
-/

set_option autoImplicit false

namespace LegalMath20261110.RemainingClosure.ProcessTransport

open MeasureTheory ProbabilityTheory Preorder
open LegalMath20261108.ClosedLoop
open scoped ENNReal ProbabilityTheory

noncomputable section

section PrefixMaps

variable {S T : Type*} [MeasurableSpace S] [MeasurableSpace T]

abbrev StatePrefix (S : Type*) (n : ℕ) := Finset.Iic n → S

def mapPrefix (φ : S → T) (n : ℕ) (p : StatePrefix S n) : StatePrefix T n :=
  fun i => φ (p i)

def mapPath (φ : S → T) (p : ℕ → S) : ℕ → T := fun n => φ (p n)

lemma measurable_mapPrefix {φ : S → T} (hφ : Measurable φ) (n : ℕ) :
    Measurable (mapPrefix φ n) :=
  measurable_pi_lambda _ (fun i => hφ.comp (measurable_pi_apply i))

lemma measurable_mapPath {φ : S → T} (hφ : Measurable φ) :
    Measurable (mapPath φ) :=
  measurable_pi_lambda _ (fun n => hφ.comp (measurable_pi_apply n))

def constantPrefix (n : ℕ) (s : S) : StatePrefix S n := fun _ => s

lemma measurable_constantPrefix (n : ℕ) :
    Measurable (constantPrefix (S := S) n) :=
  measurable_pi_lambda _ (fun _ => measurable_id)

/-- The next-state draw is appended to the whole preceding state prefix. -/
def gluePrefix (n : ℕ) (z : StatePrefix S n × S) : StatePrefix S (n+1) :=
  fun i => if hi : (i : ℕ) ≤ n then z.1 ⟨i,Finset.mem_Iic.mpr hi⟩ else z.2

lemma measurable_gluePrefix (n : ℕ) : Measurable (gluePrefix (S := S) n) := by
  classical
  refine measurable_pi_lambda _ (fun i => ?_)
  by_cases hi : (i : ℕ) ≤ n
  · simpa only [gluePrefix,dif_pos hi] using
      (measurable_pi_apply (⟨i,Finset.mem_Iic.mpr hi⟩ : Finset.Iic n)).comp measurable_fst
  · simpa only [gluePrefix,dif_neg hi] using
      (measurable_snd : Measurable (Prod.snd : StatePrefix S n × S → S))

lemma gluePrefix_restrict (n : ℕ) (p : ℕ → S) :
    gluePrefix n (frestrictLe n p,p (n+1)) = frestrictLe (n+1) p := by
  funext i
  by_cases hi : (i : ℕ) ≤ n
  · simp only [gluePrefix,dif_pos hi]
    rfl
  · simp only [gluePrefix,dif_neg hi]
    have eqn : (i : ℕ) = n+1 := by
      have bound := Finset.mem_Iic.mp i.property
      omega
    change p (n+1) = p i
    rw [eqn]

lemma mapPrefix_glue (φ : S → T) (n : ℕ) :
    mapPrefix φ (n+1) ∘ gluePrefix n =
      gluePrefix n ∘ Prod.map (mapPrefix φ n) φ := by
  classical
  funext z i
  by_cases hi : (i : ℕ) ≤ n <;> simp [Function.comp_def,mapPrefix,gluePrefix,hi]

lemma mapPath_restrict (φ : S → T) (n : ℕ) :
    frestrictLe n ∘ mapPath φ = mapPrefix φ n ∘ frestrictLe n := rfl

/-- Complete finite-prefix distributions determine a finite path measure.
This uses joint prefixes, and cannot be replaced by equality of one-time marginals. -/
theorem path_measure_ext (μ ν : Measure (ℕ → S)) [IsFiniteMeasure ν]
    (hprefix : ∀ n, μ.map (frestrictLe n) = ν.map (frestrictLe n)) : μ = ν := by
  let P : (I : Finset ℕ) → Measure (I → S) := fun I => ν.map I.restrict
  have hP : IsProjectiveMeasureFamily (α := fun _ : ℕ => S) P := by
    intro I J hJI
    change ν.map J.restrict = (ν.map I.restrict).map
      (fun p : I → S => fun j : J => p ⟨j,hJI j.property⟩)
    rw [Measure.map_map (by fun_prop) (by fun_prop)]
    rfl
  letI : ∀ I, IsFiniteMeasure (P I) := fun _ => inferInstance
  have hν : IsProjectiveLimit (α := fun _ : ℕ => S) ν P := fun _ => rfl
  have hμ : IsProjectiveLimit (α := fun _ : ℕ => S) μ P :=
    (isProjectiveLimit_nat_iff (X := fun _ : ℕ => S) hP μ).mpr (fun n => hprefix n)
  exact hμ.unique hν

end PrefixMaps

/-- Simultaneously push the old prefix and its actual next state. No product
independence of the two coordinates is asserted. -/
theorem compProd_map_semiconjugacy
    {S T U V : Type*} [MeasurableSpace S] [MeasurableSpace T]
    [MeasurableSpace U] [MeasurableSpace V]
    (μ : Measure S) [SFinite μ] (K : Kernel S T) (L : Kernel U V)
    [IsSFiniteKernel K] [IsSFiniteKernel L]
    (f : S → U) (g : T → V) (hf : Measurable f) (hg : Measurable g)
    (hstep : ∀ s, (K s).map g = L (f s)) :
    (μ ⊗ₘ K).map (Prod.map f g) = (μ.map f) ⊗ₘ L := by
  ext B hB
  rw [Measure.map_apply (hf.prodMap hg) hB,
    Measure.compProd_apply ((hf.prodMap hg) hB),
    Measure.compProd_apply hB,
    lintegral_map (Kernel.measurable_kernel_prodMk_left hB) hf]
  apply lintegral_congr
  intro s
  have h := congrArg (fun η : Measure V => η (Prod.mk (f s) ⁻¹' B)) (hstep s)
  change ((K s).map g) (Prod.mk (f s) ⁻¹' B) = L (f s) (Prod.mk (f s) ⁻¹' B) at h
  rw [Measure.map_apply hg (measurable_prodMk_left hB)] at h
  exact h

section ClosedLoopTransport

variable {H Θ A O M H' Θ' A' O' M' : Type*}
  [MeasurableSpace H] [MeasurableSpace Θ] [MeasurableSpace A]
  [MeasurableSpace O] [MeasurableSpace M]
  [MeasurableSpace H'] [MeasurableSpace Θ'] [MeasurableSpace A']
  [MeasurableSpace O'] [MeasurableSpace M']

variable (D : Dynamics H Θ A O M) (E : Dynamics H' Θ' A' O' M')
  [IsMarkovKernel D.policy] [IsMarkovKernel D.outcome]
  [IsMarkovKernel E.policy] [IsMarkovKernel E.outcome]

def prefixLaw (μ : Measure (H × Θ)) (n : ℕ) : Measure (Prefix H Θ n) :=
  (pathLaw D μ).map (frestrictLe n)

instance prefixLaw_probability (μ : Measure (H × Θ)) [IsProbabilityMeasure μ] (n : ℕ) :
    IsProbabilityMeasure (prefixLaw D μ n) :=
  Measure.isProbabilityMeasure_map (by fun_prop)

lemma prefixLaw_zero (μ : Measure (H × Θ)) :
    prefixLaw D μ 0 = μ.map (constantPrefix 0) := by
  have hr : (frestrictLe 0 : (ℕ → H × Θ) → Prefix H Θ 0) =
      constantPrefix 0 ∘ (fun p => p 0) := by
    funext p i
    change p i = p 0
    have eq0 : (i : ℕ) = 0 := Nat.eq_zero_of_le_zero (Finset.mem_Iic.mp i.property)
    rw [eq0]
  rw [prefixLaw,hr]
  calc
    (pathLaw D μ).map (constantPrefix 0 ∘ (fun p : ℕ → H × Θ => p 0)) =
        ((pathLaw D μ).map (fun p => p 0)).map (constantPrefix 0) :=
      (Measure.map_map (measurable_constantPrefix (S := H × Θ) 0)
        (measurable_pi_apply 0)).symm
    _ = μ.map (constantPrefix 0) := by rw [pathLaw_initial]

/-- Recursion of the full prefix law, obtained from the original actual
prefix/next-state joint measure rather than a marginal recursion. -/
lemma prefixLaw_succ (μ : Measure (H × Θ)) [IsProbabilityMeasure μ] (n : ℕ) :
    (prefixLaw D μ n ⊗ₘ chain D n).map (gluePrefix n) = prefixLaw D μ (n+1) := by
  have h := congrArg (fun η : Measure (Prefix H Θ n × (H × Θ)) =>
    η.map (gluePrefix n)) (complete_prefix_joint D μ n)
  dsimp only at h
  rw [Measure.map_map (measurable_gluePrefix n) (by fun_prop)] at h
  have glue : gluePrefix n ∘ (fun p : ℕ → H × Θ => (frestrictLe n p,p (n+1))) =
      frestrictLe (n+1) := funext (gluePrefix_restrict n)
  rw [glue] at h
  exact h

/-- One-step semiconjugacy transports every complete finite-prefix joint law. -/
theorem complete_prefix_transport
    (φ : H × Θ → H' × Θ') (hφ : Measurable φ)
    (hstep : ∀ s, (step D s).map φ = step E (φ s))
    (μ : Measure (H × Θ)) [IsProbabilityMeasure μ] (n : ℕ) :
    (prefixLaw D μ n).map (mapPrefix φ n) = prefixLaw E (μ.map φ) n := by
  letI : IsProbabilityMeasure (μ.map φ) := Measure.isProbabilityMeasure_map hφ.aemeasurable
  induction n with
  | zero =>
      rw [prefixLaw_zero,prefixLaw_zero,
        Measure.map_map (measurable_mapPrefix hφ 0) (measurable_constantPrefix 0),
        Measure.map_map (measurable_constantPrefix 0) hφ]
      rfl
  | succ n ih =>
      have hc : ∀ p : Prefix H Θ n,
          (chain D n p).map φ = chain E n (mapPrefix φ n p) := fun p =>
        hstep (p ⟨n,Finset.mem_Iic.mpr le_rfl⟩)
      calc
        (prefixLaw D μ (n+1)).map (mapPrefix φ (n+1)) =
            ((prefixLaw D μ n ⊗ₘ chain D n).map (gluePrefix n)).map
              (mapPrefix φ (n+1)) := by rw [prefixLaw_succ]
        _ = ((prefixLaw D μ n ⊗ₘ chain D n).map (Prod.map (mapPrefix φ n) φ)).map
              (gluePrefix n) := by
            rw [Measure.map_map (measurable_mapPrefix hφ (n+1)) (measurable_gluePrefix n),
              Measure.map_map (measurable_gluePrefix n) ((measurable_mapPrefix hφ n).prodMap hφ),
              mapPrefix_glue]
        _ = ((prefixLaw D μ n).map (mapPrefix φ n) ⊗ₘ chain E n).map
              (gluePrefix n) := by
            rw [compProd_map_semiconjugacy (prefixLaw D μ n) (chain D n) (chain E n)
              (mapPrefix φ n) φ (measurable_mapPrefix hφ n) hφ hc]
        _ = (prefixLaw E (μ.map φ) n ⊗ₘ chain E n).map (gluePrefix n) := by rw [ih]
        _ = prefixLaw E (μ.map φ) (n+1) := prefixLaw_succ E (μ.map φ) n

/-- The whole path measure, including all temporal correlations, is pushed
forward by a one-step semiconjugacy. -/
theorem pathLaw_transport
    (φ : H × Θ → H' × Θ') (hφ : Measurable φ)
    (hstep : ∀ s, (step D s).map φ = step E (φ s))
    (μ : Measure (H × Θ)) [IsProbabilityMeasure μ] :
    (pathLaw D μ).map (mapPath φ) = pathLaw E (μ.map φ) := by
  letI : IsProbabilityMeasure (μ.map φ) := Measure.isProbabilityMeasure_map hφ.aemeasurable
  apply path_measure_ext
  intro n
  rw [Measure.map_map (by fun_prop) (measurable_mapPath hφ),mapPath_restrict,
    ← Measure.map_map (measurable_mapPrefix hφ n) (by fun_prop)]
  exact complete_prefix_transport D E φ hφ hstep μ n

/-- The same result for any given target initial law, with its exact pushforward. -/
theorem pathLaw_transport_initial
    (φ : H × Θ → H' × Θ') (hφ : Measurable φ)
    (hstep : ∀ s, (step D s).map φ = step E (φ s))
    (μ : Measure (H × Θ)) [IsProbabilityMeasure μ]
    (ν : Measure (H' × Θ')) (hinitial : μ.map φ = ν) :
    (pathLaw D μ).map (mapPath φ) = pathLaw E ν := by
  rw [← hinitial]
  exact pathLaw_transport D E φ hφ hstep μ

end ClosedLoopTransport

section EventHistoryConsumer

variable {H Θ A O M : Type*}
  [MeasurableSpace H] [MeasurableSpace Θ] [MeasurableSpace A]
  [MeasurableSpace O] [MeasurableSpace M] [MeasurableSpace (List (A × O))]
  (D : Dynamics H Θ A O M)
  [IsMarkovKernel D.policy] [IsMarkovKernel D.outcome]
  (hlog : Measurable (fun z : List (A × O) × (A × O) => z.1 ++ [z.2]))

/-- Actual consumer: forgetting the appended action/outcome record transports
whole paths to the old model, using the old single-draw update projection. -/
theorem full_event_history_path_transport
    (μ : Measure ((List (A × O) × H) × Θ)) [IsProbabilityMeasure μ] :
    (pathLaw (withEventHistory D hlog) μ).map (mapPath forgetLog) =
      pathLaw D (μ.map forgetLog) :=
  pathLaw_transport (withEventHistory D hlog) D forgetLog measurable_forgetLog
    (history_step_projection D hlog) μ

/-- Any measurable readout of the complete projected path has the same joint
law. This can include balances, private parameters and every finite-time payoff. -/
theorem full_event_history_readout_transport
    (μ : Measure ((List (A × O) × H) × Θ)) [IsProbabilityMeasure μ]
    {Z : Type*} [MeasurableSpace Z] (read : (ℕ → H × Θ) → Z) (hr : Measurable read) :
    (pathLaw (withEventHistory D hlog) μ).map (read ∘ mapPath forgetLog) =
      (pathLaw D (μ.map forgetLog)).map read := by
  rw [← Measure.map_map hr (measurable_mapPath measurable_forgetLog),
    full_event_history_path_transport D hlog μ]

end EventHistoryConsumer

section NumericConsumer

open LegalMath20261108.UnifiedFeedbackBridge

local instance : MeasurableSpace (List (Bool × Bool)) := ⊤

/-- The response feedback example now transports the entire numeric process,
not only the separately proved nth-time laws. -/
theorem response_full_path_joint_law
    (μ : Measure ((List (Bool × Bool) × ℝ) × ℝ)) [IsProbabilityMeasure μ] :
    (pathLaw historyModel μ).map (fun p n => forgetLog (p n)) =
      pathLaw model (μ.map forgetLog) :=
  full_event_history_path_transport model measurable_bool_log_append μ

/-- A complete finite joint numeric prefix is a consequence of the same
semiconjugacy; the original feedback update and outcome kernel are reused. -/
theorem response_finite_prefix_joint_law
    (μ : Measure ((List (Bool × Bool) × ℝ) × ℝ)) [IsProbabilityMeasure μ] (n : ℕ) :
    (prefixLaw historyModel μ n).map (mapPrefix forgetLog n) =
      prefixLaw model (μ.map forgetLog) n :=
  complete_prefix_transport historyModel model forgetLog measurable_forgetLog
    (history_step_projection model measurable_bool_log_append) μ n

end NumericConsumer

#print axioms path_measure_ext
#print axioms compProd_map_semiconjugacy
#print axioms complete_prefix_transport
#print axioms pathLaw_transport
#print axioms full_event_history_path_transport
#print axioms full_event_history_readout_transport
#print axioms response_full_path_joint_law
#print axioms response_finite_prefix_joint_law

end

end LegalMath20261110.RemainingClosure.ProcessTransport
