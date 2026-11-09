import JurisLean.BusinessProcessRealization
import JurisLean.Review20261110.ObservationBridge
import Mathlib.Topology.Order.IsLUB

/-!
Interpretation-indexed decisions. The interpretation type is unrestricted;
only the permitted command menu is finite, as in v4 section 6.4. A prior is an
explicit, separate input. Source only; CI_NOT_RUN until subject-bound evidence.
-/
namespace LegalMath20261110.RemainingClosure.InterpretationChoice

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open LegalMath20261108.ClosedLoop

noncomputable section

variable {H A Λ : Type*}

/-- The complete interpretation-indexed value set, without an implicit prior. -/
def valueSet (V : H → A → Λ → ℝ) (h : H) (a : A) : Set ℝ :=
  Set.range (V h a)

def robustValue (V : H → A → Λ → ℝ) (h : H) (a : A) : ℝ :=
  ⨅ l, V h a l

/-- A finite legal menu selects a maximizer, without selecting a hidden interpretation. -/
def best (score : A → ℝ) (base : A) : List A → A × ℝ
  | [] => (base, score base)
  | a :: rest =>
      let prior := best score base rest
      if prior.2 < score a then (a, score a) else prior

lemma best_value (score : A → ℝ) (base : A) (menu : List A) :
    (best score base menu).2 = score (best score base menu).1 := by
  induction menu with
  | nil => rfl
  | cons a rest ih =>
      simp only [best]
      split
      · rfl
      · exact ih

lemma best_mem (score : A → ℝ) (base : A) (menu : List A) :
    (best score base menu).1 ∈ base :: menu := by
  induction menu with
  | nil => simp [best]
  | cons a rest ih =>
      simp only [best]
      split
      · simp
      · simp only [List.mem_cons] at ih ⊢
        exact ih.elim Or.inl (fun h => Or.inr (Or.inr h))

lemma best_ge_base (score : A → ℝ) (base : A) (menu : List A) :
    score base ≤ (best score base menu).2 := by
  induction menu with
  | nil => exact le_rfl
  | cons a rest ih =>
      simp only [best]
      split
      · rename_i hi
        exact ih.trans (le_of_lt hi)
      · exact ih

lemma best_ge_member (score : A → ℝ) (base : A) (menu : List A) (a : A)
    (ha : a ∈ menu) : score a ≤ (best score base menu).2 := by
  induction menu with
  | nil => simp at ha
  | cons b rest ih =>
      simp only [List.mem_cons] at ha
      simp only [best]
      split
      · rename_i hi
        rcases ha with rfl | ha
        · exact le_rfl
        · exact (ih ha).trans (le_of_lt hi)
      · rename_i hi
        rcases ha with rfl | ha
        · exact le_of_not_gt hi
        · exact ih ha

theorem finite_menu_argmax (score : A → ℝ) (base : A) (menu : List A) :
    (best score base menu).1 ∈ base :: menu ∧
      ∀ a ∈ base :: menu, score a ≤ score (best score base menu).1 := by
  refine ⟨best_mem score base menu, ?_⟩
  intro a ha
  rw [← best_value]
  rcases List.mem_cons.mp ha with rfl | ha
  · exact best_ge_base score base menu
  · exact best_ge_member score base menu a ha

/-- Empty compatible interpretation sets and empty legal menus have named exits. -/
inductive Recommendation (A : Type*)
  | incompatible
  | noAllowedAction
  | unboundedValue
  | selected (action : A)

def recommend (V : H → A → Λ → ℝ) (h : H) (menu : List A) : Recommendation A :=
  if Nonempty Λ then
    match menu with
    | [] => .noAllowedAction
    | base :: rest =>
        if ∀ a ∈ base :: rest, BddBelow (valueSet V h a) then
          .selected (best (robustValue V h) base rest).1
        else .unboundedValue
  else .incompatible

theorem empty_interpretations_exit [IsEmpty Λ] (V : H → A → Λ → ℝ)
    (h : H) (menu : List A) : recommend V h menu = .incompatible := by
  have hn : ¬ Nonempty Λ := fun ⟨l⟩ => isEmptyElim l
  simp [recommend, hn]

theorem empty_menu_exit [Nonempty Λ] (V : H → A → Λ → ℝ) (h : H) :
    recommend V h [] = .noAllowedAction := by simp [recommend]

/-- Real-valued robust optimization is meaningful only on bounded-below
value sets. The proof also supplies their greatest-lower-bound semantics. -/
theorem arbitrary_interpretations_finite_menu [Nonempty Λ]
    (V : H → A → Λ → ℝ) (h : H) (base : A) (menu : List A)
    (bounded : ∀ a ∈ base :: menu, BddBelow (valueSet V h a)) :
    ∃ a ∈ base :: menu,
      IsGLB (valueSet V h a) (robustValue V h a) ∧
      ∀ b ∈ base :: menu,
        IsGLB (valueSet V h b) (robustValue V h b) ∧
        robustValue V h b ≤ robustValue V h a := by
  refine ⟨_, (finite_menu_argmax (robustValue V h) base menu).1, ?_, ?_⟩
  · exact isGLB_ciInf (bounded _ (finite_menu_argmax _ base menu).1)
  · intro b hb
    exact ⟨isGLB_ciInf (bounded b hb),
      (finite_menu_argmax (robustValue V h) base menu).2 b hb⟩

theorem unbounded_menu_has_named_exit [Nonempty Λ]
    (V : H → A → Λ → ℝ) (h : H) (base : A) (menu : List A)
    (unbounded : ¬ ∀ a ∈ base :: menu, BddBelow (valueSet V h a)) :
    recommend V h (base :: menu) = .unboundedValue := by
  simp [recommend, unbounded]

lemma robust_le_branch (V : H → A → Λ → ℝ) (h : H) (a : A)
    (bounded : BddBelow (valueSet V h a)) (l : Λ) : robustValue V h a ≤ V h a l :=
  ciInf_le bounded l

/-- Uniform errors survive the robust criterion; no exchange of max and expectation. -/
theorem robust_error_transport [Nonempty Λ] (V W : H → A → Λ → ℝ)
    (h : H) (a : A) (η : ℝ)
    (hbV : BddBelow (valueSet V h a)) (hbW : BddBelow (valueSet W h a))
    (error : ∀ l, |V h a l - W h a l| ≤ η) :
    |robustValue V h a - robustValue W h a| ≤ η := by
  apply abs_le.mpr
  constructor
  · have lower : robustValue W h a - η ≤ robustValue V h a := by
      apply le_ciInf
      intro l
      have e := (abs_le.mp (error l)).1
      have hw := robust_le_branch W h a hbW l
      linarith
    linarith
  · have lower : robustValue V h a - η ≤ robustValue W h a := by
      apply le_ciInf
      intro l
      have e := (abs_le.mp (error l)).2
      have hv := robust_le_branch V h a hbV l
      linarith
    linarith

section MeasurableChoice
variable [MeasurableSpace H] [MeasurableSpace A]

lemma measurable_best (score : H → A → ℝ) (base : A) (menu : List A)
    (hs : ∀ a, Measurable (fun h => score h a)) :
    Measurable (fun h => best (score h) base menu) := by
  induction menu with
  | nil => exact measurable_const.prodMk (hs base)
  | cons a rest ih =>
      exact Measurable.ite (measurableSet_lt ih.snd (hs a))
        (measurable_const.prodMk (hs a)) ih

theorem measurable_countable_robust [Countable Λ] (V : H → A → Λ → ℝ)
    (ha : A) (_bounded : ∀ h, BddBelow (valueSet V h ha))
    (hm : ∀ l, Measurable (fun h => V h ha l)) :
    Measurable (fun h => robustValue V h ha) := .iInf hm

/-- Infinite, possibly uncountable interpretations: a countable dense skeleton
and continuity in interpretation prove measurability, rather than assume it. -/
theorem measurable_separable_robust [TopologicalSpace Λ]
    (V : H → A → Λ → ℝ) (a : A) (S : Set Λ) (countable : S.Countable)
    (dense : Dense S) (hcont : ∀ h, Continuous (V h a))
    (bounded : ∀ h, BddBelow (valueSet V h a))
    (hm : ∀ l ∈ S, Measurable (fun h => V h a l)) :
    Measurable (fun h => robustValue V h a) := by
  haveI : Countable S := countable.to_subtype
  have equality : (fun h => robustValue V h a) =
      (fun h => ⨅ l : S, V h a l) := by
    funext h
    exact (dense.ciInf (hcont h) (bounded h)).symm
  rw [equality]
  exact Measurable.iInf (fun l => hm l l.property)

/-- Replacing a policy does not replace the actual outcome, history or learner. -/
def withChoice {Θ O M : Type*} [MeasurableSpace Θ] [MeasurableSpace O]
    [MeasurableSpace M] (D : Dynamics H Θ A O M)
    (score : (H × Θ) → A → ℝ) (base : A) (menu : List A)
    (hs : ∀ a, Measurable (fun s => score s a)) : Dynamics H Θ A O M :=
  { D with policy := Kernel.deterministic
      (fun s => (best (score s) base menu).1) (measurable_best score base menu hs).fst }

instance choice_policy_markov {Θ O M : Type*} [MeasurableSpace Θ] [MeasurableSpace O]
    [MeasurableSpace M] (D : Dynamics H Θ A O M)
    (score : (H × Θ) → A → ℝ) (base : A) (menu : List A)
    (hs : ∀ a, Measurable (fun s => score s a)) :
    IsMarkovKernel (withChoice D score base menu hs).policy := by
  dsimp [withChoice]
  infer_instance

instance choice_outcome_markov {Θ O M : Type*} [MeasurableSpace Θ] [MeasurableSpace O]
    [MeasurableSpace M] (D : Dynamics H Θ A O M) [IsMarkovKernel D.outcome]
    (score : (H × Θ) → A → ℝ) (base : A) (menu : List A)
    (hs : ∀ a, Measurable (fun s => score s a)) :
    IsMarkovKernel (withChoice D score base menu hs).outcome := by
  change IsMarkovKernel D.outcome
  infer_instance

theorem choice_keeps_actual_update {Θ O M : Type*} [MeasurableSpace Θ]
    [MeasurableSpace O] [MeasurableSpace M] (D : Dynamics H Θ A O M)
    (score : (H × Θ) → A → ℝ) (base : A) (menu : List A)
    (hs : ∀ a, Measurable (fun s => score s a)) (z : (H × Θ) × (A × O)) :
    update (withChoice D score base menu hs) z = update D z := rfl

theorem next_choice_reads_actual_post {Θ O M : Type*} [MeasurableSpace Θ]
    [MeasurableSpace O] [MeasurableSpace M] (D : Dynamics H Θ A O M)
    [IsMarkovKernel D.outcome] (score : (H × Θ) → A → ℝ) (base : A) (menu : List A)
    (hs : ∀ a, Measurable (fun s => score s a)) (s : H × Θ)
    (B : Set A) (hB : MeasurableSet B) :
    nextAction (withChoice D score base menu hs) s B =
      ∫⁻ a, ∫⁻ o,
        (withChoice D score base menu hs).policy
          (D.append s.1 a o, D.learn s.2 (D.measure (D.append s.1 a o) a o)) B
          ∂D.outcome (s,a) ∂(withChoice D score base menu hs).policy s :=
  nextAction_apply (withChoice D score base menu hs) s hB

end MeasurableChoice

section Prior
variable [MeasurableSpace Λ]

def bayesValue (prior : Measure Λ) (V : H → A → Λ → ℝ) (h : H) (a : A) : ℝ :=
  ∫ l, V h a l ∂prior

theorem robust_le_bayes [Nonempty Λ] (prior : Measure Λ) [IsProbabilityMeasure prior]
    (V : H → A → Λ → ℝ) (h : H) (a : A)
    (hb : BddBelow (valueSet V h a)) (hi : Integrable (V h a) prior) :
    robustValue V h a ≤ bayesValue prior V h a := by
  have inequality := integral_mono_ae (integrable_const (robustValue V h a)) hi
    (Filter.Eventually.of_forall (fun l => robust_le_branch V h a hb l))
  simpa [bayesValue] using inequality

theorem measurable_bayes [MeasurableSpace H] (prior : Measure Λ) [SFinite prior]
    (V : H → A → Λ → ℝ) (a : A)
    (hm : StronglyMeasurable (fun z : H × Λ => V z.1 a z.2)) :
    Measurable (fun h => bayesValue prior V h a) :=
  hm.integral_prod_right.measurable

theorem criteria_coincide_on_interpretation_independence [Nonempty Λ]
    (prior : Measure Λ) [IsProbabilityMeasure prior]
    (V : H → A → Λ → ℝ) (score : H → A → ℝ)
    (same : ∀ h a l, V h a l = score h a) (h : H) (a : A) :
    robustValue V h a = score h a ∧ bayesValue prior V h a = score h a ∧
      valueSet V h a = {score h a} := by
  simp [robustValue, bayesValue, valueSet, same]

end Prior

def diagonalValue (a l : Bool) : ℝ := if a = l then 1 else 0

theorem minimax_and_expectation_do_not_commute :
    max (min (diagonalValue false false) (diagonalValue false true))
        (min (diagonalValue true false) (diagonalValue true true)) = 0 ∧
    min (max (diagonalValue false false) (diagonalValue true false))
        (max (diagonalValue false true) (diagonalValue true true)) = 1 ∧
    (diagonalValue false false + diagonalValue false true) / 2 = (1/2 : ℝ) := by
  norm_num [diagonalValue]

/-- Infinite action sets need attainment conditions; this is not a restriction
on the finite legal menu used by the original model. -/
theorem open_interval_has_no_maximizer (a : Set.Ioo (0 : ℝ) 1) :
    ∃ b : Set.Ioo (0 : ℝ) 1, a.val < b.val := by
  refine ⟨⟨(a.val+1)/2, ?_⟩, ?_⟩
  · constructor <;> linarith [a.property.1, a.property.2]
  · dsimp
    linarith [a.property.2]

/-- Without measurable inputs an everywhere optimal selector need not be
measurable. The unique winning action would reveal a nonmeasurable set. -/
theorem nonmeasurable_winning_region_counterexample [MeasurableSpace H]
    (S : Set H) (nonmeasurable : ¬ MeasurableSet S) :
    ¬ ∃ choose : H → Bool, Measurable choose ∧
      ∀ h a,
        (if h ∈ S then (if a then (1:ℝ) else 0) else (if a then 0 else 1)) ≤
        (if h ∈ S then (if choose h then 1 else 0) else (if choose h then 0 else 1)) := by
  classical
  rintro ⟨choose, hm, optimal⟩
  have equality : choose ⁻¹' {true} = S := by
    ext h
    by_cases hs : h ∈ S
    · have winner : choose h = true := by
        cases hc : choose h with
        | false =>
            have bad := optimal h true
            simp [hs, hc] at bad
        | true => rfl
      simp [winner, hs]
    · have winner : choose h = false := by
        cases hc : choose h with
        | false => rfl
        | true =>
            have bad := optimal h false
            simp [hs, hc] at bad
      simp [winner, hs]
  exact nonmeasurable (equality ▸ hm (measurableSet_singleton true))

section ActualBusiness
open JurisLean.Candidates.Final20261021
open JurisLean.Candidates.AdaptiveRoundLedger20261027
open LegalMath20261109.BusinessProcess

variable {W : Type} {m k : Nat}
local instance : MeasurableSpace (JurisLean.Candidates.BusinessFeedbackLoop20261027.State m) := ⊤
local instance : MeasurableSpace (RoundState m) := ⊤
local instance : MeasurableSpace (Fin k) := ⊤
local instance : MeasurableSpace (List (Fin k)) := ⊤

/-- Every interpretation evaluates the same actual business poststate. -/
def businessValue (initial : JurisLean.Candidates.BusinessFeedbackLoop20261027.State m)
    (catalog : Fin k → JurisLean.Candidates.BusinessFeedbackLoop20261027.Command W m)
    (utility : Λ → JurisLean.Candidates.BusinessFeedbackLoop20261027.State m → ℝ)
    (h : List (Fin k)) (a : Fin k) (l : Λ) : ℝ :=
  utility l (JurisLean.Candidates.BusinessFeedbackLoop20261027.step
    (replay initial catalog h) (catalog a))

theorem robust_business_closed_loop [Nonempty Λ]
    (initial : JurisLean.Candidates.BusinessFeedbackLoop20261027.State m)
    (catalog : Fin k → JurisLean.Candidates.BusinessFeedbackLoop20261027.Command W m)
    (utility : Λ → JurisLean.Candidates.BusinessFeedbackLoop20261027.State m → ℝ)
    (base : Fin k) (menu : List (Fin k))
    (valid : JurisLean.Candidates.BusinessFeedbackLoop20261027.KnownBusinessInvariant initial)
    (bounded : roundSpent initial.learning ≤ initial.learning.limit)
    (valuesBounded : ∀ history a, a ∈ base :: menu →
      BddBelow (valueSet (businessValue initial catalog utility) history a))
    (h : List (Fin k)) :
    let score := robustValue (businessValue initial catalog utility)
    let pick := fun history => (best (score history) base menu).1
    step (model initial catalog pick) (encode initial catalog h) =
        Measure.dirac (encode initial catalog (h ++ [pick h])) ∧
      pick h ∈ base :: menu ∧
      (∀ a ∈ base :: menu,
        IsGLB (valueSet (businessValue initial catalog utility) h a) (score h a) ∧
        score h a ≤ score h (pick h)) ∧
      legalInvariant initial catalog (encode initial catalog (h ++ [pick h])) := by
  dsimp only
  refine ⟨actual_step_law initial catalog _ h,
    (finite_menu_argmax _ base menu).1, ?_, ?_⟩
  · intro a ha
    exact ⟨isGLB_ciInf (valuesBounded h a ha), (finite_menu_argmax _ base menu).2 a ha⟩
  · exact replay_invariant initial catalog valid bounded _

end ActualBusiness

#print axioms arbitrary_interpretations_finite_menu
#print axioms measurable_separable_robust
#print axioms robust_error_transport
#print axioms next_choice_reads_actual_post
#print axioms robust_le_bayes
#print axioms minimax_and_expectation_do_not_commute
#print axioms robust_business_closed_loop

end
end LegalMath20261110.RemainingClosure.InterpretationChoice
