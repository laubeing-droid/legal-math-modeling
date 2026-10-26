import JurisLean.Candidates.LearningFiniteClass20261027

/-!
An executable finite empirical-risk minimizer using exact rational losses.
Its output is the data-selected member consumed by the population theorem.
The optimization and selected-risk measurability obligations are proved from
this implementation instead of being supplied as unverified fit claims.
The population and independence assumptions still describe the data process.
-/

namespace JurisLean.Candidates.LearningERM20261027

open MeasureTheory ProbabilityTheory
open JurisLean.Candidates.LearningRisk20261027
open JurisLean.Candidates.LearningFiniteClass20261027

def selectMinimum {H : Type*} (score : H → ℚ) (first : H) : List H → H
  | [] => first
  | next :: rest =>
      let best := selectMinimum score next rest
      if score first ≤ score best then first else best

def empiricalScore {H Z : Type*} {n : ℕ} (loss : H → Z → ℚ)
    (data : Fin n → Z) (h : H) : ℚ :=
  (∑ i, loss h (data i)) / (n : ℚ)

def fitNonempty {H Z : Type*} {n : ℕ} (loss : H → Z → ℚ)
    (first : H) (rest : List H) (data : Fin n → Z) : H :=
  selectMinimum (empiricalScore loss data) first rest

def proposed_empirical_fit {H Z : Type*} {n : ℕ} (loss : H → Z → ℚ)
    (models : List H) (data : Fin n → Z) : Option H :=
  if n = 0 then none else
    match models with
    | [] => none
    | first :: rest => some (fitNonempty loss first rest data)

theorem selectMinimum_spec {H : Type*} (score : H → ℚ) (first : H) (rest : List H) :
    selectMinimum score first rest ∈ first :: rest ∧
      ∀ h ∈ first :: rest, score (selectMinimum score first rest) ≤ score h := by
  induction rest generalizing first with
  | nil => simp [selectMinimum]
  | cons next rest ih =>
      have best := ih next
      change (if score first ≤ score (selectMinimum score next rest) then first
        else selectMinimum score next rest) ∈ first :: next :: rest ∧ _
      by_cases prefer : score first ≤ score (selectMinimum score next rest)
      · simp only [selectMinimum, prefer, if_true]
        refine ⟨by simp, ?_⟩
        intro h member
        rcases List.mem_cons.mp member with same | later
        · subst h; exact le_rfl
        · exact le_trans prefer (best.2 h later)
      · simp only [selectMinimum, prefer, if_false]
        refine ⟨List.mem_cons_of_mem first best.1, ?_⟩
        intro h member
        rcases List.mem_cons.mp member with same | later
        · subst h; exact le_of_lt (lt_of_not_ge prefer)
        · exact best.2 h later

theorem empiricalScore_cast {H Z : Type*} {n : ℕ} (loss : H → Z → ℚ)
    (data : Fin n → Z) (h : H) :
    (empiricalScore loss data h : ℝ) = (∑ i, (loss h (data i) : ℝ)) / (n : ℝ) := by
  simp [empiricalScore]

theorem selectMinimum_measurable {Ω H : Type*} [MeasurableSpace Ω]
    (score : H → Ω → ℚ) (value : H → ℝ) (first : H) (rest : List H)
    (scoreMeasurable : ∀ h ∈ first :: rest, Measurable (fun w => (score h w : ℝ))) :
    Measurable (fun w => (score (selectMinimum (fun h => score h w) first rest) w : ℝ)) ∧
      Measurable (fun w => value (selectMinimum (fun h => score h w) first rest)) := by
  induction rest generalizing first with
  | nil =>
      simpa only [selectMinimum] using
        And.intro (scoreMeasurable first (by simp))
          (show Measurable (fun _ : Ω => value first) from measurable_const)
  | cons next rest ih =>
      have tail := ih next (fun h hh => scoreMeasurable h (List.mem_cons_of_mem first hh))
      have firstMeasurable := scoreMeasurable first (by simp)
      have comparison : MeasurableSet {w |
          score first w ≤ score (selectMinimum (fun h => score h w) next rest) w} := by
        simpa only [Rat.cast_le] using measurableSet_le firstMeasurable tail.1
      constructor
      · have selectedScore :
            (fun w => (score (selectMinimum (fun h => score h w) first (next :: rest)) w : ℝ)) =
            (fun w => if score first w ≤ score (selectMinimum (fun h => score h w) next rest) w
              then (score first w : ℝ)
              else (score (selectMinimum (fun h => score h w) next rest) w : ℝ)) := by
          funext w
          by_cases prefer : score first w ≤ score (selectMinimum (fun h => score h w) next rest) w
          · simp [selectMinimum, prefer]
          · simp [selectMinimum, prefer]
        rw [selectedScore]
        exact Measurable.ite comparison firstMeasurable tail.1
      · simpa only [selectMinimum, apply_ite] using
          Measurable.ite comparison (measurable_const (a := value first)) tail.2

theorem u01_1_actual_empirical_fit_minimizes {H Z : Type*} {n : ℕ}
    (loss : H → Z → ℚ) (first : H) (rest : List H) (data : Fin n → Z) (hn : 0 < n) :
    proposed_empirical_fit loss (first :: rest) data = some (fitNonempty loss first rest data) ∧
    fitNonempty loss first rest data ∈ first :: rest ∧
    ∀ h ∈ first :: rest,
      empiricalScore loss data (fitNonempty loss first rest data) ≤ empiricalScore loss data h := by
  refine ⟨by simp [proposed_empirical_fit, Nat.ne_of_gt hn], ?_⟩
  exact selectMinimum_spec (empiricalScore loss data) first rest

theorem u01_1_actual_fit_consumes_iid_oracle {Ω Z H : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Z] [DecidableEq H] {n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (P : Measure Z) [IsProbabilityMeasure P]
    (hn : 0 < n) (first : H) (rest : List H)
    (sample : Fin n → Ω → Z) (sampleMeasurable : ∀ i, Measurable (sample i))
    (independent : iIndepFun sample μ) (law : ∀ i, IdentDistrib (sample i) id μ P)
    (loss : H → Z → ℚ)
    (lossMeasurable : ∀ h ∈ first :: rest, Measurable (fun z => (loss h z : ℝ)))
    (lossRange : ∀ h ∈ first :: rest, ∀ z, (loss h z : ℝ) ∈ Set.Icc (0 : ℝ) 1)
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    MeasurableSet {w | (∫ z, (loss (fitNonempty loss first rest (fun i => sample i w)) z : ℝ) ∂P) ≤
      riskInf (fun h => ∫ z, (loss h z : ℝ) ∂P) ((first :: rest).toFinset : Set H) +
        2 * finiteRadius n (first :: rest).toFinset.card δ} ∧
    1 - δ ≤ μ.real {w |
      (∫ z, (loss (fitNonempty loss first rest (fun i => sample i w)) z : ℝ) ∂P) ≤
      riskInf (fun h => ∫ z, (loss h z : ℝ) ∂P) ((first :: rest).toFinset : Set H) +
        2 * finiteRadius n (first :: rest).toFinset.card δ} := by
  let chosen := fun w => fitNonempty loss first rest (fun i => sample i w)
  have member : ∀ w, chosen w ∈ (first :: rest).toFinset := by
    intro w
    exact List.mem_toFinset.mpr
      (selectMinimum_spec (empiricalScore loss (fun i => sample i w)) first rest).1
  have meanMeasurable : ∀ h ∈ first :: rest,
      Measurable (fun w => (empiricalScore loss (fun i => sample i w) h : ℝ)) := by
    intro h hh
    have each : ∀ i, Measurable (fun w => (loss h (sample i w) : ℝ)) :=
      fun i => (lossMeasurable h hh).comp (sampleMeasurable i)
    simp_rw [empiricalScore_cast]
    fun_prop
  have selectedRisk : Measurable (fun w => ∫ z, (loss (chosen w) z : ℝ) ∂P) :=
    (selectMinimum_measurable
      (fun h w => empiricalScore loss (fun i => sample i w) h)
      (fun h => ∫ z, (loss h z : ℝ) ∂P) first rest meanMeasurable).2
  have optimization : ∀ w h, h ∈ (first :: rest).toFinset →
      empiricalMean (fun i w' => (loss (chosen w) (sample i w') : ℝ)) w ≤
        empiricalMean (fun i w' => (loss h (sample i w') : ℝ)) w + 0 := by
    intro w h hh
    have best := (selectMinimum_spec (empiricalScore loss (fun i => sample i w))
      first rest).2 h (List.mem_toFinset.mp hh)
    have castBest : (empiricalScore loss (fun i => sample i w) (chosen w) : ℝ) ≤
        (empiricalScore loss (fun i => sample i w) h : ℝ) := by
      exact_mod_cast best
    simpa only [empiricalScore_cast, empiricalMean, add_zero] using castBest
  have result := u01_1_iid_approximate_erm μ P hn (first :: rest).toFinset
    ⟨first, by simp⟩ sample sampleMeasurable independent law
    (fun h z => (loss h z : ℝ))
    (fun h hh => lossMeasurable h (List.mem_toFinset.mp hh))
    (fun h hh => lossRange h (List.mem_toFinset.mp hh))
    chosen member selectedRisk 0 optimization δ hδ hδ1
  simpa only [chosen, add_zero] using result

theorem u01_1_empty_class_rejected {H Z : Type*} {n : ℕ}
    (loss : H → Z → ℚ) (data : Fin n → Z) : proposed_empirical_fit loss [] data = none := by
  simp [proposed_empirical_fit]

theorem u01_1_empty_sample_rejected {H Z : Type*}
    (loss : H → Z → ℚ) (models : List H) (data : Fin 0 → Z) :
    proposed_empirical_fit loss models data = none := by
  simp [proposed_empirical_fit]

theorem u01_1_fit_reads_actual_sample :
    let loss := fun (h z : Bool) => if h = z then (0 : ℚ) else 1
    proposed_empirical_fit loss [false, true] (fun _ : Fin 2 => false) = some false ∧
      proposed_empirical_fit loss [false, true] (fun _ : Fin 2 => true) = some true := by
  norm_num [proposed_empirical_fit, fitNonempty, selectMinimum, empiricalScore]

end JurisLean.Candidates.LearningERM20261027

#check JurisLean.Candidates.LearningERM20261027.u01_1_actual_empirical_fit_minimizes
#print axioms JurisLean.Candidates.LearningERM20261027.u01_1_actual_empirical_fit_minimizes
#check JurisLean.Candidates.LearningERM20261027.u01_1_actual_fit_consumes_iid_oracle
#print axioms JurisLean.Candidates.LearningERM20261027.u01_1_actual_fit_consumes_iid_oracle
#check JurisLean.Candidates.LearningERM20261027.u01_1_empty_class_rejected
#print axioms JurisLean.Candidates.LearningERM20261027.u01_1_empty_class_rejected
#check JurisLean.Candidates.LearningERM20261027.u01_1_empty_sample_rejected
#print axioms JurisLean.Candidates.LearningERM20261027.u01_1_empty_sample_rejected
#check JurisLean.Candidates.LearningERM20261027.u01_1_fit_reads_actual_sample
#print axioms JurisLean.Candidates.LearningERM20261027.u01_1_fit_reads_actual_sample
