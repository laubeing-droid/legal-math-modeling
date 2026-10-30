import Mathlib

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace JurisLean.Candidates.ExchangeableRank20261031

/-!
Original split-conformal scope: exchangeable scores, independently constructed
IID continuous tie breakers, uniform test rank, and marginal score coverage.
The final finite example records the group-coverage and deployment boundaries.
-/

private def predecessorRank {N : ℕ}
    (r : Fin N → Fin N → Prop) (i : Fin N) : ℕ := by
  classical
  exact (Finset.univ.filter fun j => r j i).card

private lemma predecessorRank_lt
    {N : ℕ} {r : Fin N → Fin N → Prop}
    (hirr : ∀ i, ¬ r i i)
    (htrans : ∀ i j k, r i j → r j k → r i k)
    {i j : Fin N} (hij : r i j) :
    predecessorRank r i < predecessorRank r j := by
  classical
  let S : Finset (Fin N) := Finset.univ.filter fun a => r a i
  let T : Finset (Fin N) := Finset.univ.filter fun a => r a j
  have hsub : S ⊆ T := by
    intro a ha
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, htrans a i j (Finset.mem_filter.mp ha).2 hij⟩
  change S.card < T.card
  by_contra! hcard
  have heq : S = T := Finset.eq_of_subset_of_card_le hsub hcard
  have hiT : i ∈ T :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hij⟩
  have hiS : i ∈ S := by
    rw [heq]
    exact hiT
  exact hirr i (Finset.mem_filter.mp hiS).2

private lemma predecessorRank_lt_card
    {N : ℕ} {r : Fin N → Fin N → Prop}
    (hirr : ∀ i, ¬ r i i) (i : Fin N) :
    predecessorRank r i < N := by
  classical
  let S : Finset (Fin N) := Finset.univ.filter fun a => r a i
  have hsub : S ⊆ Finset.univ := Finset.subset_univ _
  change S.card < N
  by_contra! hcard
  have hc : (Finset.univ : Finset (Fin N)).card ≤ S.card := by
    simpa using hcard
  have heq : S = Finset.univ :=
    Finset.eq_of_subset_of_card_le hsub hc
  have hiS : i ∈ S := by simp [heq]
  exact hirr i (Finset.mem_filter.mp hiS).2

private lemma predecessorRank_injective
    {N : ℕ} {r : Fin N → Fin N → Prop}
    (hirr : ∀ i, ¬ r i i)
    (htrans : ∀ i j k, r i j → r j k → r i k)
    (htotal : ∀ i j, r i j ∨ i = j ∨ r j i) :
    Function.Injective (predecessorRank r) := by
  intro i j heq
  rcases htotal i j with hij | he | hji
  · have := predecessorRank_lt hirr htrans hij
    omega
  · exact he
  · have := predecessorRank_lt hirr htrans hji
    omega

private def predecessorPermutation
    {N : ℕ} (r : Fin N → Fin N → Prop)
    (hirr : ∀ i, ¬ r i i)
    (htrans : ∀ i j k, r i j → r j k → r i k)
    (htotal : ∀ i j, r i j ∨ i = j ∨ r j i) :
    Equiv.Perm (Fin N) :=
  let f : Fin N → Fin N :=
    fun i => ⟨predecessorRank r i, predecessorRank_lt_card hirr i⟩
  have hfi : Function.Injective f := by
    intro i j h
    exact predecessorRank_injective hirr htrans htotal
      (congrArg Fin.val h)
  Equiv.ofBijective f ⟨hfi, Finite.surjective_of_injective hfi⟩

private lemma predecessorRank_relabel
    {N : ℕ} (r : Fin N → Fin N → Prop)
    (σ : Equiv.Perm (Fin N)) (i : Fin N) :
    predecessorRank (fun a b => r (σ a) (σ b)) i =
      predecessorRank r (σ i) := by
  classical
  unfold predecessorRank
  exact Finset.card_equiv σ (by intro j; simp)

/-- Explicit lexicographic comparison, using the ordinary product measurable space. -/
def KeyLT {N : ℕ} (z : Fin N → ℝ × ℝ) (i j : Fin N) : Prop :=
  (z i).1 < (z j).1 ∨
    (z i).1 = (z j).1 ∧ (z i).2 < (z j).2

private lemma keyLT_irrefl {N : ℕ} (z : Fin N → ℝ × ℝ) :
    ∀ i, ¬ KeyLT z i i := by
  intro i
  simp [KeyLT]

private lemma keyLT_trans {N : ℕ} (z : Fin N → ℝ × ℝ) :
    ∀ i j k, KeyLT z i j → KeyLT z j k → KeyLT z i k := by
  intro i j k hij hjk
  rcases hij with hij | ⟨hij, hij'⟩
  · rcases hjk with hjk | ⟨hjk, hjk'⟩
    · exact Or.inl (lt_trans hij hjk)
    · left
      linarith
  · rcases hjk with hjk | ⟨hjk, hjk'⟩
    · left
      linarith
    · exact Or.inr ⟨hij.trans hjk, lt_trans hij' hjk'⟩

private lemma keyLT_total {N : ℕ} (z : Fin N → ℝ × ℝ)
    (hz : Function.Injective z) :
    ∀ i j, KeyLT z i j ∨ i = j ∨ KeyLT z j i := by
  intro i j
  rcases lt_trichotomy (z i).1 (z j).1 with h | h | h
  · exact Or.inl (Or.inl h)
  · rcases lt_trichotomy (z i).2 (z j).2 with h' | h' | h'
    · exact Or.inl (Or.inr ⟨h, h'⟩)
    · exact Or.inr (Or.inl (hz (Prod.ext h h')))
    · exact Or.inr (Or.inr (Or.inr ⟨h.symm, h'⟩))
  · exact Or.inr (Or.inr (Or.inl h))

/-- One-based rank of an enhanced score key. -/
def keyRank {N : ℕ} (z : Fin N → ℝ × ℝ) (i : Fin N) : ℕ :=
  predecessorRank (KeyLT z) i + 1

private def keyPermutation {N : ℕ} (z : Fin N → ℝ × ℝ)
    (hz : Function.Injective z) : Equiv.Perm (Fin N) :=
  predecessorPermutation (KeyLT z)
    (keyLT_irrefl z) (keyLT_trans z) (keyLT_total z hz)

private lemma keyPermutation_val {N : ℕ}
    (z : Fin N → ℝ × ℝ) (hz : Function.Injective z) (i : Fin N) :
    (keyPermutation z hz i).val = predecessorRank (KeyLT z) i :=
  rfl

private lemma keyRank_relabel {N : ℕ}
    (z : Fin N → ℝ × ℝ) (σ : Equiv.Perm (Fin N)) (i : Fin N) :
    keyRank (fun j => z (σ j)) i = keyRank z (σ i) := by
  unfold keyRank
  exact congrArg (fun a : ℕ => a + 1)
    (predecessorRank_relabel (KeyLT z) σ i)

private def calibrationKeys {n : ℕ} (s : Fin n → ℝ) :
    Fin n → ℝ × ℝ :=
  fun i => (s i, (i.val : ℝ))

private lemma calibrationKeys_injective {n : ℕ} (s : Fin n → ℝ) :
    Function.Injective (calibrationKeys s) := by
  intro i j h
  apply Fin.ext
  have hv := congrArg Prod.snd h
  change (i.val : ℝ) = (j.val : ℝ) at hv
  exact_mod_cast hv

/-- An ordering of all calibration indices; equal scores remain separate indices. -/
def calibrationOrder {n : ℕ} (s : Fin n → ℝ) : Equiv.Perm (Fin n) :=
  keyPermutation (calibrationKeys s) (calibrationKeys_injective s)

private lemma calibrationOrder_monotone {n : ℕ} (s : Fin n → ℝ) :
    Monotone (fun j => s ((calibrationOrder s).symm j)) := by
  intro a b hab
  by_contra! hgt
  let z := calibrationKeys s
  let e := calibrationOrder s
  have hkey : KeyLT z (e.symm b) (e.symm a) := Or.inl hgt
  have hr := predecessorRank_lt (keyLT_irrefl z) (keyLT_trans z) hkey
  have ha := congrArg Fin.val (e.apply_symm_apply a)
  have hb := congrArg Fin.val (e.apply_symm_apply b)
  change predecessorRank (KeyLT z) (e.symm a) = a.val at ha
  change predecessorRank (KeyLT z) (e.symm b) = b.val at hb
  have hab' : a.val ≤ b.val := hab
  omega

/-- The ordinary kth calibration order statistic, retaining multiplicity. -/
def calibrationQuantile {n : ℕ} (s : Fin n → ℝ)
    (k : ℕ) (hk0 : 0 < k) (hkn : k ≤ n) : ℝ :=
  s ((calibrationOrder s).symm ⟨k - 1, by omega⟩)

/--
The inverse ordering enumerates every calibration index exactly once and has
nondecreasing scores. Rank ≤ k implies coverage by the raw kth calibration score.
No distinctness assumption is needed for this coverage implication.
-/
theorem rank_order_statistic_core
    {n : ℕ} (z : Fin (n + 1) → ℝ × ℝ)
    (k : ℕ) (hk0 : 0 < k) (hkn : k ≤ n) :
    Monotone
        (fun j =>
          (z (((calibrationOrder
            (fun i : Fin n => (z i.castSucc).1)).symm j).castSucc)).1) ∧
      (keyRank z (Fin.last n) ≤ k →
        (z (Fin.last n)).1 ≤
          calibrationQuantile (fun i : Fin n => (z i.castSucc).1) k hk0 hkn) := by
  classical
  let s : Fin n → ℝ := fun i => (z i.castSucc).1
  let e := calibrationOrder s
  refine ⟨calibrationOrder_monotone s, ?_⟩
  intro hr
  by_contra! hgt
  let qidx : Fin n := ⟨k - 1, by omega⟩
  let incl : Fin k → Fin n := fun j => ⟨j.val, lt_of_lt_of_le j.isLt hkn⟩
  let f : Fin k → Fin (n + 1) := fun j => (e.symm (incl j)).castSucc
  have hf (j : Fin k) : KeyLT z (f j) (Fin.last n) := by
    left
    have hjq : incl j ≤ qidx := by
      change j.val ≤ k - 1
      omega
    have hs := calibrationOrder_monotone s hjq
    change s (e.symm (incl j)) < (z (Fin.last n)).1
    exact lt_of_le_of_lt hs hgt
  have hfinj : Function.Injective f := by
    intro i j hij
    apply Fin.ext
    have hv := congrArg Fin.val hij
    have he : e.symm (incl i) = e.symm (incl j) := Fin.ext hv
    exact congrArg (fun a : Fin n => a.val) (e.symm.injective he)
  have hc : k ≤ predecessorRank (KeyLT z) (Fin.last n) := by
    have hh := Finset.card_le_card_of_injOn f
      (s := Finset.univ)
      (t := Finset.univ.filter fun a => KeyLT z a (Fin.last n))
      (by
        intro j hj
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hf j⟩)
      (by
        intro i hi j hj hij
        exact hfinj hij)
    simpa [predecessorRank] using hh
  unfold keyRank at hr
  omega

private lemma measurable_keyRank {N : ℕ} (i : Fin N) :
    Measurable (fun z : Fin N → ℝ × ℝ => keyRank z i) := by
  classical
  have hm (j : Fin N) :
      Measurable
        (fun z : Fin N → ℝ × ℝ =>
          if KeyLT z j i then (1 : ℕ) else 0) := by
    have hfirst (a : Fin N) :
        Measurable (fun z : Fin N → ℝ × ℝ => (z a).1) :=
      measurable_fst.comp (measurable_pi_apply a)
    have hsecond (a : Fin N) :
        Measurable (fun z : Fin N → ℝ × ℝ => (z a).2) :=
      measurable_snd.comp (measurable_pi_apply a)
    have hs : MeasurableSet {z : Fin N → ℝ × ℝ | KeyLT z j i} := by
      change MeasurableSet {z : Fin N → ℝ × ℝ |
        (z j).1 < (z i).1 ∨ (z j).1 = (z i).1 ∧ (z j).2 < (z i).2}
      exact (measurableSet_lt (hfirst j) (hfirst i)).union
        ((measurableSet_eq_fun (hfirst j) (hfirst i)).inter
          (measurableSet_lt (hsecond j) (hsecond i)))
    exact measurable_const.ite hs measurable_const
  have hsum :=
    (Finset.measurable_sum Finset.univ (fun j _ => hm j)).add_const 1
  simpa only [keyRank, predecessorRank,
    Finset.card_eq_sum_ones, Finset.sum_filter] using hsum

/-- Fixed measurable scoring transports the entire vector permutation law. -/
private lemma score_vector_exchangeable
    {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    {N : ℕ} (μ : Measure Ω) (X : Ω → Fin N → E)
    (score : E → ℝ) (hscore : Measurable score)
    (hex : ∀ σ : Equiv.Perm (Fin N),
      IdentDistrib (fun ω i => X ω (σ i)) X μ μ) :
    ∀ σ : Equiv.Perm (Fin N),
      IdentDistrib
        (fun ω i => score (X ω (σ i)))
        (fun ω i => score (X ω i)) μ μ := by
  intro σ
  simpa only [Function.comp_def] using
    (hex σ).comp
      (measurable_pi_lambda
        (fun x : Fin N → E => fun i => score (x i))
        (fun i => hscore.comp (measurable_pi_apply i)))

/--
Actual vector permutation law gives equal probabilities for corresponding
rank events. Uniform rank is not a hypothesis.
-/
private lemma rank_event_relabel
    {Ω : Type*} [MeasurableSpace Ω] {N : ℕ}
    (μ : Measure Ω) (Z : Ω → Fin N → ℝ × ℝ)
    (hex : ∀ σ : Equiv.Perm (Fin N),
      IdentDistrib (fun ω i => Z ω (σ i)) Z μ μ)
    (σ : Equiv.Perm (Fin N)) (i : Fin N) (j : ℕ) :
    μ {ω | keyRank (Z ω) (σ i) = j} =
      μ {ω | keyRank (Z ω) i = j} := by
  have h := (hex σ).comp (measurable_keyRank i)
  have hp := h.measure_mem_eq (measurableSet_singleton j)
  change
    μ {ω | keyRank (fun a => Z ω (σ a)) i = j} =
      μ {ω | keyRank (Z ω) i = j} at hp
  simpa only [keyRank_relabel] using hp/-!
Second segment, CI_NOT_RUN.

The auxiliary law is constructed, rather than supplied as a uniform-rank
hypothesis. The score vector is only exchangeable.
-/

def auxiliaryBase : Measure ℝ :=
  volume.restrict (Set.Ioc 0 1)

private instance auxiliaryBase_probability :
    IsProbabilityMeasure auxiliaryBase :=
  ⟨by simp [auxiliaryBase]⟩

private instance auxiliaryBase_noAtoms : NoAtoms auxiliaryBase := by
  unfold auxiliaryBase
  infer_instance

def iidAuxLaw (N : ℕ) : Measure (Fin N → ℝ) :=
  Measure.pi (fun _ => auxiliaryBase)

private instance iidAuxLaw_probability (N : ℕ) :
    IsProbabilityMeasure (iidAuxLaw N) := by
  unfold iidAuxLaw
  infer_instance

def augmentedScore {Ω : Type*} {N : ℕ}
    (S : Ω → Fin N → ℝ) (p : Ω × (Fin N → ℝ)) :
    Fin N → ℝ × ℝ :=
  fun i => (S p.1 i, p.2 i)

private lemma measurable_augmentedScore
    {Ω : Type*} [MeasurableSpace Ω] {N : ℕ}
    {S : Ω → Fin N → ℝ} (hS : Measurable S) :
    Measurable (augmentedScore S) :=
  measurable_pi_lambda _ fun i =>
    ((measurable_pi_apply i).comp (hS.comp measurable_fst)).prodMk
      ((measurable_pi_apply i).comp measurable_snd)

private lemma measurable_reindex {N : ℕ} (σ : Equiv.Perm (Fin N)) :
    Measurable (fun u : Fin N → ℝ => fun i => u (σ i)) :=
  measurable_pi_lambda _ fun i => measurable_pi_apply (σ i)

private lemma iidAux_reindex {N : ℕ} (σ : Equiv.Perm (Fin N)) :
    (iidAuxLaw N).map (fun u i => u (σ i)) = iidAuxLaw N := by
  simpa [iidAuxLaw, MeasurableEquiv.piCongrLeft,
    Equiv.piCongrLeft, Equiv.piCongrLeft'] using
    (Measure.pi_map_piCongrLeft σ.symm
      (fun _ : Fin N => auxiliaryBase))

private lemma iidAux_independent (N : ℕ) :
    iIndepFun (fun i : Fin N => fun u : Fin N → ℝ => u i)
      (iidAuxLaw N) := by
  exact iIndepFun_pi
    (μ := fun _ : Fin N => auxiliaryBase)
    (X := fun _ : Fin N => id)
    (fun _ => measurable_id.aemeasurable)

private lemma iidAux_pair_ne {N : ℕ} {i j : Fin N} (hij : i ≠ j) :
    ∀ᵐ u ∂iidAuxLaw N, u i ≠ u j := by
  have hind := (iidAux_independent N).indepFun hij
  have hmap :
      (iidAuxLaw N).map (fun u => (u i, u j)) =
        auxiliaryBase.prod auxiliaryBase := by
    rw [hind.map_prod_eq_prod_map_map
      (measurable_pi_apply i).aemeasurable
      (measurable_pi_apply j).aemeasurable]
    change
      ((Measure.pi (fun _ : Fin N => auxiliaryBase)).map
        (Function.eval i)).prod
      ((Measure.pi (fun _ : Fin N => auxiliaryBase)).map
        (Function.eval j)) = _
    rw [(measurePreserving_eval
      (fun _ : Fin N => auxiliaryBase) i).map_eq,
      (measurePreserving_eval
        (fun _ : Fin N => auxiliaryBase) j).map_eq]
  have hd : MeasurableSet {p : ℝ × ℝ | p.1 = p.2} :=
    measurableSet_eq_fun measurable_fst measurable_snd
  have hdiag :
      auxiliaryBase.prod auxiliaryBase {p : ℝ × ℝ | p.1 = p.2} = 0 := by
    rw [Measure.prod_apply hd]
    have hsection (x : ℝ) :
        auxiliaryBase (Prod.mk x ⁻¹' {p : ℝ × ℝ | p.1 = p.2}) = 0 := by
      have hs :
          Prod.mk x ⁻¹' {p : ℝ × ℝ | p.1 = p.2} = {x} := by
        ext y
        simp [eq_comm]
      rw [hs, measure_singleton]
    simp_rw [hsection]
    simp
  have hnull :
      iidAuxLaw N {u : Fin N → ℝ | u i = u j} = 0 := by
    rw [← hmap, Measure.map_apply
      ((measurable_pi_apply i).prodMk (measurable_pi_apply j)) hd] at hdiag
    exact hdiag
  apply ae_iff.mpr
  simpa only [not_not] using hnull

private lemma iidAux_injective (N : ℕ) :
    ∀ᵐ u ∂iidAuxLaw N, Function.Injective u := by
  have hpair (i j : Fin N) :
      ∀ᵐ u ∂iidAuxLaw N, u i = u j → i = j := by
    by_cases hij : i = j
    · exact Filter.Eventually.of_forall (fun _ _ => hij)
    · filter_upwards [iidAux_pair_ne hij] with u hu
      exact fun h => False.elim (hu h)
  exact ae_all_iff.mpr fun i => ae_all_iff.mpr fun j => hpair i j

private lemma augmented_injective_ae
    {Ω : Type*} [MeasurableSpace Ω] {N : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (S : Ω → Fin N → ℝ) (hS : Measurable S) :
    ∀ᵐ p ∂μ.prod (iidAuxLaw N),
      Function.Injective (augmentedScore S p) := by
  have hm :
      MeasurableSet
        {p : Ω × (Fin N → ℝ) |
          Function.Injective (augmentedScore S p)} := by
    apply measurableSet_setOf.mpr
    unfold Function.Injective
    have hZ := measurable_augmentedScore hS
    fun_prop
  apply (Measure.ae_prod_iff_ae_ae hm).mpr
  exact Filter.Eventually.of_forall fun ω =>
    (iidAux_injective N).mono fun u hu i j hij =>
      hu (congrArg Prod.snd hij)

private lemma augmented_exchangeable
    {Ω : Type*} [MeasurableSpace Ω] {N : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (S : Ω → Fin N → ℝ) (hS : Measurable S)
    (hex : ∀ σ : Equiv.Perm (Fin N),
      IdentDistrib (fun ω i => S ω (σ i)) S μ μ) :
    ∀ σ : Equiv.Perm (Fin N),
      IdentDistrib
        (fun p i => augmentedScore S p (σ i))
        (augmentedScore S)
        (μ.prod (iidAuxLaw N)) (μ.prod (iidAuxLaw N)) := by
  intro σ
  let Sσ : Ω → Fin N → ℝ := fun ω i => S ω (σ i)
  let Uσ : (Fin N → ℝ) → Fin N → ℝ := fun u i => u (σ i)
  have hSσ : Measurable Sσ :=
    (measurable_reindex σ).comp hS
  have hUσ : Measurable Uσ := measurable_reindex σ
  have hpair :
      IdentDistrib (Prod.map Sσ Uσ) (Prod.map S id)
        (μ.prod (iidAuxLaw N)) (μ.prod (iidAuxLaw N)) := by
    refine ⟨(hSσ.prodMap hUσ).aemeasurable,
      (hS.prodMap measurable_id).aemeasurable, ?_⟩
    rw [← Measure.map_prod_map μ (iidAuxLaw N) hSσ hUσ,
      ← Measure.map_prod_map μ (iidAuxLaw N) hS measurable_id]
    rw [(hex σ).map_eq, iidAux_reindex σ, Measure.map_id]
  have hzip :
      Measurable
        (fun p : (Fin N → ℝ) × (Fin N → ℝ) =>
          fun i => (p.1 i, p.2 i)) :=
    measurable_pi_lambda _ fun i =>
      ((measurable_pi_apply i).comp measurable_fst).prodMk
        ((measurable_pi_apply i).comp measurable_snd)
  simpa [augmentedScore, Sσ, Uσ, Function.comp_def, Prod.map] using
    hpair.comp hzip

/- The finite probability calculation uses the actual full-measure rank permutation. -/
private lemma rank_point_probability
    {Ω : Type*} [MeasurableSpace Ω] {N : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (hN : 0 < N)
    (Z : Ω → Fin N → ℝ × ℝ) (hZ : Measurable Z)
    (hex : ∀ σ : Equiv.Perm (Fin N),
      IdentDistrib (fun ω i => Z ω (σ i)) Z μ μ)
    (hz : ∀ᵐ ω ∂μ, Function.Injective (Z ω))
    (i j : Fin N) :
    μ {ω | keyRank (Z ω) i = j.val + 1} =
      1 / (N : ℝ≥0∞) := by
  classical
  let G : Set Ω := {ω | Function.Injective (Z ω)}
  let E : Fin N → Set Ω :=
    fun a => G ∩ {ω | keyRank (Z ω) a = j.val + 1}
  have hmG : MeasurableSet G := by
    apply measurableSet_setOf.mpr
    unfold Function.Injective
    fun_prop
  have hm (a : Fin N) : MeasurableSet (E a) :=
    hmG.inter
      (((measurable_keyRank a).comp hZ)
        (measurableSet_singleton (j.val + 1)))
  have hG : μ G = 1 := by
    calc
      μ G = μ Set.univ := measure_congr (by
        filter_upwards [hz] with ω hω
        change Function.Injective (Z ω) ↔ True
        exact ⟨fun _ => True.intro, fun _ => hω⟩)
      _ = 1 := measure_univ
  have hE (a : Fin N) :
      μ (E a) = μ {ω | keyRank (Z ω) a = j.val + 1} :=
    measure_congr (by
      filter_upwards [hz] with ω hω
      change (Function.Injective (Z ω) ∧ keyRank (Z ω) a = j.val + 1) ↔
        keyRank (Z ω) a = j.val + 1
      exact ⟨fun h => h.2, fun h => ⟨hω, h⟩⟩)
  have hdisj :
      Set.PairwiseDisjoint
        (↑(Finset.univ : Finset (Fin N))) E := by
    intro a ha b hb hab
    apply Set.disjoint_left.mpr
    intro ω hωa hωb
    have hinj := predecessorRank_injective
      (keyLT_irrefl (Z ω)) (keyLT_trans (Z ω))
      (keyLT_total (Z ω) hωa.1)
    apply hab
    apply hinj
    have h1 := hωa.2
    have h2 := hωb.2
    unfold keyRank at h1 h2
    omega
  have hunion : (⋃ a : Fin N, E a) = G := by
    ext ω
    constructor
    · intro hω
      obtain ⟨a, ha⟩ := Set.mem_iUnion.mp hω
      exact ha.1
    · intro hω
      let e := keyPermutation (Z ω) hω
      refine Set.mem_iUnion.mpr ⟨e.symm j, hω, ?_⟩
      have hv := congrArg Fin.val (e.apply_symm_apply j)
      change predecessorRank (KeyLT (Z ω)) (e.symm j) = j.val at hv
      change predecessorRank (KeyLT (Z ω)) (e.symm j) + 1 = j.val + 1
      exact congrArg (fun r : ℕ => r + 1) hv
  have hsum :
      (∑ a : Fin N, μ {ω | keyRank (Z ω) a = j.val + 1}) = 1 := by
    calc
      _ = ∑ a : Fin N, μ (E a) :=
        Finset.sum_congr rfl (fun a _ => (hE a).symm)
      _ = μ G := by
        simpa [hunion] using
          (measure_biUnion_finset hdisj (fun a _ => hm a)).symm
      _ = 1 := hG
  have he (a : Fin N) :
      μ {ω | keyRank (Z ω) a = j.val + 1} =
        μ {ω | keyRank (Z ω) i = j.val + 1} := by
    simpa using
      rank_event_relabel μ Z hex (Equiv.swap i a) i (j.val + 1)
  simp_rw [he] at hsum
  have hmul :
      (N : ℝ≥0∞) * μ {ω | keyRank (Z ω) i = j.val + 1} = 1 := by
    simpa [nsmul_eq_mul] using hsum
  exact (ENNReal.eq_div_iff
    (by exact_mod_cast hN.ne') (by simp)).mpr hmul

private lemma rank_prefix_probability
    {Ω : Type*} [MeasurableSpace Ω] {N : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (hN : 0 < N)
    (Z : Ω → Fin N → ℝ × ℝ) (hZ : Measurable Z)
    (hex : ∀ σ : Equiv.Perm (Fin N),
      IdentDistrib (fun ω i => Z ω (σ i)) Z μ μ)
    (hz : ∀ᵐ ω ∂μ, Function.Injective (Z ω))
    (i : Fin N) (k : ℕ) (hk : k ≤ N) :
    μ {ω | keyRank (Z ω) i ≤ k} = (k : ℝ≥0∞) / N := by
  classical
  let R : Ω → ℕ := fun ω => keyRank (Z ω) i
  have hR : Measurable R := (measurable_keyRank i).comp hZ
  have hpre :
      R ⁻¹' ↑(Finset.Icc 1 k) = {ω | R ω ≤ k} := by
    ext ω
    have hp : 1 ≤ R ω := by
      dsimp [R, keyRank]
      omega
    simp only [Set.mem_preimage, Finset.mem_coe, Finset.mem_Icc,
      Set.mem_setOf_eq]
    omega
  have hu (a : ℕ) (ha : a ∈ Finset.Icc 1 k) :
      μ (R ⁻¹' {a}) = 1 / (N : ℝ≥0∞) := by
    obtain ⟨ha0, hak⟩ := Finset.mem_Icc.mp ha
    let j : Fin N := ⟨a - 1, by omega⟩
    have hj : j.val + 1 = a := by
      dsimp [j]
      omega
    simpa [R, hj] using rank_point_probability μ hN Z hZ hex hz i j
  calc
    μ {ω | R ω ≤ k} =
        ∑ a ∈ Finset.Icc 1 k, μ (R ⁻¹' {a}) := by
      rw [← hpre]
      exact (sum_measure_preimage_singleton (Finset.Icc 1 k)
        (fun a _ => hR (measurableSet_singleton a))).symm
    _ = ∑ _a ∈ Finset.Icc 1 k, 1 / (N : ℝ≥0∞) :=
      Finset.sum_congr rfl hu
    _ = (k : ℝ≥0∞) / N := by
      simp [nsmul_eq_mul, div_eq_mul_inv]

/--
Under the constructed independent iid continuous auxiliary law, every actual
test-rank prefix has probability k/N. The score vector only needs exchangeability.
-/
theorem iid_auxiliary_rank_prefix
    {Ω : Type*} [MeasurableSpace Ω] {N : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (hN : 0 < N)
    (S : Ω → Fin N → ℝ) (hS : Measurable S)
    (hex : ∀ σ : Equiv.Perm (Fin N),
      IdentDistrib (fun ω i => S ω (σ i)) S μ μ)
    (i : Fin N) (k : ℕ) (hk : k ≤ N) :
    μ.prod (iidAuxLaw N)
      {p | keyRank (augmentedScore S p) i ≤ k} =
        (k : ℝ≥0∞) / N :=
  rank_prefix_probability (μ.prod (iidAuxLaw N)) hN
    (augmentedScore S) (measurable_augmentedScore hS)
    (augmented_exchangeable μ S hS hex)
    (augmented_injective_ae μ S hS) i k hk

private lemma measurable_calibrationQuantile
    {n : ℕ} (k : ℕ) (hk0 : 0 < k) (hkn : k ≤ n) :
    Measurable (fun s : Fin n → ℝ => calibrationQuantile s k hk0 hkn) := by
  classical
  have hz : Measurable (fun s : Fin n → ℝ => calibrationKeys s) :=
    measurable_pi_lambda _ fun i =>
      (measurable_pi_apply i).prodMk measurable_const
  have hrep (s : Fin n → ℝ) :
      calibrationQuantile s k hk0 hkn =
        ∑ i : Fin n,
          if keyRank (calibrationKeys s) i = k then s i else 0 := by
    let qidx : Fin n := ⟨k - 1, by omega⟩
    let e := calibrationOrder s
    let a := e.symm qidx
    have ha : keyRank (calibrationKeys s) a = k := by
      have hv := congrArg Fin.val (e.apply_symm_apply qidx)
      change predecessorRank (KeyLT (calibrationKeys s)) a = qidx.val at hv
      dsimp [qidx] at hv
      unfold keyRank
      omega
    have hother (b : Fin n) (hba : b ≠ a) :
        keyRank (calibrationKeys s) b ≠ k := by
      intro hb
      have hinj := predecessorRank_injective
        (keyLT_irrefl (calibrationKeys s))
        (keyLT_trans (calibrationKeys s))
        (keyLT_total (calibrationKeys s) (calibrationKeys_injective s))
      apply hba
      apply hinj
      unfold keyRank at ha hb
      omega
    symm
    calc
      _ = (if keyRank (calibrationKeys s) a = k then s a else 0) := by
        apply Finset.sum_eq_single a
        · intro b hb hba
          simp [hother b hba]
        · simp
      _ = calibrationQuantile s k hk0 hkn := by
        simp [ha, calibrationQuantile, a, e, qidx]
  rw [show
    (fun s : Fin n → ℝ => calibrationQuantile s k hk0 hkn) =
      (fun s => ∑ i : Fin n,
        if keyRank (calibrationKeys s) i = k then s i else 0)
    from funext hrep]
  apply Finset.measurable_sum
  intro i hi
  exact (measurable_pi_apply i).ite
    (((measurable_keyRank i).comp hz) (measurableSet_singleton k))
    measurable_const

def conformalIndex (n : ℕ) (α : ℝ) : ℕ :=
  Nat.ceil (((n + 1 : ℕ) : ℝ) * (1 - α))

private lemma conformalIndex_pos (n : ℕ) {α : ℝ} (hα : α < 1) :
    0 < conformalIndex n α := by
  have hp : 0 < ((n + 1 : ℕ) : ℝ) * (1 - α) :=
    mul_pos (by positivity) (sub_pos.mpr hα)
  have h1 := Nat.one_le_ceil_iff.mpr hp
  change 0 < Nat.ceil (((n + 1 : ℕ) : ℝ) * (1 - α))
  omega

def conformalThreshold {n : ℕ} (s : Fin n → ℝ)
    (α : ℝ) (hα : α < 1) : WithTop ℝ :=
  if hk : conformalIndex n α ≤ n then
    (calibrationQuantile s (conformalIndex n α)
      (conformalIndex_pos n hα) hk : WithTop ℝ)
  else
    ⊤

private lemma ofReal_nat_ratio (k N : ℕ) (hN : 0 < N) :
    ENNReal.ofReal ((k : ℝ) / (N : ℝ)) =
      (k : ℝ≥0∞) / (N : ℝ≥0∞) := by
  apply (ENNReal.eq_div_iff
    (by exact_mod_cast hN.ne') (by simp)).mpr
  calc
    (N : ℝ≥0∞) * ENNReal.ofReal ((k : ℝ) / (N : ℝ)) =
        ENNReal.ofReal ((N : ℝ) * ((k : ℝ) / (N : ℝ))) := by
      rw [ENNReal.ofReal_mul (Nat.cast_nonneg N)]
      simp
    _ = (k : ℝ≥0∞) := by
      have hn0 : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
      have hr : (N : ℝ) * ((k : ℝ) / (N : ℝ)) = k := by
        field_simp [hn0]
      rw [hr]
      simp

/--
Fixed-training marginal split-conformal coverage. The finite branch retains the
sharper k/(n+1) bound; the top branch has actual coverage probability one.
-/
theorem exchangeable_split_conformal_coverage
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (S : Ω → Fin (n + 1) → ℝ) (hS : Measurable S)
    (hex : ∀ σ : Equiv.Perm (Fin (n + 1)),
      IdentDistrib (fun ω i => S ω (σ i)) S μ μ)
    (hn : 1 ≤ n) (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1) :
    let k := conformalIndex n α
    let Q := μ.prod (iidAuxLaw (n + 1))
    let C : Set (Ω × (Fin (n + 1) → ℝ)) :=
      {p | (S p.1 (Fin.last n) : WithTop ℝ) ≤
        conformalThreshold (fun i : Fin n => S p.1 i.castSucc) α hα1}
    (1 - α ≤ (k : ℝ) / ((n + 1 : ℕ) : ℝ)) ∧
      MeasurableSet C ∧
      ENNReal.ofReal (1 - α) ≤ Q C ∧
      (k ≤ n → (k : ℝ≥0∞) / (n + 1 : ℕ) ≤ Q C) ∧
      (n < k → Q C = 1) := by
  classical
  let k := conformalIndex n α
  let Q := μ.prod (iidAuxLaw (n + 1))
  let C : Set (Ω × (Fin (n + 1) → ℝ)) :=
    {p | (S p.1 (Fin.last n) : WithTop ℝ) ≤
      conformalThreshold (fun i : Fin n => S p.1 i.castSucc) α hα1}
  change
    (1 - α ≤ (k : ℝ) / ((n + 1 : ℕ) : ℝ)) ∧
      MeasurableSet C ∧
      ENNReal.ofReal (1 - α) ≤ Q C ∧
      (k ≤ n → (k : ℝ≥0∞) / (n + 1 : ℕ) ≤ Q C) ∧
      (n < k → Q C = 1)
  have hk0 : 0 < k := conformalIndex_pos n hα1
  have hN : 0 < ((n + 1 : ℕ) : ℝ) := by positivity
  have hceil : 1 - α ≤ (k : ℝ) / ((n + 1 : ℕ) : ℝ) := by
    apply (le_div_iff₀ hN).mpr
    have hc := Nat.le_ceil (((n + 1 : ℕ) : ℝ) * (1 - α))
    change ((n + 1 : ℕ) : ℝ) * (1 - α) ≤ (k : ℝ) at hc
    nlinarith
  by_cases hk : k ≤ n
  · have hC :
        C = {p : Ω × (Fin (n + 1) → ℝ) |
          S p.1 (Fin.last n) ≤
            calibrationQuantile
              (fun i : Fin n => S p.1 i.castSucc) k hk0 hk} := by
      ext p
      simp [C, conformalThreshold, k, hk]
    have hmcal :
        Measurable
          (fun p : Ω × (Fin (n + 1) → ℝ) =>
            fun i : Fin n => S p.1 i.castSucc) :=
      measurable_pi_lambda _ fun i =>
        (measurable_pi_apply i.castSucc).comp (hS.comp measurable_fst)
    have hmC : MeasurableSet C := by
      rw [hC]
      exact measurableSet_le
        ((measurable_pi_apply (Fin.last n)).comp (hS.comp measurable_fst))
        ((measurable_calibrationQuantile k hk0 hk).comp hmcal)
    have hp := iid_auxiliary_rank_prefix μ (by omega)
      S hS hex (Fin.last n) k (by omega)
    have hinc :
        {p : Ω × (Fin (n + 1) → ℝ) |
          keyRank (augmentedScore S p) (Fin.last n) ≤ k} ⊆ C := by
      intro p hp
      rw [hC]
      exact (rank_order_statistic_core
        (augmentedScore S p) k hk0 hk).2 hp
    have hbound : (k : ℝ≥0∞) / (n + 1 : ℕ) ≤ Q C := by
      rw [← hp]
      exact measure_mono hinc
    have hcover : ENNReal.ofReal (1 - α) ≤ Q C := by
      apply (ENNReal.ofReal_le_ofReal hceil).trans
      rw [ofReal_nat_ratio k (n + 1) (by omega)]
      exact hbound
    refine ⟨hceil, hmC, hcover, fun _ => hbound, ?_⟩
    intro hlt
    omega
  · have hC : C = Set.univ := by
      ext p
      simp [C, conformalThreshold, k, hk]
    have hone : Q C = 1 := by
      rw [hC]
      exact measure_univ
    have hcover : ENNReal.ofReal (1 - α) ≤ Q C := by
      rw [hone]
      simpa using ENNReal.ofReal_le_ofReal
        (show 1 - α ≤ (1 : ℝ) by linarith)
    refine ⟨hceil, ?_, hcover, ?_, fun _ => hone⟩
    · rw [hC]
      exact MeasurableSet.univ
    · intro hkn
      exact False.elim (hk hkn)

/-- Fixed measurable scoring and elimination of the independent auxiliary law. -/
theorem scored_sample_split_conformal_coverage
    {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E] {n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → Fin (n + 1) → E) (hX : Measurable X)
    (score : E → ℝ) (hscore : Measurable score)
    (hex : ∀ σ : Equiv.Perm (Fin (n + 1)),
      IdentDistrib (fun ω i => X ω (σ i)) X μ μ)
    (hn : 1 ≤ n) (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1) :
    ENNReal.ofReal (1 - α) ≤
      μ {ω | (score (X ω (Fin.last n)) : WithTop ℝ) ≤
        conformalThreshold
          (fun i : Fin n => score (X ω i.castSucc)) α hα1} := by
  let S : Ω → Fin (n + 1) → ℝ := fun ω i => score (X ω i)
  have hS : Measurable S :=
    (measurable_pi_lambda
      (fun x : Fin (n + 1) → E => fun i => score (x i))
      (fun i => hscore.comp (measurable_pi_apply i))).comp hX
  have hsx := score_vector_exchangeable μ X score hscore hex
  have hfull := exchangeable_split_conformal_coverage
    μ S hS hsx hn α hα0 hα1
  let E₀ : Set Ω :=
    {ω | (S ω (Fin.last n) : WithTop ℝ) ≤
      conformalThreshold (fun i : Fin n => S ω i.castSucc) α hα1}
  let C : Set (Ω × (Fin (n + 1) → ℝ)) :=
    {p | (S p.1 (Fin.last n) : WithTop ℝ) ≤
      conformalThreshold (fun i : Fin n => S p.1 i.castSucc) α hα1}
  have hmC : MeasurableSet C := hfull.2.1
  have hmE : MeasurableSet E₀ := by
    have hmι : Measurable
        (fun ω : Ω => (ω, (0 : Fin (n + 1) → ℝ))) :=
      measurable_id.prodMk measurable_const
    simpa [E₀, C] using hmC.preimage hmι
  have hrect : C = E₀ ×ˢ Set.univ := by
    ext p
    simp [C, E₀]
  have hbound : ENNReal.ofReal (1 - α) ≤
      μ.prod (iidAuxLaw (n + 1)) C := hfull.2.2.1
  rw [hrect, Measure.prod_prod] at hbound
  simpa [E₀, S] using hbound

/-!
Original U05.1/05.4 negative boundaries only.
The n=1 threshold below is the existing calibrationQuantile/conformalThreshold,
not a replacement threshold. The source and deployment laws are actual PMFs.
-/

local instance boundaryBoolMeasurableSpace : MeasurableSpace Bool := ⊤

private lemma boundary_bool_univ :
    (Finset.univ : Finset Bool) = {false, true} := by decide

private lemma boundary_pair_univ :
    (Finset.univ : Finset (Bool × Bool)) =
      {(false, false), (false, true), (true, false), (true, true)} := by decide

private def boundaryWeight : Bool → Bool × Bool → ℝ≥0
  | false, (false, false) => 9 / 16
  | false, (false, true) => 3 / 16
  | false, (true, false) => 3 / 16
  | false, (true, true) => 1 / 16
  | true, (false, false) => 0
  | true, (false, true) => 3 / 4
  | true, (true, false) => 0
  | true, (true, true) => 1 / 4

private lemma boundaryWeight_sum (deployed : Bool) :
    (∑ z : Bool × Bool, (boundaryWeight deployed z : ℝ≥0∞)) = 1 := by
  have h : (∑ z : Bool × Bool, boundaryWeight deployed z) = (1 : ℝ≥0) := by
    cases deployed <;> norm_num [boundaryWeight, boundary_pair_univ]
  exact_mod_cast h

private def boundaryLaw (deployed : Bool) : PMF (Bool × Bool) :=
  PMF.ofFintype (fun z => (boundaryWeight deployed z : ℝ≥0∞))
    (boundaryWeight_sum deployed)

private def boundaryMeasure (deployed : Bool) : Measure (Bool × Bool) :=
  (boundaryLaw deployed).toMeasure

private def boundaryScore (z : Bool × Bool) : Fin 2 → ℝ :=
  fun i => if i = 0 then (if z.1 then 1 else 0) else (if z.2 then 1 else 0)

private lemma boundary_index : conformalIndex 1 (1 / 2 : ℝ) = 1 := by
  norm_num [conformalIndex]

private lemma boundary_quantile (s : Fin 1 → ℝ) :
    calibrationQuantile s 1 (by decide) (by decide) = s 0 := by
  unfold calibrationQuantile
  exact congrArg s (Subsingleton.elim _ _)

private lemma boundary_threshold (s : Fin 1 → ℝ) :
    conformalThreshold s (1 / 2 : ℝ) (by norm_num) = (s 0 : WithTop ℝ) := by
  simp only [conformalThreshold, boundary_index,
    dif_pos (show 1 ≤ 1 by decide)]
  exact congrArg (fun x : ℝ => (x : WithTop ℝ)) (boundary_quantile s)

private def boundaryCoverage : Set (Bool × Bool) :=
  {z | (boundaryScore z (Fin.last 1) : WithTop ℝ) ≤
    conformalThreshold (fun i : Fin 1 => boundaryScore z i.castSucc)
      (1 / 2 : ℝ) (by norm_num)}

private def boundaryGroup : Set (Bool × Bool) := {z | z.2 = true}
private def boundaryCalGroup : Set (Bool × Bool) := {z | z.1 = true}

private lemma boundaryCoverage_iff (z : Bool × Bool) :
    z ∈ boundaryCoverage ↔
      (if z.2 then (1 : ℝ) else 0) ≤ (if z.1 then (1 : ℝ) else 0) := by
  change
    ((boundaryScore z (Fin.last 1) : WithTop ℝ) ≤
      conformalThreshold (fun i : Fin 1 => boundaryScore z i.castSucc)
        (1 / 2 : ℝ) (by norm_num)) ↔ _
  rw [boundary_threshold]
  rcases z with ⟨a, b⟩
  cases a <;> cases b <;> norm_num [boundaryScore]

private lemma boundary_events_measurable :
    MeasurableSet boundaryCoverage ∧ MeasurableSet boundaryGroup ∧
      MeasurableSet boundaryCalGroup := by
  exact ⟨.of_discrete, .of_discrete, .of_discrete⟩

open scoped Classical in
private lemma boundary_event_mass (deployed : Bool)
    (E : Set (Bool × Bool)) (hE : MeasurableSet E) :
    boundaryMeasure deployed E =
      ∑ z : Bool × Bool,
        if z ∈ E then (boundaryWeight deployed z : ℝ≥0∞) else 0 := by
  simpa [boundaryMeasure, boundaryLaw, Set.indicator, tsum_fintype] using
    (PMF.toMeasure_ofFintype_apply (boundaryWeight_sum deployed) E hE)

private lemma boundary_source_independent_bernoulli :
    boundaryLaw false =
      (PMF.bernoulli (1 / 4 : ℝ≥0) (by norm_num)).bind
        (fun a => (PMF.bernoulli (1 / 4 : ℝ≥0) (by norm_num)).map
          (fun b => (a, b))) := by
  ext z
  rw [PMF.bind_apply]
  simp only [PMF.map_apply, tsum_fintype]
  rcases z with ⟨a, b⟩
  cases a <;> cases b <;>
    norm_num [boundaryLaw, boundaryWeight, boundary_bool_univ,
      PMF.bernoulli_apply, ← ENNReal.coe_sub]
  all_goals
    apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
    simp (disch := finiteness) [ENNReal.toReal_add] <;> norm_num

private lemma boundary_source_exchangeable :
    (boundaryLaw false).map Prod.swap = boundaryLaw false := by
  ext z
  rw [PMF.map_apply, tsum_fintype]
  rcases z with ⟨a, b⟩
  cases a <;> cases b <;>
    norm_num [boundaryLaw, boundaryWeight, boundary_pair_univ]
  all_goals
    apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
    simp (disch := finiteness) [ENNReal.toReal_add] <;> norm_num

private lemma boundary_deployment_not_exchangeable :
    (boundaryLaw true).map Prod.swap ≠ boundaryLaw true := by
  intro h
  have hv := congrArg (fun p : PMF (Bool × Bool) => p (false, true)) h
  simp only [PMF.map_apply, tsum_fintype] at hv
  norm_num [boundaryLaw, boundaryWeight, boundary_pair_univ] at hv
  all_goals
    have hvReal := congrArg ENNReal.toReal hv
    simp (disch := finiteness) [ENNReal.toReal_add] at hvReal
    norm_num at hvReal

private lemma boundary_actual_masses :
    boundaryMeasure false boundaryCoverage = (13 / 16 : ℝ≥0∞) ∧
      boundaryMeasure false boundaryGroup = (1 / 4 : ℝ≥0∞) ∧
      boundaryMeasure false boundaryCalGroup = (1 / 4 : ℝ≥0∞) ∧
      boundaryMeasure true boundaryCalGroup = (1 / 4 : ℝ≥0∞) ∧
      boundaryMeasure true boundaryGroup = (1 : ℝ≥0∞) ∧
      boundaryMeasure true boundaryCoverage = (1 / 4 : ℝ≥0∞) ∧
      boundaryMeasure false (boundaryGroup ∩ boundaryCoverage) = (1 / 16 : ℝ≥0∞) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals
    rw [boundary_event_mass _ _ (by exact .of_discrete)]
    norm_num [boundary_pair_univ, boundaryWeight, boundaryGroup,
      boundaryCalGroup, Set.mem_inter_iff, boundaryCoverage_iff]
    all_goals
      apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
      simp (disch := finiteness) [ENNReal.toReal_add] <;> norm_num

/--
Original finite negative boundaries: marginal coverage does not imply group
coverage, and changing only the deployment test law can break marginal coverage.
The coverage event uses the existing n=1 split-conformal threshold.
-/
theorem finite_group_and_deployment_boundaries :
    conformalIndex 1 (1 / 2 : ℝ) = 1 ∧
      (∀ s : Fin 1 → ℝ,
        calibrationQuantile s 1 (by decide) (by decide) = s 0) ∧
      boundaryLaw false =
        (PMF.bernoulli (1 / 4 : ℝ≥0) (by norm_num)).bind
          (fun a => (PMF.bernoulli (1 / 4 : ℝ≥0) (by norm_num)).map
            (fun b => (a, b))) ∧
      (boundaryLaw false).map Prod.swap = boundaryLaw false ∧
      (boundaryMeasure false boundaryCoverage = (13 / 16 : ℝ≥0∞) ∧
        (1 / 2 : ℝ≥0∞) ≤ boundaryMeasure false boundaryCoverage) ∧
      (boundaryMeasure false boundaryGroup = (1 / 4 : ℝ≥0∞) ∧
        0 < boundaryMeasure false boundaryGroup ∧
        ProbabilityTheory.cond (boundaryMeasure false) boundaryGroup boundaryCoverage =
          (1 / 4 : ℝ≥0∞) ∧
        ProbabilityTheory.cond (boundaryMeasure false) boundaryGroup boundaryCoverage <
          (1 / 2 : ℝ≥0∞)) ∧
      (boundaryMeasure true boundaryCalGroup = boundaryMeasure false boundaryCalGroup ∧
        boundaryMeasure false boundaryCalGroup = (1 / 4 : ℝ≥0∞) ∧
        boundaryMeasure true boundaryGroup = 1 ∧
        boundaryMeasure true boundaryCoverage = (1 / 4 : ℝ≥0∞) ∧
        boundaryMeasure true boundaryCoverage < (1 / 2 : ℝ≥0∞)) ∧
      (boundaryLaw true).map Prod.swap ≠ boundaryLaw true := by
  obtain ⟨hcoverage, hgroup, hcal, hdeployCal, hdeployGroup, hdeployCoverage, hinter⟩ :=
    boundary_actual_masses
  have hcond :
      ProbabilityTheory.cond (boundaryMeasure false) boundaryGroup boundaryCoverage =
        (1 / 4 : ℝ≥0∞) := by
    rw [ProbabilityTheory.cond_apply boundary_events_measurable.2.1
      (boundaryMeasure false), hgroup, hinter]
    norm_num
    all_goals
      apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
      simp (disch := finiteness) [ENNReal.toReal_add] <;> norm_num
  refine ⟨boundary_index, boundary_quantile, boundary_source_independent_bernoulli,
    boundary_source_exchangeable, ⟨hcoverage, ?_⟩,
    ⟨hgroup, ?_, hcond, ?_⟩,
    ⟨hdeployCal.trans hcal.symm, hcal, hdeployGroup, hdeployCoverage, ?_⟩,
    boundary_deployment_not_exchangeable⟩
  · rw [hcoverage]
    apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
    norm_num
  · rw [hgroup]
    apply (ENNReal.toReal_lt_toReal (by finiteness) (by finiteness)).mp
    norm_num
  · rw [hcond]
    apply (ENNReal.toReal_lt_toReal (by finiteness) (by finiteness)).mp
    norm_num
  · rw [hdeployCoverage]
    apply (ENNReal.toReal_lt_toReal (by finiteness) (by finiteness)).mp
    norm_num
end JurisLean.Candidates.ExchangeableRank20261031
