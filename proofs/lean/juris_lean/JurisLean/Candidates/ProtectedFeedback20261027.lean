import JurisLean.Candidates.EventFeedbackConsumer20261027

/-!
Original 13/S14 and E14: actual validation loss on every declared protected
domain. The predeclared finite class includes the parent. Each domain pays its
own budget and uses its own sample size. Within-domain iid laws are explicit;
the joint theorem does not assume independence between protected domains.

The existing rational radius verifier is conservative by a factor two in the
class count. No observed identity, snapshot or protocol identifier proves iid,
correct labels, causal support, legal authority, or actual model loading.
-/

namespace JurisLean.Candidates.ProtectedFeedback20261027

open MeasureTheory ProbabilityTheory
open JurisLean.Candidates.Final20261021
open JurisLean.Candidates.LearningFiniteClass20261027
open JurisLean.Candidates.LearningERM20261027
open JurisLean.Candidates.LearningConsumer20261027
open JurisLean.Candidates.SampleCalibrationConsumer20261027
open JurisLean.Candidates.EventFeedbackConsumer20261027

-- A fixed class can be searched after seeing the validation data only with the
-- budget for that entire fixed class. Changing the class changes the theorem.
theorem protected_iid_joint_event {Ω Z H G : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Z] [Fintype G]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (P : G → Measure Z) [∀ g, IsProbabilityMeasure (P g)]
    (n : G → ℕ) (positive : ∀ g, 0 < n g)
    (models : Finset H) (nonempty : models.Nonempty)
    (sample : (g : G) → Fin (n g) → Ω → Z)
    (measurable : ∀ g i, Measurable (sample g i))
    (independent : ∀ g, iIndepFun (sample g) μ)
    (law : ∀ g i, IdentDistrib (sample g i) id μ (P g))
    (loss : H → Z → ℚ)
    (lossMeasurable : ∀ h ∈ models, Measurable (fun z => (loss h z : ℝ)))
    (bounded : ∀ h ∈ models, ∀ z, (loss h z : ℝ) ∈ Set.Icc (0 : ℝ) 1)
    (delta : G → ℝ) (deltaPositive : ∀ g, 0 < delta g) (deltaBelowOne : ∀ g, delta g < 1) :
    MeasurableSet {w | ∀ g h, h ∈ models →
      |(empiricalScore loss (fun i => sample g i w) h : ℝ) - ∫ z, (loss h z : ℝ) ∂P g| ≤
        finiteRadius (n g) models.card (delta g)} ∧
    1 - (∑ g, delta g) ≤ μ.real {w | ∀ g h, h ∈ models →
      |(empiricalScore loss (fun i => sample g i w) h : ℝ) - ∫ z, (loss h z : ℝ) ∂P g| ≤
        finiteRadius (n g) models.card (delta g)} := by
  classical
  let good (g : G) : Set Ω := {w | ∀ h ∈ models,
    |(empiricalScore loss (fun i => sample g i w) h : ℝ) - ∫ z, (loss h z : ℝ) ∂P g| ≤
      finiteRadius (n g) models.card (delta g)}
  have eachMeasurable (g : G) : MeasurableSet (good g) := by
    have deviations (h : H) (hh : h ∈ models) :
        Measurable (fun w =>
          |(empiricalScore loss (fun i => sample g i w) h : ℝ) - ∫ z, (loss h z : ℝ) ∂P g|) := by
      have hm : ∀ i, Measurable (fun w => (loss h (sample g i w) : ℝ)) :=
        fun i => (lossMeasurable h hh).comp (measurable g i)
      simp_rw [empiricalScore_cast]
      fun_prop
    have hm := models.measurableSet_biInter
      (f := fun h => {w |
        |(empiricalScore loss (fun i => sample g i w) h : ℝ) - ∫ z, (loss h z : ℝ) ∂P g| ≤
          finiteRadius (n g) models.card (delta g)})
      (fun h hh => measurableSet_le (deviations h hh) measurable_const)
    convert hm using 1 <;> ext w <;> simp [good]
  have eachBound (g : G) : 1 - delta g ≤ μ.real (good g) := by
    have bound := u01_1_iid_empirical_risk_uniform μ (P g) (positive g) models nonempty
      (sample g) (measurable g) (independent g) (law g)
      (fun h z => (loss h z : ℝ)) lossMeasurable bounded
      (delta g) (deltaPositive g) (deltaBelowOne g)
    simpa [good, empiricalScore_cast, empiricalMean] using bound
  have failed (g : G) : μ.real (good g)ᶜ ≤ delta g := by
    rw [measureReal_compl (eachMeasurable g)]
    have total : μ.real Set.univ = 1 := by simp
    rw [total]
    linarith [eachBound g]
  have unionBound : μ.real (⋃ g, (good g)ᶜ) ≤ ∑ g, delta g :=
    le_trans (measureReal_iUnion_fintype_le _) (Finset.sum_le_sum fun g _ => failed g)
  have jointMeasurable : MeasurableSet (⋂ g, good g) :=
    MeasurableSet.iInter eachMeasurable
  have complements : (⋂ g, good g)ᶜ = ⋃ g, (good g)ᶜ := by
    ext w
    simp
  rw [← complements, measureReal_compl jointMeasurable] at unionBound
  have total : μ.real Set.univ = 1 := by simp
  rw [total] at unionBound
  have jointBound : 1 - (∑ g, delta g) ≤ μ.real (⋂ g, good g) := by linarith
  have events : {w | ∀ g, w ∈ good g} = ⋂ g, good g := by ext w; simp
  change MeasurableSet {w | ∀ g, w ∈ good g} ∧
    1 - (∑ g, delta g) ≤ μ.real {w | ∀ g, w ∈ good g}
  rw [events]
  exact ⟨jointMeasurable, jointBound⟩

theorem finite_radius_mono_models (n M K : ℕ) (positive : 0 < M) (larger : M ≤ K)
    (delta : ℝ) (deltaPositive : 0 < delta) :
    finiteRadius n M delta ≤ finiteRadius n K delta := by
  have hm : (0 : ℝ) < M := by exact_mod_cast positive
  have mk : (M : ℝ) ≤ K := by exact_mod_cast larger
  apply Real.sqrt_le_sqrt
  apply div_le_div_of_nonneg_right _ (by positivity : (0 : ℝ) ≤ 2 * n)
  exact Real.log_le_log (div_pos (by positivity) deltaPositive)
    (div_le_div_of_nonneg_right (by linarith) (le_of_lt deltaPositive))

theorem verified_radius_covers_fixed_class (n M : ℕ) (delta radius : ℚ) (exponent : Nat)
    (verified : radiusVerified n M delta radius exponent = true) :
    finiteRadius n M (delta : ℝ) ≤ (radius : ℝ) := by
  have checks : 0 < n ∧ 0 < M ∧ 0 < delta ∧ delta < 1 ∧ 0 ≤ radius ∧
      4 * (M : ℚ) ≤ delta * (2 : ℚ) ^ exponent ∧
      (exponent : ℚ) ≤ 2 * (n : ℚ) * radius ^ 2 := by
    simpa only [radiusVerified, decide_eq_true_eq] using verified
  exact le_trans (finite_radius_mono_models n M (2 * M) checks.2.1
    (by omega) (delta : ℝ) (by exact_mod_cast checks.2.2.1))
    (radius_verification_sound n M delta radius exponent verified)

structure ValidationPlan where
  scope : DataScope
  protocol : Nat
  domains : List Nat
  models : List (List ℚ)
  failureBudget : ℚ
  deriving DecidableEq, Repr

structure DomainBlock (m : Nat) where
  scope : DataScope
  protocol : Nat
  domain : Nat
  snapshot : Nat
  rows : List (SampleObservation m Bool)
  delta : ℚ
  radius : ℚ
  exponent : Nat
  tolerance : ℚ
  deriving DecidableEq, Repr

def blockData {m : Nat} (block : DomainBlock m) :
    Fin block.rows.length → Fin m × Bool :=
  fun i => let row := block.rows.get i; (row.feature, row.label)

def blockRisk {m : Nat} (loss : ℚ → Bool → ℚ) (block : DomainBlock m) (table : List ℚ) : ℚ :=
  empiricalScore (tableLoss loss) (blockData block) table

def trainingEvents {m : Nat} (s : Store m) : List EventId :=
  s.cells.map Cell.event ++ s.history.map (fun change =>
    match change with
    | .observed row => row.event
    | .corrected edit => edit.supersedes.event)

def blockValid {m : Nat} (plan : ValidationPlan) (parent candidate : TrainingCandidate m)
    (loss : ℚ → Bool → ℚ) (block : DomainBlock m) : Bool :=
  decide (block.scope = plan.scope ∧ block.protocol = plan.protocol ∧ 0 ≤ block.tolerance ∧
    block.rows.Pairwise (fun a b => a.event ≠ b.event) ∧
    (∀ row ∈ block.rows, row.event ∉ trainingEvents parent.snapshot ∧
      row.event ∉ trainingEvents candidate.snapshot) ∧
    (∀ table ∈ plan.models, ∀ row ∈ block.rows,
      0 ≤ tableLoss loss table (row.feature, row.label) ∧
      tableLoss loss table (row.feature, row.label) ≤ 1)) &&
  radiusVerified block.rows.length plan.models.toFinset.card block.delta block.radius block.exponent

def scopeValid {m : Nat} (plan : ValidationPlan) (parent candidate : TrainingCandidate m) : Bool :=
  decide (parent.snapshot.scope = plan.scope ∧ candidate.snapshot.scope = plan.scope ∧
    parent.fitted.protocol.lossVersion = candidate.fitted.protocol.lossVersion) &&
  protocolMatches plan.scope parent.fitted.protocol &&
  protocolMatches plan.scope candidate.fitted.protocol

def layoutValid {m : Nat} (plan : ValidationPlan) (parent candidate : TrainingCandidate m)
    (blocks : List (DomainBlock m)) : Bool :=
  decide (plan.domains ≠ [] ∧ plan.domains.Nodup ∧ blocks.map DomainBlock.domain = plan.domains ∧
    parent.fitted.table ∈ plan.models ∧ candidate.fitted.table ∈ plan.models ∧
    (∀ table ∈ plan.models, table.length = m) ∧
    0 < plan.failureBudget ∧ plan.failureBudget < 1 ∧
    (blocks.map DomainBlock.delta).sum ≤ plan.failureBudget)

structure DomainStatistics where
  domain : Nat
  snapshot : Nat
  sampleSize : Nat
  oldEmpirical : ℚ
  newEmpirical : ℚ
  radius : ℚ
  tolerance : ℚ
  delta : ℚ
  deriving DecidableEq, Repr

def statistics {m : Nat} (parent candidate : TrainingCandidate m)
    (loss : ℚ → Bool → ℚ) (block : DomainBlock m) : DomainStatistics :=
  ⟨block.domain, block.snapshot, block.rows.length,
    blockRisk loss block parent.fitted.table, blockRisk loss block candidate.fitted.table,
    block.radius, block.tolerance, block.delta⟩

def DomainStatistics.acceptable (s : DomainStatistics) : Bool :=
  decide (s.newEmpirical + s.radius ≤ s.oldEmpirical - s.radius + s.tolerance)

structure Evaluation (m : Nat) where
  plan : ValidationPlan
  parent : TrainingCandidate m
  candidate : TrainingCandidate m
  blocks : List (DomainBlock m)
  statistics : List DomainStatistics
  deriving DecidableEq, Repr

def Evaluation.passesBounds {m : Nat} (evaluation : Evaluation m) : Bool :=
  evaluation.statistics.all DomainStatistics.acceptable

-- This Boolean records computed interval comparisons only. External sampling
-- premises, authorization, and service loading remain separate obligations.

def assembled {m : Nat} (plan : ValidationPlan) (parent candidate : TrainingCandidate m)
    (loss : ℚ → Bool → ℚ) (blocks : List (DomainBlock m)) : Evaluation m :=
  ⟨plan, parent, candidate, blocks, blocks.map (statistics parent candidate loss)⟩

def evaluate {m : Nat} (plan : ValidationPlan) (parent candidate : TrainingCandidate m)
    (loss : ℚ → Bool → ℚ) (blocks : List (DomainBlock m)) : Result (Evaluation m) :=
  if scopeValid plan parent candidate = false then .unknown .targetMismatch
  else if layoutValid plan parent candidate blocks = false then .unknown .scopeMismatch
  else if blocks.all (blockValid plan parent candidate loss) = false then .unknown .missingEvidence
  else .known (assembled plan parent candidate loss blocks)

theorem evaluation_is_actual_input_and_computation {m : Nat}
    (plan : ValidationPlan) (parent candidate : TrainingCandidate m)
    (loss : ℚ → Bool → ℚ) (blocks : List (DomainBlock m)) (out : Evaluation m)
    (produced : evaluate plan parent candidate loss blocks = .known out) :
    scopeValid plan parent candidate = true ∧ layoutValid plan parent candidate blocks = true ∧
    (∀ block ∈ blocks, blockValid plan parent candidate loss block = true) ∧
    out = assembled plan parent candidate loss blocks := by
  unfold evaluate at produced
  split at produced
  · cases produced
  · rename_i scope
    split at produced
    · cases produced
    · rename_i layout
      split at produced
      · cases produced
      · rename_i valid
        have each := List.all_eq_true.mp (show blocks.all (blockValid plan parent candidate loss) = true by
          simpa using valid)
        exact ⟨by simpa using scope, by simpa using layout, each, by cases produced; rfl⟩

theorem evaluated_models_are_in_predeclared_class {m : Nat}
    (plan : ValidationPlan) (parent candidate : TrainingCandidate m)
    (loss : ℚ → Bool → ℚ) (blocks : List (DomainBlock m)) (out : Evaluation m)
    (produced : evaluate plan parent candidate loss blocks = .known out) :
    parent.fitted.table ∈ plan.models ∧ candidate.fitted.table ∈ plan.models := by
  have layout := (evaluation_is_actual_input_and_computation plan parent candidate loss blocks out produced).2.1
  have details : plan.domains ≠ [] ∧ plan.domains.Nodup ∧ blocks.map DomainBlock.domain = plan.domains ∧
      parent.fitted.table ∈ plan.models ∧ candidate.fitted.table ∈ plan.models ∧
      (∀ table ∈ plan.models, table.length = m) ∧
      0 < plan.failureBudget ∧ plan.failureBudget < 1 ∧
      (blocks.map DomainBlock.delta).sum ≤ plan.failureBudget := by
    simpa only [layoutValid, decide_eq_true_eq] using layout
  exact ⟨details.2.2.2.1, details.2.2.2.2.1⟩

theorem bounds_gate_checks_every_actual_domain {m : Nat}
    (plan : ValidationPlan) (parent candidate : TrainingCandidate m)
    (loss : ℚ → Bool → ℚ) (blocks : List (DomainBlock m)) (out : Evaluation m)
    (produced : evaluate plan parent candidate loss blocks = .known out)
    (accepted : out.passesBounds = true) (block : DomainBlock m) (member : block ∈ blocks) :
    blockRisk loss block candidate.fitted.table + block.radius ≤
      blockRisk loss block parent.fitted.table - block.radius + block.tolerance ∧
    radiusVerified block.rows.length plan.models.toFinset.card block.delta block.radius block.exponent = true := by
  obtain ⟨_, _, checked, rfl⟩ :=
    evaluation_is_actual_input_and_computation plan parent candidate loss blocks out produced
  have metric := List.all_eq_true.mp accepted (statistics parent candidate loss block)
    (List.mem_map.mpr ⟨block, member, rfl⟩)
  have valid := checked block member
  simp only [blockValid, Bool.and_eq_true] at valid
  exact ⟨by simpa [statistics, DomainStatistics.acceptable] using metric,
    valid.2⟩

-- This is a consequence of the actual executable gate on a common confidence
-- event. The two population bounds are not supplied as acceptance decisions.
theorem bounds_gate_on_joint_event_preserves_each_risk {m : Nat}
    (plan : ValidationPlan) (parent candidate : TrainingCandidate m)
    (loss : ℚ → Bool → ℚ) (blocks : List (DomainBlock m)) (out : Evaluation m)
    (produced : evaluate plan parent candidate loss blocks = .known out)
    (accepted : out.passesBounds = true) (risk : Nat → List ℚ → ℝ)
    (confidence : ∀ block ∈ blocks, ∀ model ∈ plan.models,
      |(blockRisk loss block model : ℝ) - risk block.domain model| ≤
        finiteRadius block.rows.length plan.models.toFinset.card (block.delta : ℝ)) :
    ∀ block ∈ blocks, risk block.domain candidate.fitted.table ≤
      risk block.domain parent.fitted.table + (block.tolerance : ℝ) := by
  have models := evaluated_models_are_in_predeclared_class plan parent candidate loss blocks out produced
  intro block hb
  obtain ⟨checked, verified⟩ := bounds_gate_checks_every_actual_domain
    plan parent candidate loss blocks out produced accepted block hb
  have radius := verified_radius_covers_fixed_class _ _ _ _ _ verified
  have old := (abs_le.mp (confidence block hb parent.fitted.table models.1)).2
  have new := (abs_le.mp (confidence block hb candidate.fitted.table models.2)).1
  have gate : (blockRisk loss block candidate.fitted.table : ℝ) + block.radius ≤
      (blockRisk loss block parent.fitted.table : ℝ) - block.radius + block.tolerance := by
    exact_mod_cast checked
  linarith

theorem strict_bounds_prove_strict_improvement {m : Nat}
    (plan : ValidationPlan) (parent candidate : TrainingCandidate m)
    (loss : ℚ → Bool → ℚ) (blocks : List (DomainBlock m)) (out : Evaluation m)
    (produced : evaluate plan parent candidate loss blocks = .known out)
    (passed : out.passesBounds = true) (block : DomainBlock m) (member : block ∈ blocks)
    (risk : List ℚ → ℝ)
    (confidence : ∀ model ∈ plan.models,
      |(blockRisk loss block model : ℝ) - risk model| ≤
        finiteRadius block.rows.length plan.models.toFinset.card (block.delta : ℝ))
    (strict : blockRisk loss block candidate.fitted.table + block.radius <
      blockRisk loss block parent.fitted.table - block.radius) :
    risk candidate.fitted.table < risk parent.fitted.table := by
  have members := evaluated_models_are_in_predeclared_class plan parent candidate loss blocks out produced
  have verified := (bounds_gate_checks_every_actual_domain
    plan parent candidate loss blocks out produced passed block member).2
  have radius := verified_radius_covers_fixed_class _ _ _ _ _ verified
  have old := (abs_le.mp (confidence parent.fitted.table members.1)).2
  have new := (abs_le.mp (confidence candidate.fitted.table members.2)).1
  have gate : (blockRisk loss block candidate.fitted.table : ℝ) + block.radius <
      (blockRisk loss block parent.fitted.table : ℝ) - block.radius := by exact_mod_cast strict
  linarith

theorem observed_improvement_is_not_certified_improvement :
    (49/100 : ℚ) < 1/2 ∧
    (DomainStatistics.mk 1 1 400 (1/2) (49/100) (1/10) 0 (1/20)).acceptable = false ∧
    (DomainStatistics.mk 1 1 400 (1/2) (1/2) (1/10) (1/5) (1/20)).acceptable = true := by
  norm_num [DomainStatistics.acceptable]

def sampledBlock {m n : Nat} (plan : ValidationPlan) (domain snapshot : Nat)
    (delta radius : ℚ) (exponent : Nat) (tolerance : ℚ)
    (events : Fin n → EventId) (data : Fin n → Fin m × Bool) : DomainBlock m :=
  ⟨plan.scope, plan.protocol, domain, snapshot,
    List.ofFn (fun i => ⟨events i, (data i).1, (data i).2⟩), delta, radius, exponent, tolerance⟩

theorem sampled_block_uses_exact_losses {m n : Nat}
    (plan : ValidationPlan) (domain snapshot : Nat) (delta radius : ℚ)
    (exponent : Nat) (tolerance : ℚ) (events : Fin n → EventId)
    (data : Fin n → Fin m × Bool) (loss : ℚ → Bool → ℚ) (table : List ℚ) :
    blockRisk loss (sampledBlock plan domain snapshot delta radius exponent tolerance events data) table =
      empiricalScore (tableLoss loss) data table := by
  simp [blockRisk, blockData, sampledBlock, empiricalScore]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rfl

-- Counts and budgets are fixed outside the confidence event; returned models,
-- tolerances and verified radii may depend on its data. Every actual bounds-qualified
-- evaluation made from these very samples receives the same joint guarantee.
theorem actual_protected_evaluation_confidence {Ω : Type*} {m G : Nat}
    [MeasurableSpace Ω] [MeasurableSpace (Fin m × Bool)]
    [MeasurableSingletonClass (Fin m × Bool)]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (P : Fin G → Measure (Fin m × Bool)) [∀ g, IsProbabilityMeasure (P g)]
    (plan : ValidationPlan) (nonempty : plan.models.toFinset.Nonempty)
    (n : Fin G → Nat) (positive : ∀ g, 0 < n g)
    (sample : (g : Fin G) → Fin (n g) → Ω → Fin m × Bool)
    (measurable : ∀ g i, Measurable (sample g i))
    (independent : ∀ g, iIndepFun (sample g) μ)
    (law : ∀ g i, IdentDistrib (sample g i) id μ (P g))
    (loss : ℚ → Bool → ℚ)
    (bounded : ∀ table ∈ plan.models, ∀ z : Fin m × Bool,
      (tableLoss loss table z : ℝ) ∈ Set.Icc (0 : ℝ) 1)
    (delta : Fin G → ℚ) (deltaPositive : ∀ g, 0 < delta g)
    (deltaBelowOne : ∀ g, delta g < 1)
    (budget : (∑ g, delta g) ≤ plan.failureBudget) :
    ∃ confidence : Set Ω, MeasurableSet confidence ∧
      1 - (plan.failureBudget : ℝ) ≤ μ.real confidence ∧
      ∀ w ∈ confidence, ∀ (parent candidate : TrainingCandidate m)
        (domain snapshot : Fin G → Nat) (radius tolerance : Fin G → ℚ)
        (exponent : Fin G → Nat) (events : (g : Fin G) → Fin (n g) → EventId)
        (out : Evaluation m),
        evaluate plan parent candidate loss
          (List.ofFn (fun g => sampledBlock plan (domain g) (snapshot g) (delta g) (radius g)
            (exponent g) (tolerance g) (events g) (fun i => sample g i w))) = .known out →
        out.passesBounds = true →
        ∀ g, (∫ z, (tableLoss loss candidate.fitted.table z : ℝ) ∂P g) ≤
          (∫ z, (tableLoss loss parent.fitted.table z : ℝ) ∂P g) + (tolerance g : ℝ) := by
  have joint := protected_iid_joint_event μ P n positive plan.models.toFinset nonempty
    sample measurable independent law (tableLoss loss)
    (fun _ _ => measurable_of_finite _)
    (fun h hh => bounded h (List.mem_toFinset.mp hh))
    (fun g => (delta g : ℝ))
    (fun g => by change (0 : ℝ) < (delta g : ℝ); exact_mod_cast deltaPositive g)
    (fun g => by change (delta g : ℝ) < 1; exact_mod_cast deltaBelowOne g)
  have budgetR : (∑ g, (delta g : ℝ)) ≤ (plan.failureBudget : ℝ) := by exact_mod_cast budget
  refine ⟨_, joint.1, le_trans (by linarith) joint.2, ?_⟩
  intro w hw parent candidate domain snapshot radius tolerance exponent events out produced accepted g
  have members := evaluated_models_are_in_predeclared_class plan parent candidate loss _ out produced
  let block := sampledBlock plan (domain g) (snapshot g) (delta g) (radius g)
    (exponent g) (tolerance g) (events g) (fun i => sample g i w)
  have hb : block ∈ List.ofFn (fun j => sampledBlock plan (domain j) (snapshot j)
      (delta j) (radius j) (exponent j) (tolerance j) (events j) (fun i => sample j i w)) := by
    exact List.mem_ofFn.mpr ⟨g, rfl⟩
  obtain ⟨checked, verified⟩ := bounds_gate_checks_every_actual_domain
    plan parent candidate loss _ out produced accepted block hb
  have verified' : radiusVerified (n g) plan.models.toFinset.card (delta g)
      (radius g) (exponent g) = true := by simpa [block, sampledBlock] using verified
  have conservative := verified_radius_covers_fixed_class _ _ _ _ _ verified'
  have old := (abs_le.mp (hw g parent.fitted.table (List.mem_toFinset.mpr members.1))).2
  have new := (abs_le.mp (hw g candidate.fitted.table (List.mem_toFinset.mpr members.2))).1
  have gateQ :
      empiricalScore (tableLoss loss) (fun i => sample g i w) candidate.fitted.table + radius g ≤
      empiricalScore (tableLoss loss) (fun i => sample g i w) parent.fitted.table - radius g + tolerance g := by
    change blockRisk loss (sampledBlock plan (domain g) (snapshot g) (delta g) (radius g)
      (exponent g) (tolerance g) (events g) (fun i => sample g i w)) candidate.fitted.table + radius g ≤
      blockRisk loss (sampledBlock plan (domain g) (snapshot g) (delta g) (radius g)
      (exponent g) (tolerance g) (events g) (fun i => sample g i w)) parent.fitted.table - radius g + tolerance g at checked
    simpa only [sampled_block_uses_exact_losses] using checked
  have gateR :
      (empiricalScore (tableLoss loss) (fun i => sample g i w) candidate.fitted.table : ℝ) + radius g ≤
      (empiricalScore (tableLoss loss) (fun i => sample g i w) parent.fitted.table : ℝ) - radius g + tolerance g := by
    exact_mod_cast gateQ
  linarith

def binaryLoss (score : ℚ) (truth : Bool) : ℚ :=
  if (score = 1 ↔ truth = true) then 0 else 1

theorem average_improvement_can_harm_protected_point :
    (9/10 : ℚ) * binaryLoss 1 false + (1/10 : ℚ) * binaryLoss 0 false = 9/10 ∧
    (9/10 : ℚ) * binaryLoss 0 false + (1/10 : ℚ) * binaryLoss 1 false = 1/10 ∧
    binaryLoss 0 false = 0 ∧ binaryLoss 1 false = 1 ∧ (1/10 : ℚ) < 9/10 := by
  norm_num [binaryLoss]

end JurisLean.Candidates.ProtectedFeedback20261027
