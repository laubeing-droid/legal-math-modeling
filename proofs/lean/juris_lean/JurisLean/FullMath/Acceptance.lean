import JurisLean.FullMath.Contracts

/-! Generated acceptances: each is discharged by the mapped module
theorem (definitional equality on binder annotations). -/

open JurisLean.FullMath.Core
open JurisLean.FullMath.Logic
open JurisLean.FullMath.Evidence
open JurisLean.FullMath.Probability
open JurisLean.FullMath.Numeric
open JurisLean.FullMath.Burden
open JurisLean.FullMath.Action
open JurisLean.FullMath.Composition
open JurisLean.FullMath.Representation
open JurisLean.FullMath.Causal
open JurisLean.FullMath.Document
open JurisLean.FullMath.Roots
open JurisLean.FullMath.Gaps
open JurisLean.FullMath.Numeric.Iv

namespace JurisLean.FullMath.Acceptance

theorem root_GENERIC_FINITE : Contracts.root_GENERIC_FINITE := JurisLean.FullMath.Roots.root_GENERIC_FINITE

theorem root_SYMBOLIC_EXACT : Contracts.root_SYMBOLIC_EXACT := JurisLean.FullMath.Roots.root_SYMBOLIC_EXACT_box

theorem root_STATISTICAL_COMPOSITION : Contracts.root_STATISTICAL_COMPOSITION := JurisLean.FullMath.Roots.root_STATISTICAL_COMPOSITION

theorem root_CIVIL : Contracts.root_CIVIL := JurisLean.FullMath.Roots.root_CIVIL

theorem root_CRIMINAL : Contracts.root_CRIMINAL := JurisLean.FullMath.Roots.root_CRIMINAL

theorem root_ADMINISTRATIVE : Contracts.root_ADMINISTRATIVE := JurisLean.FullMath.Roots.root_ADMINISTRATIVE

theorem root_DOCUMENT_DELIVERY : Contracts.root_DOCUMENT_DELIVERY := JurisLean.FullMath.Roots.root_DOCUMENT_DELIVERY

theorem target_F01 : Contracts.target_F01 := JurisLean.FullMath.Core.phi_iff_components

theorem target_F02 : Contracts.target_F02 := JurisLean.FullMath.Core.migrate_main_key

theorem target_F03 : Contracts.target_F03 := JurisLean.FullMath.Core.composable_projections

theorem target_F04 : Contracts.target_F04 := JurisLean.FullMath.Evidence.deps_complete

theorem target_F05 : Contracts.target_F05 := JurisLean.FullMath.Logic.cl_mono

theorem target_F06 : Contracts.target_F06 := JurisLean.FullMath.Logic.generate_complete

theorem target_F07 : Contracts.target_F07 := JurisLean.FullMath.Logic.rooted_same_conclusion_different_identity

theorem target_F08 : Contracts.target_F08 := JurisLean.FullMath.Logic.edgeFuel_iff

theorem target_F09 : Contracts.target_F09 := JurisLean.FullMath.Logic.pending_edges_bound

theorem target_F10 : Contracts.target_F10 := JurisLean.FullMath.Logic.grounded_least

theorem target_F11 : Contracts.target_F11 := JurisLean.FullMath.Logic.incomplete_not_universal

theorem target_F12 : Contracts.target_F12 := JurisLean.FullMath.Evidence.verified_requires_source_authority

theorem target_F13 : Contracts.target_F13 := JurisLean.FullMath.Evidence.add_only_reuse

theorem target_F14 : Contracts.target_F14 := JurisLean.FullMath.Evidence.addOnly_matches_full_recompute

theorem target_P01 : Contracts.target_P01 := JurisLean.FullMath.Probability.joint_normalizes

theorem target_P02 : Contracts.target_P02 := JurisLean.FullMath.Probability.posterior_normalizes

theorem target_P03 : Contracts.target_P03 := JurisLean.FullMath.Probability.sum_out_distrib

theorem target_P04 : Contracts.target_P04 := JurisLean.FullMath.Probability.dedup_no_double_update

theorem target_P05 : Contracts.target_P05 := JurisLean.FullMath.Probability.dirWeights_update_compose

theorem target_P06 : Contracts.target_P06 := JurisLean.FullMath.Probability.hyper_data_changes_posterior

theorem target_P07 : Contracts.target_P07 := JurisLean.FullMath.Probability.mixture_within_retained

theorem target_P08 : Contracts.target_P08 := JurisLean.FullMath.Probability.contamination_bounds

theorem target_P09 : Contracts.target_P09 := JurisLean.FullMath.Probability.unprocessed_mass_bounds

theorem target_P10 : Contracts.target_P10 := JurisLean.FullMath.Probability.beta_mixture_mass

theorem target_P11 : Contracts.target_P11 := JurisLean.FullMath.Probability.time_order_enforced

theorem target_P12 : Contracts.target_P12 := JurisLean.FullMath.Probability.brier_excess_identity

theorem target_P13 : Contracts.target_P13 := JurisLean.FullMath.Probability.pav_two_point_optimal

theorem target_E01 : Contracts.target_E01 := JurisLean.FullMath.Probability.e01_within_iff

theorem target_N01 : Contracts.target_N01 := JurisLean.FullMath.Numeric.conservation

theorem target_N02 : Contracts.target_N02 := JurisLean.FullMath.Numeric.Iv.mul_sound

theorem target_N03 : Contracts.target_N03 := JurisLean.FullMath.Numeric.weak_duality

theorem target_N04 : Contracts.target_N04 := JurisLean.FullMath.Numeric.seen_span_not_global_bound

theorem target_N05 : Contracts.target_N05 := JurisLean.FullMath.Numeric.equal_objectives_certify

theorem target_N06 : Contracts.target_N06 := JurisLean.FullMath.Numeric.kkt1_sufficient

theorem target_N07 : Contracts.target_N07 := JurisLean.FullMath.Numeric.branch_cover

theorem target_N08 : Contracts.target_N08 := JurisLean.FullMath.Numeric.T_contraction

theorem target_N09 : Contracts.target_N09 := JurisLean.FullMath.Numeric.T_fixed_point

theorem target_N10 : Contracts.target_N10 := JurisLean.FullMath.Numeric.T_fixed_interior

theorem target_B01 : Contracts.target_B01 := JurisLean.FullMath.Burden.conflict_without_rule_is_pending

theorem target_B02 : Contracts.target_B02 := JurisLean.FullMath.Burden.no_terminal_when_incomplete

theorem target_B03 : Contracts.target_B03 := JurisLean.FullMath.Burden.gate_established_iff

theorem target_B04 : Contracts.target_B04 := JurisLean.FullMath.Burden.civil_allocation_complete

theorem target_B05 : Contracts.target_B05 := JurisLean.FullMath.Burden.criminal_allocation_complete

theorem target_B06 : Contracts.target_B06 := JurisLean.FullMath.Burden.admin_allocation_complete

theorem target_B07 : Contracts.target_B07 := JurisLean.FullMath.Burden.version_change_invalidates

theorem target_G01 : Contracts.target_G01 := JurisLean.FullMath.Numeric.vf_dominates

theorem target_G02 : Contracts.target_G02 := JurisLean.FullMath.Action.gross_voi_nonneg

theorem target_G03 : Contracts.target_G03 := JurisLean.FullMath.Action.admissible_settlement_bounds

theorem target_G04 : Contracts.target_G04 := JurisLean.FullMath.Action.dsic_of_label

theorem target_G05 : Contracts.target_G05 := JurisLean.FullMath.Action.rectangle_lower_bound

theorem target_C01 : Contracts.target_C01 := JurisLean.FullMath.Composition.relComp_assoc

theorem target_C02 : Contracts.target_C02 := JurisLean.FullMath.Composition.outer_two_step

theorem target_C03 : Contracts.target_C03 := JurisLean.FullMath.Composition.scenario_bridge

theorem target_C04 : Contracts.target_C04 := JurisLean.FullMath.Composition.joint_instance

theorem target_C05 : Contracts.target_C05 := JurisLean.FullMath.Composition.chain_carries_ids

theorem target_C06 : Contracts.target_C06 := JurisLean.FullMath.Composition.checker_correspondence

theorem target_C07 : Contracts.target_C07 := ⟨JurisLean.FullMath.Composition.complete_requires_equality, Acceptance.root_GENERIC_FINITE, Acceptance.root_SYMBOLIC_EXACT, Acceptance.root_STATISTICAL_COMPOSITION, Acceptance.root_CIVIL, Acceptance.root_CRIMINAL, Acceptance.root_ADMINISTRATIVE, Acceptance.root_DOCUMENT_DELIVERY⟩

theorem target_EXT01 : Contracts.target_EXT01 := JurisLean.FullMath.Representation.certificate_implies_mode

theorem target_EXT02 : Contracts.target_EXT02 := JurisLean.FullMath.Core.carries_binds_identity

theorem target_EXT03 : Contracts.target_EXT03 := JurisLean.FullMath.Logic.grounded_fixpoint

theorem target_EXT04 : Contracts.target_EXT04 := JurisLean.FullMath.Representation.splitBox_cover

theorem target_EXT05 : Contracts.target_EXT05 := JurisLean.FullMath.Evidence.invalidated_of_retired_used

theorem target_EXT06 : Contracts.target_EXT06 := JurisLean.FullMath.Probability.parts_cover

theorem target_EXT07 : Contracts.target_EXT07 := JurisLean.FullMath.Causal.sup_not_attained

theorem target_EXT08 : Contracts.target_EXT08 := JurisLean.FullMath.Action.shared_theta_total_identity

theorem target_EXT09 : Contracts.target_EXT09 := ⟨JurisLean.FullMath.Roots.ext09_domainComposition, Acceptance.root_CIVIL, Acceptance.root_CRIMINAL, Acceptance.root_ADMINISTRATIVE⟩

theorem demand_D001 : Contracts.demand_D001 := And.intro JurisLean.FullMath.Core.locator_not_identity
  (by
    intro scope paras
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact fun t h => of_decide_eq_true (List.mem_filter.mp h).2
    · exact fun t hsc hp => List.mem_filter.mpr ⟨of_decide_eq_true hp, decide_eq_true hsc⟩
    · exact fun p hp hno =>
        List.mem_filter.mpr ⟨hp, decide_eq_true (of_decide_eq_false hno)⟩
    · exact fun p h => of_decide_eq_true (List.mem_filter.mp h).2)

theorem demand_D002 : Contracts.demand_D002 := And.intro JurisLean.FullMath.Core.locator_not_identity
  (by
    intro table s facts
    refine ⟨fun e he => List.mem_of_find?_eq_some he, ?_, ?_⟩
    · exact fun e _ hh => by subst hh; rfl
    · exact fun r => by cases r <;> rfl)

theorem demand_D003 : Contracts.demand_D003 := And.intro JurisLean.FullMath.Core.locator_not_identity
  (by
    intro bindings person matter stage
    refine ⟨fun e he => List.mem_of_find?_eq_some he, ?_, ?_⟩
    · intro p r₁ r₂ hr hEq
      simp at hEq
      exact hr hEq
    · intro n₁ n₂ r hn hEq
      simp at hEq
      exact hn hEq)

theorem demand_D004 : Contracts.demand_D004 := And.intro JurisLean.FullMath.Core.locator_not_identity
  (by
    refine ⟨fun ok required => List.all_eq_true, ?_⟩
    intro u v x y huv hxy
    refine ⟨?_, ?_⟩
    · simpa using hxy
    · have hne : v ≠ u := Ne.symm huv
      have e1 : (fun d : String => if d = u then (x:ℕ) else if d = v then y else 0) u = x := by
        simp
      have e2 : (fun d : String => if d = u then (x:ℕ) else if d = v then y else 0) v = y := by
        simp [hne]
      have e3 : (fun d : String => if d = u then (y:ℕ) else if d = v then x else 0) u = y := by
        simp
      have e4 : (fun d : String => if d = u then (y:ℕ) else if d = v then x else 0) v = x := by
        simp [hne]
      rw [e1, e2, e3, e4]
      omega)

theorem demand_D005 : Contracts.demand_D005 := And.intro JurisLean.FullMath.Core.locator_not_identity
  (by
    intro c₁ c₂ nm rest hc
    refine ⟨?_, ?_, ?_⟩
    · simp
    · simp [hc]
    · exact fun e he => List.mem_of_find?_eq_some he)

theorem demand_D006 : Contracts.demand_D006 := And.intro JurisLean.FullMath.Core.locator_not_identity
  (by
    intro c₁ c₂ k₁ k₂ addr rules hc
    refine ⟨?_, ?_, ?_⟩
    · intro hEq
      simp at hEq
      exact hc hEq.1
    · intro e he
      obtain ⟨r, hr, rfl⟩ := List.mem_map.mp he
      exact ⟨r, hr, rfl⟩
    · intro h
      subst h
      rfl)

theorem demand_D007 : Contracts.demand_D007 := And.intro JurisLean.FullMath.Core.locator_not_identity
  (by
    intro courts sources t exclusions cd inst lv
    refine ⟨fun e he => List.mem_of_find?_eq_some he, ?_, ?_⟩
    · exact fun hnone hnot =>
        JurisLean.FullMath.Burden.unknown_is_pending sources t exclusions cd hnone hnot
    · intro d₂ i₁ i₂ l hcd hEq
      simp at hEq
      exact hcd hEq.1)

theorem demand_D008 : Contracts.demand_D008 := And.intro JurisLean.FullMath.Core.locator_not_identity
  (by
    intro claims
    refine ⟨?_, ?_, ?_⟩
    · intro e he
      obtain ⟨c, hc, rfl⟩ := List.mem_map.mp he
      exact ⟨c, hc, rfl⟩
    · intro a r bs bj₁ bj₂ rm sc hb hEq
      simp at hEq
      exact hb hEq
    · intro a r har hEq
      simp at hEq
      exact har hEq.1)

theorem demand_D009 : Contracts.demand_D009 := And.intro JurisLean.FullMath.Burden.unknown_is_pending
  (by
    intro source st en span v q hkey hend hspan
    refine ⟨hspan.symm, ?_, ?_, ?_⟩
    · subst hspan
      rw [List.length_drop, List.length_take, Nat.min_eq_left hend]
    · subst hspan
      simp
    · exact JurisLean.FullMath.Burden.version_change_invalidates v q hkey)

theorem demand_D010 : Contracts.demand_D010 := And.intro JurisLean.FullMath.Burden.unknown_is_pending
  (by
    intro rules hits hhits
    subst hhits
    refine ⟨?_, ?_, ?_⟩
    · intro s hs
      obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hs
      obtain ⟨he, hp⟩ := List.mem_filter.mp hr
      exact ⟨r, he, rfl, hp⟩
    · intro e he hp
      exact List.mem_map.mpr ⟨e, List.mem_filter.mpr ⟨he, hp⟩, rfl⟩
    · intro e he hp hmem
      obtain ⟨_, htrue⟩ := List.mem_filter.mp hmem
      simp [hp] at htrue)

theorem demand_D011 : Contracts.demand_D011 := And.intro JurisLean.FullMath.Burden.unknown_is_pending
  (by
    intro old new t p e r _hlt hlate
    refine ⟨JurisLean.FullMath.Burden.not_yet_effective new t hlate, rfl, rfl, ?_⟩
    intro hle hrep
    exact JurisLean.FullMath.Burden.effective_window_applicable old t hle hrep)

theorem demand_D012 : Contracts.demand_D012 := And.intro JurisLean.FullMath.Burden.unknown_is_pending
  (by
    intro defs cites x m fuel
    refine ⟨?_, rfl, ?_⟩
    · intro h
      simp only [Contracts.citeChase, h]
    · intro x' m' h
      simp only [Contracts.citeChase, h])

theorem demand_D013 : Contracts.demand_D013 := And.intro JurisLean.FullMath.Burden.unknown_is_pending
  (by
    intro score a b tgtFeats relevant copied
    refine ⟨decide_eq_true_iff, ?_, ?_⟩
    · intro h1 h2
      exact absurd (lt_trans h1 h2) (lt_irrefl (score b))
    · intro hcop hw
      subst hcop
      cases h : relevant.all (fun f => decide (f ∈ tgtFeats)) with
      | false => rfl
      | true =>
        exfalso
        obtain ⟨f, hfr, hfn⟩ := hw
        exact hfn (of_decide_eq_true (List.all_eq_true.mp h f hfr)))

theorem demand_D014 : Contracts.demand_D014 := And.intro JurisLean.FullMath.Burden.unknown_is_pending
  (by
    intro corpus pool returned relevant hret
    subst hret
    refine ⟨?_, ?_, ?_⟩
    · intro s hs
      exact List.mem_filter.mp hs
    · intro s hsp hrel
      exact List.mem_filter.mpr ⟨hsp, hrel⟩
    · intro ex hall
      obtain ⟨s, hsc, hsp, hsr⟩ := ex
      obtain ⟨hmem, _⟩ := List.mem_filter.mp (hall s hsc hsr)
      exact hsp hmem)

theorem demand_D015 : Contracts.demand_D015 := And.intro JurisLean.FullMath.Burden.unknown_is_pending
  (by
    intro cites edges propId hedges
    subst hedges
    refine ⟨?_, ?_, ?_⟩
    · intro e he
      obtain ⟨c, hc, rfl⟩ := List.mem_map.mp he
      obtain ⟨hcm, hcp⟩ := List.mem_filter.mp hc
      exact ⟨c, hcm, rfl, hcp⟩
    · intro c _hc hcon hmem
      obtain ⟨_, htrue⟩ := List.mem_filter.mp hmem
      simp [hcon] at htrue
    · intro c hc
      exact ⟨c.2.1, hc, rfl⟩)

theorem demand_D016 : Contracts.demand_D016 := And.intro JurisLean.FullMath.Burden.unknown_is_pending
  (by
    intro overruled c i j t d hc hd
    refine ⟨?_, ?_⟩
    · cases h : (overruled.filter (fun o => decide (o.1 = c ∧ o.2.1 = i))).all
        (fun o => decide (t < o.2.2)) with
      | false => rfl
      | true =>
        exfalso
        have hmem : (c, i, d) ∈ overruled.filter (fun o => decide (o.1 = c ∧ o.2.1 = i)) :=
          List.mem_filter.mpr ⟨hc, by simp⟩
        have hall := List.all_eq_true.mp h (c, i, d) hmem
        simp at hall
        omega
    · intro hall
      refine List.all_eq_true.mpr ?_
      intro o ho
      obtain ⟨hov, hdec⟩ := List.mem_filter.mp ho
      exact decide_eq_true (hall o hov (of_decide_eq_true hdec)))

theorem demand_D017 : Contracts.demand_D017 := And.intro JurisLean.FullMath.Burden.unknown_is_pending
  (by
    intro cands name b₁ b₂ b₃ b₄ hfind
    refine ⟨?_, ?_, ?_, ?_⟩
    · cases b₁ <;> cases b₂ <;> cases b₃ <;> cases b₄ <;> decide
    · cases b₁ <;> cases b₂ <;> cases b₃ <;> cases b₄ <;> decide
    · intro h1 h2
      simp [h1, h2]
    · exact List.mem_of_find?_eq_some hfind)

theorem demand_D018 : Contracts.demand_D018 := And.intro JurisLean.FullMath.Burden.unknown_is_pending
  (by
    intro a b m
    refine ⟨?_, ?_, ?_⟩
    · intro hm
      subst hm
      exact ⟨rfl, rfl, rfl, rfl⟩
    · intro _h1 h2 heq
      exact h2 (by rw [heq])
    · intro _h1 h2
      rw [if_neg h2]
      simp)

theorem demand_D019 : Contracts.demand_D019 := And.intro JurisLean.FullMath.Probability.dedup_conflict_not_overwrite
  (by
    intro source tags hbound
    refine ⟨?_, ?_, ?_⟩
    · intro ty acs ob q st en hq hmem
      obtain ⟨_, hdec⟩ := List.mem_filter.mp hmem
      exact absurd (of_decide_eq_true hdec) (by simp [hq])
    · intro ty acs ob q st en hmem hlen
      rw [List.length_drop, List.length_take, Nat.min_eq_left hlen]
    · intro ty ty' ob acs₁ acs₂ q st en hne hEq
      simp at hEq
      exact hne hEq.1)

theorem demand_D020 : Contracts.demand_D020 := And.intro JurisLean.FullMath.Probability.dedup_conflict_not_overwrite
  (by
    intro edges c
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro e hmem
      obtain ⟨_, hdec⟩ := List.mem_filter.mp hmem
      exact of_decide_eq_true hdec
    · intro p o s g hmem
      exact List.mem_filter.mpr ⟨hmem, decide_eq_true rfl⟩
    · intro c' p o s g hc' hmem
      obtain ⟨_, hdec⟩ := List.mem_filter.mp hmem
      have hkey : (c', p, o, s, g).1 = c' := rfl
      rw [hkey] at hdec
      exact hc' (of_decide_eq_true hdec)
    · intro p₁ p₂ o s g hne hEq
      simp at hEq
      exact hne hEq)

theorem demand_D021 : Contracts.demand_D021 := And.intro JurisLean.FullMath.Probability.dedup_conflict_not_overwrite
  (by
    intro evts
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro e hmem hnone hmemF
      obtain ⟨_, hdec⟩ := List.mem_filter.mp hmemF
      have hdec' : e.2.isSome = true := hdec
      rw [hnone] at hdec'
      exact absurd hdec' (by simp)
    · intro e d hmem hsome
      have hb : e.2.isSome = true := by rw [hsome]; rfl
      exact List.mem_filter.mpr ⟨hmem, hb⟩
    · intro e hmem
      by_cases h : e.2.isSome = true
      · exact Or.inl (List.mem_filter.mpr ⟨hmem, h⟩)
      · cases h2 : e.2 with
        | none => exact Or.inr rfl
        | some d => exact absurd (show e.2.isSome = true from by rw [h2]; rfl) h
    · exact fun _ _ _ h1 h2 => lt_trans h1 h2
    · exact fun a h => lt_irrefl a h)

theorem demand_D022 : Contracts.demand_D022 := And.intro JurisLean.FullMath.Probability.dedup_conflict_not_overwrite
  (by
    intro cands ctres
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro r hmem
      obtain ⟨_, hdec⟩ := List.mem_filter.mp hmem
      exact of_decide_eq_true hdec
    · intro r hmem hne hmemF
      obtain ⟨_, hdec⟩ := List.mem_filter.mp hmemF
      exact hne (of_decide_eq_true hdec).2.1
    · intro r hmem hnc hmemF
      obtain ⟨_, hdec⟩ := List.mem_filter.mp hmemF
      exact hnc (of_decide_eq_true hdec).2.2.1
    · intro r hmem
      exact List.mem_map.mpr ⟨r, hmem, rfl⟩)

theorem demand_D023 : Contracts.demand_D023 := And.intro JurisLean.FullMath.Probability.dedup_conflict_not_overwrite
  (by
    intro rec scope q
    refine ⟨?_, ?_, ?_⟩
    · intro hmiss hneg
      obtain ⟨r, hr, hrq, _⟩ := hneg
      exact hmiss (List.mem_map.mpr ⟨r, hr, hrq⟩)
    · intro hout
      exact decide_eq_false hout
    · intro hEq
      exact absurd hEq (by decide))

theorem demand_D024 : Contracts.demand_D024 := And.intro JurisLean.FullMath.Probability.dedup_conflict_not_overwrite
  (by
    intro links a s₁ s₂ st en h₁ h₂ hle _hne
    refine ⟨⟨List.mem_filter.mpr ⟨h₁, decide_eq_true hle⟩,
             List.mem_filter.mpr ⟨h₂, decide_eq_true hle⟩⟩, ?_, ?_⟩
    · intro l hmem
      obtain ⟨_, hdec⟩ := List.mem_filter.mp hmem
      exact of_decide_eq_true hdec
    · intro l hmem hbad hmemF
      obtain ⟨_, hdec⟩ := List.mem_filter.mp hmemF
      exact absurd (lt_of_le_of_lt (of_decide_eq_true hdec) hbad) (lt_irrefl _))

theorem demand_D025 : Contracts.demand_D025 := And.intro JurisLean.FullMath.Probability.dedup_conflict_not_overwrite
  (by
    intro s fb
    refine ⟨?_, ?_, ?_⟩
    · cases s with
      | none => exact Or.inl rfl
      | some s' =>
        cases s' with
        | none => exact Or.inr (Or.inl rfl)
        | some b => exact Or.inr (Or.inr ⟨b, rfl⟩)
    · refine ⟨?_, ?_⟩
      · intro hEq
        simp at hEq
      · intro hEq
        simp at hEq
    · cases s with
      | none => exact Or.inl rfl
      | some s' =>
        cases s' with
        | none => exact Or.inl rfl
        | some b => exact Or.inr ⟨b, rfl⟩)

theorem demand_D026 : Contracts.demand_D026 := And.intro JurisLean.FullMath.Probability.dedup_conflict_not_overwrite
  (by
    intro recs
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro kd c s u
      exact ⟨rfl, rfl⟩
    · intro c s u hmem
      obtain ⟨_, hdec⟩ := List.mem_filter.mp hmem
      exact absurd (of_decide_eq_true hdec)
        (by simp : ¬ (("asserted", c, s, u).1 = "adjudicated"))
    · intro r hmem
      obtain ⟨hmem', hdec⟩ := List.mem_filter.mp hmem
      exact ⟨hmem', of_decide_eq_true hdec⟩
    · intro c s u hEq
      exact absurd hEq
        (by simp : ¬ (("asserted", c, s, u) = ("adjudicated", c, s, u))))

theorem demand_D027 : Contracts.demand_D027 := And.intro JurisLean.FullMath.Probability.dedup_conflict_not_overwrite
  (by
    intro draft admitted conditional tamper
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro d hmem
      obtain ⟨_, hdec⟩ := List.mem_filter.mp hmem
      exact of_decide_eq_true hdec
    · intro d hdraft h₁ h₂ hmemF
      obtain ⟨_, hdec⟩ := List.mem_filter.mp hmemF
      rcases of_decide_eq_true hdec with h | h
      · exact h₁ h
      · exact h₂ h
    · intro d hdraft
      by_cases h : d ∈ admitted ∨ d ∈ conditional
      · exact Or.inl (List.mem_filter.mpr ⟨hdraft, decide_eq_true h⟩)
      · exact Or.inr (List.mem_filter.mpr ⟨hdraft, decide_eq_true h⟩)
    · intro d hdraft htam hpend
      have hdelta : d ∈ draft.filter (fun x =>
          decide (x ∈ tamper ∧ ¬ (x ∈ admitted ∨ x ∈ conditional))) :=
        List.mem_filter.mpr ⟨hdraft, decide_eq_true ⟨htam, hpend⟩⟩
      cases hlist : draft.filter (fun x =>
          decide (x ∈ tamper ∧ ¬ (x ∈ admitted ∨ x ∈ conditional))) with
      | nil => rw [hlist] at hdelta; simp at hdelta
      | cons _ _ => exact Nat.succ_le_succ (Nat.zero_le _))

theorem demand_D028 : Contracts.demand_D028 := And.intro JurisLean.FullMath.Probability.dedup_conflict_not_overwrite
  (by
    intro acts rules c
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro a hmem
      obtain ⟨_, hdec⟩ := List.mem_filter.mp hmem
      exact (of_decide_eq_true hdec).1
    · intro e x hmem
      obtain ⟨_, hdec⟩ := List.mem_filter.mp hmem
      exact (of_decide_eq_true hdec).2 rfl
    · intro r hmem
      exact (List.mem_filter.mp hmem).1
    · intro r hmem hrt
      exact List.mem_filter.mpr ⟨hmem, hrt⟩
    · intro c₁ c₂ e x hne hEq
      simp at hEq
      exact hne hEq
    · intro e₁ e₂ x hne hEq
      simp at hEq
      exact hne hEq)

theorem demand_D029 : Contracts.demand_D029 := And.intro JurisLean.FullMath.Logic.generate_sound
  (by
    intro table p i pr alt awards hpi hpr hawards
    subst hawards
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro c hc
      obtain ⟨e, hf, hc1⟩ := List.mem_map.mp hc
      obtain ⟨hmem', hdec⟩ := List.mem_filter.mp hf
      exact ⟨e, hmem', hc1, hdec⟩
    · intro e he hp
      exact List.mem_map.mpr ⟨e, List.mem_filter.mpr ⟨he, hp⟩, rfl⟩
    · intro d x y hEq
      simp at hEq
    · intro hmem
      rw [hpr] at hmem
      simp at hmem
      exact hpi hmem.symm)

theorem demand_D030 : Contracts.demand_D030 := And.intro JurisLean.FullMath.Logic.generate_sound
  (by
    refine ⟨⟨⟨by decide, by decide, by decide⟩, ⟨by decide, by decide⟩, by decide⟩, ?_⟩
    intro filed sup awd echo table hsup hawd hecho
    subst hsup
    subst hawd
    subst hecho
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro r hr
      exact (List.mem_filter.mp hr).1
    · intro r hr
      exact (List.mem_filter.mp (List.mem_filter.mp hr).1).1
    · intro r hr
      exact (List.mem_filter.mp hr).1
    · intro e he
      obtain ⟨h1, h2⟩ := List.mem_filter.mp he
      obtain ⟨_, hpre⟩ := List.mem_filter.mp h1
      exact ⟨hpre, h2⟩
    · intro e he hpre hnotin hEq
      have hmem : e.1 ∈ (table.filter (fun r => r.2)).map (fun r => r.1) :=
        List.mem_map.mpr ⟨e, List.mem_filter.mpr ⟨he, hpre⟩, rfl⟩
      rw [← hEq] at hmem
      exact hnotin hmem)

theorem demand_D031 : Contracts.demand_D031 := And.intro JurisLean.FullMath.Logic.generate_sound
  (by
    intro rows defs r₁ r₂ p₁ c₁ p₂ c₂ adm contra hr₁ hfind₁ hfind₂ hadm hcontra
    subst hadm
    subst hcontra
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro hEq
      simp at hEq
      exact hr₁ hEq.1
    · exact ⟨List.mem_of_find?_eq_some hfind₁, List.mem_of_find?_eq_some hfind₂⟩
    · intro d hd h1 h2
      refine ⟨?_, ?_⟩
      · intro hmem
        obtain ⟨_, hdec⟩ := List.mem_filter.mp hmem
        simp at hdec
        rw [h2] at hdec
        simp at hdec
      · intro hmem
        obtain ⟨_, hdec⟩ := List.mem_filter.mp hmem
        simp at hdec
        rw [h1] at hdec
        simp at hdec
    · intro d hmem
      obtain ⟨_, hdec⟩ := List.mem_filter.mp hmem
      simp at hdec
      exact hdec.2
    · intro d hmem
      obtain ⟨_, hdec⟩ := List.mem_filter.mp hmem
      simp at hdec
      exact hdec.2)

theorem demand_D032 : Contracts.demand_D032 := And.intro JurisLean.FullMath.Logic.generate_sound
  (by
    intro bV bI hbV h1 h2
    refine ⟨⟨⟨by decide, by decide⟩, by decide, by decide⟩, ?_, ?_⟩
    · intro hEq
      rw [hEq] at hbV
      exact hbV rfl
    · rw [h1, h2])

theorem demand_D033 : Contracts.demand_D033 := And.intro JurisLean.FullMath.Logic.generate_sound
  (by
    intro due raised ack ackDay restart dismissed alive hdis halive hrestart
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro hdue hra
      rw [hdis, halive]
      simp [hdue, hra]
    · intro hdue hra
      rw [hdis]
      simp [hdue, hra]
    · intro _
      exact hrestart
    · intro _
      exact hdis)

theorem demand_D034 : Contracts.demand_D034 := And.intro JurisLean.FullMath.Logic.generate_sound
  (by
    intro row issues supOk proved hmem hproved
    refine ⟨List.mem_map.mpr ⟨row, hmem, rfl⟩, ?_, ?_, ?_⟩
    · intro c₁ c₂ i r p a hne hEq
      simp at hEq
      exact hne hEq
    · intro h
      simp [hproved, h]
    · intro _
      exact hproved)

theorem demand_D035 : Contracts.demand_D035 := And.intro JurisLean.FullMath.Logic.generate_sound
  (by
    intro defs admissions reviewed hadm hrev
    subst hadm
    subst hrev
    refine ⟨?_, ?_⟩
    · intro p hp
      obtain ⟨d, hf, hd1⟩ := List.mem_map.mp hp
      obtain ⟨hmem', hdec⟩ := List.mem_filter.mp hf
      refine ⟨d, hmem', hd1, ?_⟩
      cases hA : d.2.2.2.2 with
      | true => rfl
      | false => rw [hA] at hdec; simp at hdec
    · intro d hd ha hs
      exact List.mem_map.mpr ⟨d, List.mem_filter.mpr ⟨hd, by rw [ha, hs]; rfl⟩, rfl⟩)

theorem demand_D036 : Contracts.demand_D036 := And.intro JurisLean.FullMath.Logic.generate_sound
  (by
    intro p₁ p₂ s₁ s₂ e₁ e₂ total hp1 hsum hext
    refine ⟨?_, ?_, ?_⟩
    · intro hEq
      simp at hEq
      exact hp1 hEq.1
    · have h : s₁ * total + s₂ * total = (s₁ + s₂) * total := by ring
      rw [h, hsum]
      simp
    · intro hne hEq
      simp at hEq
      exact hne hEq.1.symm)

theorem demand_D037 : Contracts.demand_D037 := And.intro JurisLean.FullMath.Burden.perPerson_slots_distinct
  (by
    intro cands outs houts
    subst houts
    refine ⟨?_, ?_, ?_⟩
    · intro l hl
      obtain ⟨e, hf, hc1⟩ := List.mem_map.mp hl
      obtain ⟨hmem', hdec⟩ := List.mem_filter.mp hf
      rw [Bool.and_eq_true] at hdec
      rw [Bool.and_eq_true] at hdec
      exact ⟨e, hmem', hc1, hdec.1.1, hdec.1.2, hdec.2⟩
    · intro e he f1 f2 f3
      exact List.mem_map.mpr ⟨e, List.mem_filter.mpr ⟨he, by rw [f1, f2, f3]; rfl⟩, rfl⟩
    · intro c₁ c₂ hc₁ hc₂ hne a1 a2 a3 b1 b2 b3
      refine ⟨List.mem_map.mpr ⟨c₁, List.mem_filter.mpr ⟨hc₁, by rw [a1, a2, a3]; rfl⟩, rfl⟩,
        List.mem_map.mpr ⟨c₂, List.mem_filter.mpr ⟨hc₂, by rw [b1, b2, b3]; rfl⟩, rfl⟩, ?_⟩
      have hmem : c₂.1 ∈ (cands.filter (fun c => c.2.1 && c.2.2.1 && c.2.2.2)).map
          (fun c => c.1) :=
        List.mem_map.mpr ⟨c₂, List.mem_filter.mpr ⟨hc₂, by rw [b1, b2, b3]; rfl⟩, rfl⟩
      intro hEq
      rw [← hEq] at hmem
      simp at hmem
      exact hne hmem.symm)

theorem demand_D038 : Contracts.demand_D038 := And.intro JurisLean.FullMath.Burden.perPerson_slots_distinct
  (by
    intro dict n art cls hfind huniq
    have hmem : (n, art, cls) ∈ dict := List.mem_of_find?_eq_some hfind
    have hpred : decide ((n, art, cls).2.1 = art ∧ (n, art, cls).2.2 = cls) = true := by
      simp
    have find_unique : ∀ {α : Type} (p : α → Bool) (l : List α) (v : α),
        v ∈ l → p v = true → (∀ u ∈ l, p u = true → u = v) → l.find? p = some v := by
      intro α p l
      induction l with
      | nil => intro v hv _ _; exact absurd hv (by simp)
      | cons a l ih =>
        intro v hv hpv huni
        by_cases hpa : p a = true
        · rw [List.find?_cons_of_pos hpa]
          exact congrArg some (huni a List.mem_cons_self hpa)
        · rw [List.find?_cons_of_neg hpa]
          refine ih v ?_ hpv ?_
          · rcases List.mem_cons.mp hv with heq | hm
            · subst heq
              exact absurd hpv hpa
            · exact hm
          · intro u hu hpu
            exact huni u (List.mem_cons_of_mem _ hu) hpu
    refine ⟨find_unique (fun d => decide (d.2.1 = art ∧ d.2.2 = cls)) dict (n, art, cls)
      hmem hpred ?_, ⟨rfl, rfl, rfl⟩, ?_, ?_⟩
    · intro u hu hpu
      obtain ⟨u₁, u₂, u₃⟩ := u
      have hp := of_decide_eq_true hpu
      have h1 : u₁ = n := huniq (u₁, u₂, u₃) (n, art, cls) hu hmem hp.1 hp.2
      have e2 : u₂ = art := hp.1
      have e3 : u₃ = cls := hp.2
      simp [h1, e2, e3]
    · intro n' hne hEq
      simp at hEq
      exact hne hEq
    · intro m hno
      exact List.find?_eq_none.mpr (fun d hd => by simp [hno d hd]))

theorem demand_D039 : Contracts.demand_D039 := And.intro JurisLean.FullMath.Burden.perPerson_slots_distinct
  (by
    intro rows
    refine ⟨?_, ?_, ?_, ⟨?_, ?_, ?_, ?_⟩⟩
    · intro hall
      simp [Contracts.penTotal, hall]
    · intro h
      obtain ⟨r, hr, hr2⟩ := h
      by_cases hall : rows.all (fun r => r.1 = 1 && r.2.isSome) = true
      · exfalso
        have h1 := List.all_eq_true.mp hall r hr
        simp at h1
        omega
      · simp [Contracts.penTotal, hall]
    · intro h
      obtain ⟨r, hr, hr2⟩ := h
      by_cases hall : rows.all (fun r => r.1 = 1 && r.2.isSome) = true
      · exfalso
        have h1 := List.all_eq_true.mp hall r hr
        simp at h1
        omega
      · simp [Contracts.penTotal, hall]
    · rfl
    · rfl
    · rfl
    · rfl)

theorem demand_D040 : Contracts.demand_D040 := And.intro JurisLean.FullMath.Burden.perPerson_slots_distinct
  (by
    intro hw ho n s h1 h2 h3 h4
    subst h1
    subst h2
    subst h4
    subst h3
    have hl : ([0, 1, 2] : List ℕ).length = 3 := rfl
    have ho2 : ([0, 1] : List ℕ).length = 2 := rfl
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · decide
    · decide
    · decide
    · decide
    · rw [hl]
      norm_num
    · rw [hl, ho2]
      norm_num)

theorem demand_D041 : Contracts.demand_D041 := And.intro JurisLean.FullMath.Burden.perPerson_slots_distinct
  (by
  intro p q ep ec x y hpq hxy
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp
  · simp [hpq]
  · simp <;> omega
  · simp <;> omega
  · simp
  · intro hEq
    have h1 : (p, ep, ec, y) = (p, ep, ec, x) := Option.some.inj hEq
    have h2 : y = x := congrArg (fun t : ℕ × String × String × ℕ => t.2.2.2) h1
    exact hxy h2.symm)

theorem demand_D042 : Contracts.demand_D042 := And.intro JurisLean.FullMath.Burden.perPerson_slots_distinct
  (by
    intro required vd relationOk d₁ d₂ s₁ s₂
    refine ⟨?_, ?_, ?_⟩
    · intro hall hrel
      have h1 : required.all (fun d => vd d == some true) = true :=
        List.all_eq_true.mpr (fun d hd => by rw [hall d hd]; simp)
      rw [h1, hrel]
      rfl
    · intro h
      obtain ⟨d, hd, hdnone⟩ := h
      by_cases hall : required.all (fun d => vd d == some true) = true
      · exfalso
        rw [List.all_eq_true] at hall
        have h2 := hall d hd
        rw [hdnone] at h2
        simp at h2
      · exact Bool.of_not_eq_true hall
    · intro hreq hne h1 h2 h3 hs1 hs2
      subst hreq
      refine ⟨?_, ?_, ⟨?_, ?_⟩⟩
      · simp [h1, h2]
      · simp [h1, h2]
      · rw [hs1, hs2]
        norm_num
      · simp [h1, h2])

theorem demand_D043 : Contracts.demand_D043 := And.intro JurisLean.FullMath.Burden.perPerson_slots_distinct
  (by
    intro rec txt
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro h
      obtain ⟨h1, h2, h3⟩ := h
      simp [Contracts.readBack, h1, h2, h3]
    · intro hne
      simp [Contracts.readBack, hne]
    · simp [Contracts.readBack]
    · simp [Contracts.readBack])

theorem demand_D044 : Contracts.demand_D044 := And.intro JurisLean.FullMath.Burden.perPerson_slots_distinct
  (by
    intro paths conclusions
    refine ⟨?_, ?_, ?_⟩
    · intro x hx
      obtain ⟨hm, hd⟩ := List.mem_filter.mp hx
      exact ⟨hm, of_decide_eq_true hd⟩
    · intro x hx hnp hmem
      obtain ⟨_, hd⟩ := List.mem_filter.mp hmem
      simp [hnp] at hd
    · intro hp hc
      subst hp
      subst hc
      refine ⟨?_, ?_⟩
      · simp
      · intro hEq
        simp at hEq)

theorem demand_D045 : Contracts.demand_D045 := And.intro JurisLean.FullMath.Burden.perPerson_slots_distinct
  (by
    intro items x
    refine ⟨?_, ?_, ?_, ?_, ⟨?_, ?_⟩⟩
    · intro hin hok hmem
      obtain ⟨_, hd⟩ := List.mem_filter.mp hmem
      rw [hok] at hd
      simp at hd
    · intro y hy
      exact (List.mem_filter.mp hy).1
    · intro s t a b hne
      simp [Contracts.countOnce, Contracts.crimOK, Ne.symm hne] <;> norm_num
    · intro s a b
      simp [Contracts.countOnce, Contracts.crimOK] <;> norm_num
    · rfl
    · rfl)

theorem demand_D046 : Contracts.demand_D046 := And.intro JurisLean.FullMath.Burden.perPerson_slots_distinct
  (by
    intro rows v e x u
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro r hr
      exact of_decide_eq_true (List.mem_filter.mp hr).2
    · intro r hr1 hmem
      obtain ⟨_, hd⟩ := List.mem_filter.mp hmem
      simp [hr1] at hd
    · intro l b hEq
      simp at hEq
    · intro ⟨hv, he, hx, hu⟩
      simp [Contracts.hearsayResolve, hv, he, hx, hu]
    · intro hv
      simp [Contracts.hearsayResolve, hv])

/-! D047-D056 (group 06 借贷、担保与共同债务, W2-A batch B06): each
theorem discharges the demand's own contract; the first conjunct is
the group-registered quantity component inlined as `parts_nonneg`.
The ledger/charge/security constructions are consumed from the shared
carrier `Seams/UnifiedQuantLedger.lean` (B06 prerequisite); the
group-06 qualitative helpers live in `Contracts`. -/

open JurisLean.FullMath.Contracts (loanRow SigningCapacity respOf SpousalDebt
  jointDebt CorpEdge personalityMix corpJointDue)

open JurisLean.Seams.UnifiedQuantLedger (LedgerItem DebtKind FeeBasis
  ClaimStatus feeSupported loanLedger outstanding
  afterStream afterPay allocsOf demoLedger StreamLegal InterestSeg LoanCharges
  termInterest segInterest ChargesWithin totalCharges sampleAll sampleNoPenalty
  SecKind SecEvent requiredEvent secEstablished corpSuretyEstablished
  distributeProceeds FactCand admittedFact CashRule CashFact statusConsistent
  outstanding_loanLedger outstanding_afterStream discharged_iff_paid_covered
  delivery_repayment_separate_readout allocsOf_mem_nonneg allocsOf_sum_le
  afterPay_idents duplicate_payment_rejected demoLedger_readout
  termInterest_indep seg_split stacking_not_default
  signing_not_mortgage_established signing_not_pledge_established
  distribute_conserve distribute_priority no_blanket_invalidation
  unsourced_not_admitted income_not_impossible self_quoted_not_supported
  sum_filter_partition)

open JurisLean.Seams.UnifiedQuantities (remainingAfter)

theorem demand_D047 : Contracts.demand_D047 := And.intro JurisLean.FullMath.Numeric.parts_nonneg
  (by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro id p
      exact (outstanding_loanLedger id p).2
    · intro items hnn ps hps
      exact discharged_iff_paid_covered items hnn ps hps
    · exact delivery_repayment_separate_readout
    · have hnn : ∀ it ∈ loanLedger true 1 200, 0 ≤ it.amount := by
        intro it hit
        simp only [loanLedger] at hit
        split at hit
        · rcases List.mem_cons.1 hit with rfl | hit
          · norm_num
          · cases hit
        · cases hit
      rw [outstanding_afterStream [200] _ hnn (by norm_num),
        (outstanding_loanLedger 1 200).1]
      norm_num)

theorem demand_D048 : Contracts.demand_D048 := And.intro JurisLean.FullMath.Numeric.parts_nonneg
  (by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro items p hnn hp
      exact ⟨allocsOf_mem_nonneg items p hnn hp, allocsOf_sum_le items p hp,
        afterPay_idents p items⟩
    · exact duplicate_payment_rejected
    · exact demoLedger_readout.1
    · have h : allocsOf 150
          [loanRow 2 DebtKind.interest 100, loanRow 3 DebtKind.principal 200]
          = [100, 50] := by
        norm_num [allocsOf, loanRow, min_def]
      refine ⟨h, ?_⟩
      intro heq
      rw [h] at heq
      have hsum := congrArg List.sum heq
      simp only [List.sum_cons, List.sum_nil] at hsum
      norm_num at hsum)

theorem demand_D049 : Contracts.demand_D049 := And.intro JurisLean.FullMath.Numeric.parts_nonneg
  (by
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact termInterest_indep
    · exact seg_split
    · intro cap c h
      exact h
    · exact stacking_not_default)

theorem demand_D050 : Contracts.demand_D050 := And.intro JurisLean.FullMath.Numeric.parts_nonneg
  (by
    refine ⟨⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_⟩⟩
    · rfl
    · rfl
    · rfl
    · simp [requiredEvent]
    · exact signing_not_mortgage_established
    · exact signing_not_pledge_established
    · simp [secEstablished, requiredEvent]
    · simp [secEstablished, requiredEvent]
    · exact distribute_conserve
    · exact distribute_priority)

theorem demand_D051 : Contracts.demand_D051 := And.intro JurisLean.FullMath.Numeric.parts_nonneg
  (by
    refine ⟨?_, ?_, ?_⟩
    · intro evs
      exact Iff.rfl
    · exact no_blanket_invalidation
    · simp [corpSuretyEstablished])

theorem demand_D052 : Contracts.demand_D052 := And.intro JurisLean.FullMath.Numeric.parts_nonneg
  (by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro signer p
      rfl
    · intro signer
      rfl
    · intro h
      simp [respOf] at h
    · intro p items
      induction items generalizing p with
      | nil => rfl
      | cons it rest ih =>
          show LedgerItem.beneficiary { it with amount := it.amount - min p it.amount } ::
              (afterPay (p - min p it.amount) rest).map LedgerItem.beneficiary
              = it.beneficiary :: rest.map LedgerItem.beneficiary
          exact congrArg (fun l => it.beneficiary :: l) (ih (p - min p it.amount)))

theorem demand_D053 : Contracts.demand_D053 := And.intro JurisLean.FullMath.Numeric.parts_nonneg
  (by
    refine ⟨?_, ?_, ?_⟩
    · intro d
      simp [jointDebt]
    · rfl
    · exact ⟨rfl, rfl⟩)

theorem demand_D054 : Contracts.demand_D054 := And.intro JurisLean.FullMath.Numeric.parts_nonneg
  (by
    refine ⟨?_, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · intro edges
      exact Iff.rfl
    · simp [personalityMix]
    · simp [corpJointDue, personalityMix]
    · simp [personalityMix]
    · simp [corpJointDue, personalityMix])

theorem demand_D055 : Contracts.demand_D055 := And.intro JurisLean.FullMath.Numeric.parts_nonneg
  (by
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact unsourced_not_admitted
    · intro id
      simp [admittedFact]
    · exact income_not_impossible
    · simp [admittedFact])

theorem demand_D056 : Contracts.demand_D056 := And.intro JurisLean.FullMath.Numeric.parts_nonneg
  (by
    refine ⟨⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩
    · decide
    · decide
    · decide
    · decide
    · exact self_quoted_not_supported
    · simp [statusConsistent, feeSupported]
    · exact sum_filter_partition)

/-! D057-D064 (group 07 侵权责任与损害, W2-A batch B07): each
theorem discharges the demand's own contract; the first conjunct is
the group-registered interval component inlined as
`JurisLean.FullMath.Numeric.Iv.fixed_y_bounds`. The interval/tort
constructions (QIv/TIv, tort kinds, gates/shares, liability modes,
loss ledger, remedies, scenario witnesses) are consumed from the
shared carrier `Seams/UnifiedQuantLedger.lean` (B07 prerequisite). -/

open JurisLean.Seams.UnifiedQuantLedger (TortKind TortCand
  selectByElements toResidual unmatched_partition unknown_kept_in_residual
  IvTag TIv tMem tScale FaultOK causeTimesLoss causeTimesLoss_sound
  FaultOK_scale imputed ivStrongCause correlation_not_imputation
  ivCause ivLossC ivLossA ivLossB ivInter interval_readout
  Shares LegalShares no_resp_zero_share small_share_mask_rejected badShares
  goodShares goodGate goodShares_legal
  RespMode externalDue JointRecoveryOK joint_double_full_violates recourseOf
  deficitOf recourse_pool_balanced suppDistribution supp_zero_when_primary_covers
  pays_sum_base joint_external_not_share_reduced
  LossEntry lossTotal dedupFirst dedupFirst_keys_nodup dedup_sum_le
  dedupFirst_id_of_nodup invoiceEntry appraisalEntry
  invoice_double_count_prevented
  Remedy amountOf nonmonetary_no_amount monetaryTotal monetary_total_blind_spot
  ScenarioWitness SummaryRecord FromSameWitness same_witness_consistent
  cross_scenario_mix_rejected wA wB mixedRecord)

open JurisLean.Seams.UnifiedQuantLedger.QIv

theorem demand_D057 : Contracts.demand_D057 := And.intro JurisLean.FullMath.Numeric.Iv.fixed_y_bounds
  (by
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact unmatched_partition
    · intro cands c hc
      by_cases hmet : c.elementsMet = true
      · exact Or.inl (List.mem_filter.mpr ⟨hc, by simp [hmet]⟩)
      · exact Or.inr (List.mem_filter.mpr ⟨hc, by simp [hmet]⟩)
    · exact unknown_kept_in_residual.1
    · exact unknown_kept_in_residual.2)

theorem demand_D058 : Contracts.demand_D058 := And.intro JurisLean.FullMath.Numeric.Iv.fixed_y_bounds
  (by
    refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ⟨?_, ?_⟩, ?_, ?_⟩
    · decide
    · decide
    · decide
    · exact causeTimesLoss_sound
    · exact fun a c ha hc0 hc1 => FaultOK_scale a ha c hc0 hc1
    · intro g ci
      exact Iff.rfl
    · exact correlation_not_imputation
    · exact interval_readout.2.2.2.1
    · exact interval_readout.2.2.2.2)

theorem demand_D059 : Contracts.demand_D059 := And.intro JurisLean.FullMath.Numeric.Iv.fixed_y_bounds
  (by
    refine ⟨?_, ?_, ?_⟩
    · exact fun s h i hg => no_resp_zero_share s h i hg
    · exact small_share_mask_rejected
    · exact goodShares_legal)

theorem demand_D060 : Contracts.demand_D060 := And.intro JurisLean.FullMath.Numeric.Iv.fixed_y_bounds
  (by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro loss share p d
      rfl
    · intro loss share p d
      rfl
    · intro loss share p d
      rfl
    · exact joint_double_full_violates
    · exact fun paid internalShare hsum => recourse_pool_balanced paid internalShare hsum
    · exact supp_zero_when_primary_covers)

theorem demand_D061 : Contracts.demand_D061 := And.intro JurisLean.FullMath.Numeric.Iv.fixed_y_bounds
  (by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · exact dedupFirst_keys_nodup
    · intro l h
      exact dedup_sum_le l [] h
    · exact dedupFirst_id_of_nodup
    · exact invoice_double_count_prevented.1
    · exact invoice_double_count_prevented.2)

theorem demand_D062 : Contracts.demand_D062 := And.intro JurisLean.FullMath.Numeric.Iv.fixed_y_bounds
  (by
    refine ⟨?_, ?_, ⟨?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact pays_sum_base
    · exact joint_external_not_share_reduced
    · intro loss recoveries
      exact Iff.rfl
    · norm_num [JointRecoveryOK]
    · exact fun paid internalShare hsum => recourse_pool_balanced paid internalShare hsum
    · exact vadd_assoc
    · exact vadd_comm
    · exact scale_distrib
    · exact scale_assoc
    · exact interval_readout.1
    · have hall : ∀ i : Fin 2, goodShares.gate i = true := by
        intro i
        fin_cases i <;> simp [goodShares, goodGate]
      exact pays_sum_base 100 goodShares.share (goodShares_legal.2.2 hall))

theorem demand_D063 : Contracts.demand_D063 := And.intro JurisLean.FullMath.Numeric.Iv.fixed_y_bounds
  (by
    refine ⟨nonmonetary_no_amount, ?_, monetary_total_blind_spot⟩
    intro q
    rfl)

theorem demand_D064 : Contracts.demand_D064 := And.intro JurisLean.FullMath.Numeric.Iv.fixed_y_bounds
  (by
    refine ⟨?_, same_witness_consistent, cross_scenario_mix_rejected⟩
    intro r w h
    exact h)

/-! D065-D076 (group 08 合同条款与权利义务审核, W2-A batch B08): each
theorem discharges the demand's own contract; the first conjunct is the
group-registered clause component inlined as `docPut_docPut`. -/

theorem demand_D065 : Contracts.demand_D065 := And.intro JurisLean.FullMath.Document.docPut_docPut
  (by
    intro e f x obs
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · cases f <;> cases x <;> rfl
    · rfl
    · rfl
    · rfl
    · decide
    · intro h
      exact h)

theorem demand_D066 : Contracts.demand_D066 := And.intro JurisLean.FullMath.Document.docPut_docPut
  (by
    intro cands chosen
    refine ⟨?_, ?_, ?_⟩
    · intro row hf
      simp only [Contracts.lawFinal]
      rw [hf]
    · intro hnone
      simp [Contracts.lawFinal, hnone]
    · intro hfind
      simp [Contracts.lawFinal, hfind])

theorem demand_D067 : Contracts.demand_D067 := And.intro JurisLean.FullMath.Document.docPut_docPut
  (by
    intro rows s a r p x f hfind
    refine ⟨?_, ⟨?_, ?_⟩, ?_⟩
    · exact fun e he => List.mem_of_find?_eq_some he
    · rfl
    · intro a' hne hEq
      simp at hEq
      exact hne hEq.symm
    · intro hEq
      exact absurd hEq (by simp))

theorem demand_D068 : Contracts.demand_D068 := And.intro JurisLean.FullMath.Document.docPut_docPut
  (by
    intro out k₁ k₂
    refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    · exact ⟨rfl, rfl, rfl, rfl⟩
    · decide
    · intro hne
      simp [Contracts.scopedApply, hne]
    · simp [Contracts.scopedApply]
    · simp [Contracts.scopedApply]
    · simp [Contracts.prioEval])

theorem demand_D069 : Contracts.demand_D069 := And.intro JurisLean.FullMath.Document.docPut_docPut
  (by
    intro rec
    refine ⟨?_, ?_, ?_, ?_⟩
    · decide
    · decide
    · exact ⟨rfl, rfl, rfl, rfl⟩
    · rfl)

theorem demand_D070 : Contracts.demand_D070 := And.intro JurisLean.FullMath.Document.docPut_docPut
  (by
    intro n c t
    refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ⟨?_, ?_⟩⟩
    · rfl
    · rfl
    · rfl
    · norm_num [Contracts.cocTrigger]
    · norm_num [Contracts.cocTrigger]
    · norm_num [Contracts.cocTrigger]
    · simp
    · simp)

theorem demand_D071 : Contracts.demand_D071 := And.intro JurisLean.FullMath.Document.docPut_docPut
  (by
    intro g
    refine ⟨?_, ?_, ⟨?_, ?_⟩⟩
    · rfl
    · simp
    · simp [Contracts.convertLicense]
    · simp [Contracts.convertLicense])

theorem demand_D072 : Contracts.demand_D072 := And.intro JurisLean.FullMath.Document.docPut_docPut
  (by
    intro rows g
    refine ⟨⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩⟩
    · decide
    · decide
    · decide
    · decide
    · intro h
      simp only [Contracts.grantOf, h]
    · intro h
      simp only [Contracts.grantOf, h]
    · intro h
      have hnone : rows.find? (fun r => decide (r.1 = Contracts.relAff)) = none :=
        List.find?_eq_none.mpr
          (fun r hr hdec => absurd (of_decide_eq_true hdec) (h r hr))
      simp only [Contracts.grantOf, hnone])

theorem demand_D073 : Contracts.demand_D073 := And.intro JurisLean.FullMath.Document.docPut_docPut
  (by
    intro p r t c
    refine ⟨⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_⟩⟩
    · simp
    · simp
    · simp
    · simp
    · simp
    · simp)

theorem demand_D074 : Contracts.demand_D074 := And.intro JurisLean.FullMath.Document.docPut_docPut
  (by
    intro p u a
    refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ⟨?_, ?_⟩⟩
    · rfl
    · rfl
    · rfl
    · norm_num [Contracts.revShare]
    · norm_num [Contracts.revShare]
    · norm_num [Contracts.revShare]
    · simp [Contracts.feeLine]
    · norm_num [Contracts.feeLine])

theorem demand_D075 : Contracts.demand_D075 := And.intro JurisLean.FullMath.Document.docPut_docPut
  (by
    intro a c
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_, ?_⟩, ?_⟩
    · simp [Contracts.applyCap]
    · simp [Contracts.applyCap]
    · simp [Contracts.applyCap]
    · norm_num [Contracts.applyCap]
    · norm_num [Contracts.applyCap]
    · simp)

theorem demand_D076 : Contracts.demand_D076 := And.intro JurisLean.FullMath.Document.docPut_docPut
  (by
    intro rows
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro s hs
      simp only [Contracts.survivors] at hs
      obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hs
      obtain ⟨hmem, hp⟩ := List.mem_filter.mp hr
      exact ⟨r, hmem, rfl, hp⟩
    · intro r hr hp
      simp only [Contracts.survivors]
      exact List.mem_map.mpr ⟨r, List.mem_filter.mpr ⟨hr, hp⟩, rfl⟩
    · intro kind hno hmem
      simp only [Contracts.survivors] at hmem
      obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hmem
      obtain ⟨hmemR, _⟩ := List.mem_filter.mp hr
      exact hno r hmemR rfl
    · intro hall hne hnil
      simp only [Contracts.survivors, List.map_eq_nil_iff] at hnil
      have hself : rows.filter (fun r => r.2) = rows :=
        List.filter_eq_self.mpr hall
      rw [hself] at hnil
      exact hne hnil)

/-! D077-D086 (group 09 并购与交割条件, W2-A batch B09): each
theorem discharges the demand's own contract; the first conjunct is the
group-registered Horn fixpoint component inlined as `cl_least_iterate`. -/

theorem demand_D077 : Contracts.demand_D077 := And.intro JurisLean.FullMath.Logic.cl_least_iterate
  (by
    intro rows times
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro r _hr
      simp [Contracts.repVerdict]
    · intro r _hr hs hc
      simp [Contracts.repVerdict, hs, hc]
    · simp
    · decide)

theorem demand_D078 : Contracts.demand_D078 := And.intro JurisLean.FullMath.Logic.cl_least_iterate
  (by
    intro k₁
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_⟩
    · simp [Contracts.maeHit]
    · simp [Contracts.maeHit]
    · simp [Contracts.maeHit]
    · simp [Contracts.maeHit]
    · intro k₂ hne
      show (if k₂ = k₁ ∧ true = true then false else true) = true ∧
          (if k₂ = k₁ ∧ true = true then true else true) = true
      exact ⟨if_neg (fun h => hne h.1.symm), if_neg (fun h => hne h.1.symm)⟩
    · simp [Contracts.maeHit])

theorem demand_D079 : Contracts.demand_D079 := And.intro JurisLean.FullMath.Logic.cl_least_iterate
  (by
    intro g kind b
    refine ⟨?_, ⟨?_, ?_⟩, ?_⟩
    · decide
    · simp [Contracts.knOf]
    · simp [Contracts.knOf]
    · intro hne hEq
      simp at hEq
      exact hne hEq.symm)

theorem demand_D080 : Contracts.demand_D080 := And.intro JurisLean.FullMath.Logic.cl_least_iterate
  (by
    intro acts
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro a ha
      obtain ⟨hmem, hc⟩ := List.mem_filter.mp ha
      simp only [Contracts.contactLegal, Bool.and_eq_true] at hc
      obtain ⟨h1, h2⟩ := hc
      exact ⟨hmem, h1, h2⟩
    · intro a ha h1 h2
      exact List.mem_filter.mpr ⟨ha, by
        simp only [Contracts.contactLegal, Bool.and_eq_true]
        exact ⟨h1, h2⟩⟩
    · intro a _ha hfalse hmem
      obtain ⟨_, hc⟩ := List.mem_filter.mp hmem
      simp [Contracts.contactLegal, hfalse] at hc
    · decide)

theorem demand_D081 : Contracts.demand_D081 := And.intro JurisLean.FullMath.Logic.cl_least_iterate
  (by
    intro day noticeDay windowEnd recChanged matched _horder
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro hle
      simp [Contracts.canTerm, hle]
    · intro hlt hm
      have hnle : ¬(day ≤ windowEnd) := by omega
      simp [Contracts.canTerm, hnle, hm]
    · intro _ hle
      simp [Contracts.canTerm, hle]
    · decide)

theorem demand_D082 : Contracts.demand_D082 := And.intro JurisLean.FullMath.Logic.cl_least_iterate
  (by
    intro inWindow
    refine ⟨⟨?_, ?_⟩, ?_, ?_, ⟨?_, ?_⟩, ?_⟩
    · norm_num [Contracts.isSuperiorOffer]
    · decide
    · norm_num [Contracts.isSuperiorOffer]
    · norm_num [Contracts.isSuperiorOffer]
    · rfl
    · have hlt : ((100 : ℚ) < 110) := by norm_num
      simp [Contracts.isSuperiorOffer, decide_eq_true hlt]
    · norm_num)

theorem demand_D083 : Contracts.demand_D083 := And.intro JurisLean.FullMath.Logic.cl_least_iterate
  (by
    intro ordinary consent
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp [Contracts.actionAllowed]
    · decide
    · simp
    · simp [Contracts.actionAllowed])

theorem demand_D084 : Contracts.demand_D084 := And.intro JurisLean.FullMath.Logic.cl_least_iterate
  (by
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
    · simp [Contracts.closingRemedies]
    · simp [Contracts.closingRemedies]
    · intro closingAlive wantsSP wantsTerm
      cases closingAlive <;> cases wantsSP <;> cases wantsTerm <;>
        simp [Contracts.closingRemedies]
    · intro wantsSP wantsTerm
      cases wantsSP <;> cases wantsTerm <;> simp [Contracts.closingRemedies])

theorem demand_D085 : Contracts.demand_D085 := And.intro JurisLean.FullMath.Logic.cl_least_iterate
  (by
    intro price
    refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_⟩
    · simp [Contracts.doubleTriggerPayout]
    · simp [Contracts.doubleTriggerPayout]
    · simp [Contracts.doubleTriggerPayout]
    · simp
    · norm_num [Contracts.doubleTriggerPayout])

theorem demand_D086 : Contracts.demand_D086 := And.intro JurisLean.FullMath.Logic.cl_least_iterate
  (by
    intro rows entity period prop
    refine ⟨?_, ?_, ⟨?_, ?_⟩, ?_⟩
    · simp [Contracts.diffWitness]
    · simp [Contracts.diffWitness]
    · simp [Contracts.schedStatus]
    · simp [Contracts.schedStatus]
    · simp)

/-! D087-D094 (group 10 企业调查、诉讼与执行数据, W2-A batch B10): each
theorem discharges the demand's own contract; the first conjunct is the
group-registered query-aggregation component inlined as
`exists_extension_witnessed`. -/

theorem demand_D087 : Contracts.demand_D087 := And.intro JurisLean.FullMath.Logic.exists_extension_witnessed
  (by
    intro key field v₁ v₂ hne
    refine ⟨?_, ⟨?_, ?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩
    · simp [Contracts.regSnapshot]
    · simp [Contracts.regSnapshot]
    · simp [Contracts.regSnapshot]
    · simp [Contracts.regSnapshot]
    · simp [Contracts.regSnapshot]
    · simp [Contracts.regSnapshot]
    · intro hEq
      simp at hEq)

theorem demand_D088 : Contracts.demand_D088 := And.intro JurisLean.FullMath.Logic.exists_extension_witnessed
  (by
    intro p q hp hq
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_, ?_⟩⟩
    · simp [Contracts.penHop]
    · simp [Contracts.penHop]
    · simp [Contracts.chainStake]
    · rfl
    · simp [Contracts.chainStake]
    · exact mul_ne_zero (ne_of_gt hp) (ne_of_gt hq)
    · norm_num [Contracts.controlOf]
    · norm_num [Contracts.controlOf]
    · rfl)

theorem demand_D089 : Contracts.demand_D089 := And.intro JurisLean.FullMath.Logic.exists_extension_witnessed
  (by
    intro ent caseId role text amt
    refine ⟨?_, ⟨?_, ?_⟩, ⟨?_, ?_, ?_⟩, ?_⟩
    · simp [Contracts.caseRowOf]
    · simp [Contracts.caseRowOf]
    · simp [Contracts.caseRowOf]
    · simp [Contracts.caseKeysOf, Contracts.keySeen]
    · simp [Contracts.caseKeysOf, Contracts.keySeen]
    · simp [Contracts.caseKeysOf, Contracts.keySeen]
    · simp)

theorem demand_D090 : Contracts.demand_D090 := And.intro JurisLean.FullMath.Logic.exists_extension_witnessed
  (by
    intro subject
    refine ⟨?_, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
    · decide
    · simp [Contracts.ecOf]
    · simp [Contracts.ecOf, Contracts.ecTerminated, Contracts.ecDishonest]
    · simp [Contracts.ecOf, Contracts.ecTerminated, Contracts.ecRestrictHigh]
    · simp [Contracts.ecOf, Contracts.ecTerminated, Contracts.ecDebtCleared]
    · intro hEq
      simp [Contracts.ecTerminated, Contracts.ecDishonest] at hEq)

theorem demand_D091 : Contracts.demand_D091 := And.intro JurisLean.FullMath.Logic.exists_extension_witnessed
  (by
    intro u t w hu ht _hw
    refine ⟨?_, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_⟩⟩
    · decide
    · simp [Contracts.amtTotalOf, Contracts.amtUnpaid]
    · simp [Contracts.amtTotalOf, Contracts.amtUnpaid, Contracts.amtTarget]
    · simp [Contracts.amtTotalOf, Contracts.amtUnpaid]
    · simp [Contracts.amtTotalOf, Contracts.amtUnpaid, Contracts.amtTarget]
    · simp [Contracts.amtTotalOf, Contracts.amtUnpaid, Contracts.amtTarget]
    · simp [Contracts.amtTotalOf, Contracts.amtUnpaid]
    · simp [Contracts.amtTotalOf, Contracts.amtUnpaid, Contracts.amtTarget]
    · intro h
      simp [Contracts.amtTotalOf, Contracts.amtCase, Contracts.amtTarget,
        Contracts.amtUnpaid] at h
      linarith)

theorem demand_D092 : Contracts.demand_D092 := And.intro JurisLean.FullMath.Logic.exists_extension_witnessed
  (by
    intro auth subject conduct date
    refine ⟨⟨?_, ?_⟩, ?_, ⟨?_, ?_⟩⟩
    · simp [Contracts.penaltyCurrent, Contracts.penEffective]
    · simp [Contracts.penaltyCurrent, Contracts.penEffective, Contracts.penRevoked]
    · rfl
    · decide
    · simp [Contracts.currentPenalties, Contracts.penaltyCurrent, Contracts.penEffective, Contracts.penRevoked])

theorem demand_D093 : Contracts.demand_D093 := And.intro JurisLean.FullMath.Logic.exists_extension_witnessed
  (by
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
    · simp [Contracts.organRowAt]
    · simp [Contracts.organRowAt]
    · simp [Contracts.organRowAt]
    · simp [Contracts.organRowAt]
    · simp [Contracts.organRowAt]
    · simp [Contracts.organRowAt]
    · simp)

theorem demand_D094 : Contracts.demand_D094 := And.intro JurisLean.FullMath.Logic.exists_extension_witnessed
  (by
    refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩⟩
    · simp [Contracts.repEdgeOf]
    · simp [Contracts.repEdgeOf]
    · simp [Contracts.repEdgeOf]
    · simp [Contracts.repEdgeOf]
    · simp [Contracts.repEdgeOf]
    · simp [Contracts.servedBy]
    · simp [Contracts.servedBy]
    · simp [Contracts.servedBy]
    · simp [Contracts.infersAllCases, Contracts.servedBy, Contracts.repEdgeOf]
    · simp [Contracts.infersAllCases, Contracts.servedBy, Contracts.repEdgeOf]
    · simp [Contracts.infersAllCases, Contracts.servedBy, Contracts.repEdgeOf])

/-! D095-D103 (group 11 金额、时间和经济敞口, W2-A batch B11): each
theorem discharges the demand's own contract; the first conjunct is
the group-registered calendar component inlined as
`succDay_ordinal_mono`. The calendar facts are consumed from
`Seams/UnifiedCalendar.lean`; the group-11 helpers live in
`Contracts`. -/

open JurisLean.FullMath.Contracts (taInterestSeg taImputeAll taStepRate
  taCappedMult taConsideration taRound taTriggered taMakeWhole
  taDeadlineArrived taRightArises taBackItem taAggregate taSurvivalUpdate
  taWorkingCapital taAdjustment)

open JurisLean.Seams.UnifiedCalendar (daysDiff toEpochDay)

set_option maxRecDepth 100000 in
theorem demand_D095 : Contracts.demand_D095 := And.intro JurisLean.FullMath.Numeric.succDay_ordinal_mono
  (by
    refine ⟨?_, ?_, ?_⟩
    · intro a m b base rate
      have h : (daysDiff a m : ℤ) + (daysDiff m b : ℤ) = daysDiff a b :=
        JurisLean.Seams.UnifiedCalendar.daysDiff_split a m b
      have hq : ((daysDiff a m : ℤ) : ℚ) + ((daysDiff m b : ℤ) : ℚ)
          = ((daysDiff a b : ℤ) : ℚ) := by exact_mod_cast h
      simp only [taInterestSeg]
      linear_combination (base * rate) * hq
    · intro pay buckets hpay hnn
      induction buckets generalizing pay with
      | nil =>
        refine ⟨?_, ?_⟩
        · simp only [taImputeAll, List.sum_nil]
          linarith
        · intro htot
          rw [List.sum_nil] at htot
          simp only [taImputeAll, List.sum_nil]
          linarith
      | cons b rest ih =>
        have hb : 0 ≤ b := hnn b (by simp)
        have hrest : ∀ x ∈ rest, 0 ≤ x := fun x hx => hnn x (by simp [hx])
        have hsub : 0 ≤ pay - min pay b := by
          have hmin := min_le_left pay b
          linarith
        obtain ⟨h1, h2⟩ := ih (pay - min pay b) hsub hrest
        simp only [taImputeAll, List.sum_cons]
        refine ⟨?_, ?_⟩
        · linarith
        · intro htot
          have hge : 0 ≤ List.sum rest := List.sum_nonneg hrest
          have key : pay - min pay b ≤ List.sum rest := by
            by_cases hle : pay ≤ b
            · have hm : min pay b = pay := min_eq_left hle
              linarith
            · have hm : min pay b = b := min_eq_right (by linarith)
              linarith
          have heq := h2 key
          linarith
    · refine ⟨?_, ?_, ?_⟩
      · have h1 : daysDiff ⟨2024, 1, 15⟩ ⟨2024, 3, 10⟩ = 55 := by decide
        simp only [taInterestSeg, h1]
        norm_num
      · have h2 : daysDiff ⟨2024, 1, 15⟩ ⟨2024, 2, 1⟩ = 17 := by decide
        have h3 : daysDiff ⟨2024, 2, 1⟩ ⟨2024, 3, 10⟩ = 38 := by decide
        simp only [taInterestSeg, h2, h3]
        norm_num
      · norm_num)

set_option maxRecDepth 100000 in
theorem demand_D096 : Contracts.demand_D096 := And.intro JurisLean.FullMath.Numeric.succDay_ordinal_mono
  (by
    refine ⟨?_, ?_, ?_⟩
    · intro ev a b oldRate newRate h1 h2
      have ha : ¬ (toEpochDay ev ≤ toEpochDay a) := by omega
      have hb : ¬ (toEpochDay ev ≤ toEpochDay b) := by omega
      simp only [taStepRate, if_neg ha, if_neg hb]
    · intro mult base
      simp only [taCappedMult]
      rfl
    · refine ⟨?_, ?_, ?_, ?_⟩
      · decide
      · have hc : ¬ (toEpochDay ⟨2024, 1, 1⟩ ≤ toEpochDay ⟨2023, 6, 30⟩) := by decide
        simp only [taStepRate, taCappedMult]
        rw [if_neg hc]
        rfl
      · have hc2 : toEpochDay ⟨2024, 1, 1⟩ ≤ toEpochDay ⟨2024, 1, 1⟩ := le_refl _
        simp only [taStepRate, taCappedMult]
        rw [if_pos hc2]
        rfl
      · norm_num)

set_option maxRecDepth 100000 in
theorem demand_D097 : Contracts.demand_D097 := And.intro JurisLean.FullMath.Numeric.succDay_ordinal_mono
  (by
    refine ⟨?_, ?_, ?_⟩
    · intro cash shares p1 p2 hs hne h
      apply hne
      simp only [taConsideration] at h
      have hm : shares * p1 = shares * p2 := by linarith
      exact mul_left_cancel₀ hs hm
    · intro shares price fx
      ring
    · refine ⟨?_, ?_, ?_⟩
      · simp only [taRound, taConsideration]
        norm_num
      · simp only [taRound]
        norm_num
      · norm_num)

set_option maxRecDepth 100000 in
theorem demand_D098 : Contracts.demand_D098 := And.intro JurisLean.FullMath.Numeric.succDay_ordinal_mono
  (by
    refine ⟨?_, ?_, ?_⟩
    · intro facility balance ratio hr hne h
      apply hne
      exact mul_right_cancel₀ hr h
    · intro trigger prepay balance ratio h
      have hd : taTriggered trigger prepay = false := by simp [taTriggered, h]
      rw [hd]
      rfl
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · decide
      · decide
      · decide
      · norm_num [taMakeWhole]
      · norm_num [taMakeWhole]
      · norm_num)

set_option maxRecDepth 100000 in
theorem demand_D099 : Contracts.demand_D099 := And.intro JurisLean.FullMath.Numeric.succDay_ordinal_mono
  (by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro p q ha hb hanchor hlt
      exact JurisLean.Seams.UnifiedCalendar.PeriodSpec.base_strict_order p q ha hb hanchor hlt
    · intro p h
      exact JurisLean.Seams.UnifiedCalendar.nextBiz_fixpoint p.holiday p.rollFuel p.deadline
        ((JurisLean.Seams.UnifiedCalendar.PeriodSpec.deadline_ge_base p h).1)
    · refine ⟨?_, ?_, ?_⟩
      · decide
      · decide
      · decide
    · refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · decide
      · decide
      · decide
      · decide
      · decide)

set_option maxRecDepth 100000 in
theorem demand_D100 : Contracts.demand_D100 := And.intro JurisLean.FullMath.Numeric.succDay_ordinal_mono
  (by
    refine ⟨?_, ?_, ?_⟩
    · intro deadline lead a hdv h
      exact JurisLean.Seams.UnifiedCalendar.backSchedule_some_addBack deadline lead a hdv h
    · intro floor deadline lead s hback hlt
      simp only [taBackItem, hback, if_neg (by omega : ¬ (toEpochDay floor ≤ toEpochDay s))]
    · refine ⟨?_, ?_, ?_, ?_⟩
      · decide
      · decide
      · decide
      · decide)

set_option maxRecDepth 100000 in
theorem demand_D101 : Contracts.demand_D101 := And.intro JurisLean.FullMath.Numeric.succDay_ordinal_mono
  (by
    refine ⟨?_, ?_, ?_, ?_⟩
    · decide
    · intro p c hp0 hp1 hc0
      have hpos : 0 < c * (1 - p) := mul_pos hc0 (by linarith)
      have hring : c * (1 - p) = c - p * c := by ring
      linarith
    · refine ⟨?_, ?_, ?_, ?_⟩
      · simp only [taAggregate]
        norm_num
      · norm_num
      · norm_num
      · norm_num
    · refine ⟨?_, ?_⟩
      · decide
      · decide)

set_option maxRecDepth 100000 in
theorem demand_D102 : Contracts.demand_D102 := And.intro JurisLean.FullMath.Numeric.succDay_ordinal_mono
  (by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro amount endDay termDay
      rfl
    · intro amount startDay endDay termDay hse hts
      have hn : ¬ (endDay ≤ termDay) := by omega
      simp only [taSurvivalUpdate, if_neg hn]
    · intro amount endDay termDay h
      simp only [taSurvivalUpdate, if_pos h]
    · intro term a b hab
      exact JurisLean.Seams.UnifiedCalendar.interval_in_ray_iff term a b hab
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · decide
      · decide
      · decide
      · decide
      · decide
      · decide)

set_option maxRecDepth 100000 in
theorem demand_D103 : Contracts.demand_D103 := And.intro JurisLean.FullMath.Numeric.succDay_ordinal_mono
  (by
    refine ⟨?_, ?_, ?_⟩
    · intro d1 d2 h1 h2 h
      exact JurisLean.Seams.UnifiedCalendar.toEpochDay_inj d1 d2 h1 h2 h
    · intro accounts exclusions e v h
      show (if exclusions.contains e then taWorkingCapital accounts exclusions
            else v + taWorkingCapital accounts exclusions)
          = taWorkingCapital accounts exclusions
      rw [h]
      rfl
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp [taWorkingCapital]
        norm_num
      · simp [taWorkingCapital]
        norm_num
      · simp [taWorkingCapital]
        norm_num
      · norm_num [taAdjustment]
      · simp [taWorkingCapital]
        norm_num
      · norm_num [taAdjustment]
      · norm_num)

/-! D104-D115 (group 12 起草、修订与交付, W2-A batch B12): each
theorem discharges the demand's own contract; the first conjunct is the
group-registered byte-syntax component inlined as
`parse_render_roundtrip`. -/

theorem demand_D104 : Contracts.demand_D104 := And.intro JurisLean.FullMath.Document.parse_render_roundtrip
  (by
    intro req src asmp hsrc hasmp
    refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩⟩
    · intro r hr
      simp at hr
      exact ⟨(req, Contracts.ansAdmits, src, asmp), by simp, hr.symm,
        Or.inl rfl, hsrc, hasmp⟩
    · intro r hr
      simp at hr
      exact ⟨(req, Contracts.ansDenies, src, asmp), by simp, hr.symm,
        Or.inr (Or.inl rfl), hsrc, hasmp⟩
    · intro r hr
      simp at hr
      exact ⟨(req, Contracts.ansReserves, src, asmp), by simp, hr.symm,
        Or.inr (Or.inr rfl), hsrc, hasmp⟩
    · intro h
      obtain ⟨a, hmem, -, hstance, -, -⟩ := h req (by simp)
      simp at hmem
      subst hmem
      rcases hstance with h | h | h <;>
        simp [Contracts.ansAdmits, Contracts.ansDenies,
          Contracts.ansReserves] at h
    · intro h
      obtain ⟨a, hmem, -, -, h2, -⟩ := h req (by simp)
      simp at hmem
      subst hmem
      exact h2 rfl
    · intro h
      obtain ⟨a, hmem, -, -, -, h3⟩ := h req (by simp)
      simp at hmem
      subst hmem
      exact h3 rfl
    · simp [Contracts.ansAdmits, Contracts.ansReserves]
    · simp [Contracts.ansAdmits, Contracts.ansDenies]
    · simp [Contracts.ansDenies, Contracts.ansReserves])

theorem demand_D105 : Contracts.demand_D105 := And.intro JurisLean.FullMath.Document.parse_render_roundtrip
  (by
    refine ⟨⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_⟩⟩
    · intro p hp
      simp at hp
      subst hp
      simp
    · intro p hp
      simp at hp
      rcases hp with rfl | rfl <;> simp
    · intro p hp
      simp at hp
      rcases hp with rfl | rfl <;> simp
    · intro d hd
      simp only [List.cons_append, List.nil_append]
      simp at hd
      rcases hd with rfl | rfl <;> (intro _; simp)
    · intro h
      have hg := h "gold-9" (by simp)
      simp at hg
    · intro h
      have hd := h ("res-1", "arg-1") (by simp)
      have harg := hd (by simp)
      simp at harg)

theorem demand_D106 : Contracts.demand_D106 := And.intro JurisLean.FullMath.Document.parse_render_roundtrip
  (by
    intro amt
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · intro c hc
      simp at hc
      rcases hc with rfl | rfl <;> simp
    · simp
    · intro h
      have hb := h ("claim-b", "pay-costs", amt) (by simp)
      simp at hb
    · intro h
      have hb := h ("claim-b", "pay-costs", amt) (by simp)
      simp at hb)

theorem demand_D107 : Contracts.demand_D107 := And.intro JurisLean.FullMath.Document.parse_render_roundtrip
  (by
    intro t src
    refine ⟨⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩⟩, ?_⟩
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · simp [Contracts.alertRowOf, Contracts.chgEnforcePosture]
    · simp [Contracts.alertRowOf, Contracts.chgEnforcePosture,
      Contracts.chgStatute]
    · simp [Contracts.alertRowOf, Contracts.chgEnforcePosture,
      Contracts.chgCaseEffect]
    · simp [Contracts.alertRowOf, Contracts.chgEnforcePosture,
      Contracts.chgReformPlan]
    · simp)

theorem demand_D108 : Contracts.demand_D108 := And.intro JurisLean.FullMath.Document.parse_render_roundtrip
  (by
    refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_⟩⟩
    · intro s hs
      simp at hs
      rcases hs with rfl | rfl | rfl | rfl
      · exact ⟨"structure-1", by decide, by simp⟩
      · exact ⟨"concl-1", by decide, by simp⟩
      · exact ⟨"cite-1", by decide, by simp⟩
      · exact ⟨"900-fen", by decide, by simp⟩
    · intro a ha
      simp at ha
      subst ha
      simp
    · decide
    · intro h
      have happ := h "assumption-1" (by simp)
      simp at happ
    · intro h
      obtain ⟨v, hv, -⟩ := h "numeric" (by simp)
      have hn : docGet [("section", "structure-1"), ("conclusion", "concl-1"),
          ("citation", "cite-1")] "numeric" = none := by decide
      rw [hn] at hv
      contradiction)

theorem demand_D109 : Contracts.demand_D109 := And.intro JurisLean.FullMath.Document.parse_render_roundtrip
  (by
    intro organ vote item safeguard
    refine ⟨⟨rfl, rfl⟩, rfl, ?_, ?_⟩
    · simp [Contracts.approvedBy]
    · simp [Contracts.approvedBy])

theorem demand_D110 : Contracts.demand_D110 := And.intro JurisLean.FullMath.Document.parse_render_roundtrip
  (by
    refine ⟨⟨fun d t v => JurisLean.FullMath.Document.docGet_put d t v,
      ⟨?_, ?_⟩⟩, ⟨?_, ?_, ?_, ?_⟩⟩
    · decide
    · decide
    · simp [Contracts.staleClient, docGet]
    · simp [Contracts.staleClient, docGet]
    · simp [Contracts.exclConflict, docGet]
    · simp [Contracts.exclConflict, docGet])

theorem demand_D111 : Contracts.demand_D111 := And.intro JurisLean.FullMath.Document.parse_render_roundtrip
  (by
    refine ⟨⟨?_, ?_, ?_, ⟨?_, ?_⟩⟩, ⟨?_, ?_, ?_⟩⟩
    · decide
    · decide
    · intro h
      have hn : ¬ ("preamble-9" ∈ Contracts.spreadOnce
          [("def-1", "clause-2"), ("clause-2", "outcome-3")]
          (Contracts.spreadOnce [("def-1", "clause-2")] ["def-1"])) := by decide
      exact hn h
    · decide
    · decide
    · decide
    · decide
    · decide)

theorem demand_D112 : Contracts.demand_D112 := And.intro JurisLean.FullMath.Document.parse_render_roundtrip
  (by
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_, ?_⟩⟩
    · intro x hx y hy
      have hvals : Contracts.valuesOf [[("commitment-amount", "500-fen")],
          [("commitment-amount", "500-fen"), ("closing-event", "signed")]]
          "commitment-amount" = ["500-fen", "500-fen"] := by decide
      rw [hvals] at hx hy
      simp at hx hy
      rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> rfl
    · decide
    · intro h
      have hx := h "500-fen" (by decide) "800-fen" (by decide)
      exact absurd hx (by decide)
    · decide
    · decide)

theorem demand_D113 : Contracts.demand_D113 := And.intro JurisLean.FullMath.Document.parse_render_roundtrip
  (by
    intro role amt
    refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ⟨?_, ?_⟩⟩
    · simp [Contracts.translateTerm]
    · simp [Contracts.translateTerm]
    · simp [Contracts.translateTerm]
    · rfl
    · simp
    · rfl
    · simp [Contracts.translateChecked, Contracts.translateTerm]
    · simp [Contracts.translateChecked])

theorem demand_D114 : Contracts.demand_D114 := And.intro JurisLean.FullMath.Document.parse_render_roundtrip
  (by
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · intro p hp
      simp at hp
      rcases hp with rfl | rfl <;> simp
    · intro k hk
      simp at hk
      rcases hk with rfl | rfl
      · exact ⟨("support-1", "src-1"), by simp, rfl⟩
      · exact ⟨("exception-1", "src-2"), by simp, rfl⟩
    · intro h
      have hk := h "exception-1" (by simp)
      obtain ⟨p, hp, h1⟩ := hk
      simp at hp
      subst hp
      simp at h1
    · intro h
      have hpp := h ("exception-1", "") (by simp)
      simp at hpp)

theorem demand_D115 : Contracts.demand_D115 := And.intro JurisLean.FullMath.Document.parse_render_roundtrip
  (by
    refine ⟨⟨⟨⟨?_, ?_, ?_⟩, ?_⟩, ?_⟩, ⟨?_, ?_, ?_⟩⟩
    · rfl
    · simp
    · intro r hr
      simp at hr
      subst hr
      simp
    · intro r hr
      simp at hr
      subst hr
      simp
    · exact JurisLean.FullMath.Document.docGet_put [] "claim-1" "900-fen"
    · intro h
      exact h.1.2.1 rfl
    · intro h
      have h1 := h.1.1
      have hf : Contracts.prefixDl "motion.csv" = false := rfl
      rw [hf] at h1
      exact Bool.noConfusion h1
    · intro h
      have hbad := h.2 ("internal-scratch", "draft-notes") (by simp)
      exact hbad rfl)

/-! D116-D123 (group 13 办案、交易工作流与策略, W2-A batch B13): each
theorem discharges the demand's own contract; the first conjunct is the
group-registered Bellman component
(JurisLean.FullMath.Numeric.bellman_onesided) inlined, the remaining
conjuncts are discharged against the region-local operational defs in
Contracts (VDR gap, closing-order legality, clarification actions,
risk ranking, market-sample advice, subpoena options, outline coverage,
provenance sourcing). -/

private theorem strIn_iff {d : String} {l : List String} :
    Contracts.strIn d l = true ↔ d ∈ l := by
  induction l with
  | nil =>
    constructor
    · intro h; simp [Contracts.strIn] at h
    · intro h; cases h
  | cons x xs ih =>
    by_cases hx : x = d
    · subst hx
      constructor
      · intro _; exact List.Mem.head _
      · intro _
        simp [Contracts.strIn]
    · simp only [Contracts.strIn, if_neg hx, ih, List.mem_cons]
      constructor
      · intro h; exact Or.inr h
      · intro h
        cases h with
        | inl he => exact absurd he.symm hx
        | inr h => exact h

theorem demand_D116 : Contracts.demand_D116 := And.intro JurisLean.FullMath.Numeric.bellman_onesided
  (by
    refine ⟨?_, ?_, ?_⟩
    · intro required vdr d
      constructor
      · intro hmem
        obtain ⟨h1, h2⟩ := List.mem_filter.mp hmem
        refine ⟨h1, ?_⟩
        intro hc
        rw [strIn_iff.mpr hc] at h2
        simp at h2
      · intro hmem
        obtain ⟨h1, h2⟩ := hmem
        refine List.mem_filter.mpr ⟨h1, ?_⟩
        cases hv : Contracts.strIn d vdr with
        | false => rfl
        | true => exact absurd (strIn_iff.mp hv) h2
    · intro required vdr d hd
      exact List.mem_map_of_mem hd
    · exact ⟨by rfl, by decide⟩)

theorem demand_D117 : Contracts.demand_D117 := And.intro JurisLean.FullMath.Numeric.bellman_onesided
  (by
    refine ⟨?_, rfl, ?_⟩
    · intro ts order t hlegal hmem
      simp only [Contracts.cloLegalOrder, Bool.and_eq_true] at hlegal
      obtain ⟨_, hall⟩ := hlegal
      have hft : Contracts.strIn t.name order = true
          ∧ Contracts.cloReady order t = true :=
        Bool.and_eq_true_iff.mp (List.all_eq_true.mp hall t hmem)
      exact hft.2
    · intro order
      cases order with
      | nil => rfl
      | cons x xs =>
        cases xs with
        | nil => rfl
        | cons y ys =>
          cases ys with
          | cons z zs => rfl
          | nil =>
            by_contra hfalse
            have h : Contracts.cloLegalOrder Contracts.cycTasks [x, y] = true := by
              cases hbool : Contracts.cloLegalOrder Contracts.cycTasks [x, y] with
              | true => rfl
              | false => exact absurd hbool hfalse
            simp only [Contracts.cloLegalOrder, Bool.and_eq_true] at h
            obtain ⟨_, hall⟩ := h
            have hA := List.all_eq_true.mp hall
              { name := "task-a", prereq := "task-b", permitted := true }
              (by simp [Contracts.cycTasks])
            have hB := List.all_eq_true.mp hall
              { name := "task-b", prereq := "task-a", permitted := true }
              (by simp [Contracts.cycTasks])
            simp only [Bool.and_eq_true] at hA hB
            obtain ⟨_, hA⟩ := hA
            obtain ⟨_, hB⟩ := hB
            have hA' : Contracts.cloBefore [x, y] "task-b" "task-a" = true := by
              have hthis : Contracts.cloReady [x, y]
                  { name := "task-a", prereq := "task-b", permitted := true }
                    = true := hA
              simp only [Contracts.cloReady] at hthis
              exact hthis
            have hB' : Contracts.cloBefore [x, y] "task-a" "task-b" = true := by
              have hthis : Contracts.cloReady [x, y]
                  { name := "task-b", prereq := "task-a", permitted := true }
                    = true := hB
              simp only [Contracts.cloReady] at hthis
              exact hthis
            unfold Contracts.cloBefore at hA' hB'
            by_cases hxB : x = "task-b"
            · rw [if_pos hxB] at hA'
              have hy : y = "task-a" := by
                have hmem := strIn_iff.mp hA'
                simp at hmem
                exact hmem.symm
              have hxB2 : ¬ (x = "task-a") := fun hx => by
                have hne : ("task-a" : String) = "task-b" := hx.symm.trans hxB
                exact absurd hne (by decide)
              rw [if_neg hxB2, hy] at hB'
              unfold Contracts.cloBefore at hB'
              simp [Contracts.strIn] at hB'
            · rw [if_neg hxB] at hA'
              unfold Contracts.cloBefore at hA'
              by_cases hyB : y = "task-b"
              · rw [if_pos hyB] at hA'
                simp [Contracts.strIn] at hA'
              · rw [if_neg hyB] at hA'
                simp [Contracts.cloBefore] at hA')

theorem demand_D118 : Contracts.demand_D118 := And.intro JurisLean.FullMath.Numeric.bellman_onesided
  (by
    refine ⟨?_, ?_, rfl, ⟨by simp only [Contracts.clarValue]; norm_num,
      by simp only [Contracts.clarValue]; norm_num⟩⟩
    · intro a hk hw
      cases kind : a.kind with
      | writtenConfirm => rw [kind] at hk; exact absurd hk (by decide)
      | supplement => rw [kind] at hk; exact absurd hk (by decide)
      | waiver =>
        simp only [Contracts.clarLegal, kind, hw]
    · intro norm pq g c
      exact ⟨rfl, rfl⟩)

theorem demand_D119 : Contracts.demand_D119 := And.intro JurisLean.FullMath.Numeric.bellman_onesided
  (by
    refine ⟨by rfl, ?_, by rfl, ⟨rfl, by decide⟩, by decide⟩
    · intro items i hblocked hmem
      obtain ⟨_, h2⟩ := List.mem_filter.mp hmem
      rw [hblocked] at h2
      simp at h2)

theorem demand_D120 : Contracts.demand_D120 := And.intro JurisLean.FullMath.Numeric.bellman_onesided
  (by
    refine ⟨?_, ⟨by norm_num [Contracts.marketShare, Contracts.majoritySample],
      by norm_num [Contracts.marketShare, Contracts.majoritySample]⟩, ?_⟩
    · intro s
      exact ⟨rfl, rfl, fun h => Contracts.AdviceKind.noConfusion h⟩
    · intro clause q basis h
      have hk : (Contracts.adviseFromMarket Contracts.majoritySample).kind
          = Contracts.AdviceKind.legalDuty := by
        rw [h]
      exact Contracts.AdviceKind.noConfusion hk)

theorem demand_D121 : Contracts.demand_D121 := And.intro JurisLean.FullMath.Numeric.bellman_onesided
  (by
    refine ⟨?_, rfl, rfl, rfl⟩
    intro c m h
    cases m with
    | quash =>
      simp only [Contracts.measureLegal, Bool.and_eq_true] at h
      obtain ⟨_, h2⟩ := h
      exact h2
    | vacate => exact h
    | protective =>
      simp only [Contracts.measureLegal, Bool.and_eq_true] at h
      obtain ⟨_, h2⟩ := h
      exact h2)

theorem demand_D122 : Contracts.demand_D122 := And.intro JurisLean.FullMath.Numeric.bellman_onesided
  (by
    refine ⟨by rfl, ?_, ⟨by rfl, rfl⟩⟩
    intro g o hcov n hn
    have hft : (Contracts.strIn n.id o.covered && Contracts.depsKeptFor o n
        && Contracts.altsKeptFor o n) = true := List.all_eq_true.mp hcov n hn
    have hall : (Contracts.strIn n.id o.covered && Contracts.depsKeptFor o n)
        = true ∧ Contracts.altsKeptFor o n = true := Bool.and_eq_true_iff.mp hft
    have hall2 : Contracts.strIn n.id o.covered = true
        ∧ Contracts.depsKeptFor o n = true := Bool.and_eq_true_iff.mp hall.1
    exact ⟨hall2.1, hall2.2, hall.2⟩)

theorem demand_D123 : Contracts.demand_D123 := And.intro JurisLean.FullMath.Numeric.bellman_onesided
  (by
    refine ⟨?_, ⟨by rfl, by rfl⟩, ⟨rfl, ?_, by rfl⟩, by rfl⟩
    · intro a hs
      simp only [Contracts.sourced, Bool.and_eq_true] at hs
      obtain ⟨h1, h2⟩ := hs
      obtain ⟨h3, h4⟩ := h2
      obtain ⟨h5, h6⟩ := h4
      constructor
      · intro hnil
        rw [hnil] at h1
        simp at h1
      · intro hnil
        rw [hnil] at h5
        simp at h5
    · intro h
      exact Contracts.FactReadout.noConfusion h)

theorem demand_D124 : Contracts.demand_D124 := JurisLean.FullMath.Evidence.step_rules_mono

theorem demand_D125 : Contracts.demand_D125 := JurisLean.FullMath.Evidence.step_rules_mono

theorem demand_D126 : Contracts.demand_D126 := JurisLean.FullMath.Evidence.step_rules_mono

theorem demand_D127 : Contracts.demand_D127 := JurisLean.FullMath.Evidence.step_rules_mono

theorem demand_D128 : Contracts.demand_D128 := JurisLean.FullMath.Evidence.step_rules_mono

theorem demand_D129 : Contracts.demand_D129 := JurisLean.FullMath.Evidence.step_rules_mono

theorem demand_D130 : Contracts.demand_D130 := JurisLean.FullMath.Evidence.step_rules_mono

theorem demand_D131 : Contracts.demand_D131 := JurisLean.FullMath.Probability.condition_incompatible_iff

theorem demand_D132 : Contracts.demand_D132 := JurisLean.FullMath.Probability.condition_incompatible_iff

theorem demand_D133 : Contracts.demand_D133 := JurisLean.FullMath.Probability.condition_incompatible_iff

theorem demand_D134 : Contracts.demand_D134 := JurisLean.FullMath.Probability.condition_incompatible_iff

theorem gap_X01 : Contracts.gap_X01 := JurisLean.FullMath.Gaps.gap_X01

theorem gap_X02 : Contracts.gap_X02 := JurisLean.FullMath.Gaps.gap_X02

theorem gap_X03 : Contracts.gap_X03 := JurisLean.FullMath.Gaps.gap_X03

theorem gap_X04 : Contracts.gap_X04 := JurisLean.FullMath.Gaps.gap_X04

theorem gap_X05 : Contracts.gap_X05 := JurisLean.FullMath.Gaps.gap_X05

theorem gap_X06 : Contracts.gap_X06 := JurisLean.FullMath.Gaps.gap_X06

theorem gap_X07 : Contracts.gap_X07 := JurisLean.FullMath.Gaps.gap_X07

theorem gap_X08 : Contracts.gap_X08 := JurisLean.FullMath.Gaps.gap_X08

theorem gap_X09 : Contracts.gap_X09 := JurisLean.FullMath.Gaps.gap_X09

theorem gap_X10 : Contracts.gap_X10 := JurisLean.FullMath.Gaps.gap_X10

end JurisLean.FullMath.Acceptance
