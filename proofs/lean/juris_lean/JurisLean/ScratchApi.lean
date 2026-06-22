 import Mathlib.Data.Finset.Basic
 import Mathlib.Tactic

 open Finset

 /-! ScratchApi: Lock down actual mathlib4 (v4.30.0) API names.

 Each #check command produces the exact fully-qualified name and type.
 Use this file as the authoritative API reference for all proofs.
 -/

 -- Finset card lemmas
 #check Finset.card_le_card
 #check Finset.card_lt_card
 #check Finset.card_strictMono

 -- Finset subset / strict subset
 #check Finset.ssubset_iff_subset_ne
 #check Finset.Subset.antisymm
 #check Finset.Subset.trans

 -- Finset induction principles
 #check Finset.strongInduction
 #check Finset.strongInductionOn
 #check Finset.strongDownwardInduction

 -- Finset well-foundedness
 #check Finset.lt_wf

 -- Finset extensionality
 #check Finset.ext

 -- Finset empty / nonempty
 #check Finset.not_nonempty_iff_eq_empty
 #check Finset.eq_empty_iff_forall_not_mem
 #check Finset.nonempty_of_ne_empty
 #check Finset.ne_empty_of_nonempty

 -- Finset sdiff / union
 #check Finset.sdiff_eq_empty_iff_subset
 #check Finset.union_sdiff_self
 #check Finset.union_subset
 #check Finset.subset_union_left
 #check Finset.subset_union_right

 -- Finset filter
 #check Finset.filter_subset
 #check Finset.filter_subset_filter
 #check Finset.mem_filter

 -- Finset inter / empty
 #check Finset.inter_empty
 #check Finset.empty_inter

 -- Nat
 #check Nat.find
 #check Nat.find_spec
 #check Nat.find_min'
 #check Nat.le_induction

 -- Monotone / Function.iterate
 #check Monotone
 #check Function.iterate

 -- Card lemmas (alternate names to try)
 #check Finset.card_le_univ
 #check Finset.card_le_card_of_subset
