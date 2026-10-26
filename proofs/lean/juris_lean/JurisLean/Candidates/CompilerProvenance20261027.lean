import JurisLean.Candidates.CompilerClosure20261026

/-!
Original 03.5 / S03: a finite, topologically ordered provenance graph.
The executable checker consumes exact earlier outputs, checks every premise,
and reports the actual recursively collected leaves of the selected root.
Interpretation and rule applicability checks are supplied for the same Gamma.
Their truth in the world remains an explicit external semantic assumption.
-/

namespace JurisLean.Candidates.CompilerProvenance20261027

open JurisLean.Candidates.Final20261021
open JurisLean.Candidates.Final20261021.Compiler

structure Leaf where
  source : SourceRef
  position : Nat
  interpretationVersion : Nat
  atom : Nat
  deriving DecidableEq, Repr

structure RuleUse where
  reference : Nat
  normVersion : Nat
  rule : Rule Nat
  deriving DecidableEq, Repr

inductive Node where
  | leaf (claim : Leaf)
  | fire (rule : RuleUse) (parents : List Nat)
  deriving DecidableEq, Repr

structure Evidence where
  atom : Nat
  leaves : List Leaf
  deriving DecidableEq, Repr

def activeRules (ctx : Gamma) (catalog : List RuleUse)
    (ruleGate : Gamma → RuleUse → Bool) : List (Rule Nat) :=
  (catalog.filter fun r => decide (r.normVersion = ctx.normVersion) && ruleGate ctx r).map
    RuleUse.rule

def evalNode (ctx : Gamma) (catalog : List RuleUse)
    (leafCheck : Gamma → Leaf → Bool) (ruleGate : Gamma → RuleUse → Bool)
    (known : List Evidence) : Node → Option Evidence
  | .leaf claim =>
      if claim.interpretationVersion = ctx.interpretation ∧ leafCheck ctx claim = true then
        some ⟨claim.atom, [claim]⟩
      else none
  | .fire use parents =>
      let selected := parents.filterMap fun i => known[i]?
      if use ∈ catalog ∧ use.normVersion = ctx.normVersion ∧ ruleGate ctx use = true ∧
          (∀ i ∈ parents, i < known.length) ∧ selected.map Evidence.atom = use.rule.premises then
        some ⟨use.rule.conclusion, selected.flatMap Evidence.leaves⟩
      else none

def scan (ctx : Gamma) (catalog : List RuleUse)
    (leafCheck : Gamma → Leaf → Bool) (ruleGate : Gamma → RuleUse → Bool) :
    List Evidence → List Node → Option (List Evidence)
  | known, [] => some known
  | known, node :: rest =>
      match evalNode ctx catalog leafCheck ruleGate known node with
      | none => none
      | some next => scan ctx catalog leafCheck ruleGate (known ++ [next]) rest

def proposed_provenance_input (ctx : Gamma) (catalog : List RuleUse)
    (leafCheck : Gamma → Leaf → Bool) (ruleGate : Gamma → RuleUse → Bool)
    (nodes : List Node) (root query : Nat) : Result Evidence :=
  match scan ctx catalog leafCheck ruleGate [] nodes with
  | none => .unknown .checkIncomplete
  | some known =>
      match known[root]? with
      | none => .unknown .missingEvidence
      | some evidence =>
          if evidence.atom = query then .known evidence else .unknown .checkIncomplete

def Certified (ctx : Gamma) (catalog : List RuleUse)
    (leafCheck : Gamma → Leaf → Bool) (ruleGate : Gamma → RuleUse → Bool)
    (evidence : Evidence) : Prop :=
  Derives (· ∈ evidence.leaves.map Leaf.atom) (· ∈ activeRules ctx catalog ruleGate)
    evidence.atom ∧
  ∀ claim ∈ evidence.leaves,
    claim.interpretationVersion = ctx.interpretation ∧ leafCheck ctx claim = true

theorem evalNode_certified (ctx : Gamma) (catalog : List RuleUse)
    (leafCheck : Gamma → Leaf → Bool) (ruleGate : Gamma → RuleUse → Bool)
    (known : List Evidence) (node : Node) (out : Evidence)
    (prior : ∀ e ∈ known, Certified ctx catalog leafCheck ruleGate e)
    (accepted : evalNode ctx catalog leafCheck ruleGate known node = some out) :
    Certified ctx catalog leafCheck ruleGate out := by
  cases node with
  | leaf claim =>
      simp only [evalNode] at accepted
      split at accepted
      next valid =>
        cases accepted
        refine ⟨Derives.fact _ (by simp), ?_⟩
        intro leaf member
        have eq : leaf = claim := List.mem_singleton.mp member
        simpa only [eq] using valid
      next invalid => cases accepted
  | fire use parents =>
      simp only [evalNode] at accepted
      split at accepted
      next valid =>
        cases accepted
        rcases valid with ⟨inCatalog, version, permitted, backward, exactPremises⟩
        have allowed : use.rule ∈ activeRules ctx catalog ruleGate := by
          apply List.mem_map.mpr
          refine ⟨use, List.mem_filter.mpr ⟨inCatalog, ?_⟩, rfl⟩
          simp [version, permitted]
        have selectedSound : ∀ child ∈ parents.filterMap (fun i => known[i]?),
            Certified ctx catalog leafCheck ruleGate child := by
          intro child member
          obtain ⟨i, _, atIndex⟩ := List.mem_filterMap.mp member
          exact prior child (List.mem_of_getElem? atIndex)
        refine ⟨Derives.fire use.rule allowed ?_, ?_⟩
        · intro atom member
          rw [← exactPremises] at member
          obtain ⟨child, childMember, atomEq⟩ := List.mem_map.mp member
          rw [← atomEq]
          apply derives_mono_facts (rules := (· ∈ activeRules ctx catalog ruleGate))
            (larger := (· ∈ ((parents.filterMap fun i => known[i]?).flatMap
              Evidence.leaves).map Leaf.atom)) _ (selectedSound child childMember).1
          intro a sourceMember
          obtain ⟨leaf, leafMember, atomEq⟩ := List.mem_map.mp sourceMember
          exact List.mem_map.mpr ⟨leaf,
            List.mem_flatMap.mpr ⟨child, childMember, leafMember⟩, atomEq⟩
        · intro leaf member
          obtain ⟨child, childMember, leafMember⟩ := List.mem_flatMap.mp member
          exact (selectedSound child childMember).2 leaf leafMember
      next invalid => cases accepted

theorem scan_certified (ctx : Gamma) (catalog : List RuleUse)
    (leafCheck : Gamma → Leaf → Bool) (ruleGate : Gamma → RuleUse → Bool)
    (nodes : List Node) (known out : List Evidence)
    (prior : ∀ e ∈ known, Certified ctx catalog leafCheck ruleGate e)
    (accepted : scan ctx catalog leafCheck ruleGate known nodes = some out) :
    ∀ e ∈ out, Certified ctx catalog leafCheck ruleGate e := by
  induction nodes generalizing known with
  | nil => cases accepted; exact prior
  | cons node rest ih =>
      cases step : evalNode ctx catalog leafCheck ruleGate known node with
      | none => simp [scan, step] at accepted
      | some next =>
          simp only [scan, step] at accepted
          apply ih (known ++ [next]) _ accepted
          intro e member
          rcases List.mem_append.mp member with old | new
          · exact prior e old
          · have eq : e = next := List.mem_singleton.mp new
            rw [eq]
            exact evalNode_certified ctx catalog leafCheck ruleGate known node next prior step

def parentIndices : Node → List Nat
  | .leaf _ => []
  | .fire _ parents => parents

-- Strictly earlier indices provide a finite topological order. In particular
-- a self-reference or any directed cycle cannot pass this check.
def BackwardFrom : Nat → List Node → Prop
  | _, [] => True
  | count, node :: rest =>
      (∀ i ∈ parentIndices node, i < count) ∧ BackwardFrom (count + 1) rest

theorem evalNode_backward (ctx : Gamma) (catalog : List RuleUse)
    (leafCheck : Gamma → Leaf → Bool) (ruleGate : Gamma → RuleUse → Bool)
    (known : List Evidence) (node : Node) (out : Evidence)
    (accepted : evalNode ctx catalog leafCheck ruleGate known node = some out) :
    ∀ i ∈ parentIndices node, i < known.length := by
  cases node with
  | leaf claim => simp [parentIndices]
  | fire use parents =>
      simp only [evalNode] at accepted
      split at accepted
      next valid => exact valid.2.2.2.1
      next invalid => cases accepted

theorem scan_backward (ctx : Gamma) (catalog : List RuleUse)
    (leafCheck : Gamma → Leaf → Bool) (ruleGate : Gamma → RuleUse → Bool)
    (nodes : List Node) (known out : List Evidence)
    (accepted : scan ctx catalog leafCheck ruleGate known nodes = some out) :
    BackwardFrom known.length nodes := by
  induction nodes generalizing known with
  | nil => trivial
  | cons node rest ih =>
      cases step : evalNode ctx catalog leafCheck ruleGate known node with
      | none => simp [scan, step] at accepted
      | some next =>
          simp only [scan, step] at accepted
          refine ⟨evalNode_backward ctx catalog leafCheck ruleGate known node next step, ?_⟩
          simpa only [List.length_append, List.length_singleton] using
            ih (known ++ [next]) accepted

theorem u03_1_checked_provenance_sound (ctx : Gamma) (catalog : List RuleUse)
    (leafCheck : Gamma → Leaf → Bool) (ruleGate : Gamma → RuleUse → Bool)
    (nodes : List Node) (root query : Nat) (out : Evidence)
    (accepted : proposed_provenance_input ctx catalog leafCheck ruleGate nodes root query =
      .known out) :
    out.atom = query ∧ Certified ctx catalog leafCheck ruleGate out ∧ BackwardFrom 0 nodes := by
  unfold proposed_provenance_input at accepted
  cases run : scan ctx catalog leafCheck ruleGate [] nodes with
  | none => simp [run] at accepted
  | some known =>
      simp only [run] at accepted
      cases atRoot : known[root]? with
      | none => simp [atRoot] at accepted
      | some evidence =>
          simp only [atRoot] at accepted
          split at accepted
          next sameQuery =>
            cases accepted
            refine ⟨sameQuery, ?_, ?_⟩
            · exact scan_certified ctx catalog leafCheck ruleGate nodes [] known
                (by simp) run out (List.mem_of_getElem? atRoot)
            · exact scan_backward ctx catalog leafCheck ruleGate nodes [] known run
          next differentQuery => cases accepted

theorem backward_lookup (nodes : List Node) (count i : Nat) (node : Node)
    (ordered : BackwardFrom count nodes) (atIndex : nodes[i]? = some node) :
    ∀ parent ∈ parentIndices node, parent < count + i := by
  induction nodes generalizing count i with
  | nil => simp at atIndex
  | cons first rest ih =>
      cases i with
      | zero =>
          have same : first = node := by simpa using atIndex
          subst node
          simpa using ordered.1
      | succ i =>
          have lookup : rest[i]? = some node := by simpa using atIndex
          have smaller := ih (count + 1) i ordered.2 lookup
          intro parent member
          have bound := smaller parent member
          omega

def Edge (nodes : List Node) (child parent : Nat) : Prop :=
  ∃ node, nodes[child]? = some node ∧ parent ∈ parentIndices node

theorem u03_1_checked_provenance_acyclic (ctx : Gamma) (catalog : List RuleUse)
    (leafCheck : Gamma → Leaf → Bool) (ruleGate : Gamma → RuleUse → Bool)
    (nodes : List Node) (root query : Nat) (out : Evidence)
    (accepted : proposed_provenance_input ctx catalog leafCheck ruleGate nodes root query =
      .known out) : ∀ i, ¬Relation.TransGen (Edge nodes) i i := by
  have ordered := (u03_1_checked_provenance_sound ctx catalog leafCheck ruleGate
    nodes root query out accepted).2.2
  have edgeLess : ∀ i j, Edge nodes i j → j < i := by
    rintro i j ⟨node, atIndex, member⟩
    simpa using backward_lookup nodes 0 i node ordered atIndex j member
  have pathLess : ∀ i j, Relation.TransGen (Edge nodes) i j → j < i := by
    intro i j path
    induction path with
    | single edge => exact edgeLess _ _ edge
    | tail _ edge ih => exact lt_trans (edgeLess _ _ edge) ih
  intro i cycle
  exact Nat.lt_irrefl i (pathLess i i cycle)

-- The preceding accepted output supplies the actual facts of the next call.
-- Its leaf references are not replaced by a separate hand-written fact list.
def closureFromEvidence (ctx : Gamma) (catalog : List RuleUse)
    (ruleGate : Gamma → RuleUse → Bool) (out : Evidence) : List Nat :=
  let rules := activeRules ctx catalog ruleGate
  let facts := out.leaves.map Leaf.atom
  proposed_rule_input rules (finiteCarrier rules facts).card facts

theorem u03_1_provenance_consumed_by_finite_closure (ctx : Gamma) (catalog : List RuleUse)
    (leafCheck : Gamma → Leaf → Bool) (ruleGate : Gamma → RuleUse → Bool)
    (nodes : List Node) (root query : Nat) (out : Evidence)
    (accepted : proposed_provenance_input ctx catalog leafCheck ruleGate nodes root query =
      .known out) : query ∈ closureFromEvidence ctx catalog ruleGate out := by
  have checked := u03_1_checked_provenance_sound ctx catalog leafCheck ruleGate
    nodes root query out accepted
  rw [← checked.1]
  exact (u03_2_computed_at_carrier_iff _ _ _).mpr checked.2.1.1

theorem u03_1_provenance_semantic_composition (ctx : Gamma) (catalog : List RuleUse)
    (leafCheck : Gamma → Leaf → Bool) (ruleGate : Gamma → RuleUse → Bool)
    (nodes : List Node) (root query : Nat) (out : Evidence) (truth : Nat → Prop)
    (sourceSound : ∀ leaf, leaf.interpretationVersion = ctx.interpretation →
      leafCheck ctx leaf = true → truth leaf.atom)
    (rulesSound : ∀ r ∈ activeRules ctx catalog ruleGate,
      (∀ a ∈ r.premises, truth a) → truth r.conclusion)
    (accepted : proposed_provenance_input ctx catalog leafCheck ruleGate nodes root query =
      .known out) : truth query := by
  have checked := u03_1_checked_provenance_sound ctx catalog leafCheck ruleGate
    nodes root query out accepted
  rw [← checked.1]
  apply u03_1_relative_soundness (truth := truth) _ checked.2.1.1
  refine ⟨?_, rulesSound⟩
  intro a member
  obtain ⟨leaf, leafMember, atomEq⟩ := List.mem_map.mp member
  rw [← atomEq]
  have valid := checked.2.1.2 leaf leafMember
  exact sourceSound leaf valid.1 valid.2

theorem u03_1_reject_forward_reference (ctx : Gamma) (catalog : List RuleUse)
    (leafCheck : Gamma → Leaf → Bool) (ruleGate : Gamma → RuleUse → Bool)
    (known : List Evidence) (use : RuleUse) (parents : List Nat) (i : Nat)
    (member : i ∈ parents) (notEarlier : known.length ≤ i) :
    evalNode ctx catalog leafCheck ruleGate known (.fire use parents) = none := by
  cases checked : evalNode ctx catalog leafCheck ruleGate known (.fire use parents) with
  | none => rfl
  | some out =>
      have smaller := evalNode_backward ctx catalog leafCheck ruleGate known
        (.fire use parents) out checked i member
      omega

theorem u03_1_reject_wrong_premises (ctx : Gamma) (catalog : List RuleUse)
    (leafCheck : Gamma → Leaf → Bool) (ruleGate : Gamma → RuleUse → Bool)
    (known : List Evidence) (use : RuleUse) (parents : List Nat)
    (mismatch : (parents.filterMap fun i => known[i]?).map Evidence.atom ≠
      use.rule.premises) :
    evalNode ctx catalog leafCheck ruleGate known (.fire use parents) = none := by
  simp [evalNode, mismatch]

theorem u03_1_reject_unsupported_leaf (ctx : Gamma) (catalog : List RuleUse)
    (leafCheck : Gamma → Leaf → Bool) (ruleGate : Gamma → RuleUse → Bool)
    (known : List Evidence) (claim : Leaf) (unsupported : leafCheck ctx claim = false) :
    evalNode ctx catalog leafCheck ruleGate known (.leaf claim) = none := by
  simp [evalNode, unsupported]

theorem u03_1_reject_wrong_rule_version (ctx : Gamma) (catalog : List RuleUse)
    (leafCheck : Gamma → Leaf → Bool) (ruleGate : Gamma → RuleUse → Bool)
    (known : List Evidence) (use : RuleUse) (parents : List Nat)
    (wrongVersion : use.normVersion ≠ ctx.normVersion) :
    evalNode ctx catalog leafCheck ruleGate known (.fire use parents) = none := by
  simp [evalNode, wrongVersion]

-- S03's coverage relation connects individual interpretations. The desired
-- universal answer is derived from it, not supplied as a coverage assumption.
theorem u03_3_conservative_abstraction_sound {Concrete Abstract : Type*}
    (relation : Concrete → Abstract → Prop) (concreteQuery : Concrete → Prop)
    (abstractQuery : Abstract → Prop)
    (coverage : ∀ c, ∃ a, relation c a)
    (reflects : ∀ c a, relation c a → abstractQuery a → concreteQuery c)
    (abstractAnswer : ∀ a, abstractQuery a) : ∀ c, concreteQuery c := by
  intro c
  obtain ⟨a, related⟩ := coverage c
  exact reflects c a related (abstractAnswer a)

theorem u03_3_conservative_abstraction_exact {Concrete Abstract : Type*}
    (relation : Concrete → Abstract → Prop) (concreteQuery : Concrete → Prop)
    (abstractQuery : Abstract → Prop)
    (coverage : ∀ c, ∃ a, relation c a) (reverseCoverage : ∀ a, ∃ c, relation c a)
    (sameAnswer : ∀ c a, relation c a → (abstractQuery a ↔ concreteQuery c)) :
    (∀ a, abstractQuery a) ↔ ∀ c, concreteQuery c := by
  constructor
  · exact u03_3_conservative_abstraction_sound relation concreteQuery abstractQuery
      coverage (fun c a related => (sameAnswer c a related).mp)
  · intro concreteAnswer a
    obtain ⟨c, related⟩ := reverseCoverage a
    exact (sameAnswer c a related).mpr (concreteAnswer c)

theorem u03_3_interpretation_bijection_preserves_robust_queries
    {Left Right Query : Type*} (correspondence : Left ≃ Right)
    (leftEval : Left → Query → Bool) (rightEval : Right → Query → Bool)
    (sameAnswer : ∀ c q, rightEval (correspondence c) q = leftEval c q) (q : Query) :
    (∀ r, rightEval r q = true) ↔ ∀ l, leftEval l q = true := by
  constructor
  · intro allRight l
    rw [← sameAnswer l q]
    exact allRight (correspondence l)
  · intro allLeft r
    have equal := sameAnswer (correspondence.symm r) q
    rw [correspondence.apply_symm_apply] at equal
    exact equal.trans (allLeft (correspondence.symm r))

end JurisLean.Candidates.CompilerProvenance20261027

#check JurisLean.Candidates.CompilerProvenance20261027.u03_1_checked_provenance_sound
#print axioms JurisLean.Candidates.CompilerProvenance20261027.u03_1_checked_provenance_sound
#check JurisLean.Candidates.CompilerProvenance20261027.u03_1_provenance_consumed_by_finite_closure
#print axioms JurisLean.Candidates.CompilerProvenance20261027.u03_1_provenance_consumed_by_finite_closure
#check JurisLean.Candidates.CompilerProvenance20261027.u03_1_provenance_semantic_composition
#print axioms JurisLean.Candidates.CompilerProvenance20261027.u03_1_provenance_semantic_composition
#check JurisLean.Candidates.CompilerProvenance20261027.u03_1_checked_provenance_acyclic
#print axioms JurisLean.Candidates.CompilerProvenance20261027.u03_1_checked_provenance_acyclic
#check JurisLean.Candidates.CompilerProvenance20261027.u03_1_reject_forward_reference
#print axioms JurisLean.Candidates.CompilerProvenance20261027.u03_1_reject_forward_reference
#check JurisLean.Candidates.CompilerProvenance20261027.u03_1_reject_wrong_premises
#print axioms JurisLean.Candidates.CompilerProvenance20261027.u03_1_reject_wrong_premises
#check JurisLean.Candidates.CompilerProvenance20261027.u03_1_reject_unsupported_leaf
#print axioms JurisLean.Candidates.CompilerProvenance20261027.u03_1_reject_unsupported_leaf
#check JurisLean.Candidates.CompilerProvenance20261027.u03_1_reject_wrong_rule_version
#print axioms JurisLean.Candidates.CompilerProvenance20261027.u03_1_reject_wrong_rule_version
#check JurisLean.Candidates.CompilerProvenance20261027.u03_3_conservative_abstraction_exact
#print axioms JurisLean.Candidates.CompilerProvenance20261027.u03_3_conservative_abstraction_exact
#check JurisLean.Candidates.CompilerProvenance20261027.u03_3_interpretation_bijection_preserves_robust_queries
#print axioms JurisLean.Candidates.CompilerProvenance20261027.u03_3_interpretation_bijection_preserves_robust_queries
