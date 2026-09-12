import JurisLean.FullMath.Core.Foundations

/-!
F06/F07 — Soundness and completeness of bounded argument generation.

Arguments have sourced leaves and rule nodes; `Generate facts rules d`
enumerates every rule application over combinations of previously generated
arguments. Generation is sound (everything generated is well-formed and of
height at most `d`) and complete within the bound (every well-formed argument
of height at most `d` is generated). The source layer is deliberately
separate from syntax.
-/

namespace JurisLean.FullMath.Logic

section Arguments
variable {A : Type} [DecidableEq A]

/-- A rule with declared premises and head. -/
structure Rul (A : Type) where
  premises : List A
  head : A

/-- Argument syntax: sourced leaves and rule applications. -/
inductive Arg (A : Type) where
  /-- Sourced fact leaf; the source layer is tracked separately. -/
  | leaf (conc : A)
  /-- Rule application over child arguments. -/
  | node (r : Rul A) (children : List (Arg A))

/-- Conclusion of an argument. -/
def Arg.concl {A : Type} : Arg A → A
  | .leaf c => c
  | .node r _ => r.head

/-- Structural height. -/
def Arg.height {A : Type} : Arg A → ℕ
  | .leaf _ => 0
  | .node _ cs => (cs.map Arg.height).foldr max 0 + 1

/-- Well-formedness: leaf conclusions are declared facts; nodes use declared
rules, children align with the rule premises and are themselves well-formed. -/
def WellFormed {A : Type} (facts : List A) (rules : List (Rul A)) : Arg A → Prop
  | .leaf c => c ∈ facts
  | .node r cs => r ∈ rules ∧ cs.map Arg.concl = r.premises ∧
      ∀ p ∈ cs, WellFormed facts rules p

/-- Max-fold bound helper. -/
theorem foldr_max_le (l : List ℕ) : ∀ a ∈ l, a ≤ l.foldr max 0 := by
  intro a ha
  induction l with
  | nil => exact absurd ha (by simp)
  | cons x xs ih =>
    rcases List.mem_cons.mp ha with rfl | ha
    · exact Nat.le_max_left _ _
    · exact Nat.le_trans (ih ha) (Nat.le_max_right _ _)

/-- Max-fold of a list bounded pointwise. -/
theorem foldr_max_le_of_forall (l : List ℕ) (k : ℕ) (h : ∀ x ∈ l, x ≤ k) :
    l.foldr max 0 ≤ k := by
  induction l with
  | nil => exact Nat.zero_le _
  | cons x xs ih =>
    show max x (List.foldr max 0 xs) ≤ k
    exact max_le (h x (by simp)) (ih (fun y hy => h y (by simp [hy])))

/-! Combinatorial rule applications. -/

/-- Choose, for each premise `p`, a previously generated argument concluding
`p`. -/
def ruleAppsGo {A : Type} [DecidableEq A] (prev : List (Arg A)) : List A → List (List (Arg A))
  | [] => [[]]
  | p :: ps =>
    (prev.filter (fun a => decide (Arg.concl a = p))).flatMap
      (fun x => (ruleAppsGo prev ps).map (fun xs => x :: xs))

/-- All combinations of children satisfying the premises of `r`. -/
def ruleApps {A : Type} [DecidableEq A] (r : Rul A) (prev : List (Arg A)) : List (List (Arg A)) :=
  ruleAppsGo prev r.premises

/-- Generated combinations align with the premises. -/
theorem ruleApps_align {A : Type} [DecidableEq A] (r : Rul A) (prev : List (Arg A)) :
    ∀ ps ∈ ruleApps r prev, ps.map Arg.concl = r.premises := by
  have hgo : ∀ (qs : List A) (xs : List (Arg A)), xs ∈ ruleAppsGo prev qs →
      xs.map Arg.concl = qs := by
    intro qs
    induction qs with
    | nil =>
      intro xs hx
      simp only [ruleAppsGo] at hx
      have hxs : xs = [] := by simpa using hx
      subst hxs
      rfl
    | cons p ps ih =>
      intro xs hx
      simp only [ruleAppsGo, List.mem_flatMap] at hx
      obtain ⟨x, hxfilter, hrest⟩ := hx
      simp only [List.mem_map] at hrest
      obtain ⟨ys, hys, heq⟩ := hrest
      subst heq
      simp only [List.mem_filter] at hxfilter
      obtain ⟨_, hconcl⟩ := hxfilter
      have hxeq : Arg.concl x = p := of_decide_eq_true hconcl
      show (x :: ys).map Arg.concl = p :: ps
      rw [List.map_cons, hxeq, ih ys hys]
  intro xs hx
  exact hgo r.premises xs hx

/-- Elements of generated combinations come from `prev`. -/
theorem ruleApps_prev {A : Type} [DecidableEq A] (r : Rul A) (prev : List (Arg A)) :
    ∀ ps ∈ ruleApps r prev, ∀ x ∈ ps, x ∈ prev := by
  have hgo : ∀ (qs : List A) (xs : List (Arg A)), xs ∈ ruleAppsGo prev qs →
      ∀ x ∈ xs, x ∈ prev := by
    intro qs
    induction qs with
    | nil =>
      intro xs hx x hxmem
      simp only [ruleAppsGo] at hx
      have hxs : xs = [] := by simpa using hx
      subst hxs
      exact absurd hxmem (by simp)
    | cons p ps ih =>
      intro xs hx x hxmem
      simp only [ruleAppsGo, List.mem_flatMap] at hx
      obtain ⟨y, hy, hrest⟩ := hx
      simp only [List.mem_map] at hrest
      obtain ⟨ys, hys, heq⟩ := hrest
      subst heq
      simp only [List.mem_filter] at hy
      rcases List.mem_cons.mp hxmem with rfl | hxmem
      · exact hy.1
      · exact ih ys hys x hxmem
  intro xs hx x hxmem
  exact hgo r.premises xs hx x hxmem

/-- Helper for completeness: aligned selections from `prev` are generated. -/
theorem ruleApps_complete {A : Type} [DecidableEq A] (r : Rul A) (prev : List (Arg A))
    (ps : List (Arg A))
    (halign : ps.map Arg.concl = r.premises)
    (hprev : ∀ x ∈ ps, x ∈ prev) : ps ∈ ruleApps r prev := by
  have hgo : ∀ (qs : List A) (xs : List (Arg A)), xs.map Arg.concl = qs →
      (∀ x ∈ xs, x ∈ prev) → xs ∈ ruleAppsGo prev qs := by
    intro qs
    induction qs with
    | nil =>
      intro xs hmap _
      cases xs with
      | nil => simp [ruleAppsGo]
      | cons x xs' => simp at hmap
    | cons p ps' ih =>
      intro xs hmap hmem
      obtain ⟨x, xs', hxs⟩ : ∃ (x : Arg A) (xs' : List (Arg A)), xs = x :: xs' := by
        cases xs with
        | nil => exact absurd hmap (by simp)
        | cons x xs' => exact ⟨x, xs', rfl⟩
      subst hxs
      have hmapc : Arg.concl x :: xs'.map Arg.concl = p :: ps' := by
        simpa using hmap
      obtain ⟨hx, hxs'⟩ := List.cons.inj hmapc
      have hxmem : x ∈ prev := hmem x (by simp)
      have hxs'mem : ∀ y ∈ xs', y ∈ prev := fun y hy =>
        hmem y (List.mem_cons_of_mem _ hy)
      simp only [ruleApps, ruleAppsGo, List.mem_flatMap]
      refine ⟨x, ?_, ?_⟩
      · simp only [List.mem_filter]
        exact ⟨hxmem, decide_eq_true hx⟩
      · simp only [List.mem_map]
        exact ⟨xs', ih xs' hxs' hxs'mem, rfl⟩
  exact hgo r.premises ps halign hprev

/-- Bounded enumeration. -/
def Generate {A : Type} [DecidableEq A] (facts : List A) (rules : List (Rul A)) : ℕ → List (Arg A)
  | 0 => facts.map Arg.leaf
  | d + 1 =>
    Generate facts rules d ++
    rules.flatMap (fun r => (ruleApps r (Generate facts rules d)).map
      (fun ps => Arg.node r ps))

/-- F06: generation is sound — every generated argument is well-formed with
height at most the budget. -/
theorem generate_sound {A : Type} [DecidableEq A] (facts : List A) (rules : List (Rul A)) :
    ∀ d a, a ∈ Generate facts rules d → WellFormed facts rules a ∧ Arg.height a ≤ d := by
  intro d
  induction d with
  | zero =>
    intro a ha
    simp only [Generate, List.mem_map] at ha
    obtain ⟨c, hc, heq⟩ := ha
    have ha' : a = Arg.leaf c := heq.symm
    subst ha'
    simp only [WellFormed]
    exact ⟨hc, by simp [Arg.height]⟩
  | succ d ih =>
    intro a ha
    simp only [Generate, List.mem_append] at ha
    rcases ha with ha | ha
    · have h := ih a ha
      exact ⟨h.1, Nat.le_succ_of_le h.2⟩
    · simp only [List.mem_flatMap] at ha
      obtain ⟨r, hrules, hmap⟩ := ha
      simp only [List.mem_map] at hmap
      obtain ⟨ps, hps, heq⟩ := hmap
      have ha' : a = Arg.node r ps := heq.symm
      subst ha'
      have halign : ps.map Arg.concl = r.premises := ruleApps_align r _ ps hps
      have hprev : ∀ p ∈ ps, p ∈ Generate facts rules d := fun p hp =>
        ruleApps_prev r _ ps hps p hp
      simp only [WellFormed]
      refine ⟨⟨hrules, halign, fun p hp => (ih p (hprev p hp)).1⟩, ?_⟩
      have hfold : (ps.map Arg.height).foldr max 0 ≤ d :=
        foldr_max_le_of_forall _ d (by
          intro h hh
          simp only [List.mem_map] at hh
          obtain ⟨p, hp, heq⟩ := hh
          exact heq ▸ (ih p (hprev p hp)).2)
      have hheight : Arg.height (Arg.node r ps) = (ps.map Arg.height).foldr max 0 + 1 := by
        simp only [Arg.height]
      omega

/-- F07: generation is complete within the bound. -/
theorem generate_complete {A : Type} [DecidableEq A] (facts : List A) (rules : List (Rul A)) :
    ∀ d a, WellFormed facts rules a → Arg.height a ≤ d → a ∈ Generate facts rules d := by
  intro d
  induction d with
  | zero =>
    intro a hw hh
    cases a with
    | leaf c =>
      have hc : c ∈ facts := by simpa only [WellFormed] using hw
      simp only [Generate, List.mem_map]
      exact ⟨c, hc, rfl⟩
    | node r cs =>
      have hheight : Arg.height (Arg.node r cs) = (cs.map Arg.height).foldr max 0 + 1 := by
        simp only [Arg.height]
      omega
  | succ d ih =>
    intro a hw hh
    cases a with
    | leaf c =>
      simp only [Generate, List.mem_append]
      exact Or.inl (ih _ hw (by simp [Arg.height]))
    | node r cs =>
      simp only [WellFormed] at hw
      obtain ⟨hrules, halign, hwf⟩ := hw
      have hheight : Arg.height (Arg.node r cs) = (cs.map Arg.height).foldr max 0 + 1 := by
        simp only [Arg.height]
      have hchild : ∀ p ∈ cs, Arg.height p ≤ d := by
        intro p hp
        have hle : Arg.height p ≤ (cs.map Arg.height).foldr max 0 :=
          foldr_max_le _ (Arg.height p) (List.mem_map_of_mem hp)
        omega
      have hprev : ∀ p ∈ cs, p ∈ Generate facts rules d := fun p hp =>
        ih p (hwf p hp) (hchild p hp)
      simp only [Generate, List.mem_append]
      refine Or.inr ?_
      simp only [List.mem_flatMap]
      refine ⟨r, hrules, ?_⟩
      simp only [List.mem_map]
      refine ⟨cs, ruleApps_complete r (Generate facts rules d) cs halign hprev, ?_⟩
      rfl
end Arguments

end JurisLean.FullMath.Logic
