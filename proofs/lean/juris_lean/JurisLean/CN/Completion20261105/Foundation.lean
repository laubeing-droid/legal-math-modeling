import JurisLean.CN.Revision20261101.World

/-!
Completion of V4 P3/P5 and audit A03/A04/A10.
The finite key certificate describes the stored evidence, not a Ready conclusion.
A supplied possible world is checked against every stored receipt and constraint.
An arbitrary ProofPolicy is permitted, but its actual guard answer must agree with
the independently computed admitted-evidence answer. No soundness field is assumed.
Frozen KernelV3 and the accepted Revision20261101 declarations remain unchanged.
-/
namespace JurisLean.CN.Completion20261105

open JurisLean.KernelV3
open JurisLean.CN.Revision20261101

structure CaseState where
  state : Sit
  keys : List (Ref .material)
  closed : ∀ i, i ∉ keys → state.E i = .absent

def initialCase : CaseState :=
  ⟨initial, [], by intro i _; rfl⟩

def constraintCheck (w : PossibleWorld) : JurisLean.CN.Revision20261101.SharedConstraint → Bool
  | .exclusive a b => !(w.active a && w.active b)
  | .sameLoss a b => w.lossIdentity a == w.lossIdentity b
  | .equalReduction a b => w.reduction a == w.reduction b

def cellCheck (w : PossibleWorld) {i : Ref .material} : EvidenceCell i → Bool
  | .accepted raw _ => w.fact raw.atom == raw.asserted
  | _ => true

def worldCheck (x : CaseState) (w : PossibleWorld) : Bool :=
  x.keys.all (fun i => cellCheck w (x.state.E i)) &&
  x.state.constraints.all (constraintCheck w)

/- Obligation: derive nonempty K from executed finite checks, rather than
   placing nonemptiness/Ready into RuleTicket. -/
theorem constraintCheck_sound (w : PossibleWorld)
    (c : JurisLean.CN.Revision20261101.SharedConstraint)
    (h : constraintCheck w c = true) : satisfies w c := by
  cases c with
  | exclusive a b =>
    cases ha : w.active a <;> cases hb : w.active b <;>
      simp_all [constraintCheck, satisfies]
  | sameLoss a b => simpa [constraintCheck, satisfies] using h
  | equalReduction a b => simpa [constraintCheck, satisfies] using h

theorem worldCheck_sound (x : CaseState) (w : PossibleWorld)
    (h : worldCheck x w = true) : compatible x.state w := by
  have hh : x.keys.all (fun i => cellCheck w (x.state.E i)) = true ∧
      x.state.constraints.all (constraintCheck w) = true := by
    simpa only [worldCheck, Bool.and_eq_true] using h
  constructor
  · intro i raw rc he
    by_cases hi : i ∈ x.keys
    · have hc := List.all_eq_true.mp hh.1 i hi
      simpa [cellCheck, he] using hc
    · have hz := x.closed i hi
      rw [hz] at he
      cases he
  · intro c hc
    exact constraintCheck_sound w c (List.all_eq_true.mp hh.2 c hc)

/- Evidence answer computed from actual accepted cells. Excluded/pending cells
   are skipped; the nonempty-world gate separately rejects inconsistent inputs. -/
def admittedVote (s : Sit) : List (Ref .material) → Atom → Judgment
  | [], _ => .undetermined
  | i :: ids, a =>
    match s.E i with
    | .accepted raw _ =>
      if raw.atom == a then
        if raw.asserted then .established else .notEstablished
      else admittedVote s ids a
    | _ => admittedVote s ids a

def factJudge (w : PossibleWorld) (a : Atom) : Judgment :=
  if w.fact a then .established else .notEstablished

def Refines (a b : Judgment) : Prop := a = .undetermined ∨ a = b

/- Obligation: every non-unknown policy fact comes from an admitted receipt and
   is true in every compatible world, not from an arbitrary function value. -/
theorem admittedVote_refines (s : Sit) (ids : List (Ref .material))
    (w : PossibleWorld) (hw : compatible s w) (a : Atom) :
    Refines (admittedVote s ids a) (factJudge w a) := by
  induction ids with
  | nil => exact Or.inl rfl
  | cons i ids ih =>
    cases he : s.E i with
    | absent => simpa [admittedVote, he] using ih
    | pending raw => simpa [admittedVote, he] using ih
    | excluded raw reason => simpa [admittedVote, he] using ih
    | accepted raw rc =>
      by_cases ha : raw.atom = a
      · have hf := hw.1 i raw rc he
        rw [ha] at hf
        cases hb : raw.asserted <;>
          simp_all [admittedVote, he, Refines, factJudge]
      · simpa [admittedVote, he, ha] using ih

theorem andJ_refines (a b c d : Judgment)
    (ha : Refines a c) (hb : Refines b d) :
    Refines (andJ a b) (andJ c d) := by
  cases a <;> cases b <;> cases c <;> cases d <;>
    simp_all [Refines, andJ]

theorem orJ_refines (a b c d : Judgment)
    (ha : Refines a c) (hb : Refines b d) :
    Refines (orJ a b) (orJ c d) := by
  cases a <;> cases b <;> cases c <;> cases d <;>
    simp_all [Refines, orJ]

theorem notJ_refines (a b : Judgment) (h : Refines a b) :
    Refines (notJ a) (notJ b) := by
  cases a <;> cases b <;> simp_all [Refines, notJ]

theorem formula_refines (v z : Atom → Judgment) (f : Formula)
    (h : ∀ a, Refines (v a) (z a)) :
    Refines (evalFormula v f) (evalFormula z f) := by
  induction f with
  | atom a => exact h a
  | both a b ha hb => exact andJ_refines _ _ _ _ ha hb
  | either a b ha hb => exact orJ_refines _ _ _ _ ha hb
  | neg a ha => exact notJ_refines _ _ ha

def SemanticReady (x : CaseState) (law : Rule) : Prop :=
  (∃ w, compatible x.state w) ∧
  ∀ w, compatible x.state w →
    evalFormula (factJudge w) law.guard = .established

def readyCheck (x : CaseState) (law : Rule) (p : ProofPolicy)
    (w : PossibleWorld) : Bool :=
  worldCheck x w &&
  (evalFormula (p.evaluate (admittedView x.state.E law.materials)) law.guard ==
    evalFormula (admittedVote x.state law.materials) law.guard) &&
  (evalFormula (admittedVote x.state law.materials) law.guard == .established)

theorem readyCheck_sound (x : CaseState) (law : Rule) (p : ProofPolicy)
    (w : PossibleWorld) (h : readyCheck x law p w = true) :
    SemanticReady x law := by
  have hc : worldCheck x w = true ∧
      evalFormula (p.evaluate (admittedView x.state.E law.materials)) law.guard =
        evalFormula (admittedVote x.state law.materials) law.guard ∧
      evalFormula (admittedVote x.state law.materials) law.guard = .established := by
    simpa [readyCheck, Bool.and_eq_true, and_assoc] using h
  refine ⟨⟨w, worldCheck_sound x w hc.1⟩, ?_⟩
  intro z hz
  have hr := formula_refines (admittedVote x.state law.materials) (factJudge z)
    law.guard (admittedVote_refines x.state law.materials z hz)
  rw [hc.2.2] at hr
  rcases hr with bad | good
  · cases bad
  · exact good.symm

theorem empty_worlds_not_ready (x : CaseState) (law : Rule)
    (h : ∀ w, ¬ compatible x.state w) : ¬ SemanticReady x law := by
  rintro ⟨⟨w, hw⟩, _⟩
  exact h w hw

/- The existing policy interface stays general. A constant positive policy
   cannot manufacture evidence support at the actual checked entry. -/
theorem empty_materials_not_ready (x : CaseState) (law : Rule)
    (p : ProofPolicy) (w : PossibleWorld) (a : Atom)
    (hm : law.materials = []) (hg : law.guard = .atom a) :
    readyCheck x law p w = false := by
  simp [readyCheck, hm, hg, evalFormula, admittedVote]

def requestGate (x : CaseState) (req : Request) (law : Rule)
    (p : ProofPolicy) : Bool :=
  x.state.N.version == req.version &&
  law.source.id == req.rule && law.source.version == req.version &&
  law.scope == req.scope && req.act == effectAction law.effect &&
  p.scope == law.scope && p.source.id == law.source.id &&
  p.source.version == law.source.version &&
  (match law.effect, law.formed with
   | .constitutive, some r => r.scope == req.scope
   | .constitutive, none => false
   | _, _ => true)

def executeChecked (x : CaseState) (req : Request) (law : Rule)
    (p : ProofPolicy) (mode : Mode) (w : PossibleWorld) : Execution :=
  if automationAllowed x.state req.scope mode = false then ⟨x.state, .blockedHuman⟩
  else if authorized x.state.N req = false then ⟨x.state, .unauthorized⟩
  else if requestGate x req law p = false then ⟨x.state, .awaiting .inputUnchecked⟩
  else if readyCheck x law p w = false then ⟨x.state, .awaiting .inputUnchecked⟩
  else ⟨applyEffect x.state (effectEvent x.state law .established), .applied⟩

/- Obligations F02/D5/A10: success of the actual function entails derived Ready;
   no authorization preserves the whole state; refusal precedes every policy. -/
theorem executeChecked_ready (x : CaseState) (r : Request) (law : Rule)
    (p : ProofPolicy) (m : Mode) (w : PossibleWorld)
    (h : (executeChecked x r law p m w).status = .applied) :
    SemanticReady x law := by
  unfold executeChecked at h
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · cases h
      · split at h
        · cases h
        · rename_i hc
          exact readyCheck_sound x law p w (by
            cases hr : readyCheck x law p w <;> simp_all)

theorem executeChecked_no_authority (x : CaseState) (r : Request) (law : Rule)
    (p : ProofPolicy) (m : Mode) (w : PossibleWorld)
    (h : authorized x.state.N r = false) :
    (executeChecked x r law p m w).after = x.state := by
  by_cases hm : automationAllowed x.state r.scope m = false <;>
    simp [executeChecked, hm, h]

theorem executeChecked_refused (x : CaseState) (r : Request) (law : Rule)
    (p : ProofPolicy) (w : PossibleWorld)
    (h : x.state.refusals.contains r.scope = true) :
    (executeChecked x r law p .automated w).status = .blockedHuman := by
  have hb : automationAllowed x.state r.scope .automated = false := by
    simp only [automationAllowed, h, Bool.not_true]
  simp [executeChecked, hb]

theorem executeChecked_frame (x : CaseState) (r : Request) (law : Rule)
    (p : ProofPolicy) (m : Mode) (w : PossibleWorld) :
    (executeChecked x r law p m w).after.F = x.state.F ∧
    (executeChecked x r law p m w).after.N = x.state.N ∧
    (executeChecked x r law p m w).after.E = x.state.E := by
  unfold executeChecked
  repeat' first | split | exact ⟨rfl, rfl, rfl⟩

/- Nonempty, supported and unjudicial success. The world is data inspected by
   worldCheck, and no Ready proof is an input to this construction. -/
def preparedCase : CaseState :=
  ⟨prepared, [⟨9⟩], by
    intro i hi
    have hn : i ≠ ⟨9⟩ := by simpa using hi
    simp [prepared, admitEvidence, recorded, initial, setEvidence, hn]⟩

def supportPolicy : ProofPolicy := ⟨toyNorm, toyScope, support⟩

theorem registration_checked_success :
    (executeChecked preparedCase toyRequest toyRule supportPolicy .human toyWorld).status =
      .applied := by decide

theorem registration_checked_relations :
    (executeChecked preparedCase toyRequest toyRule supportPolicy .human toyWorld).after.L =
      [toyRelation] := by decide

theorem checked_registration_is_ready :
    SemanticReady preparedCase toyRule :=
  executeChecked_ready preparedCase toyRequest toyRule supportPolicy .human toyWorld
    registration_checked_success

def constantPolicy : ProofPolicy :=
  ⟨toyNorm, toyScope, fun _ _ => .established⟩

theorem constant_policy_no_receipt :
    (executeChecked initialCase toyRequest toyRule constantPolicy .human toyWorld).status =
      .awaiting .inputUnchecked := by decide

#print axioms worldCheck_sound
#print axioms admittedVote_refines
#print axioms formula_refines
#print axioms readyCheck_sound
#print axioms empty_worlds_not_ready
#print axioms empty_materials_not_ready
#print axioms executeChecked_ready
#print axioms executeChecked_no_authority
#print axioms executeChecked_refused
#print axioms executeChecked_frame
#print axioms registration_checked_success
#print axioms registration_checked_relations
#print axioms checked_registration_is_ready
#print axioms constant_policy_no_receipt

end JurisLean.CN.Completion20261105

