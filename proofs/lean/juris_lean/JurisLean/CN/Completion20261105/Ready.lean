import JurisLean.CN.Completion20261105.State

/-!
F07/A10 repair of the public entry, preserving the older mathematical fragment.
Admitted testimony constrains the legally approved assessment, not natural truth.
Ready is derived by executing the scoped template, request checks and a finite
legal-world check. Neither Ready nor policy soundness is an input certificate.
The source-bound template is a legal parameter approved under D2, not a claim
that this finite criterion language exhausts any statutory proof standard.
-/
namespace JurisLean.CN.Completion20261105
open JurisLean.KernelV3
open JurisLean.CN.Revision20261101

def legalCompatible (s : Situation) (w : PossibleWorld) : Prop :=
  (∀ o ∈ s.core.state.F, w.fact o.atom = true) ∧
  (∀ c ∈ s.core.state.constraints, satisfies w c) ∧
  (∀ r ∈ s.core.state.L, s.choices r.scope = some r.id → w.active r = true)

def legalWorldCheck (s : Situation) (w : PossibleWorld) : Bool :=
  s.core.state.F.all (fun o => w.fact o.atom) &&
  s.core.state.constraints.all (constraintCheck w) &&
  s.core.state.L.all (fun r =>
    s.choices r.scope != some r.id || w.active r)

/- C1/P3: one projection is actually used by the legal transition. Evidence
   and the proof criterion are deliberately absent from natural truth here. -/
def legalKernel (s : Situation) : KernelState (List LegalRelation) PossibleWorld :=
  ⟨s.core.state.L, legalCompatible s⟩

theorem legalWorldCheck_sound (s : Situation) (w : PossibleWorld)
    (h : legalWorldCheck s w = true) : legalCompatible s w := by
  have hc : s.core.state.F.all (fun o => w.fact o.atom) = true ∧
      s.core.state.constraints.all (constraintCheck w) = true ∧
      s.core.state.L.all (fun r => s.choices r.scope != some r.id || w.active r) = true := by
    simpa only [legalWorldCheck, Bool.and_eq_true, and_assoc] using h
  refine ⟨?_, ?_, ?_⟩
  · intro o ho
    exact List.all_eq_true.mp hc.1 o ho
  · intro c hc'
    exact constraintCheck_sound w c (List.all_eq_true.mp hc.2.1 c hc')
  · intro r hr hs
    have ha := List.all_eq_true.mp hc.2.2 r hr
    simpa [hs] using ha

theorem effect_uses_legal_projection (s : Situation)
    (event : JudgmentEvent (List LegalRelation)) :
    (applyEffect s.core.state event).L = (transfer (legalKernel s) event).R_t := by
  cases event <;> rfl

def templateGate (s : Situation) (issued : IssuedTemplate) : Bool :=
  let r := issued.request
  let t := issued.body
  authorized s.core.state.N r && r.act == .addTemplate && t.scoped &&
  s.core.state.N.version == r.version && r.actor == t.issuer &&
  r.rule == t.source.id && r.version == t.source.version && r.scope == t.scope &&
  !(selectedRules s.core r).isEmpty

def templateMatches (law : Rule) (issued : IssuedTemplate) : Bool :=
  issued.body.scope == law.scope && issued.body.source.id == law.source.id &&
  issued.body.source.version == law.source.version && issued.body.source.source == law.source.source

def selectedTemplates (s : Situation) (law : Rule) : List IssuedTemplate :=
  s.templates.filter (fun t => templateMatches law t && templateGate s t)

def registerTemplate (s : Situation) (r : Request) (t : ProofTemplate) :
    Reply (Ref .document) :=
  if templateGate s ⟨r,t⟩ then
    ⟨{s with templates := ⟨r,t⟩ :: s.templates}, .success t.document⟩
  else quiet s (.rejected .unauthorized)

theorem no_template_authority_no_registration (s : Situation) (r : Request)
    (t : ProofTemplate) (h : authorized s.core.state.N r = false) :
    (registerTemplate s r t).after = s := by
  simp [registerTemplate, templateGate, h, quiet]

def assessed (s : Situation) (law : Rule) (t : ProofTemplate) : Check Judgment :=
  evalProofFormula t (admittedView s.core.state.E law.materials) law.guard

def policyAgreement (s : Situation) (law : Rule) (p : ProofPolicy) (j : Judgment) : Bool :=
  evalFormula (p.evaluate (admittedView s.core.state.E law.materials)) law.guard == j

def Ready (s : Situation) (law : Rule) (t : IssuedTemplate) (p : ProofPolicy) : Prop :=
  (∃ w, legalCompatible s w) ∧ t ∈ selectedTemplates s law ∧
  assessed s law t.body = .known .established ∧
  policyAgreement s law p .established = true

def checkedLaw (s : Situation) (r : Request) (law : Rule) (p : ProofPolicy)
    (w : PossibleWorld) (t : IssuedTemplate) : Reply Unit :=
  if requestGate s.core r law p = false then quiet s (.rejected .unsupported)
  else if legalWorldCheck s w = false then quiet s (.unknown .inputUnchecked)
  else
    match assessed s law t.body with
    | .unknown k => quiet s (.unknown k)
    | .known .undetermined => quiet s (.unknown .systemNotJudge)
    | .known .notEstablished => quiet s (.rejected .prerequisites)
    | .known .established =>
      if policyAgreement s law p .established then
        let st := applyEffect s.core.state (effectEvent s.core.state law .established)
        ⟨s.withCore (s.core.putState st rfl), .success ()⟩
      else quiet s (.rejected .unsupported)

/- Success here is permission for the particular triggered effect, not a
   procedural dismissal on a negative proof result. Decide below records all
   three judgments independently of constitutive triggering. -/
def legalDispatch (s : Situation) (r : Request) (p : ProofPolicy)
    (m : Mode) (w : PossibleWorld) : Reply Unit :=
  if automationAllowed s.core.state r.scope m = false then quiet s .blockedHuman
  else if authorized s.core.state.N r = false then quiet s (.rejected .unauthorized)
  else
    match selectedRules s.core r with
    | [] => quiet s (.unknown .inputUnchecked)
    | [law] =>
      match selectedTemplates s law with
      | [] => quiet s (.unknown .inputUnchecked)
      | [t] => checkedLaw s r law p w t
      | _ :: _ :: _ => quiet s (.conflict .competentReview)
    | _ :: _ :: _ => quiet s (.conflict .competentReview)

/- A10: actual successful checkedLaw execution entails the separately defined
   Ready. The only premise about the call is its returned success branch. -/
theorem checkedLaw_ready (s : Situation) (r : Request) (law : Rule) (p : ProofPolicy)
    (w : PossibleWorld) (t : IssuedTemplate)
    (ht : t ∈ selectedTemplates s law)
    (h : (checkedLaw s r law p w t).answer = .success ()) : Ready s law t p := by
  unfold checkedLaw at h
  split at h
  · cases h
  · split at h
    · cases h
    · rename_i hw
      have hc : legalWorldCheck s w = true := by cases hh : legalWorldCheck s w <;> simp_all
      cases ha : assessed s law t.body with
      | unknown k => simp [ha, quiet] at h
      | known j =>
        cases j with
        | notEstablished => simp [ha, quiet] at h
        | undetermined => simp [ha, quiet] at h
        | established =>
          simp only [ha] at h
          split at h
          · rename_i hp
            exact ⟨⟨w, legalWorldCheck_sound s w hc⟩, ht, ha, hp⟩
          · cases h

theorem legalDispatch_success_ready (s : Situation) (r : Request) (p : ProofPolicy)
    (m : Mode) (w : PossibleWorld)
    (h : (legalDispatch s r p m w).answer = .success ()) :
    ∃ law t, law ∈ s.core.state.N.rules ∧ Ready s law t p := by
  unfold legalDispatch at h
  split at h
  · cases h
  · split at h
    · cases h
    · cases hs : selectedRules s.core r with
      | nil => simp [hs, quiet] at h
      | cons law rest =>
        cases rest with
        | cons b tail => simp [hs, quiet] at h
        | nil =>
          simp only [hs] at h
          cases ht : selectedTemplates s law with
          | nil => simp [ht, quiet] at h
          | cons t rest =>
            cases rest with
            | cons b tail => simp [ht, quiet] at h
            | nil =>
              simp only [ht] at h
              refine ⟨law, t, selected_rule_member s.core r law hs, ?_⟩
              exact checkedLaw_ready s r law p w t (by rw [ht]; simp) h

theorem legalDispatch_refused (s : Situation) (r : Request) (p : ProofPolicy)
    (w : PossibleWorld) (h : s.core.state.refusals.contains r.scope = true) :
    (legalDispatch s r p .automated w).answer = .blockedHuman := by
  have hg : automationAllowed s.core.state r.scope .automated = false := by
    simp only [automationAllowed, h, Bool.not_true]
  simp [legalDispatch, hg, quiet]

/- No-fact assertion and a qualified admitted assertion may coexist. This
   disproves the old public-entry inference Admit -> natural Truth. -/
def testimonySituation : Situation :=
  { Situation.initial with core := ⟨prepared, [⟨9⟩], by
      intro i hi
      have hn : i ≠ ⟨9⟩ := by simpa using hi
      simp [prepared, admitEvidence, recorded, setEvidence, hn, initial]⟩ }

def dissentingWorld : PossibleWorld :=
  ⟨fun _ => false, fun _ => false, fun _ => ⟨0⟩, fun _ => ⟨0⟩⟩

theorem admitted_not_natural_truth :
    legalCompatible testimonySituation dissentingWorld ∧
    evalCriterion (admittedView testimonySituation.core.state.E [⟨9⟩]) qualifiedExample =
      .known .established ∧ dissentingWorld.fact toyAtom = false := by
  constructor
  · simp [legalCompatible, testimonySituation, prepared, admitEvidence, recorded, initial]
  · exact ⟨qualified_admitted_is_assessed, rfl⟩

theorem selected_exclusive_empty (s : Situation) (a b : LegalRelation)
    (ha : a ∈ s.core.state.L) (hb : b ∈ s.core.state.L)
    (hc : SharedConstraint.exclusive a b ∈ s.core.state.constraints)
    (sa : s.choices a.scope = some a.id) (sb : s.choices b.scope = some b.id) :
    ∀ w, ¬ legalCompatible s w := by
  intro w hw
  exact hw.2.1 _ hc ⟨hw.2.2 a ha sa, hw.2.2 b hb sb⟩

#print axioms legalWorldCheck_sound
#print axioms effect_uses_legal_projection
#print axioms no_template_authority_no_registration
#print axioms checkedLaw_ready
#print axioms legalDispatch_success_ready
#print axioms legalDispatch_refused
#print axioms admitted_not_natural_truth
#print axioms selected_exclusive_empty
end JurisLean.CN.Completion20261105
