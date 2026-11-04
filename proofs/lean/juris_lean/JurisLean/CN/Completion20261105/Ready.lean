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

def unitsAgree (s : Situation) : JurisLean.CN.Revision20261101.SharedConstraint → Bool
  | .equalReduction a b =>
    match s.accounts a.id,s.accounts b.id with
    | some x,some y => x.debt.amount.tag == y.debt.amount.tag
    | _,_ => true
  | _ => true

def legalCompatible (s : Situation) (w : PossibleWorld) : Prop :=
  (∀ o ∈ s.core.state.F, w.fact o.atom = true) ∧
  (∀ c ∈ s.core.state.constraints, satisfies w c ∧ unitsAgree s c = true) ∧
  (∀ r ∈ s.core.state.L, s.choices r.scope = some r.id → w.active r = true) ∧
  (∀ r ∈ s.core.state.L, ∀ q, knownReduction s r = some q → w.reduction r = q)

def legalWorldCheck (s : Situation) (w : PossibleWorld) : Bool :=
  s.core.state.F.all (fun o => w.fact o.atom) &&
  s.core.state.constraints.all (fun c => constraintCheck w c && unitsAgree s c) &&
  s.core.state.L.all (fun r =>
    s.choices r.scope != some r.id || w.active r) &&
  s.core.state.L.all (fun r => match knownReduction s r with
    | none => true | some q => w.reduction r == q)

/- C1/P3: one projection is actually used by the legal transition. Evidence
   and the proof criterion are deliberately absent from natural truth here. -/
def legalKernel (s : Situation) : KernelState (List LegalRelation) PossibleWorld :=
  ⟨s.core.state.L, legalCompatible s⟩

theorem legalWorldCheck_sound (s : Situation) (w : PossibleWorld)
    (h : legalWorldCheck s w = true) : legalCompatible s w := by
  have hc : s.core.state.F.all (fun o => w.fact o.atom) = true ∧
      s.core.state.constraints.all (fun c => constraintCheck w c && unitsAgree s c) = true ∧
      s.core.state.L.all (fun r => s.choices r.scope != some r.id || w.active r) = true ∧
      s.core.state.L.all (fun r => match knownReduction s r with
        | none => true | some q => w.reduction r == q) = true := by
    simpa only [legalWorldCheck, Bool.and_eq_true, and_assoc] using h
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro o ho
    exact List.all_eq_true.mp hc.1 o ho
  · intro c hc'
    have hp : constraintCheck w c = true ∧ unitsAgree s c = true := by
      simpa only [Bool.and_eq_true] using List.all_eq_true.mp hc.2.1 c hc'
    exact ⟨constraintCheck_sound w c hp.1,hp.2⟩
  · intro r hr hs
    have ha := List.all_eq_true.mp hc.2.2.1 r hr
    simpa [hs] using ha
  · intro r hr q hq
    have ha := List.all_eq_true.mp hc.2.2.2 r hr
    simpa [hq] using ha

/- C1: successful finite checks link shared equality to actual native accounts.
   Neither the desired equality nor an arbitrary quantity vector is a ticket. -/
theorem shared_actual_reduction (s : Situation) (w : PossibleWorld)
    (a b : LegalRelation) (qa qb : Quantity .money)
    (hw : legalCompatible s w) (ha : a ∈ s.core.state.L) (hb : b ∈ s.core.state.L)
    (hc : SharedConstraint.equalReduction a b ∈ s.core.state.constraints)
    (hqa : knownReduction s a = some qa) (hqb : knownReduction s b = some qb) : qa = qb := by
  have eq := (hw.2.1 _ hc).1
  exact (hw.2.2.2 a ha qa hqa).symm.trans (eq.trans (hw.2.2.2 b hb qb hqb))

def rebasedWorld (s : Situation) (w : PossibleWorld) : PossibleWorld :=
  {w with
    reduction := fun r => (knownReduction s r).getD (w.reduction r)
    active := fun r => w.active r && s.core.state.L.any (fun live => live.id == r.id)}

def checkPost {α : Type} (before : Situation) (w : PossibleWorld) (reply : Reply α) : Reply α :=
  match reply.answer with
  | .success _ =>
    if legalWorldCheck reply.after (rebasedWorld reply.after w) then reply
    else quiet before (.conflict .competentReview)
  | other => quiet before other

 theorem checkPost_success_nonempty {α : Type} (before : Situation) (w : PossibleWorld)
    (reply : Reply α) (value : α)
    (h : (checkPost before w reply).answer = .success value) :
    ∃ z, legalCompatible (checkPost before w reply).after z := by
  unfold checkPost at h ⊢
  cases ha : reply.answer with
  | success v =>
    simp only [ha] at h ⊢
    split at h
    · rename_i hc
      simp only [hc, ↓reduceIte]
      exact ⟨rebasedWorld reply.after w,legalWorldCheck_sound _ _ hc⟩
    · cases h
  | rejected k => simp [ha,quiet] at h
  | unknown k => simp [ha,quiet] at h
  | conflict k => simp [ha,quiet] at h
  | blockedHuman => simp [ha,quiet] at h

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
  (match selectedRules s.core r with
   | [law] => t.clauses.all (fun clause => containsAtom clause.1 law.guard)
   | _ => false)

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
        checkPost s w ⟨s.withCore (s.core.putState st rfl), .success ()⟩
      else quiet s (.rejected .unsupported)

/- Success here is permission for the particular triggered effect, not a
   procedural dismissal on a negative proof result. Decide below records all
   three judgments independently of constitutive triggering. -/
def legalDispatch (s : Situation) (r : Request) (p : ProofPolicy)
    (m : Mode) (w : PossibleWorld) : Reply Unit :=
  if automationAllowed s.core.state r.scope m = false then quiet s .blockedHuman
  else if authorized s.core.state.N r = false then quiet s (.rejected .unauthorized)
  else if (activeConflict s r.scope).isSome then
    quiet s (.conflict ((activeConflict s r.scope).getD .competentReview))
  else
    match selectedRules s.core r with
    | [] => quiet s (.unknown .inputUnchecked)
    | [law] =>
      match selectedTemplates s law with
      | [] => quiet s (.unknown .inputUnchecked)
      | [t] => checkedLaw s r law p w t
      | _ :: _ :: _ => quiet s (.conflict .competentReview)
    | _ :: _ :: _ => quiet s (.conflict .competentReview)

/- Institutional effects may delete/re-attribute R or freeze a proceeding.
   Their permission check must not demand a fictitious positive `formed`
   relation, and must not execute a staged append. Source/effect checking and
   the very same registered assessment remain mandatory. -/
def permissionRequestGate (s : Situation) (r : Request) (law : Rule) (p : ProofPolicy) : Bool :=
  s.core.state.N.version == r.version && law.source.id == r.rule &&
  law.source.version == r.version && law.scope == r.scope &&
  r.act == effectAction law.effect && p.scope == law.scope &&
  p.source.id == law.source.id && p.source.version == law.source.version

def permissionLaw (s : Situation) (r : Request) (law : Rule) (p : ProofPolicy)
    (w : PossibleWorld) (t : IssuedTemplate) : Reply Unit :=
  if permissionRequestGate s r law p = false then quiet s (.rejected .unsupported)
  else if legalWorldCheck s w = false then quiet s (.unknown .inputUnchecked)
  else match assessed s law t.body with
    | .unknown k => quiet s (.unknown k)
    | .known .undetermined => quiet s (.unknown .systemNotJudge)
    | .known .notEstablished => quiet s (.rejected .prerequisites)
    | .known .established =>
      if policyAgreement s law p .established then quiet s (.success ())
      else quiet s (.rejected .unsupported)

def permissionDispatch (s : Situation) (r : Request) (p : ProofPolicy)
    (m : Mode) (w : PossibleWorld) : Reply Unit :=
  if automationAllowed s.core.state r.scope m = false then quiet s .blockedHuman
  else if authorized s.core.state.N r = false then quiet s (.rejected .unauthorized)
  else if (activeConflict s r.scope).isSome then
    quiet s (.conflict ((activeConflict s r.scope).getD .competentReview))
  else match selectedRules s.core r with
    | [] => quiet s (.unknown .inputUnchecked)
    | [law] => match selectedTemplates s law with
      | [] => quiet s (.unknown .inputUnchecked)
      | [t] => permissionLaw s r law p w t
      | _ :: _ :: _ => quiet s (.conflict .competentReview)
    | _ :: _ :: _ => quiet s (.conflict .competentReview)

theorem permissionLaw_ready (s : Situation) (r : Request) (law : Rule) (p : ProofPolicy)
    (w : PossibleWorld) (t : IssuedTemplate) (ht : t ∈ selectedTemplates s law)
    (h : (permissionLaw s r law p w t).answer = .success ()) : Ready s law t p := by
  unfold permissionLaw at h
  split at h
  · cases h
  · split at h
    · cases h
    · rename_i hw
      have hc : legalWorldCheck s w = true := by cases hh : legalWorldCheck s w <;> simp_all
      cases ha : assessed s law t.body with
      | unknown k => simp [ha,quiet] at h
      | known j =>
        cases j with
        | notEstablished => simp [ha,quiet] at h
        | undetermined => simp [ha,quiet] at h
        | established =>
          simp only [ha] at h
          split at h
          · rename_i hp
            exact ⟨⟨w,legalWorldCheck_sound s w hc⟩,ht,ha,hp⟩
          · cases h

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

theorem permissionDispatch_success_ready (s : Situation) (r : Request) (p : ProofPolicy)
    (m : Mode) (w : PossibleWorld)
    (h : (permissionDispatch s r p m w).answer = .success ()) :
    ∃ law t, law ∈ s.core.state.N.rules ∧ Ready s law t p := by
  unfold permissionDispatch at h
  split at h
  · cases h
  · split at h
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
                refine ⟨law,t,selected_rule_member s.core r law hs,?_⟩
                exact permissionLaw_ready s r law p w t (by rw [ht]; simp) h

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
  exact (hw.2.1 _ hc).1 ⟨hw.2.2.1 a ha sa, hw.2.2.1 b hb sb⟩

#print axioms shared_actual_reduction
#print axioms checkPost_success_nonempty
#print axioms legalWorldCheck_sound
#print axioms effect_uses_legal_projection
#print axioms no_template_authority_no_registration
#print axioms checkedLaw_ready
#print axioms legalDispatch_success_ready
#print axioms permissionDispatch_success_ready
#print axioms legalDispatch_refused
#print axioms admitted_not_natural_truth
#print axioms selected_exclusive_empty
#print axioms permissionLaw_ready
end JurisLean.CN.Completion20261105
