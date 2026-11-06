import JurisLean.CN.Completion20261105.EngineConsumers

/-!
C1/C5, F02/F06/F07: the remaining public edges use the same actual Situation.
An assessment may record any of the three judgments; it is not a default
dismissal and is not itself a constitutive event. Binding requires that exact
record. Payment consumes the stored native cash state and accepted conservation
results, while learning remains unable to install a norm or a binding.
-/
namespace JurisLean.CN.Completion20261105
open JurisLean.KernelV3
open JurisLean.CN.Revision20261101

def assessDispatch (s : Situation) (c : Law.Call) : Reply Judgment :=
  let r := c.request
  if automationAllowed s.core.state r.scope c.mode = false then quiet s .blockedHuman
  else if !freshRequest s r || r.act != .decide then quiet s (.rejected .unauthorized)
  else if (activeConflict s r.scope).isSome then
    quiet s (.conflict ((activeConflict s r.scope).getD .competentReview))
  else match selectedRules s.core r with
    | [law] =>
      if c.policy.source.id != law.source.id ||
          c.policy.source.version != law.source.version || c.policy.scope != law.scope then
        quiet s (.rejected .unsupported)
      else if !legalWorldCheck s c.world then quiet s (.unknown .inputUnchecked)
      else match selectedTemplates s law with
        | [t] =>
          match assessed s law t.body with
          | .unknown k => quiet s (.unknown k)
          | .known j =>
            if policyAgreement s law c.policy j then quiet s (.success j)
            else quiet s (.rejected .unsupported)
        | [] => quiet s (.unknown .inputUnchecked)
        | _ :: _ :: _ => quiet s (.conflict .competentReview)
    | [] => quiet s (.unknown .inputUnchecked)
    | _ :: _ :: _ => quiet s (.conflict .competentReview)

def decisionSourceMatches (s : Situation) (d : DecisionSource) : Bool :=
  freshRequest s d.request && d.request.act == .decide && d.index.subject == d.request.scope &&
  (match s.core.state.E d.material with
   | .accepted raw receipt => raw.source == d.document && raw.atom.scope == d.request.scope &&
       receipt.issuer == d.request.actor && receipt.norm.id == d.request.rule &&
       receipt.norm.version == d.request.version
   | _ => false)

def admitDecisionSource (s : Situation) (r : Request) (d : DecisionSource) : Reply Unit :=
  if !freshRequest s r || r.act != .admitEvidence || r.scope != d.request.scope then
    quiet s (.rejected .unauthorized)
  else if decisionSourceMatches s d then
    match s.decisionSources.find? (fun old => old.document == d.document) with
    | none => ⟨{s with decisionSources := d :: s.decisionSources},.success ()⟩
    | some old => if old == d then quiet s (.success ()) else quiet s (.conflict .competentReview)
  else quiet s (.unknown .inputUnchecked)

/- Decide observes an actual issued document. It never upgrades an AI proof
   assessment into a judgment, and does not demand agreement with the model. -/
def recordDecision (s : Situation) (c : Law.Call) (document : Ref .document) : Reply DecisionRecord :=
  if automationAllowed s.core.state c.request.scope c.mode = false then quiet s .blockedHuman
  else if !freshRequest s c.request || c.request.act != .decide then quiet s (.rejected .unauthorized)
  else match s.decisionSources.filter (fun d => d.document == document && d.request == c.request &&
      decisionSourceMatches s d) with
    | [] => quiet s (.unknown .inputUnchecked)
    | [source] =>
      let d := source.record
      match s.core.state.decisions.find? (fun old => old.document == document) with
      | none =>
        let st := {s.core.state with decisions := d :: s.core.state.decisions}
        ⟨s.withCore (s.core.putState st rfl),.success d⟩
      | some old => if old == d then quiet s (.success old) else quiet s (.conflict .competentReview)
    | _ :: _ :: _ => quiet s (.conflict .competentReview)

def sourceBindingAllows (s : Situation) (b : DecideBinding) : Bool :=
  s.decisionSources.any (fun d => d.record == b.decision && d.kinds.contains b.kind &&
    d.index == b.index && decisionSourceMatches s d &&
    (if b.kind == .resJudicata || b.kind == .constitutive || b.kind == .executable then
      s.core.state.N.grants.any (fun g => g.role == .court && grantMatches g d.request)
     else true))

def bindDecided (s : Situation) (b : DecideBinding) (mode : Mode) : Reply Unit :=
  if automationAllowed s.core.state b.decision.request.scope mode = false then
    quiet s .blockedHuman
  else if s.core.state.decisions.contains b.decision &&
      freshRequest s b.decision.request && b.decision.request.act == .decide && sourceBindingAllows s b then
    ⟨EffectIR.adjust [.binding (.decide b)] s, .success ()⟩
  else quiet s (.rejected .unauthorized)

def registeredInScope (s : Situation) (scope : Scope) (n : NormRef) : Bool :=
  registeredNorm s n && s.core.state.N.rules.any (fun law =>
    law.source.id == n.id && law.source.version == n.version && law.scope == scope)

def otherSourceAllowed (s : Situation) (scope : Scope) : OtherSource → Bool
  | .persuasive _ => true
  | .referential _ norm | .credit _ norm | .publicValidity _ norm => registeredInScope s scope norm

def otherDocumentAvailable (s : Situation) (b : OtherBinding) : Bool :=
  s.core.keys.any (fun id =>
    match b.source,s.core.state.E id with
    | .persuasive document,cell =>
      (rawOf cell).any (fun raw => raw.source == document && raw.atom.scope == b.request.scope)
    | .referential document _,.accepted raw _ =>
      raw.source == document && raw.atom.scope == b.request.scope
    | .credit document _,.accepted raw receipt |
      .publicValidity document _,.accepted raw receipt =>
      raw.source == document && raw.atom.scope == b.request.scope && receipt.issuer == b.request.actor
    | _,_ => false)

def bindOtherSource (s : Situation) (b : OtherBinding) (mode : Mode) : Reply Unit :=
  if automationAllowed s.core.state b.request.scope mode = false then quiet s .blockedHuman
  else if !freshRequest s b.request || b.request.act != .otherBind then quiet s (.rejected .unauthorized)
  else if !(otherSourceAllowed s b.request.scope b.source) || !otherDocumentAvailable s b then
    quiet s (.unknown .inputUnchecked)
  else
    ⟨EffectIR.adjust [.binding (.other b)] s, .success ()⟩

def learnMaterial (s : Situation) (r : Request) (theta : List Rat)
    (i : Ref .material) (raw : Raw i) : Reply Unit :=
  if !freshRequest s r || r.act != .learnModel || r.scope != raw.atom.scope then
    quiet s (.rejected .unauthorized)
  else match rawOf (s.core.state.E i) with
    | some _ => quiet s (.rejected .prerequisites)
    | none =>
      ⟨EffectIR.adjust (EffectIR.learning theta i raw) s, .success ()⟩

def performPayment (s : Situation) (r : Request) (mode : Mode)
    (relation : Ref .relation) (payment : Native.PaymentPayload) : Reply Unit :=
  if automationAllowed s.core.state r.scope mode = false then quiet s .blockedHuman
  else if !freshRequest s r || r.act != .perform || payment.normVersion != r.version ||
      payment.relation.value != relation.value then quiet s (.rejected .unauthorized)
  else match s.accounts relation with
    | none => quiet s (.unknown .inputUnchecked)
    | some before =>
      if before.debt.relation.value != relation.value ||
          before.debt.obligor != payment.payer || before.debt.creditor != payment.payee ||
          !s.core.state.L.any (fun rel => rel.id == relation && rel.scope == r.scope &&
            rel.holder.value == before.debt.creditor.value &&
            rel.counterparty.value == before.debt.obligor.value) ||
          !admittedSource s ⟨payment.source.value⟩ r.scope ||
          !s.core.state.F.any (fun event => event.id.value == payment.cashId.value &&
            event.atom.scope == r.scope && event.actor.value == payment.payer.value) then
        quiet s (.rejected .prerequisites)
      else if s.core.state.ledger.any (fun p => p.event.value == payment.cashId.value) then
        quiet s (.rejected .prerequisites)
      else match cashSource before payment with
        | .known after =>
          let entry : Performance :=
            ⟨⟨payment.cashId.value⟩, relation, ⟨after.allocated - before.allocated⟩, r⟩
          ⟨EffectIR.adjust (EffectIR.payment entry relation after) s, .success ()⟩
        | .rejected _ => quiet s (.rejected .prerequisites)
        | .unknown reason => quiet s (.unknown (sourceUnknown reason))
        | .conflict _ _ => quiet s (.conflict .competentReview)

/- C4/C5: performance is a stateful consumer of the accepted cash theorem;
   it never manufactures a natural occurrence. The actual ledger stores only
   the debt allocation; the native state separately retains full cash/surplus. -/
theorem performance_preserves_F_L (s : Situation) (r : Request) (m : Mode)
    (rel : Ref .relation) (p : Native.PaymentPayload) :
    (performPayment s r m rel p).after.core.state.F = s.core.state.F ∧
    (performPayment s r m rel p).after.core.state.L = s.core.state.L := by
  unfold performPayment
  split
  · exact ⟨rfl,rfl⟩
  · split
    · exact ⟨rfl,rfl⟩
    · split
      · exact ⟨rfl,rfl⟩
      · split
        · exact ⟨rfl,rfl⟩
        · split
          · exact ⟨rfl,rfl⟩
          · split <;> exact ⟨rfl,rfl⟩

/- C4: closing the actual Perform consumer requires the stored post, not
   just a theorem about a different call to consumeCash. Success below derives
   the native prior/post equality and reuses the accepted conservation result. -/
theorem performance_success_conserves (s : Situation) (r : Request) (m : Mode)
    (rel : Ref .relation) (p : Native.PaymentPayload)
    (h : (performPayment s r m rel p).answer = .success ()) :
    ∃ before after, s.accounts rel = some before ∧ cashSource before p = .known after ∧
      (performPayment s r m rel p).after.accounts rel = some after ∧
      Native.Cash.Conserves after ∧ Native.Cash.CashConsistent after := by
  unfold performPayment at h ⊢
  split at h
  · cases h
  · rename_i hm
    split at h
    · cases h
    · rename_i ha
      cases hb : s.accounts rel with
      | none => simp [hb,quiet] at h
      | some before =>
        simp only [hb] at h ⊢
        split at h
        · cases h
        · rename_i hp
          split at h
          · cases h
          · rename_i hd
            cases hc : cashSource before p with
            | known after =>
              refine ⟨before,after,rfl,hc,?_,?_⟩
              · simp [hm,ha,hp,hd,hc,EffectIR.adjust,EffectIR.payment,EffectIR.write]
              · exact cash_actual_post_conserves s ⟨r.scope,r.scope.question⟩ before p after hc
            | unknown k => simp [hc,quiet] at h
            | rejected k => simp [hc,quiet] at h
            | conflict a b => simp [hc,quiet] at h

/- F06: having a decision candidate, score, template or model output never
   satisfies the exact stored-decision membership check. -/
theorem no_decision_no_binding (s : Situation) (b : DecideBinding) (m : Mode)
    (h : s.core.state.decisions.contains b.decision = false) :
    (bindDecided s b m).after = s := by
  unfold bindDecided
  split
  · rfl
  · simp only [h, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
    rfl

theorem learning_frame (s : Situation) (r : Request) (theta : List Rat)
    (i : Ref .material) (raw : Raw i) :
    (learnMaterial s r theta i raw).after.core.state.N = s.core.state.N ∧
    (learnMaterial s r theta i raw).after.core.state.L = s.core.state.L ∧
    (learnMaterial s r theta i raw).after.core.state.F = s.core.state.F ∧
    (learnMaterial s r theta i raw).after.core.state.bindings = s.core.state.bindings := by
  unfold learnMaterial
  split
  · exact ⟨rfl,rfl,rfl,rfl⟩
  · split <;> exact ⟨rfl,rfl,rfl,rfl⟩

theorem decision_assessment_preserves_relations (s : Situation) (c : Law.Call)
    (document : Ref .document) : (recordDecision s c document).after.core.state.L = s.core.state.L := by
  unfold recordDecision
  repeat' first | rfl | split
  all_goals dsimp only
  all_goals split <;> rfl

#print axioms no_decision_no_binding
#print axioms learning_frame
#print axioms decision_assessment_preserves_relations
#print axioms performance_preserves_F_L
#print axioms performance_success_conserves
end JurisLean.CN.Completion20261105
