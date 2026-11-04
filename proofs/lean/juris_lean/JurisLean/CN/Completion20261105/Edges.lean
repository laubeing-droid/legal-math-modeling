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

def recordDecision (s : Situation) (c : Law.Call) (document : Ref .document) : Reply DecisionRecord :=
  match (assessDispatch s c).answer with
  | .success j =>
    let d : DecisionRecord := ⟨document, c.request, j, true⟩
    match s.core.state.decisions.find? (fun old => old.document == document) with
    | none =>
      let st := {s.core.state with decisions := d :: s.core.state.decisions}
      ⟨s.withCore (s.core.putState st rfl), .success d⟩
    | some old =>
      if old == d then quiet s (.success old) else quiet s (.conflict .competentReview)
  | .rejected k => quiet s (.rejected k)
  | .unknown k => quiet s (.unknown k)
  | .conflict k => quiet s (.conflict k)
  | .blockedHuman => quiet s .blockedHuman

def bindDecided (s : Situation) (b : DecideBinding) (mode : Mode) : Reply Unit :=
  if automationAllowed s.core.state b.decision.request.scope mode = false then
    quiet s .blockedHuman
  else if s.core.state.decisions.contains b.decision &&
      freshRequest s b.decision.request && b.decision.request.act == .decide then
    ⟨s.withCore (s.core.putState (bindDecision s.core.state b) rfl), .success ()⟩
  else quiet s (.rejected .unauthorized)

def otherSourceAllowed (s : Situation) : OtherSource → Bool
  | .persuasive _ => true
  | .referential _ norm | .credit _ norm | .publicValidity _ norm => registeredNorm s norm

def bindOtherSource (s : Situation) (b : OtherBinding) (mode : Mode) : Reply Unit :=
  if automationAllowed s.core.state b.request.scope mode = false then quiet s .blockedHuman
  else if freshRequest s b.request && b.request.act == .otherBind &&
      otherSourceAllowed s b.source then
    ⟨s.withCore (s.core.putState (bindOther s.core.state b) rfl), .success ()⟩
  else quiet s (.rejected .unauthorized)

def learnMaterial (s : Situation) (r : Request) (theta : List Rat)
    (i : Ref .material) (raw : Raw i) : Reply Unit :=
  if !freshRequest s r || r.act != .learnModel || r.scope != raw.atom.scope then
    quiet s (.rejected .unauthorized)
  else match rawOf (s.core.state.E i) with
    | some _ => quiet s (.rejected .prerequisites)
    | none =>
      let x := s.core.setCell i (.pending raw)
      let st := {x.state with A := {x.state.A with theta := theta}}
      ⟨s.withCore (x.putState st rfl), .success ()⟩

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
          let st := {s.core.state with ledger := s.core.state.ledger ++ [entry]}
          ⟨{s with
              core := s.core.putState st rfl
              accounts := fun key => if key = relation then some after else s.accounts key},
            .success ()⟩
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
              · simp [hm,ha,hp,hd,hc]
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
  cases he : (assessDispatch s c).answer with
  | success j =>
    cases hf : s.core.state.decisions.find? (fun old => old.document == document) with
    | none => rfl
    | some old =>
      simp only [hf]
      split <;> rfl
  | rejected k => rfl
  | unknown k => rfl
  | conflict k => rfl
  | blockedHuman => rfl

#print axioms no_decision_no_binding
#print axioms learning_frame
#print axioms decision_assessment_preserves_relations
#print axioms performance_preserves_F_L
#print axioms performance_success_conserves
end JurisLean.CN.Completion20261105
