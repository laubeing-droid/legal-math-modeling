import JurisLean.CN.Completion20261105.Edges

/-!
C1/P3/P12 and C4: connect actual committed allocation to the represented
same-currency equal-reduction subclass. A source-bound rule is mandatory;
sharing a loss alone never authorizes cancelling another claim. The primary
cash operation is performed once. Secondary reductions use the accepted native
non-cash writeOff, not fictional second payments. The public call is atomic.
Source: main b3bdaed..., Ledger.performance/writeOff/writeoff_conserves.
-/
namespace JurisLean.CN.Completion20261105
open JurisLean.CN.Revision20261101

def equalLinked (s : Situation) (a b : Ref .relation) : Bool :=
  s.core.state.constraints.any (fun c => match c with
    | .equalReduction x y => (x.id == a && y.id == b) || (x.id == b && y.id == a)
    | _ => false)

def reached (s : Situation) (members : List (Ref .relation)) :
    Nat → List (Ref .relation) → List (Ref .relation)
  | 0,seen => seen
  | n+1,seen => reached s members n
      ((seen ++ members.filter (fun id => seen.any (equalLinked s id))).eraseDups)

def groupValid (s : Situation) (primary : Ref .relation) (members : List (Ref .relation)) : Bool :=
  members.contains primary &&
  members.all (fun id => s.core.state.L.any (fun r => r.id == id)) &&
  members.all (fun id => (reached s members members.length [primary]).contains id) &&
  s.core.state.constraints.all (fun c => match c with
    | .equalReduction a b =>
      !(members.contains a.id || members.contains b.id) ||
        (members.contains a.id && members.contains b.id)
    | _ => true)

def reductionGroup (s : Situation) (r : Request) (primary : Ref .relation) : Answer (List (Ref .relation)) :=
  if !(s.core.state.constraints.any (fun c => match c with
      | .equalReduction a b => a.id == primary || b.id == primary
      | _ => false)) then .success []
  else match s.equalReductionRules.filter (fun rule => rule.scope == r.scope &&
      rule.source.id == r.rule && rule.source.version == r.version && registeredInScope s r.scope rule.source) with
    | [] => .unknown .inputUnchecked
    | [rule] =>
      let group := rule.group.eraseDups
      if groupValid s primary group then .success (group.filter (fun id => id != primary))
      else .conflict .competentReview
    | _ :: _ :: _ => .conflict .competentReview

private instance (s : Native.Cash.State) : Decidable (Native.Cash.Conserves s) := by
  unfold JurisLean.Candidates.Final20261021.Ledger.Conserves
  infer_instance
private instance (s : Native.Cash.State) : Decidable (Native.Cash.CashConsistent s) := by
  unfold JurisLean.Candidates.Final20261021.Ledger.CashConsistent
  infer_instance

def reductionSource (before : Native.Cash.State) (q : Rat) : Native.Result Native.Cash.State :=
  if Native.Cash.Conserves before ∧ Native.Cash.CashConsistent before ∧
      0 ≤ q ∧ q ≤ Native.Cash.balance before then .known (Native.Cash.writeOff before q)
  else .rejected .stateConservationMismatch

/- This is a connection to the accepted theorem, not a re-proof of U09. -/
theorem reduction_source_conserves (before after : Native.Cash.State) (q : Rat)
    (h : reductionSource before q = .known after) :
    Native.Cash.Conserves after ∧ Native.Cash.CashConsistent after ∧
    after.cash = before.cash ∧ after.paid = before.paid := by
  unfold reductionSource at h
  split at h
  · rename_i valid
    cases h
    refine ⟨Native.Cash.writeoff_conserves before q valid.1 valid.2.2.1 valid.2.2.2,?_,rfl,rfl⟩
    exact valid.2.1
  · cases h

def reduceTargets (r : Request) (tag : Native.AmountTag) (q : Rat) :
    Situation → List (Ref .relation) → Reply Unit
  | s,[] => quiet s (.success ())
  | s,id :: rest =>
    match s.accounts id with
    | none => quiet s (.unknown .inputUnchecked)
    | some before =>
      if before.debt.amount.tag != tag ||
          !s.core.state.L.any (fun rel => rel.id == id &&
            rel.scope.matter == r.scope.matter && rel.scope.object == r.scope.object &&
            rel.holder.value == before.debt.creditor.value &&
            rel.counterparty.value == before.debt.obligor.value) then
        quiet s (.rejected .prerequisites)
      else match reductionSource before q with
        | .known after =>
          reduceTargets r tag q {s with accounts := fun key => if key = id then some after else s.accounts key} rest
        | .rejected _ => quiet s (.rejected .prerequisites)
        | .unknown reason => quiet s (.unknown (sourceUnknown reason))
        | .conflict _ _ => quiet s (.conflict .competentReview)

def performPaired (s : Situation) (r : Request) (mode : Mode) (rel : Ref .relation)
    (payment : Native.PaymentPayload) : Reply Unit :=
  match reductionGroup s r rel with
  | .success targets =>
    match s.accounts rel with
    | none => quiet s (.unknown .inputUnchecked)
    | some before =>
      Law.continueWith (performPayment s r mode rel payment) (fun staged =>
        match staged.accounts rel with
        | none => quiet s (.unknown .inputUnchecked)
        | some after => reduceTargets r before.debt.amount.tag
            (after.allocated - before.allocated) staged targets)
  | .unknown k => quiet s (.unknown k)
  | .rejected k => quiet s (.rejected k)
  | .conflict k => quiet s (.conflict k)
  | .blockedHuman => quiet s .blockedHuman

def performCall (s : Situation) (c : Law.Call) (rel : Ref .relation)
    (payment : Native.PaymentPayload) : Reply Unit :=
  checkPost s c.world (Law.atomic s
    (Law.continueWith (permissionDispatch s c.request c.policy c.mode c.world)
      (fun _ => performPaired s c.request c.mode rel payment)))

theorem performCall_success_nonempty (s : Situation) (c : Law.Call) (rel : Ref .relation)
    (payment : Native.PaymentPayload) (h : (performCall s c rel payment).answer = .success ()) :
    ∃ w, legalCompatible (performCall s c rel payment).after w :=
  checkPost_success_nonempty s c.world _ () h

/- The actual successful public call enforces the declared equality between
   actual account reductions. Desired equality is derived, not a premise. -/
theorem performCall_shared_reduction (s : Situation) (c : Law.Call) (rel : Ref .relation)
    (p : Native.PaymentPayload) (a b : LegalRelation) (qa qb : Quantity .money)
    (h : (performCall s c rel p).answer = .success ())
    (ha : a ∈ (performCall s c rel p).after.core.state.L)
    (hb : b ∈ (performCall s c rel p).after.core.state.L)
    (hc : SharedConstraint.equalReduction a b ∈ (performCall s c rel p).after.core.state.constraints)
    (hqa : knownReduction (performCall s c rel p).after a = some qa)
    (hqb : knownReduction (performCall s c rel p).after b = some qb) : qa = qb := by
  obtain ⟨w,hw⟩ := performCall_success_nonempty s c rel p h
  exact shared_actual_reduction _ w a b qa qb hw ha hb hc hqa hqb

#print axioms reduction_source_conserves
#print axioms performCall_success_nonempty
#print axioms performCall_shared_reduction
end JurisLean.CN.Completion20261105
