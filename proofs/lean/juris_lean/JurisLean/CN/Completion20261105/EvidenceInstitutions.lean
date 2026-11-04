import JurisLean.CN.Completion20261105.Edges

/-!
C3/A07: public representative queries derive their judgments from the same
approved method and admitted materials as legalDispatch. Legal parameters
(party identities, charge elements, procedural branches) are not scores.
The pure InstitutionRules remain reusable, but are not the public evidence gate.
-/
namespace JurisLean.CN.Completion20261105
open JurisLean.KernelV3
open JurisLean.CN.Revision20261101
open InstitutionRules

def proofAt (s : Situation) (c : Law.Call) (body : Formula) : Check Judgment :=
  match selectedRules s.core c.request with
  | [law] =>
    if c.policy.scope != law.scope || c.policy.source.id != law.source.id ||
        c.policy.source.version != law.source.version then .unknown .inputUnchecked
    else match selectedTemplates s law with
      | [t] =>
        let items := admittedView s.core.state.E law.materials
        match evalProofFormula t.body items body with
        | .unknown k => .unknown k
        | .known j =>
          if evalFormula (c.policy.evaluate items) body == j then .known j
          else .unknown .inputUnchecked
      | _ => .unknown .inputUnchecked
  | _ => .unknown .inputUnchecked

def judgmentReply (s : Situation) : Check Judgment → Reply Judgment
  | .unknown k => quiet s (.unknown k)
  | .known .undetermined => quiet s (.unknown .systemNotJudge)
  | .known j => quiet s (.success j)

def burdenEvidence (s : Situation) (c : Law.Call) (body : Formula) : Reply Judgment :=
  if automationAllowed s.core.state c.request.scope c.mode = false then quiet s .blockedHuman
  else judgmentReply s (proofAt s c body)

def acquisitionEvidence (s : Situation) (c : Law.Call) (parties : AcquisitionParties)
    (route : AcqRoute) (faith price publicity : Atom) : Reply Judgment :=
  if automationAllowed s.core.state c.request.scope c.mode = false then quiet s .blockedHuman
  else if faith.scope != c.request.scope || price.scope != c.request.scope ||
      publicity.scope != c.request.scope then quiet s (.rejected .unsupported)
  else if !s.core.state.L.any (fun r => r.scope == c.request.scope &&
      r.holder == parties.originalOwner) ||
      !s.core.state.F.any (fun o => o.atom.scope == c.request.scope &&
        o.actor == parties.unauthorizedDisposer) ||
      !s.core.state.F.any (fun o => o.atom.scope == c.request.scope &&
        o.actor == parties.transferee) then quiet s (.unknown .inputUnchecked)
  else match route with
    | .ordinary311 => judgmentReply s (combineAnd (proofAt s c (.atom faith))
        (combineAnd (proofAt s c (.atom price)) (proofAt s c (.atom publicity))))
    | _ => quiet s (.unknown .systemNotJudge)

/- The participation source is a legal-assessment atom for this person/event;
   a group member is not an automatic premise about an excess event. The
   elements/charge query is tied to the selected norm's scope.question. -/
def offenseEvidence (s : Situation) (c : Law.Call)
    (person : Ref .actor) (event : Ref .event) (commonScope : Ref .query)
    (ability elements : Atom) : Reply (Ref .query) :=
  if automationAllowed s.core.state c.request.scope c.mode = false then quiet s .blockedHuman
  else if !s.core.state.F.any (fun o => o.id == event) then
    quiet s (.unknown .inputUnchecked)
  else if !hasJoint s.participations person event commonScope then quiet s (.rejected .prerequisites)
  else if ability.scope != c.request.scope || elements.scope != c.request.scope then
    quiet s (.rejected .unsupported)
  else match combineAnd (proofAt s c (.atom ability)) (proofAt s c (.atom elements)) with
    | .known .established => quiet s (.success c.request.scope.question)
    | .known .notEstablished => quiet s (.rejected .prerequisites)
    | .known .undetermined => quiet s (.unknown .systemNotJudge)
    | .unknown k => quiet s (.unknown k)

def storedResJudicata (s : Situation) (document : Ref .document)
    (person : Ref .actor) (scope : Scope) (time : Nat) : Reply Bool :=
  match s.core.state.bindings.filterMap (fun b => match b with
      | .decide db => if db.decision.document == document && db.kind == .resJudicata then
          some db.index else none
      | .other _ => none) with
  | [] => quiet s (.unknown .inputUnchecked)
  | indices => quiet s (.success (indices.any (fun i => withinBinding i person scope time)))

def lookupMeaning : List (Ref .object × Formula) → Ref .object → Option Formula
  | [], _ => none
  | (key,value) :: rest, target =>
    if key = target then some value else lookupMeaning rest target

def contractQuery (s : Situation) (c : Law.Call) (obj : Ref .object) : Reply Judgment :=
  if obj != c.request.scope.object then quiet s (.rejected .unauthorized)
  else match s.meanings obj with
    | none => quiet s (.unknown .inputUnchecked)
    | some body =>
      if lookupMeaning s.core.state.interpretations obj == some body then
        burdenEvidence s c body
      else quiet s (.conflict .competentReview)

/- C3: the actual latest interpretation is read, scoped and evaluated; it
   does not rewrite N. The mirror check prevents inconsistent projections
   from being silently treated as a contract term. -/
theorem interpretation_lookup_current (s : Situation) (obj : Ref .object) (f : Formula) :
    lookupMeaning (Law.interpretLocal s obj f).after.core.state.interpretations obj = some f ∧
    (Law.interpretLocal s obj f).after.meanings obj = some f := by
  simp [Law.interpretLocal, lookupMeaning, assign]

theorem proofAt_unknown_reaches_query (s : Situation) (c : Law.Call)
    (body : Formula) (k : UnknownKind)
    (hg : automationAllowed s.core.state c.request.scope c.mode ≠ false)
    (h : proofAt s c body = .unknown k) :
    (burdenEvidence s c body).answer = .unknown k := by
  simp [burdenEvidence, hg, h, judgmentReply, quiet]

theorem offense_evidence_never_changes_reality (s : Situation) (c : Law.Call)
    (person : Ref .actor) (event : Ref .event)
    (commonScope : Ref .query) (ability elements : Atom) :
    (offenseEvidence s c person event commonScope ability elements).after = s := by
  unfold offenseEvidence
  split
  · rfl
  · split
    · rfl
    · split
      · rfl
      · split
        · rfl
        · split <;> rfl

#print axioms interpretation_lookup_current
#print axioms proofAt_unknown_reaches_query
#print axioms offense_evidence_never_changes_reality
end JurisLean.CN.Completion20261105
