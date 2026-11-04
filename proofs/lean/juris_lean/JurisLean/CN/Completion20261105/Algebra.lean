import JurisLean.CN.Completion20261105.Program
import Mathlib.Logic.Relation

/-!
Original v3 1.2 / A01: KAT equations concern successful endpoint relations,
not the ordered list of attempts or the complete History. Mathlib's Comp,
ReflTransGen, composition associativity and closure elimination are reused.
The new connection proofs are needed because failed/unknown replies stop bind.
No success, Ready or legal conclusion is assumed in a constructor's ticket.
-/
namespace JurisLean.CN.Completion20261105.Algebra
open JurisLean.CN.Revision20261101

abbrev Rel := Situation → Situation → Prop
abbrev seqR := @Relation.Comp Situation Situation Situation
def plusR (r s : Rel) : Rel := fun a b => r a b ∨ s a b
def zeroR : Rel := fun _ _ => False
def oneR : Rel := Eq
abbrev starR (r : Rel) : Rel := Relation.ReflTransGen r
def testR (p : Situation → Bool) : Rel := fun a b => a = b ∧ p a = true

def Success (p : Program Unit) : Rel := fun a b =>
  ∃ r ∈ runProgram p a, r.answer = .success () ∧ r.after = b

theorem successful_join (r : Reply Unit) (q : Program Unit) (b : Situation) :
    (∃ out ∈ joinReply r (fun _ => runProgram q),
      out.answer = .success () ∧ out.after = b) ↔
    r.answer = .success () ∧ Success q r.after b := by
  cases r with
  | mk s answer =>
    cases answer with
    | success v => cases v; simp [joinReply,Success]
    | rejected k => simp [joinReply]
    | unknown k => simp [joinReply]
    | conflict k => simp [joinReply]
    | blockedHuman => simp [joinReply]

theorem success_bind (p q : Program Unit) :
    Success (.bind p (fun _ => q)) = seqR (Success p) (Success q) := by
  funext a b
  apply propext
  constructor
  · rintro ⟨out,hm,ha,hb⟩
    obtain ⟨pre,hpre,hout⟩ := List.mem_flatMap.mp hm
    have hj := (successful_join pre q b).mp ⟨out,hout,ha,hb⟩
    exact ⟨pre.after,⟨pre,hpre,hj.1,rfl⟩,hj.2⟩
  · rintro ⟨mid,⟨pre,hpre,hpa,hpm⟩,hq⟩
    have hj := (successful_join pre q b).mpr ⟨hpa,by simpa [hpm] using hq⟩
    obtain ⟨out,hm,ha,hb⟩ := hj
    exact ⟨out,List.mem_flatMap.mpr ⟨pre,hpre,hm⟩,ha,hb⟩

theorem success_choice (p q : Program Unit) :
    Success (.choice p q) = plusR (Success p) (Success q) := by
  funext a b
  apply propext
  simp only [Success,runProgram,List.mem_append,plusR]
  constructor
  · rintro ⟨r,hp | hq,h⟩
    · exact Or.inl ⟨r,hp,h⟩
    · exact Or.inr ⟨r,hq,h⟩
  · rintro (⟨r,hp,h⟩ | ⟨r,hq,h⟩)
    · exact ⟨r,Or.inl hp,h⟩
    · exact ⟨r,Or.inr hq,h⟩

theorem success_identity : Success (.pure ()) = oneR := by
  funext a b
  apply propext
  simp [Success,runProgram,quiet,oneR]

theorem success_test (p : Situation → Bool) :
    Success (.call (.check p)) = testR p := by
  funext a b
  apply propext
  cases hp : p a <;> simp [Success,runProgram,executeCommand,hp,quiet,testR,eq_comm]

theorem plus_assoc (r s t : Rel) : plusR (plusR r s) t = plusR r (plusR s t) := by
  funext a b; exact propext or_assoc
theorem plus_comm (r s : Rel) : plusR r s = plusR s r := by
  funext a b; exact propext or_comm
theorem plus_idempotent (r : Rel) : plusR r r = r := by
  funext a b; simp [plusR]
theorem plus_zero (r : Rel) : plusR r zeroR = r := by
  funext a b; simp [plusR,zeroR]
theorem sequence_assoc (r s t : Rel) : seqR (seqR r s) t = seqR r (seqR s t) :=
  Relation.comp_assoc
theorem sequence_identity (r : Rel) : seqR oneR r = r ∧ seqR r oneR = r :=
  ⟨Relation.eq_comp,Relation.comp_eq⟩
theorem sequence_zero (r : Rel) : seqR zeroR r = zeroR ∧ seqR r zeroR = zeroR := by
  constructor <;> funext a b <;> simp [seqR,Relation.Comp,zeroR]
theorem sequence_distributes_left (r s t : Rel) :
    seqR r (plusR s t) = plusR (seqR r s) (seqR r t) := by
  funext a b; apply propext
  simp [seqR,Relation.Comp,plusR,and_or_left,exists_or]
theorem sequence_distributes_right (r s t : Rel) :
    seqR (plusR r s) t = plusR (seqR r t) (seqR s t) := by
  funext a b; apply propext
  simp [seqR,Relation.Comp,plusR,or_and_right,exists_or]

theorem star_unfold_left (r : Rel) : starR r = plusR oneR (seqR r (starR r)) := by
  funext a b
  exact propext Relation.ReflTransGen.cases_head_iff
theorem star_unfold_right (r : Rel) : starR r = plusR oneR (seqR (starR r) r) := by
  funext a b
  apply propext
  constructor
  · intro h
    rcases Relation.ReflTransGen.cases_tail h with he | ⟨mid,hm,hs⟩
    · exact Or.inl he.symm
    · exact Or.inr ⟨mid,hm,hs⟩
  · rintro (he | ⟨mid,hm,hs⟩)
    · subst b; exact .refl
    · exact Relation.ReflTransGen.tail hm hs

/- The two induction rules, on this actual state carrier, complete the star
   obligations; they do not assert an infinite execution terminates. -/
theorem star_induction_left (r t : Rel)
    (closed : ∀ a b c, r a b → t b c → t a c)
    (a b c : Situation) (h : starR r a b) (ht : t b c) : t a c := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact ht
  | @head x y hxy hyb ih => exact closed x y c hxy ih

theorem star_induction_right (r t : Rel)
    (closed : ∀ a b c, t a b → r b c → t a c)
    (a b c : Situation) (ht : t a b) (h : starR r b c) : t a c := by
  induction h with
  | refl => exact ht
  | @tail x y hbx hxy ih => exact closed a x y ih hxy

theorem successful_star_is_actual_finite_iteration (p : Program Unit) (a b : Situation) :
    starR (Success p) a b ↔ ∃ n, Success (repeatProgram p n) a b := by
  constructor
  · intro h
    induction h using Relation.ReflTransGen.head_induction_on with
    | refl => exact ⟨0,⟨quiet _ (.success ()),by simp [repeatProgram,runProgram],rfl,rfl⟩⟩
    | @head x y hxy hyb ih =>
      obtain ⟨n,hn⟩ := ih
      refine ⟨n+1,?_⟩
      change Success (.bind p (fun _ => repeatProgram p n)) x b
      rw [success_bind]
      exact ⟨y,hxy,hn⟩
  · rintro ⟨n,h⟩
    induction n generalizing a with
    | zero =>
      have he : a = b := by simpa only [repeatProgram,success_identity,oneR] using h
      subst b
      exact .refl
    | succ n ih =>
      change Success (.bind p (fun _ => repeatProgram p n)) a b at h
      rw [success_bind] at h
      obtain ⟨mid,hp,hn⟩ := h
      exact Relation.ReflTransGen.head hp (ih mid hn)

theorem tests_compose (p q : Situation → Bool) :
    seqR (testR p) (testR q) = testR (fun s => p s && q s) := by
  funext a b; apply propext
  constructor
  · rintro ⟨mid,⟨ham,hp⟩,hmb,hq⟩
    subst mid
    exact ⟨hmb,by simpa only [Bool.and_eq_true] using And.intro hp hq⟩
  · rintro ⟨hab,hpq⟩
    subst b
    have h : p a = true ∧ q a = true := by simpa only [Bool.and_eq_true] using hpq
    exact ⟨a,⟨rfl,h.1⟩,rfl,h.2⟩
theorem tests_complement (p : Situation → Bool) :
    plusR (testR p) (testR (fun s => !p s)) = oneR ∧
    seqR (testR p) (testR (fun s => !p s)) = zeroR := by
  constructor
  · funext a b
    apply propext
    cases hp : p a <;> simp [plusR,testR,oneR,hp]
  · rw [tests_compose]
    funext a b
    cases hp : p a <;> simp [testR,zeroR,hp]

#print axioms success_bind
#print axioms success_choice
#print axioms success_identity
#print axioms success_test
#print axioms star_induction_left
#print axioms star_induction_right
#print axioms successful_star_is_actual_finite_iteration
#print axioms tests_compose
#print axioms tests_complement
end JurisLean.CN.Completion20261105.Algebra
