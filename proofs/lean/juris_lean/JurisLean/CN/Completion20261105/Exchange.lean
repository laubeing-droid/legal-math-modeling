import JurisLean.CN.Completion20261105.Institutions

/-!
V4 P6 and audit A02: expressions expose actual dependencies; local assignment
  writes are singleton keys. Shared permission/version gates are outside this
  store and unchanged by interpretation updates. Histories are not quotiented.
-/
namespace JurisLean.CN.Completion20261105
open JurisLean.CN.Revision20261101

inductive MeaningExpr
  | literal (value : Option Formula)
  | read (key : Ref .object)
  | fallback (first second : MeaningExpr)

def MeaningExpr.reads : MeaningExpr → List (Ref .object)
  | .literal _ => []
  | .read key => [key]
  | .fallback a b => a.reads ++ b.reads

def MeaningExpr.eval (m : Ref .object → Option Formula) : MeaningExpr → Option Formula
  | .literal v => v
  | .read k => m k
  | .fallback a b => match a.eval m with | some value => some value | none => b.eval m

structure MeaningAssignment where
  target : Ref .object
  expression : MeaningExpr

def MeaningAssignment.apply (a : MeaningAssignment)
    (m : Ref .object → Option Formula) : Ref .object → Option Formula :=
  assign m a.target (a.expression.eval m)

/- The dependency lemma is derived from syntax, not supplied as a commutation
   assumption. Both branches of fallback conservatively contribute reads. -/
theorem expression_local (e : MeaningExpr) (m n : Ref .object → Option Formula)
    (h : ∀ k ∈ e.reads, m k = n k) : e.eval m = e.eval n := by
  induction e with
  | literal v => rfl
  | read k => exact h k (by simp [MeaningExpr.reads])
  | fallback a b ha hb =>
    simp only [MeaningExpr.eval]
    rw [ha (by intro k hk; exact h k (by simp [MeaningExpr.reads, hk])),
      hb (by intro k hk; exact h k (by simp [MeaningExpr.reads, hk]))]

theorem expression_after_unread_write (e : MeaningExpr) (a : MeaningAssignment)
    (m : Ref .object → Option Formula) (h : a.target ∉ e.reads) :
    e.eval (a.apply m) = e.eval m := by
  apply expression_local
  intro k hk
  have hn : k ≠ a.target := by
    intro he
    subst k
    exact h hk
  simp [MeaningAssignment.apply, assign, hn]

def Independent (a b : MeaningAssignment) : Prop :=
  a.target ≠ b.target ∧ a.target ∉ b.expression.reads ∧
    b.target ∉ a.expression.reads

instance (a b : MeaningAssignment) : Decidable (Independent a b) := by
  unfold Independent
  infer_instance

theorem assignments_commute (a b : MeaningAssignment)
    (m : Ref .object → Option Formula) (h : Independent a b) :
    b.apply (a.apply m) = a.apply (b.apply m) := by
  have ha := expression_after_unread_write a.expression b m h.2.2
  have hb := expression_after_unread_write b.expression a m h.2.1
  simp only [MeaningAssignment.apply] at ha hb ⊢
  rw [ha, hb]
  funext k
  by_cases hka : k = a.target
  · subst k
    simp [assign, h.1, Ne.symm h.1]
  · by_cases hkb : k = b.target
    · subst k
      simp [assign, h.1, Ne.symm h.1]
    · simp [assign, hka, hkb]

def assignLocal (s : Situation) (a : MeaningAssignment) : Reply Formula :=
  match a.expression.eval s.meanings with
  | none => quiet s (.unknown .inputUnchecked)
  | some f => Law.interpretLocal s a.target f

/- The actual state update has the abstract assignment as its observation
   when its expression is defined. This links the local theorem to calls. -/
theorem assignLocal_view (s : Situation) (a : MeaningAssignment) (f : Formula)
    (h : a.expression.eval s.meanings = some f) :
    (assignLocal s a).after.meanings = a.apply s.meanings := by
  simp [assignLocal, h, Law.interpretLocal, MeaningAssignment.apply]

theorem assignment_two_defined (s : Situation) (a b : MeaningAssignment)
    (fa fb : Formula) (h : Independent a b)
    (ha : a.expression.eval s.meanings = some fa)
    (hb : b.expression.eval s.meanings = some fb) :
    (assignLocal (assignLocal s a).after b).after.meanings =
      (assignLocal (assignLocal s b).after a).after.meanings := by
  have va := assignLocal_view s a fa ha
  have vb := assignLocal_view s b fb hb
  have hab : b.expression.eval (assignLocal s a).after.meanings = some fb := by
    rw [va, expression_after_unread_write b.expression a s.meanings h.2.1, hb]
  have hba : a.expression.eval (assignLocal s b).after.meanings = some fa := by
    rw [vb, expression_after_unread_write a.expression b s.meanings h.2.2, ha]
  rw [assignLocal_view _ b fb hab, assignLocal_view _ a fa hba, va, vb]
  exact assignments_commute a b s.meanings h

/- The omitted cross-read condition is refuted on the actual meaning store.
   W(a)∩W(b)=∅ and R(a)∩R(b)=∅ hold, yet the observed endpoint differs. -/
def counterA : MeaningAssignment := ⟨⟨0⟩, .read ⟨1⟩⟩
def counterB : MeaningAssignment := ⟨⟨1⟩, .literal (some (.atom toyAtom))⟩
def counterMemory : Ref .object → Option Formula :=
  fun k => if k = ⟨1⟩ then some (.neg (.atom toyAtom)) else some (.atom toyAtom)

theorem cross_read_counterexample :
    counterB.apply (counterA.apply counterMemory) ⟨0⟩ ≠
      counterA.apply (counterB.apply counterMemory) ⟨0⟩ := by
  decide

theorem assignments_preserve_norm_gate (s : Situation) (a : MeaningAssignment)
    (r : Request) :
    authorized (assignLocal s a).after.core.state.N r =
      authorized s.core.state.N r := by
  unfold assignLocal
  split <;> rfl

#print axioms expression_local
#print axioms expression_after_unread_write
#print axioms assignments_commute
#print axioms assignLocal_view
#print axioms assignment_two_defined
#print axioms cross_read_counterexample
#print axioms assignments_preserve_norm_gate
end JurisLean.CN.Completion20261105

