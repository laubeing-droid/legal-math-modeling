import JurisLean.Seams.InstitutionalEffects
import JurisLean.Seams.UnifiedQuantLedger
import JurisLean.Candidates.Final20261021.Acceptance

/-!
Frozen original 10.8 L157 preparation. CI_NOT_RUN.
This is a mathematical rendering of the GIVEN two-step definition on the
fixed nonnegative-integer payment fragment (which contains 10/7/7).
It is NOT recovered FixedOneCaseTwoPaymentsV2 source, NOT its runStates API,
and NOT Final20261021.Trace.correctStep. TS and SVB are not redefined here.
The complete quantity ledger is retained, never replaced by its balance.
Only two missing named connections are added; local forms and numerical
fixture results below are reused without changing their contracts.
-/

namespace JurisLean.Candidates.FixedDriverSeparationAudit20261105

open JurisLean.Seams

abbrev JointState (Rel : Type) :=
  InstitutionalEffects.Ledger Rel × List UnifiedQuantLedger.LedgerItem
abbrev TwoPosts (Rel : Type) := JointState Rel × JointState Rel

-- A mathematical input for the integer subfragment, not the unknown V2 type.
structure GivenPayment (Rel : Type) where
  eventId : String
  obligor : String
  relation : Rel
  amount : Nat

def consumeGiven {Rel : Type} (s : JointState Rel) (p : GivenPayment Rel) : JointState Rel :=
  (InstitutionalEffects.next s.1 (.performance p.eventId p.obligor p.relation p.amount),
    UnifiedQuantLedger.afterPay (p.amount : ℚ) s.2)

def fixedStepGiven {Rel : Type} (s0 : JointState Rel)
    (p1 p2 : GivenPayment Rel) : TwoPosts Rel :=
  let s1 := consumeGiven s0 p1
  (s1, consumeGiven s1 p2)

-- The quantifier over posts is exactly the replaceable Q-only interface.
-- Empty relation ledgers preserve both COMPLETE supplied Q records.
theorem q_only_two_posts_do_not_certify_forms {Rel : Type} [DecidableEq Rel]
    (q1 q2 : List UnifiedQuantLedger.LedgerItem) (r : Rel) :
    ¬ (∀ posts : TwoPosts Rel,
      posts.1.2 = q1 → posts.2.2 = q2 →
      InstitutionalEffects.forms posts.1.1 r ∧
        InstitutionalEffects.forms posts.2.1 r) := by
  intro accepted
  have bad := (accepted (([], q1), ([], q2)) rfl rfl).1
  change false = true at bad
  cases bad

-- No correctness premise: both clauses follow from the actual two-step
-- mathematical definition and the already-proved local performance lemma.
theorem fixed_given_two_steps_preserve_forms {Rel : Type} [DecidableEq Rel]
    (s0 : JointState Rel) (p1 p2 : GivenPayment Rel) (r : Rel) :
    (InstitutionalEffects.forms (fixedStepGiven s0 p1 p2).1.1 r ↔
      InstitutionalEffects.forms s0.1 r) ∧
    (InstitutionalEffects.forms (fixedStepGiven s0 p1 p2).2.1 r ↔
      InstitutionalEffects.forms (fixedStepGiven s0 p1 p2).1.1 r) := by
  constructor
  · exact InstitutionalEffects.performance_not_creation s0.1
      p1.eventId p1.obligor p1.relation p1.amount r
  · exact InstitutionalEffects.performance_not_creation (consumeGiven s0 p1).1
      p2.eventId p2.obligor p2.relation p2.amount r

#check q_only_two_posts_do_not_certify_forms
#print axioms q_only_two_posts_do_not_certify_forms
#check fixed_given_two_steps_preserve_forms
#print axioms fixed_given_two_steps_preserve_forms
#check JurisLean.Seams.InstitutionalEffects.performance_not_creation
#print axioms JurisLean.Seams.InstitutionalEffects.performance_not_creation
#check JurisLean.Seams.InstitutionalEffects.projection_append_form
#print axioms JurisLean.Seams.InstitutionalEffects.projection_append_form
#check JurisLean.Candidates.Final20261021.Acceptance.a_u09_continuous_10_7_7
#print axioms JurisLean.Candidates.Final20261021.Acceptance.a_u09_continuous_10_7_7
#check JurisLean.Candidates.Final20261021.Acceptance.a_u09_three_observations
#print axioms JurisLean.Candidates.Final20261021.Acceptance.a_u09_three_observations

end JurisLean.Candidates.FixedDriverSeparationAudit20261105
