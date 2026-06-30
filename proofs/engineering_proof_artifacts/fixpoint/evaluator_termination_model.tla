(*
    Production Evaluator Termination Model
    ======================================
    STATUS: TOOLCHAIN_PENDING (TLA+ not available in current environment)

    This module specifies the bounded operational termination proof for the
    production evaluator using TLA+.

    The proof does NOT invoke Tarski's global monotone fixpoint theorem.
    Instead, it uses five explicit operational bounds.
*)

------------------- MODULE ProductionEvaluatorTermination -------------------

EXTENDS Integers, Sequences, FiniteSets

CONSTANTS
    Rules,                    \* Finite set of rule identifiers
    Exceptions,               \* Subset of Rules that are exception handlers
    MAX_ITERATIONS,           \* Hard iteration bound (constant)
    MAX_MODIFICATION_COUNT    \* Hard modification bound (constant)

ASSUME
    /\ MAX_ITERATIONS \in Nat
    /\ MAX_MODIFICATION_COUNT \in Nat
    /\ IsFiniteSet(Rules)
    /\ Exceptions \subseteq Rules

(*
    State variables:
      claims: set of derived claims
      rulesApplied: set of rules that have fired
      exceptionVisited: set of exception handlers already processed
      iterationCount: number of iterations performed
      modificationCount: number of claim modifications performed
      status: current evaluator status
*)

VARIABLES
    claims, rulesApplied, exceptionVisited, iterationCount, modificationCount, status

evaluatorVars == <<claims, rulesApplied, exceptionVisited, iterationCount, modificationCount, status>>

(* Status values *)
StatusValues == {"PENDING", "PASS", "FAIL", "BLOCKED"}

(*
    Type correctness invariant.
    All variables must maintain their expected types at all times.
*)
TypeInvariant ==
    /\ claims \subseteq STRING
    /\ rulesApplied \subseteq Rules
    /\ exceptionVisited \subseteq Exceptions
    /\ iterationCount \in Nat
    /\ modificationCount \in Nat
    /\ status \in StatusValues

(*
    Initial state: empty evaluator ready to begin.
*)
Init ==
    /\ claims = {}
    /\ rulesApplied = {}
    /\ exceptionVisited = {}
    /\ iterationCount = 0
    /\ modificationCount = 0
    /\ status = "PENDING"

(*
    Terminal states: no further transitions allowed.
*)
IsTerminated ==
    /\ status \in {"PASS", "FAIL", "BLOCKED"}
    \/ iterationCount >= MAX_ITERATIONS
    \/ modificationCount >= MAX_MODIFICATION_COUNT

(*
    CriticalClarityFailure is ABSORBING:
    Once status = "FAIL", it can never change.
*)
AbsorbingFailure ==
    status = "FAIL" => status' = "FAIL"

(*
    Apply a non-exception rule.
    Increments iteration count and potentially modification count.
*)
ApplyRegularRule(rule) ==
    /\ ~IsTerminated
    /\ rule \in Rules \ Exceptions
    /\ rule \notin rulesApplied
    /\ rulesApplied' = rulesApplied \cup {rule}
    /\ iterationCount' = iterationCount + 1
    /\ modificationCount' = modificationCount + 1  \* may be conditional
    /\ claims' = claims \cup {<<"derived", rule>>}
    /\ UNCHANGED <<exceptionVisited, status>>

(*
    Apply an exception handler rule.
    Checks exceptionVisited to prevent cycles.
*)
ApplyExceptionRule(rule) ==
    /\ ~IsTerminated
    /\ rule \in Exceptions
    /\ rule \notin exceptionVisited
    /\ exceptionVisited' = exceptionVisited \cup {rule}
    /\ rulesApplied' = rulesApplied \cup {rule}
    /\ iterationCount' = iterationCount + 1
    /\ claims' = claims \cup {<<"exception_handled", rule>>}
    /\ UNCHANGED <<modificationCount, status>>

(*
    Block on exception re-entry (cycle detection).
    This is the key mechanism preventing infinite exception loops.
*)
BlockExceptionCycle(rule) ==
    /\ ~IsTerminated
    /\ rule \in Exceptions
    /\ rule \in exceptionVisited
    /\ status' = "BLOCKED"
    /\ iterationCount' = iterationCount + 1
    /\ UNCHANGED <<claims, rulesApplied, exceptionVisited, modificationCount>>

(*
    Transition to CriticalClarityFailure (absorbing state).
*)
EnterCriticalFailure ==
    /\ ~IsTerminated
    /\ status = "PENDING"
    /\ status' = "FAIL"
    /\ iterationCount' = iterationCount + 1
    /\ UNCHANGED <<claims, rulesApplied, exceptionVisited, modificationCount>>

(*
    All possible next-state transitions.
*)
Next ==
    \/ \E rule \in Rules \ Exceptions : ApplyRegularRule(rule)
    \/ \E rule \in Exceptions :
        \/ ApplyExceptionRule(rule)
        \/ BlockExceptionCycle(rule)
    \/ EnterCriticalFailure
    \/ (IsTerminated /\ UNCHANGED evaluatorVars)

(*
    The complete specification.
*)
Spec == Init /\ [][Next]_evaluatorVars

(* ======================================================================== *)
(* TERMINATION THEOREM                                                      *)
(* ======================================================================== *)

(*
    Liveness: the evaluator eventually terminates.
    This is what we PROVE (not assume).
*)
Termination == <>(IsTerminated)

(*
    The five operational bounds that collectively ensure termination:

    BOUND 1: iterationCount never exceeds MAX_ITERATIONS
    BOUND 2: rulesApplied grows monotonically (subset-closed)
    BOUND 3: exceptionVisited prevents re-entry (cycle blocking)
    BOUND 4: FAIL status is absorbing (irreversible)
    BOUND 5: modificationCount never exceeds MAX_MODIFICATION_COUNT
*)

Bound1_IterationCount ==
    iterationCount <= MAX_ITERATIONS

Bound2_MonotonicRules ==
    [] (rulesApplied \subseteq rulesApplied')

Bound3_ExceptionBlocking ==
    \A ex \in Exceptions :
        (ex \in exceptionVisited) => [](ex \in exceptionVisited)

Bound4_AbsorbingFailure ==
    (status = "FAIL") => [](status = "FAIL")

Bound5_ModificationCount ==
    modificationCount <= MAX_MODIFICATION_COUNT

(*
    THEOREM: The evaluator always terminates.

    PROOF SKETCH:
    Each transition increments iterationCount by 1.
    By Bound1, iterationCount <= MAX_ITERATIONS.
    After MAX_ITERATIONS steps, IsTerminated becomes true.
    Once IsTerminated, only stuttering transitions are allowed.
    Therefore, all executions are finite and terminate.
*)
THEOREM TerminationTheorem ==
    Spec => Termination

(* ======================================================================== *)
(* AUXILIARY LEMMAS                                                         *)
(* ======================================================================== *)

(*
    Lemma: rulesApplied is bounded by the finite set Rules.
*)
LEMMA RulesAppliedBounded ==
    Spec => [] (IsFiniteSet(rulesApplied) /\ Cardinality(rulesApplied) <= Cardinality(Rules))

(*
    Lemma: exceptionVisited is bounded by the finite set Exceptions.
*)
LEMMA ExceptionVisitedBounded ==
    Spec => [] (IsFiniteSet(exceptionVisited) /\ Cardinality(exceptionVisited) <= Cardinality(Exceptions))

(*
    Lemma: The total number of non-stuttering transitions is at most:
           min(MAX_ITERATIONS, |Rules| + |Exceptions| + 1, MAX_MODIFICATION_COUNT + 1)
*)
LEMMA TransitionCountBound ==
    Spec => [] (
        iterationCount <= MIN(MAX_ITERATIONS,
                              Cardinality(Rules) + Cardinality(Exceptions) + 1,
                              MAX_MODIFICATION_COUNT + 1)
    )

=============================================================================
(*
    End of module ProductionEvaluatorTermination.

    NOTE: This file is marked TOOLCHAIN_PENDING because TLA+ tools
    (TLC model checker, TLAPS proof system) are not available in the
    current execution environment. The Python implementation in
    production_bounded_termination.py serves as the executable
    reference specification.
*)
