# Fixpoint Termination -- Engineering Verification Artifacts

> **Nature of artifact:** Python exhaustive testing, NOT a Lean formal proof.
> TLA+ specification is present but unverified (TOOLCHAIN_PENDING).

## Proposition 1: Pure Horn Termination

**Statement:** In a finite universe of ground facts, monotonic Horn rule
application reaches a fixpoint in finitely many steps.

**Proof method:** Constructive bound via finite chain argument.

**Key steps:**

1. T_H is extensive: S subset T_H(S) for all S
2. Chain F_0 subset F_1 subset F_2 subset ... is monotonically increasing
3. Each F_i subset U (the finite universe)
4. A strictly increasing chain in a finite set has at most |U| strict increases
5. Therefore fixpoint reached in <= |U| + 1 loop iterations (<= |U| applications of T_H)

**Verification:** Exhaustive enumeration on universes of size 2, 3, 4, 5 with
various rule configurations (chain, diamond, cyclic, merged).

**Result:** ALL TESTS PASSED.

## Proposition 2: Production Evaluator Bounded Operational Termination

**Statement:** The production evaluator terminates due to explicit operational
bounds, NOT via Tarski's global monotone fixpoint theorem.

**Why NOT Tarski:**
- The evaluator state space is NOT a complete lattice
- The transition function is NOT monotone
- Status.FAIL is an operational sink, not a lattice supremum

**Five operational bounds:**

| Bound | Mechanism | Role |
|-------|-----------|------|
| 1 | iteration_count <= MAX_ITERATIONS | Hard counter, primary termination guarantee |
| 2 | rules_applied grows monotonically | Finite rule set exhaustion |
| 3 | exception_visited blocks re-entry | Cycle detection for exception handlers |
| 4 | CriticalClarityFailure is absorbing | Irreversible sink state |
| 5 | modification_count <= MAX_MODIFICATION_COUNT | Bounds rebuttal mutation chains |

**Verification:** Six test scenarios covering normal execution, monotonicity,
exception blocking, absorbing failure, modification bounds, and hard iteration
stop.

**Result:** ALL TESTS PASSED.

## TLA+ status

The TLA+ module `evaluator_termination_model.tla` contains a complete
PlusCal-free specification of the evaluator with:

- State variables and type invariant
- All five operational bounds as invariants
- Termination theorem statement
- Auxiliary boundedness lemmas

Marked **TOOLCHAIN_PENDING** -- the TLA+ tools (TLC, TLAPS) are not
available. The Python implementation serves as the executable reference.

## Artifacts

| File | Description |
|------|-------------|
| `production_bounded_termination.py` | Python implementation of both propositions with exhaustive tests |
| `evaluator_termination_model.tla` | TLA+ formal specification (TOOLCHAIN_PENDING) |

## Running

```bash
python production_bounded_termination.py
```

Expected output: Both propositions verified with all test cases passing.
