# Horn -> AAF Contract — Frozen Compilation Specification

**Date:** 2026-06-28
**Status:** FROZEN (spec-first-transition-ready)
**Gate M3:** SUBSTANTIAL_PARTIAL
**Authority:** `legal-math-modeling` (this repo)
**Implementation:** `juris-calculus` must honor this contract at the compilation boundary.

---

## 1. Purpose

This document freezes the **compilation contract** between the Horn closure
layer and the Dung AAF layer. The two-stage pipeline is:

```
Stage 1: Horn Closure  ->  Stage 2: AAF Construction  ->  Grounded Extension
```

The contract defines what the Horn layer produces, how arguments and attacks
are constructed, and what properties the downstream runtime must preserve.

---

## 2. Horn Closure Output Domain

The Horn forward-chaining engine produces a **fixed-point closure**:

```
Input:  facts: [LegalFact],  rules: [LegalRule]
Output: HornClosureState
  - claims: dict[str, str]    -> fact_id -> fact content (the closure set)
  - derivations: dict[str, [str]]  -> fact_id -> rule_ids that derived it
  - blocked_claims: set[str]  -> facts that were NOT derived (blocked by
                                 exception rules)
  - iteration_count: int
```

### Key Lean-proven properties (existing files):

| Property | Theorem | File |
|----------|---------|------|
| Closure operator monotone | `horn_operator_monotone` | `HornFixedPoint.lean` |
| Closure operator bounded by universe | `horn_operator_subset_univ` | `HornFixedPoint.lean` |
| Closure iteration monotone | `horn_iteration_monotone` | `HornFixedPoint.lean` |
| Closure reaches fixed point | `horn_finite_termination` | `HornFixedPoint.lean` |
| Closure iteration bounded | `horn_iteration_bound` | `HornFixedPoint.lean` |
| Closure result is fixed point | `horn_result_fixed_point` | `HornFixedPoint.lean` |
| Closure result is least fixed point | `horn_result_least_fixed_point` | `HornFixedPoint.lean` |
| Horn soundness | `horn_soundness` | `HornFixedPoint.lean` |
| Horn completeness | `horn_completeness` | `HornFixedPoint.lean` |
| Result is minimal model | `horn_result_is_minimal_model` | `HornFixedPoint.lean` |

Additionally, `HornDefinitions.lean` defines `TH` (the Horn operator) with:
- `TH_monotone`: `TH` is monotone
- `TH_subset_univ`: `TH` output is bounded by universe

These 12 theorems (10 core + 2 definitional) establish the Lean-proven
mathematical foundation for Horn closure.

### Python-verified properties:

- Closure is **extensive**: input facts are a subset of the closure
  (Python-verified via `evaluate_horn()` tests)
- Closure of closure equals closure
  (Python-verified via fixpoint iteration tests)

**What Horn closure does NOT do:**
- It does not resolve conflicts between rules
- It does not determine which conclusions survive attack
- It does not produce grounded extensions

---

## 3. Argument Construction Rules

Each argument in the AAF is constructed from a Horn-derived conclusion:

```
Argument:
  argument_id: str
  claim_id: str              -> which claim this argument supports
  rule_id: str               -> which rule produced the conclusion
  conclusion: str            -> the derived fact
  support_facts: [str]       -> fact_ids used by the rule
  exception_facts: [str]     -> fact_ids that could defeat this argument
```

**Construction rule:**
For each derived fact `f` in the Horn closure:
- If `f` was derived by rule `r`, create an argument `A` where:
  - `A.support_facts <= closure_facts` (traceability invariant)
  - `A.exception_facts` = exception facts declared by `r`
  - `A.conclusion` = `f`

**Contract invariant (machine-checked by `validate_horn_aaf_contract()`):**
All arguments MUST be traceable to closure facts. An argument with
`support_facts` not in the closure is a contract violation.

---

## 4. Attack / Defeat Formation Conditions

Attacks are directed edges in the Dung AAF. Three kinds are recognized:

### 4.1 REBUTTAL

```
Attack(attacker=A, target=B, kind=REBUTTAL)
```

When argument A's conclusion **directly contradicts** argument B's conclusion.
This is the standard Dung attack: "A argues for not-p, B argues for p."

### 4.2 EXCEPTION

```
Attack(attacker=A, target=B, kind=EXCEPTION)
```

When argument A provides a **legal exception** that defeats B's conclusion.
The exception attack carries an explicit defeat direction in its `reason` field
(must contain "defeats").

This models: "B argues for liability; A argues force majeure applies."

Exception kinds (from DDL):
- **DEFEATER**: Defeats the liability conclusion entirely
- **JUSTIFICATION**: The act was lawful
- **EXCUSE**: The actor is not blameworthy

### 4.3 PRIORITY_DEFEAT

```
Attack(attacker=A, target=B, kind=PRIORITY_DEFEAT)
```

When a **priority relation** says A's norm wins over B's norm. Both arguments
may be valid, but the priority ordering determines which survives in the
grounded extension.

This models: "A valid license defeats the general unauthorized-use prohibition."

**Contract invariant:**
Priority defeat MUST be represented as an explicit AAF attack edge.
It MUST NOT be resolved during Horn closure.

---

## 5. Priority / Exception Rules Entering the Attack Graph

Exceptions and priorities are not annotations — they **become attack edges**:

| Source | AAF representation |
|--------|-------------------|
| Defense (DEFEATER/JUSTIFICATION/EXCUSE) | EXCEPTION attack from defense's argument to the violated norm's argument |
| Priority relation (winner > loser) | PRIORITY_DEFEAT attack from winner's argument to loser's argument |
| Rebuttal (contradictory conclusions) | REBUTTAL attack between the two arguments |

**The bridge rule:**
```
If norm N1 has defense D that defeats N1's consequence:
  -> D's argument attacks N1's argument (EXCEPTION)

If priority P says N2 > N1:
  -> N2's argument attacks N1's argument (PRIORITY_DEFEAT)
```

---

## 6. Grounded Extension Input Structure

The AAF feeds into the grounded extension computation:

```
Input to grounded extension:
  - arguments: [Argument]         -> AAF nodes
  - attacks: [Attack]             -> AAF edges
  - attack_count: int             -> for complexity classification

Output:
  - grounded_set: set[str]        -> accepted argument_ids
  - status: DecisionStatus        -> PROVED / REFUTED / UNDECIDED / TAINTED
```

### Lean-proven grounded extension properties (DungFixedPoint.lean, 17 core theorems):

| Property | Theorem |
|----------|---------|
| Monotone operator | `F_monotone` |
| Iteration monotone | `iteration_monotone` |
| Specification equals computed | `grounded_eq_groundedSpec` |
| Finite termination | `finite_termination` |
| Iteration bounded | `iteration_bound` |
| Specification is fixed point | `groundedSpec_is_fixed_point` |
| Computed is fixed point | `grounded_is_fixed_point` |
| Specification is least fixed point | `groundedSpec_is_least_fixed_point` |
| Computed is least fixed point | `grounded_is_least_fixed_point` |
| Computed is least complete | `grounded_is_least_complete` |
| Specification uniqueness | `groundedSpec_unique_least_fixed_point` |
| Labelling partition | `labelling_partition` |
| IN soundness | `in_soundness` |
| OUT soundness | `out_soundness` |
| Undecided characterization | `undecided_characterization` |
| Self-attack precise | `self_attack_precise_theorem` |
| Self-attack excluded | `self_attack_not_in_grounded` |

### Complexity classification (engineering, not Lean-proven):

| Attack count | Status | Guarantee |
|-------------|--------|-----------|
| <= 3 | Exact grounded extension | Sound and complete (Python-verified via exhaustive enumeration tests) |
| >= 4 | TAINTED | Fail-closed: always rejected by checker |

**What the grounded extension guarantees (Lean-proven):**
- No accepted argument is attacked by another accepted argument
  (`in_soundness`, `DungFixedPoint.lean`)
- Every non-accepted argument is either attacked by an accepted argument
  (`out_soundness`) or is undecided (`undecided_characterization`)

---

## 7. Soundness / Completeness / Exactness Boundaries

### 7.1 For n <= 3 (exact zone)

Soundness and completeness for n <= 3 are currently verified by Python
exhaustive enumeration tests, NOT Lean-proven.

**PLANNED Lean formalization:**

```
-- PLANNED (no Lean file exists for this):
-- theorem aaf_soundness_exact ...
-- theorem aaf_completeness_exact ...
```

**Soundness**: Every accepted argument is not attacked by another accepted argument.
**Completeness**: Every non-accepted argument is attacked by an accepted argument.

Note: The general `in_soundness` and `out_soundness` theorems in `DungFixedPoint.lean`
cover the general case. The n <= 3 exact complexity bound is a separate PLANNED result.

### 7.2 For n >= 4

No Lean guarantee. The runtime MUST set status = TAINTED.
TAINTED means: "the checker rejects this; human review required."

### 7.3 What is NOT proven

- The **four-stage pipeline** (Horn -> AAF -> grounded -> trust labels) is not
  proven end-to-end in Lean. Each stage has separate proofs, but the
  composition is an engineering contract, not a Lean theorem.
- The **correctness of the argument construction algorithm** (Section 3)
  is enforced by `validate_horn_aaf_contract()`, not by a Lean proof.
- The **mapping from DDL norms to AAF attacks** (Section 5) is a semantic
  bridge, not a formalized translation.

### 7.4 PLANNED Lean formalization (files do not yet exist)

| Property | Target File | Status |
|----------|------------|--------|
| `aaf_soundness_exact` (n <= 3) | No file created | PLANNED |
| `aaf_completeness_exact` (n <= 3) | No file created | PLANNED |
| Reparation mode theorems | `DDLDefinitions.lean` | PLANNED — file does not exist |
| Certificate checker soundness | `CertificateChecker.lean` | PLANNED — file does not exist |

---

## 8. Machine-Testable Contract (`validate_horn_aaf_contract`)

The contract is implemented in `theory/spec/horn_aaf_contract.py` and checks:

| Check | What it verifies |
|-------|-----------------|
| All arguments traceable to closure | `support_facts <= closure` |
| All attacks refer to known args | `attacker_id, target_id in argument_ids` |
| Exception attacks carry defeat direction | `reason` contains "defeats" |
| Exception vs rebuttal distinguished | Both kinds present -> distinction noted |
| Priority defeat is explicit | PRIORITY_DEFEAT edges present in attack graph |
| Accepted-set bounded | `accepted <= argument_ids` |

A runtime that passes `validate_horn_aaf_contract()` preserves the
compilation contract. A runtime that fails it has a bug at the bridge.

---

## 9. What This Contract Does NOT Cover

- **How the runtime loads facts/rules** — that is JC's parser layer
- **How the runtime serializes the grounded extension** — that is JC's output layer
- **How trust labels are assigned** — that is the trust label layer (separate contract)
- **How cross-jurisdiction conflicts are detected** — that is the CBL layer
- **How certificate/checker validates the output** — see `certificate_checker_boundary.md`

---

## 10. Verification

```bash
# Verify the contract module exists and is importable
python -c "
from theory.spec.horn_aaf_contract import validate_horn_aaf_contract, CompilationContractReport
print('Contract module OK')
print('Report fields:', [f.name for f in CompilationContractReport.__dataclass_fields__.values()])
"

# Verify Lean umbrella still builds (existing modules)
cd proofs/lean/juris_lean && lake build JurisLean

# Verify AxiomAudit
cd proofs/lean/juris_lean && lake build +JurisLean.AxiomAudit
```

---

## 11. Gate Status

**M3: Horn -> AAF Contract** — SUBSTANTIAL_PARTIAL

- Horn monotonicity/finiteness: Lean-proven (`HornFixedPoint.lean`, `FiniteMonotoneIteration.lean`)
- Grounded extension properties: Lean-proven (`DungFixedPoint.lean`)
- Argument/attack construction: Python-verified (`validate_horn_aaf_contract()`)
- n <= 3 soundness/completeness: Python-verified (exhaustive tests); Lean PLANNED
- Close condition: At least soundness + completeness of the Horn->AAF compilation are verified. Currently MET.
