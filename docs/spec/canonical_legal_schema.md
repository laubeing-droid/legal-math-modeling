# Canonical Legal Schema — Single Semantic Truth Source

**Date:** 2026-06-28
**Status:** FROZEN (spec-first-transition-ready)
**Gate M1:** SUBSTANTIAL_PARTIAL
**Upstream:** `legal-math-modeling` (this repo)
**Downstream:** `juris-calculus` runtime

---

## 1. Purpose

This document defines the **unique canonical data model** shared by Python
reference semantics and the JC runtime. The Lean formalization of these types
is PLANNED but not yet implemented — the canonical Lean files
(`LegalSyntax.lean`, `DDLDefinitions.lean`) do not yet exist in this repo.
There must be exactly one definition per core type — no name collision,
no "same name different meaning" across repos.

---

## 2. Core Types (11 Canonical Types)

### 2.1 LegalFact

| Attribute | Value |
|-----------|-------|
| Lean definition | PLANNED — `LegalSyntax.lean` does not yet exist |
| Python canonical | `canonical_semantics.py:CanonicalFact` |
| JC runtime | `types.py:LegalFact` |
| Frozen? | YES (Python definition frozen; Lean formalization pending) |
| Fields | `fact_id`, `predicate`, `arguments`, `source_ref`, `attributes` |
| Semantics | An atomic ground fact in the legal knowledge base. Identified by `fact_id`; `key` property returns `predicate(args)` for matching. |

### 2.2 LegalRule

| Attribute | Value |
|-----------|-------|
| Lean definition | PLANNED — `LegalSyntax.lean` does not yet exist |
| Python canonical | `canonical_semantics.py:CanonicalRule` |
| JC runtime | `types.py:LegalRule` |
| Frozen? | YES (Python definition frozen; Lean formalization pending) |
| Fields | `rule_id`, `kind` (HORN/EXCEPTION/PRIORITY/CONSTITUTIVE), `premises`, `conclusions`, `exceptions`, `priority_over` |
| Semantics | A Horn-style rule with optional exception and priority relationships. `kind` determines how the rule enters the AAF. |

### 2.3 LegalNorm

| Attribute | Value |
|-----------|-------|
| Lean definition | PLANNED — `LegalSyntax.lean` does not yet exist |
| Python canonical | `canonical_semantics.py:CanonicalNorm` + `ddl_core.py` |
| JC runtime | `types.py:LegalNorm` |
| Frozen? | YES (Python definition frozen; Lean formalization pending) |
| Fields | `norm_id`, `modality`, `actor`, `action`, `condition_facts`, `conclusion_fact`, `exception_facts`, `violation` |
| Semantics | A deontic norm with activation conditions and optional violation consequence. NOT the same as LegalRule — norms carry modality and violation semantics. |

### 2.4 LegalClaim

| Attribute | Value |
|-----------|-------|
| Lean definition | PLANNED — `LegalSyntax.lean` does not yet exist |
| Python canonical | `canonical_semantics.py:CanonicalClaim` |
| JC runtime | `types.py:LegalClaim` |
| Frozen? | YES (Python definition frozen; Lean formalization pending) |
| Fields | `claim_id`, `conclusion`, `basis_rules` |
| Semantics | A claim submitted to the argumentation layer. Derived from rule firings. |

### 2.5 Argument

| Attribute | Value |
|-----------|-------|
| Lean definition | PLANNED — `LegalSyntax.lean` does not yet exist |
| Python canonical | `canonical_semantics.py:CanonicalArgument` |
| JC runtime | `argumentation.py` / `types.py` |
| Frozen? | YES (Python definition frozen; Lean formalization pending) |
| Fields | `argument_id`, `claim_id`, `rule_id`, `conclusion`, `support_facts`, `exception_facts` |
| Semantics | A structured argument from rule + facts. Enters the AAF as a node. |
| **Note** | `UnifiedModel.lean` defines a separate `Argument` (Nat-based) which is currently in the umbrella build. That type is NOT the canonical type. It is a standalone composition proof (Kripke -> Horn -> AAF -> Banach) and does NOT represent production end-to-end correctness. |

### 2.6 Attack

| Attribute | Value |
|-----------|-------|
| Lean definition | PLANNED — `LegalSyntax.lean` does not yet exist |
| Python canonical | `canonical_semantics.py:CanonicalAttack` |
| JC runtime | `argumentation.py:build_attack_graph_from_evaluator()` |
| Frozen? | YES (Python definition frozen; Lean formalization pending) |
| Fields | `attack_id`, `attacker_id`, `target_id`, `kind` (REBUTTAL/EXCEPTION/PRIORITY_DEFEAT), `reason` |
| Semantics | A directed defeat edge in the AAF. `kind` determines the legal structure of the defeat. |

### 2.7 Priority

| Attribute | Value |
|-----------|-------|
| Lean definition | PLANNED — `LegalSyntax.lean` does not yet exist |
| Python canonical | `canonical_semantics.py:CanonicalPriority` |
| JC runtime | embedded in rule `priority_over` field |
| Frozen? | YES (Python definition frozen; Lean formalization pending) |
| Fields | `priority_id`, `winner`, `loser`, `reason` |
| Semantics | A priority relation between two rules. The winner's conclusion survives when both fire. |

### 2.8 Violation

| Attribute | Value |
|-----------|-------|
| Lean definition | PLANNED — `LegalSyntax.lean` does not yet exist |
| Python canonical | `canonical_semantics.py:CanonicalViolation` |
| JC runtime | via evaluator constraint checking |
| Frozen? | YES (Python definition frozen; Lean formalization pending) |
| Fields | `violation_id`, `norm_id`, `trigger_fact`, `consequence_fact`, `reparations` |
| Semantics | The consequence of an unexcused norm breach. Links to reparations. |

### 2.9 Reparation

| Attribute | Value |
|-----------|-------|
| Lean definition | PLANNED — `LegalSyntax.lean` does not yet exist |
| Python canonical | `canonical_semantics.py:CanonicalReparation` |
| JC runtime | via evaluator output |
| Frozen? | YES (Python definition frozen; Lean formalization pending) |
| Fields | `reparation_id`, `mode` (ALTERNATIVE/ORDERED_CHAIN/CONCURRENT/COURT_SELECTED), `options`, `notes` |
| Semantics | How remedies compose once liability is established. 4 modes defined in Python; Lean theorems are PLANNED. |

### 2.10 DecisionStatus

| Attribute | Value |
|-----------|-------|
| Lean definition | PLANNED — `LegalSyntax.lean` does not yet exist |
| Python canonical | `canonical_semantics.py:DecisionStatus` |
| JC runtime | `types.py:DecisionStatus` |
| Frozen? | YES (Python definition frozen; Lean formalization pending) |
| Values | `PROVED`, `REFUTED`, `UNDECIDED`, `TAINTED` |
| Semantics | The epistemic status of an argument in the grounded extension. TAINTED = fail-closed (always rejected by checker). |

### 2.11 ProofTrace

| Attribute | Value |
|-----------|-------|
| Lean definition | N/A (runtime construct, not Lean-level) |
| Python canonical | `canonical_semantics.py:CanonicalProofTrace` |
| JC runtime | `proof_trace.py` |
| Frozen? | YES |
| Fields | `trace_id`, `status`, `steps` (sequence of `CanonicalProofStep`), `fail_closed_reason` |
| Semantics | A full trace of the reasoning pipeline for audit and debugging. Each step records phase, event, and payload. |

---

## 3. Enums

| Enum | Values | Lean | Python |
|------|--------|------|--------|
| Modality | OBLIGATION, PROHIBITION, PERMISSION, CONSTITUTIVE | PLANNED | `canonical_semantics.py` |
| AttackKind | REBUTTAL, EXCEPTION, PRIORITY_DEFEAT | PLANNED | `canonical_semantics.py` |
| ReparationMode | ALTERNATIVE, ORDERED_CHAIN, CONCURRENT, COURT_SELECTED | PLANNED | `canonical_semantics.py` |
| DecisionStatus | PROVED, REFUTED, UNDECIDED, TAINTED | PLANNED | `canonical_semantics.py` |
| RuleKind | HORN, EXCEPTION, PRIORITY, CONSTITUTIVE | PLANNED | `canonical_semantics.py` |
| ExceptionKind | DEFEATER, JUSTIFICATION, EXCUSE | PLANNED | `ddl_core.py` |
| BurdenOfProof | CLAIMANT, RESPONDENT, COURT, PRESUMED_UNLESS_REBUTTED | PLANNED | `ddl_core.py` |

> **Note:** All Lean definitions are PLANNED. The Lean files (`LegalSyntax.lean`,
> `DDLDefinitions.lean`) do not yet exist. Python `canonical_semantics.py` and
> `ddl_core.py` are the current sole authorities.

---

## 4. Existing Lean Modules — What They Provide

The following Lean files DO exist and contribute to the formalization. They
define mathematical structures (finite monotone systems, Dung AAF, Horn systems)
that underpin the canonical types, but they do NOT directly define the 11
canonical types above.

| Lean File | What It Formalizes | Relevant Canonical Types |
|-----------|-------------------|-------------------------|
| `DungDefinitions.lean` | Dung AAF definitions (args, attacks) | Argument, Attack (abstract) |
| `DungFixedPoint.lean` | Grounded extension as least fixed point (17 core theorems) | DecisionStatus (grounded semantics) |
| `HornDefinitions.lean` | Horn system definitions, monotone operator `TH` | LegalRule, LegalFact (abstract) |
| `HornFixedPoint.lean` | Horn closure as least fixed point (10 core theorems) | LegalRule, LegalFact (closure semantics) |
| `FiniteMonotoneIteration.lean` | Finite monotone iteration convergence (9 core theorems) | Underpins both Horn and Dung layers |
| `ContractionCondition.lean` | Lipschitz coupling implies weighted contraction (1 core theorem) | Bridge to Banach (supporting) |
| `WeightedSupNorm.lean` | Weighted sup-norm metric properties (4 core theorems) | Metric foundation (supporting) |
| `UnifiedModel.lean` | Composition proof Kripke -> Horn -> AAF -> Banach (16 supporting theorems) | NOT canonical; standalone research artifact |
| `JC_Formalization.lean` | JC-specific formalization (12 supporting theorems) | Supporting layer |

**Important:** `UnifiedModel.lean` defines its own `Argument` type (Nat-based)
which is NOT the canonical `Argument` (ArgumentId-based). It participates in
the umbrella build but is NOT part of the canonical schema contract.

---

## 5. Truth Source Hierarchy

When Lean and Python disagree:

1. **Python `canonical_semantics.py` is the current sole authority.** The frozen
   dataclass definitions are the machine-readable contract. There is currently
   no Lean formalization of these 11 types.
2. **Lean formalization is PLANNED.** When `LegalSyntax.lean` is implemented,
   Lean will become the semantic authority and Python must satisfy the Lean theorems.
3. **JC runtime implements the contract.** It may add fields but must not
   change the meaning of canonical fields.

---

## 6. What This Schema Does NOT Cover

- Full legal ontology (L0/L1/L2 primitives) — that is a broader research scope
- Empirical rule corpus structure — that belongs in JC's rule management layer
- Customer-specific adaptations — private layer concern
- Banach pricing structures — archived research track (UNPROVED_TRACK_B)

---

## 7. Verification

```bash
# Verify Lean umbrella builds (existing modules — LegalSyntax.lean not yet present)
cd proofs/lean/juris_lean && lake build JurisLean

# Verify Lean AxiomAudit (reproducible, 0 sorry / 0 admit in core)
cd proofs/lean/juris_lean && lake build +JurisLean.AxiomAudit

# Verify Python canonical types import
python -c "from theory.spec.canonical_semantics import CanonicalFact, CanonicalRule, CanonicalNorm; print('OK')"

# Verify JC runtime types exist
cd ../juris-calculus && python -c "from compiler_core.types import LegalFact, LegalRule, LegalClaim; print('OK')"
```

---

## 8. Gate Status

**M1: Canonical Schema** — SUBSTANTIAL_PARTIAL

- Python definitions: FROZEN for all 11 types
- Lean definitions: PLANNED for all 11 types (files do not yet exist)
- `UnifiedModel.lean` Argument type collision: documented, non-blocking
- Close condition: All 11 types have exactly one canonical definition used by both Lean and Python. Currently met for the blocking-path types.
