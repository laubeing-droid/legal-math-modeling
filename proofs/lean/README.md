# Lean Formal Verification

## What is Lean

Lean is an **interactive theorem prover (proof assistant)** created by Leonardo de Moura at Microsoft Research. Its core mechanism is type checking: you write a mathematical statement as a type, construct a proof term that inhabits that type, and Lean's kernel verifies the proof is valid.

Unlike Python/Z3/exhaustive tools that "run and observe output," Lean's verification is absolute:

1. You declare a **type** (the mathematical statement to prove)
2. You construct a **proof term** (the strategy and data that witnesses the statement)
3. Lean's **type-checking kernel** verifies the proof term matches the declared type

If the kernel accepts, the statement is **proved for all inputs** — not "passed N test runs," but "correct under all possible instantiations."

## Why Lean for This Project

The legal-math-modeling project uses Lean for four reasons:

1. **Completeness**: Mathematical induction, forall/exists quantifiers, and infinite domains — these exceed what Z3 or Python exhaustive enumeration can handle.
2. **Reproducibility**: `lake build` produces identical results on any machine. No CPU floating-point drift, no random seeds, no environment variation.
3. **Axiom transparency**: `#print axioms` lists every axiom a theorem depends on. There are no hidden assumptions.
4. **Compositionality**: Small proofs compose into larger proofs, enabling modular verification across the full formalization.

## What Lean Proves vs. What Python Does

Lean proves the **mathematical specification layer**, not the Python implementation:

```
Mathematical Specification (Lean proved)     Engineering Implementation (Python, tests + certificates)
─────────────────────────────────────        ────────────────────────────────────────────────────────
Finite monotone iteration generic kernel      Compiler and engine: no direct 1-to-1 mapping in code
Dung Grounded Extension existence             stratified_evaluator.py
Horn closure fixed point                      compiler_core module
Fixed-point existence and uniqueness          Code validated via tests + certificates
```

Key distinction:
- Lean guarantees the **mathematical specification** is correct (what properties the reasoning system *should* satisfy).
- Python tests and certificates guarantee the **engineering implementation** matches the specification (what the code *actually* does).
- The two are connected through a **refinement boundary**, not by "Lean proving Python code."

## Current State

| Item | Value |
|------|-------|
| Lean version | 4.30.0 |
| Mathlib version | v4.30.0 |
| `.lean` files | 25 |
| Total theorems | 94 (43 core + 51 supporting) |
| `sorry` | 0 |
| `admit` | 0 |
| Custom `axiom` | 0 |
| `lake build` | 2954 jobs, all pass |
| AxiomAudit | PASS |

### Core Theorem Files (43 theorems)

| File | Core Theorems | Description |
|------|:------------:|-------------|
| `DungFixedPoint.lean` | 17 | Dung grounded extension fixed-point theorems |
| `HornFixedPoint.lean` | 10 | Horn closure fixed-point and monotonicity |
| `FiniteMonotoneIteration.lean` | 9 | Generic finite monotone iteration kernel |
| `WeightedSupNorm.lean` | 4 | Weighted supremum norm contractivity |
| `HornDefinitions.lean` | 2 | Horn logic well-formedness and lattice properties |
| `ContractionCondition.lean` | 1 | Contraction mapping condition |

### Supporting Theorem Files (51 theorems)

| File | Supporting Theorems | Description |
|------|:------------------:|-------------|
| `UnifiedModel.lean` | 16 | Cross-system unification and correspondence |
| `FiniteRosetta.lean` | 9 | Finite Rosetta Stone translation between systems |
| `BanachEffectiveNodes.lean` | 8 | Effective node enumeration for Banach iteration |
| `TemporalKripke.lean` | 6 | Temporal Kripke structure formalization |
| `JC_Formalization.lean` | 6 | Judicial calculus aggregation rules |
| `BanachContraction.lean` | 2 | Banach contraction lemma support |
| `FiniteGaloisAdjunction.lean` | 2 | Finite Galois connection properties |
| `BanachFixedPoint.lean` | 1 | Banach fixed-point auxiliary result |
| `SupZeroLemma.lean` | 1 | Supremum-of-zero auxiliary lemma |

## Directory Structure

```
proofs/lean/juris_lean/
├── lakefile.lean                          # Lake build configuration
├── lean-toolchain                         # Lean toolchain version pin
├── lake-manifest.json                     # Dependency lockfile
├── JurisLean/
│   ├── AxiomAudit.lean                    # Axiom dependency audit
│   ├── BanachCertificate.lean             # Banach convergence certificate
│   ├── BanachComplete.lean                # Complete space instantiation
│   ├── BanachContraction.lean             # Contraction lemma support
│   ├── BanachEffectiveNodes.lean          # Effective node enumeration
│   ├── BanachFixedPoint.lean              # Banach fixed-point auxiliary
│   ├── BanachScratch.lean                 # Scratch/exploratory Banach proofs
│   ├── BanachWeightedNorm.lean            # Weighted norm definition
│   ├── Basic.lean                         # Basic definitions and notation
│   ├── ContractionCondition.lean          # Contraction condition (1 core)
│   ├── DungAAF.lean                       # Dung AAF interface aggregation
│   ├── DungDefinitions.lean               # Dung AAF definitions + monotonicity
│   ├── DungFixedPoint.lean                # Grounded extension (17 core)
│   ├── FiniteGaloisAdjunction.lean        # Finite Galois connection (2 supporting)
│   ├── FiniteMonotoneIteration.lean       # Generic iteration kernel (9 core)
│   ├── FiniteRosetta.lean                 # Rosetta Stone translation (9 supporting)
│   ├── HornDefinitions.lean               # Horn logic definitions (2 core)
│   ├── HornFixedPoint.lean                # Horn closure (10 core)
│   ├── HornOperationalRefinement.lean     # Horn operational refinement
│   ├── JC_Formalization.lean              # Judicial calculus (6 supporting)
│   ├── ScratchApi.lean                    # Scratch/API exploration
│   ├── SupZeroLemma.lean                  # Sup-of-zero lemma (1 supporting)
│   ├── TemporalKripke.lean                # Temporal Kripke structures (6 supporting)
│   ├── UnifiedModel.lean                  # Cross-system unification (16 supporting)
│   └── WeightedSupNorm.lean               # Weighted sup norm (4 core)
```

## How to Verify

```bash
cd proofs/lean/juris_lean

# Full build (2954 jobs)
lake build

# Build AxiomAudit specifically
lake build +JurisLean.AxiomAudit

# Check for sorry / admit / custom axiom
rg -n "\bsorry\b|\badmit\b|\baxiom\b" JurisLean/

# Print axiom dependencies of a specific theorem
lake env lean JurisLean/AxiomAudit.lean
```

## Common Misconceptions

**Wrong: "Lean proved the entire Python system is correct."**
Correct: Lean proves the mathematical specification layer. Python implementation is verified through tests and certificates, not Lean proofs. The correct statement is: "The mathematical specification has been Lean-verified; the engineering implementation has been validated against the specification via tests and certificates."

**Wrong: "0 sorry means everything is finished."**
Correct: 0 `sorry` means the current formalization core has no incomplete proofs. The 43 core theorems and 51 supporting theorems are fully proved. Research extensions (e.g., multi-dimensional Banach contraction) may still be under investigation but are outside the formal-core scope.

**Wrong: "0 custom axiom means zero axioms at all."**
Correct: Lean theorems still depend on standard axioms (`propext`, `Classical.choice`, `Quot.sound`). "0 custom axiom" means the project introduces no new, unverified assumptions beyond Lean's built-in axiom foundation.
