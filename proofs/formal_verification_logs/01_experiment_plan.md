# juris-calculus Multi-Tool Formal Verification Experiment Plan

Date: 2026-06-09
Status: Experiment design only; no experiments executed yet
Operator: Codex
Target project: `<juris-calculus-src>`
External tool repository: `<external-proof-tools-root>`
Suggested output directory: `<verification-runs-root>`

## 1. Experiment Objectives

This experiment does not aim to "prove all theorems in the reports are true." Its purpose is to establish a repeatable, auditable, incrementally upgradeable formal verification pipeline.

Core objectives span four layers:

1. Counterexample discovery: Use Hypothesis, CrossHair, Alloy, TLA+ to rapidly find false theorems, boundary errors, and state machine anomalies.
2. Invariant proof: Use Z3/pySMT to prove finite-domain, linear-constraint, range-constraint, and satisfiability properties.
3. State machine verification: Use TLA+ to model evaluator, rebuttal, oscillation guard, and critical halt operational semantics.
4. Machine-checked mathematical proof: Use Lean 4/mathlib4 for Galois connection, lattice/fixpoint, Banach contraction, category theory, and other genuine mathematical propositions.

Principle: Every theorem must first receive a trust label before entering any prover. Print output, single-case tests, and empirical curve-fitting must never be packaged as proof.

## 2. Tool Layer Table

| Layer | Tool | Local Directory | Purpose |
| --- | --- | --- | --- |
| Property testing | Hypothesis | `<external-proof-tools-root>\hypothesis` | Generate inputs at scale, discover counterexamples |
| Symbolic execution | CrossHair | `<external-proof-tools-root>\CrossHair` | Check function contracts, find counterexamples |
| SMT solving | Z3 | `<external-proof-tools-root>\z3` | Prove range, invariant, finite-domain propositions |
| SMT abstraction | pySMT | `<external-proof-tools-root>\pysmt` | Unified SMT-LIB generation and export |
| State machine model | TLA+ / TLC | `<external-proof-tools-root>\tlaplus` | Evaluator state machine and temporal invariants |
| Structural counterexample | Alloy | `<external-proof-tools-root>\alloy` | Relational structures, exclusivity, mapping counterexamples |
| Proof language | Lean 4 | `<external-proof-tools-root>\lean4` | Machine-checked mathematical proof |
| Mathematical library | mathlib4 | `<external-proof-tools-root>\mathlib4` | Order theory, lattice, category, analysis |
| Verifiable implementation | Dafny | `<external-proof-tools-root>\dafny` | Long-term rewrite of core algorithms or proof of loop invariants |

## 3. Experiment Directory Structure

Suggested layout:

```text
<verification-runs-root>\
  README.md
  manifest.yaml
  00_baseline\
    source_snapshot.txt
    git_status.txt
    file_hashes.json
    theorem_inventory.csv
  01_property_tests\
    tests\
    results\
    counterexamples\
  02_smt_z3\
    specs\
    smt2\
    results\
    unsat_cores\
  03_crosshair\
    contracts\
    results\
    counterexamples\
  04_tla\
    specs\
    configs\
    traces\
    results\
  05_alloy\
    models\
    instances\
    results\
  06_lean\
    JurisCalculus\
    build_logs\
    proof_status\
  07_report\
    daily_log.md
    final_summary.md
    theorem_status_matrix.csv
```

Each experiment must have an independent run ID:

```text
RUN_ID = YYYYMMDD-HHMMSS-tool-topic
Example: 20260609-213000-z3-galois-reverse-index
```

## 4. Trust Label Definitions

Every theorem or claim receives a label before the experiment route is decided.

| Label | Definition | Permitted Report Phrasing |
| --- | --- | --- |
| `CODE_FACT` | Fact directly read from source code | "Source code implements..." |
| `TESTED_PROPERTY` | Passed property testing but not proof | "No counterexample found within generated samples..." |
| `SMT_PROVED_FINITE` | Proved by SMT within finite or constrained domain | "Proved within the given abstract domain..." |
| `MODEL_CHECKED` | TLA+/Alloy bounded model checking passed | "No violation found within model boundaries..." |
| `LEAN_PROVED` | Lean machine-checked proof passed | "Formally proved..." |
| `EMPIRICAL_HYPOTHESIS` | Empirical fit or statistical observation | "Empirical hypothesis..." |
| `CONJECTURE` | No proof yet | "Conjecture..." |
| `REFUTED` | Counterexample found or source code does not support claim | "Does not hold..." |

Prohibited conflations:

```text
print output => proof
single example => universal theorem
empirical threshold => mathematical constant
model sketch => machine-checked proof
```

## 5. Experiment Phases

### Phase 0: Freeze Baseline

Purpose: Guarantee that all subsequent experiments can be traced to a specific source code version.

Record:

1. `git status --short`
2. `git rev-parse HEAD`; if `源码/` is not Git tracked, also record the directory hash.
3. Key file SHA256:
   - `compiler_core/evaluator.py`
   - `compiler_core/constraint_validator.py`
   - `legalos_services/legalos_pricing.py`
   - `legalos_services/differential_privacy.py`
   - `extractors/zh_CN/semantic_fact_matcher.py`
   - `theory/*.py`
4. Python version, pip freeze, external repository HEAD.

Output:

```text
00_baseline/source_snapshot.txt
00_baseline/file_hashes.json
00_baseline/tool_versions.json
```

### Phase 1: Theorem Inventory

Purpose: Break down theorems from reports into executable tasks.

Input:

1. `<handoff-root>\juris_calculus_math_reverse_engineering.md`
2. `<handoff-root>\juris_calculus_math_reverse_engineering_audit.md`
3. `<handoff-root>\juris_calculus_20_proof_audit_report.md`
4. `<handoff-root>\juris_calculus_handoff_codex_response.md`

Output table fields:

```csv
id,file,claim,source_location,current_evidence,target_tool,expected_artifact,trust_label,status,notes
```

Example:

```csv
T01,galois_reverse_index.py,"alpha/gamma form Galois connection",theory file,finite Python check,Z3+Lean,smt proof + lean theorem,SMT_PROVED_FINITE,pending,
T17,banach_pricing_contraction.py,"pricing is Banach contraction",theory file,suspect constant,Z3+Hypothesis,counterexample search,CONJECTURE,pending,
```

### Phase 2: Hypothesis Property Tests

Priority targets:

1. `compute_formalizable()`:
   - Output within `[0,1]`
   - Monotone in coverage
   - Non-Horn smoothing does not produce hard discontinuities
2. `compute_graph_similarity()`:
   - Output within `[0,1]`
   - Symmetry
   - Reflexivity boundary
   - Triangle inequality counterexample search
3. `RatioPreservingDP`:
   - Output non-negative
   - `dp_diagnostics` fields complete
   - Ratio error after rounding below declared threshold
4. `FixpointEvaluator`:
   - Finite random rule sets do not exceed `max_iterations`
   - Mutual exception does not cause recursion overflow

Every property test must record:

```yaml
property_id:
  function:
  invariant:
  input_strategy:
  max_examples:
  seed:
  result: pass|fail|error
  counterexample_path:
  runtime_seconds:
```

On failure, save the minimal counterexample:

```json
{
  "property_id": "PBT-GRAPH-TRIANGLE",
  "input": {},
  "expected": "triangle inequality holds",
  "actual": "violated",
  "shrunk_by": "hypothesis",
  "source_file": "",
  "reproduce_command": ""
}
```

### Phase 3: Z3 / pySMT Invariant Proofs

Priority targets:

1. Galois reverse index:
   - Verify `alpha(d) <= a iff d <= gamma(a)` over a finite domain.
   - Clarify whether vacuous branches are merely vacuously true or lack a reverse proof.
2. Scoring bounds:
   - Whether the abstract expression of `compute_formalizable()` always stays within `[0,1]` over the input domain.
3. Graph similarity:
   - Prove range `[0,1]`.
   - Automatically generate non-metric counterexamples.
4. Constraint guard:
   - After exceeding `MAX_MODIFICATION_COUNT`, `triggered=False`.
5. Horn bounded evaluator:
   - Python evaluator equivalent to abstract Horn semantics on small finite knowledge bases.

Record format:

```yaml
smt_case_id:
  theorem_id:
  solver: z3|pysmt-z3
  logic: QF_LIA|QF_LRA|AUFLIA|custom
  assumptions:
  query:
  result: sat|unsat|unknown
  model_path:
  unsat_core_path:
  smt2_path:
  runtime_seconds:
  interpretation:
```

Rules:

1. When `unsat` proves "no counterexample exists," the SMT-LIB file must be saved.
2. When `sat`, the model must be saved as a counterexample.
3. `unknown` must never be written as PASS.

### Phase 4: CrossHair Contracts

Applicable targets: Pure functions or near-pure Python logic.

Priority functions:

1. `_smooth_sigmoid_cap`
2. `compute_formalizable`
3. `LegalOSPricingEngine.compute_graph_similarity`
4. `RatioPreservingDP.anonymize_amounts`

Record:

```yaml
crosshair_case_id:
  function:
  contract_style: pep316|asserts|icontract
  preconditions:
  postconditions:
  result: confirmed|refuted|unknown|analysis_error
  counterexample:
  limitations:
```

Note: CrossHair executes Python code. It must only be used on functions with no IO, no network, no file deletion, and no real business side effects.

### Phase 5: TLA+ State Machine Models

Priority models:

1. Fixpoint evaluator loop
2. Exception recursion visited set
3. ConstraintValidator oscillation guard
4. CriticalClarityFailure absorbing halt

Core variables:

```text
facts
claims
rulesApplied
iteration
rebuttalCount
halted
visited
```

Candidate invariants:

```text
iteration <= MaxIterations
rulesApplied \subseteq Rules
halted => UNCHANGED claims
rebuttalCount[c] > 3 => no further modification for c
visited prevents exception recursion cycles
```

Record:

```yaml
tla_case_id:
  spec:
  config:
  constants:
  invariants:
  temporal_properties:
  result: passed|failed|error
  trace_path:
  state_count:
  diameter:
  runtime_seconds:
```

Failed traces must be transcribed into Python unit tests or Hypothesis regression seeds.

### Phase 6: Alloy Structural Counterexamples

Targets:

1. `R_supersedes` and `R_corrects` exclusivity.
2. counts-as institutional fact mapping.
3. Non-existence of natural transformation from CN to US.
4. Policy layer stratifiable CTRS structural boundaries.

Record:

```yaml
alloy_case_id:
  model:
  command:
  scope:
  result: instance|no_instance|error
  instance_path:
  interpretation:
```

Principles:

1. Alloy's `no instance` means no counterexample within the given scope, not an infinite-domain proof.
2. When an instance is found, prioritize it as a fatal counterexample for the audit report.

### Phase 7: Lean 4 / mathlib4 Machine Proof

Only genuine mathematical theorems enter Lean.

First batch of candidates:

1. Galois connection skeleton:
   - Define a finite preorder.
   - Define `alpha` and `gamma`.
   - Prove adjunction.
2. Abstract interpretation:
   - Abstract theorems for lattice, monotone function, and least fixpoint.
   - Do not directly claim that all 18 source-code theorems follow.
3. Banach contraction:
   - Define contraction on a metric space.
   - Prove or identify unprovable conditions for the pricing map.
4. Graph similarity:
   - Prove symmetry.
   - Provide a triangle inequality counterexample; do not call it a metric.

Lean record:

```yaml
lean_case_id:
  theorem:
  file:
  imports:
  proof_status: proved|sorry|failed|not_started
  axiom_count:
  sorry_count:
  build_command:
  build_log:
  notes:
```

Acceptance criteria:

```text
lake build succeeds
no sorry
no unexpected axioms
#print axioms check passes
```

### Phase 8: Dafny Verifiable Implementation Exploration

Dafny is not a first-phase main-line tool. It is enabled only when:

1. A Python function is too complex for stable SMT/CrossHair proof.
2. Loop invariants and termination proofs are needed.
3. A core algorithm is being rewritten as a verifiable pseudo-implementation.

Candidates:

1. Bounded Horn evaluator.
2. Graph similarity.
3. Scoring function.

Record:

```yaml
dafny_case_id:
  source_python:
  dafny_model:
  ensures:
  invariants:
  decreases:
  verification_result:
  compile_target:
```

## 6. Experiment Execution Order

Recommended sequence:

1. Phase 0: Freeze baseline.
2. Phase 1: Generate theorem inventory.
3. Phase 2: Run Hypothesis; find counterexamples quickly.
4. Phase 3: Write Z3/pySMT for properties with no counterexamples.
5. Phase 4: Add CrossHair contracts to pure functions.
6. Phase 5: Write TLA+ for the evaluator state machine.
7. Phase 6: Write Alloy for relational structures.
8. Phase 7: Send only stable, abstract, mathematically rigorous propositions to Lean.
9. Phase 8: Use Dafny to rewrite small core algorithms when necessary.

Every phase must produce:

```text
Input manifest
Command manifest
Output artifacts
Conclusion label
Counterexample or proof path
Next action
```

## 7. Pass / Fail Criteria

### PASS

Any of:

1. Lean proof passes with no sorry.
2. SMT query returns `unsat` with correct counterexample encoding and SMT-LIB saved.
3. TLA+/Alloy passes within declared scope; report clearly states the scope.
4. Hypothesis/CrossHair finds no counterexample, but may only be labeled `TESTED_PROPERTY`; must not be upgraded to full proof.

### FAIL

Any of:

1. Counterexample found.
2. Source code behavior contradicts the theorem statement.
3. Proof artifact consists only of print/docstring.
4. Solver returns `unknown` but report writes "proved."
5. Lean uses `sorry`, undeclared axioms, or proof bypass.

### CONDITIONAL

Any of:

1. Checked only within a finite scope.
2. Theorem depends on additional premises not declared in the original report.
3. What is proved is an abstract model, not the source implementation.
4. Toolchain runtime is missing; result cannot be reproduced.

## 8. Recording Templates

### manifest.yaml

```yaml
project: juris-calculus
run_root: <verification-runs-root>
source_root: <juris-calculus-src>
external_tools_root: <external-proof-tools-root>
created_at: 2026-06-09
status: planned
experiments_executed: false
operator: Codex
```

### theorem_status_matrix.csv

```csv
theorem_id,source_file,claim,tool,status,trust_label,artifact_path,counterexample_path,notes
T01,galois_reverse_index.py,alpha-gamma Galois connection,Z3,pending,CONJECTURE,,,
T02,bounded_horn_correctness.py,k<=3 evaluator equivalence,Hypothesis+Z3,pending,CONJECTURE,,,
```

### experiment_result.json

```json
{
  "run_id": "",
  "theorem_id": "",
  "tool": "",
  "command": "",
  "started_at": "",
  "finished_at": "",
  "exit_code": null,
  "result": "not_run",
  "trust_label_before": "CONJECTURE",
  "trust_label_after": null,
  "artifacts": [],
  "counterexamples": [],
  "limitations": []
}
```

### counterexample.json

```json
{
  "counterexample_id": "",
  "theorem_id": "",
  "found_by": "",
  "input": {},
  "observed": {},
  "expected": "",
  "reproduce_command": "",
  "source_location": "",
  "minimal": false
}
```

### daily_log.md

```markdown
# Daily Log

## YYYY-MM-DD

### Planned

### Executed

### New Counterexamples

### Proofs Promoted

### Blockers

### Next Actions
```

## 9. First Batch of Suggested Experiment Tasks

| Priority | Theorem/File | Tool | Goal |
| --- | --- | --- | --- |
| P0 | `legalos_pricing.compute_graph_similarity` | Hypothesis + Z3 | Prove range and symmetry; generate non-metric counterexamples |
| P0 | `evaluator.compute_formalizable` | Hypothesis + CrossHair | Check range, monotonicity, Non-Horn smoothing boundary |
| P0 | `constraint_validator` guard | TLA+ + Python regression | Prove that exceeding limit stops modification |
| P0 | `galois_reverse_index.py` | Z3 + Lean | Distinguish vacuous truth from genuine bidirectional adjunction |
| P1 | `bounded_horn_correctness.py` | Hypothesis + Z3 | Exhaust small KBs, not single-case tests |
| P1 | `banach_pricing_contraction.py` | Hypothesis + Z3 + Lean | Find counterexample where contraction factor equals 1 |
| P1 | `differential_privacy.py` | Hypothesis + SMT sketch | Check ratio/floor/rounding; downgrade DP theorem |
| P2 | `abstract_interpretation_unified.py` | Lean | Prove abstract interpretation skeleton only; do not claim all 18 theorems follow automatically |

## 10. Audit Delivery Criteria

After each experiment round, produce a report at:

```text
<verification-runs-root>\07_report\final_summary.md
```

The report must contain:

1. Which experiments were actually run this round.
2. Which theorems had their trust level promoted.
3. Which theorems were demoted or refuted.
4. Reproduction commands for every counterexample.
5. Paths to every proof artifact.
6. Missing or non-reproducible toolchain items.
7. Repair suggestions for the next round.

## 11. Current Notes

1. This file is experiment design only; no proof experiments have been executed.
2. The Python verification chain can start immediately; Lean/TLA+/Alloy/Dafny require runtime dependency confirmation.
3. The Git state of `<juris-calculus-root>` must be treated carefully: previously observed large numbers of deleted items at root, and `源码/` may be an untracked directory. Directory hashes must be frozen before experiments begin.
4. Do not write "no counterexample found" from Hypothesis/CrossHair as mathematical proof.
5. Do not write bounded TLA+/Alloy checks as infinite-domain proofs.
6. Do not retain `sorry` in Lean and then claim a proof is complete.

## 12. Approval Checkpoints

Please review the following decisions:

1. Whether to adopt `<verification-runs-root>` as the unified experiment output directory.
2. Whether to agree to run the four P0 items first: graph similarity, formalizable score, constraint guard, Galois connection.
3. Whether to allow adding Python-side test dependencies: `pytest`, `hypothesis`, `z3-solver`, `crosshair-tool`.
4. Whether Lean/TLA+/Alloy/Dafny should only produce models and scaffolding, waiting until runtimes are available before execution.

## 13. External Audit Feedback Integration

The received external audit feedback broadly endorses this plan's layered incremental approach, specifically affirming four points:

1. The layered objectives from counterexample discovery to machine proof follow formal verification engineering best practice.
2. The toolchain matches the project form: Python source verification first, Lean/TLA+/Alloy/Dafny for higher-level verification.
3. Baseline freezing, templated recording, run IDs, and artifact paths meet traceable audit requirements.
4. Trust labels effectively prevent false-proof packaging ("print output as proof," "single-case test as universal theorem").

The external audit also identifies five risk categories:

| Risk | Impact | Plan Revision |
| --- | --- | --- |
| Missing dependencies | TLA+/Alloy/Lean/Dafny cannot fully execute | Add dependency remediation plan and `03_check_dependencies.ps1` |
| High execution barrier | Incorrect tool usage may distort conclusions | Add minimal templates for each tool |
| Insufficient baseline freezing | Untracked directory changes hard to reproduce | Add directory snapshot script and SHA256 |
| Lean deployment risk | Proof progress may be slow; theorem statements may be non-standard | Start with Lean proof skeleton, then incrementally remove `sorry` |
| Non-standard recording | Audit chain breaks | Add record integrity validation script |

## 14. Dependency Remediation Plan

| Missing Dependency | Target Version / Suggestion | Affected Tool | Priority | Verification Command |
| --- | --- | --- | --- | --- |
| Java | OpenJDK 17 or 21 | TLA+, Alloy | P1 | `java -version` |
| Maven | 3.9+ | TLA+ source build | P1 | `mvn -version` |
| Gradle | 8.x | Alloy source build | P1 | `gradle -version` |
| Lean/Lake | Stable Lean 4 via elan | Lean/mathlib4 | P1 | `lean --version`; `lake --version` |
| .NET SDK | .NET 8 SDK | Dafny source build | P2 | `dotnet --list-sdks` |
| MSVC Build Tools | C++ Build Tools | CrossHair local editable build | P3 | `cl` or VS Build Tools detection |

Execution strategy:

1. Short-term: rely only on the ready Python verification chain; do not block P0 tasks.
2. Java and Lean are first-priority remediation targets, unlocking TLA+/Alloy and Lean/mathlib respectively.
3. .NET SDK and MSVC Build Tools are second-phase; Dafny and CrossHair source development are not short-term critical path.

## 15. Minimal Template Requirements

To lower the execution barrier, each toolchain must have a minimal template before entering formal experiments.

Templates to prepare:

```text
01_property_tests\tests\test_graph_similarity_template.py
02_smt_z3\specs\galois_connection_smt_template.py
03_crosshair\contracts\graph_similarity_contract_template.py
04_tla\specs\EvaluatorSkeleton.tla
04_tla\configs\EvaluatorSkeleton.cfg
05_alloy\models\RelationsSkeleton.als
06_lean\JurisCalculus\GaloisConnectionSkeleton.lean
```

Templates must satisfy:

1. Do not modify source code directly.
2. Default to not running formal experiments; show structure only.
3. Include record field hints: theorem_id, command, artifact_path, trust_label_before/after.
4. If a template contains an incomplete proof, it must be explicitly marked `skeleton_only` or `sorry_not_proof`.

## 16. Baseline Freezing Enhancements

If `源码/` is not Git tracked, recording only key file hashes is insufficient for full directory reproduction.

New requirements:

1. Generate a source directory file listing before each experiment round.
2. Generate a source directory archive or at minimum a full file hash manifest before each round.
3. Snapshot artifacts must be recorded in the `experiment_result.json` `artifacts` field.

Suggested output:

```text
00_baseline\source_tree_manifest.csv
00_baseline\source_tree_hashes.json
00_baseline\source_snapshot.zip
00_baseline\source_snapshot.sha256
```

If approved, a dedicated Git baseline may also be initialized for `源码/`. However, in the current shared workspace, `git init/add/commit` must not be performed without approval.

## 17. Cross-Check System

After each Phase completes, a cross-check is mandatory:

```text
Phase executor: runs experiment and fills in records
Reviewer: independently reads artifacts and reproduces at least one key command
Decision: PASS / NEEDS_FIX / INVALID
```

Check items:

1. `experiment_result.json` fields are complete.
2. Commands are reproducible.
3. PASS entries have proof artifacts or clear scope declarations.
4. FAIL entries have counterexamples and reproduce commands.
5. Hypothesis/CrossHair results are not incorrectly upgraded to proof.
6. Lean has no `sorry` or undeclared axioms.

## 18. Automated Record Integrity Validation

New script requirement:

```text
scripts\05_validate_records.ps1
```

Validation targets:

1. Every run directory must have an `experiment_result.json`.
2. `run_id`, `tool`, `command`, `result` must not be empty.
3. If `result=pass`, an artifact must exist.
4. If `result=fail` or `refuted`, a counterexample or explanation must exist.
5. If `trust_label_after=LEAN_PROVED`, a Lean build log must exist and contain no `sorry`.
6. If `trust_label_after=SMT_PROVED_FINITE`, a `.smt2` file or solver transcript must exist.

## 19. Timeline Suggestion

| Timeframe | Goal | Deliverables |
| --- | --- | --- |
| Weeks 1-2 | Python P0 verification chain + Java/Lean dependency remediation | Initial results for graph/formalizable/guard/DP; dependency status report |
| Weeks 2-4 | TLA+/Alloy model checking | Evaluator state machine; relational structure counterexample/pass records |
| Week 4+ | Lean/Dafny deep verification | Galois skeleton to sorry-free proof; Dafny small-core exploration |

Priority remains: counterexample discovery first, then finite-domain proof, then model checking, then machine mathematical proof.

## 20. Algorithm and Source Code Improvement Loop (ARV Closure)

External experiments must not only record "how to run" but also record "how problems were found, how the algorithm was improved, how the source was patched, and how the fix was validated." This requires an ARV (Audit-Repair-Validation) closure loop:

```text
Audit Finding -> Algorithm Diagnosis -> Repair Proposal -> Source Patch -> Regression/Proof -> Promotion/Demotion
```

### 20.1 Algorithm Improvement Records

Algorithm improvements target mathematical models, scoring functions, semantic definitions, and proof premises. They do not necessarily require immediate source code changes.

Record locations:

```text
07_report\algorithm_improvement_log.md
07_report\algorithm_improvement_backlog.csv
```

Each record must answer:

1. What property did the original algorithm claim.
2. What problem did the experiment or audit discover.
3. Whether the problem is a mathematical error, boundary gap, empirical parameter, missing proof premise, or implementation deviation.
4. What is the suggested algorithmic alternative.
5. What new invariants or proof obligations does the alternative require.
6. Whether it changes the public API or historical results.

Algorithm improvement classification:

| Type | Example | Record Requirement |
| --- | --- | --- |
| `THEOREM_DOWNGRADE` | Banach contraction demoted to empirical heuristic | Must explain why original theorem fails |
| `MODEL_REFORMULATION` | DP tuple-level privacy redefines adjacency | Must list new mathematical premises |
| `SCORING_SMOOTHING` | Non-Horn hard cap changed to sigmoid shoulder | Must record continuity, monotonicity, range |
| `SIMILARITY_REDEFINITION` | Graph similarity adds edge ratio | Must record symmetry, range, non-metric |
| `PARAMETER_EXTERNALIZATION` | Threshold/weights moved to adapter | Must record defaults and calibration method |
| `PROOF_OBLIGATION_ADDED` | Galois bidirectional adjunction supplements reverse proof | Must record target tool and artifact |

### 20.2 Source Code Improvement Records

Source code improvements target specific patches. Any source modification must first have a patch proposal, then a validation result.

Record locations:

```text
07_report\source_change_proposals\
07_report\source_change_log.md
07_report\repair_validation_matrix.csv
```

Each patch proposal uses a fixed template:

```yaml
change_id:
theorem_or_finding_id:
target_files:
change_type: bugfix|refactor|algorithm_change|instrumentation|test_only|docs
problem:
algorithm_rationale:
source_rationale:
expected_behavior_before:
expected_behavior_after:
compatibility_risk:
proof_obligations:
tests_required:
rollback_plan:
status: proposed|implemented|validated|rejected
```

### 20.3 Repair Validation Matrix

Every source code change must map to validation items:

```csv
change_id,target_file,claim_fixed,validation_tool,validation_artifact,result,trust_label_after,residual_risk
```

Example:

```csv
SRC-0001,legalos_services/legalos_pricing.py,empty feature similarity no longer defaults to 0.5,Hypothesis+Z3,,pending,CONJECTURE,
SRC-0002,compiler_core/evaluator.py,Non-Horn cap is continuous at 0.4,Hypothesis+CrossHair,,pending,TESTED_PROPERTY,
```

### 20.4 Improvement Reports Must Separate Algorithm and Source Code

Final reports must not merely state "tests passed." They must have two sections:

```text
Algorithm Improvements
- Mathematical model-level changes
- Theorem demotions/restatements
- New proof obligations

Source Code Improvements
- Specific files and functions
- Patch summary
- Regression tests and proof artifacts
- Compatibility risks
```

### 20.5 Prohibitions

1. Source patches must not be treated as mathematical proofs.
2. Algorithm proposals must not be written as if already implemented.
3. Tests passing must not be written as theorem proved.
4. The final diff must not be recorded without recording why the change was made.
5. Algorithm suggestions must not be recorded without specifying which source files they affect.
