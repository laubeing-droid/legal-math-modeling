# PLANS.md -- Execution State (machine-readable)

## Track A: Formal Core Release

```
status: IN_PROGRESS
last_verified_commit: fb95f83

current_task: none

completed: []

blocked: []

next:
  - P0-1: Investigate juris-calculus 4 collection errors (262 tests, 4 errors)
  - P0-2: Full theorem manifest (75 theorems, statement digest)
  - P0-3: #print axioms audit for 6 key theorems
  - P0-4: .gitignore -- add *.olean *.ilean *.trace *.hash
  - P0-5: Clean clone rebuild verification
  - P0-6: Tag formal-core-v1, generate release report

last_test_command: none
```

## Track B: Banach Completion

```
status: NOT_STARTED
worktree: D:\Claude\数学证明\legal-math-banach
branch: track-b-banach
blocked_by: Track A completion

next:
  - B1: Prove weighted sup space is complete metric (scaling isomorphism route)
  - B2: Prove Lw <= qw implies ContractingWith q T
  - B3: Instantiate Mathlib fixedPoint, convergence, error bounds
  - B4: Python certificate verifier
```

## Track C: Data Protocols

```
status: NOT_STARTED
repo: deli-autoresearch

next:
  - Calibration data schema for 38 constants
  - DP adjacency definition and privacy budget model
  - Robust regression holdout protocol
  - NO fake calibration data
```
