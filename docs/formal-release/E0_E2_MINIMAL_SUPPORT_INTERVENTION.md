# Track E0/E2: Minimal Support Set & Minimum-Cost Intervention (MVM)

## E0: Minimal Support Set

### Goal
`
target in closure(S)
AND no smaller S' subset of S infers target
`

### Flow
1. Build provenance DAG (D0)
2. Z3/MaxSAT find candidate sets
3. HornCertificate verifies inferability
4. UNSAT proof certifies no lower-cost set exists

### Cost components
- evidence cost
- proof difficulty
- time
- availability

## E2: Minimum-Cost Intervention (UNDEC->IN first)

### Target transitions (ordered by priority)
1. UNDEC -> IN
2. OUT -> IN
3. IN -> OUT

### Allowed operations
- add fact
- confirm fact
- add counterargument
- remove attack
- establish priority
- disable rule

### Output naming
MUST be called: "minimum-cost intervention under declared cost model"
NOT: "optimal litigation strategy"

### MVM scope
- UNDEC->IN for single-argument target
- Cost model: evidence cost only (simplest case)
- UNSAT proof of minimality via Z3

## E1/E3: Deferred
- E1: minimal rebuttal set (depends on C2/C3 soundness)
- E3: minimality certificate (depends on E0+E2 complete)
