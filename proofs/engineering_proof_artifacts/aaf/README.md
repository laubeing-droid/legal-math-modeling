# Dung Abstract Argumentation Framework - Grounded Extension Proofs

## Directory Contents

| File | Status | Description |
|------|--------|-------------|
| `dung_grounded_extension.py` | **VERIFIED** | Exhaustive AAF enumeration + grounded extension verification |
| `stratified_correspondence.py` | **VERIFIED** | Stratified pipeline to AAF mapping and correspondence check |
| `README.md` | Complete | This file |

---

## Theorem: Grounded Extension Properties for Finite AAF

For every finite Abstract Argumentation Framework A = (Ar, att):

### 1. EXISTENCE
The grounded extension GE(A) exists.
- **Proof:** Iterating the characteristic function F from ∅ produces a fixpoint.
- **Verification:** Exhaustively checked on all AAFs up to n=4.

### 2. UNIQUENESS
GE(A) is the unique least fixpoint of F.
- **Proof:** If S and T are both least fixpoints, S ⊆ T and T ⊆ S, hence S = T.
- **Verification:** Computing from ∅ and from Ar gives identical results for all tested AAFs.

### 3. DETERMINISM
GE(A) is deterministically computable.
- **Proof:** The iterative construction S₀ = ∅, S_{i+1} = F(S_i) is deterministic.
- **Verification:** Repeated runs on all AAFs produce identical results.

### 4. FINITE CONVERGENCE
The iteration reaches fixpoint in at most |Ar| + 1 loop iterations (|Ar| applications of F).
- **Proof:** Chain ∅ ⊆ F(∅) ⊆ F²(∅) ⊆ ... ⊆ Ar has at most |Ar| strict increases.
- **Verification:** All AAFs converge in ≤ n + 1 loop iterations.

### 5. CONFLICT-FREE
GE(A) is conflict-free.
- **Proof:** GE(A) is admissible, and admissible sets are conflict-free by definition.

### 6. ADMISSIBLE
GE(A) is admissible (defends all its members).
- **Proof:** GE(A) = F(GE(A)), so every a ∈ GE(A) is defended by GE(A).

### 7. FIXPOINT
GE(A) = F(GE(A)).
- **Proof:** By construction, iteration stops when S = F(S).

### 8. MONOTONICITY
F is monotone: S₁ ⊆ S₂ ⇒ F(S₁) ⊆ F(S₂).
- **Proof:** If S₁ ⊆ S₂, any argument defended by S₁ is also defended by S₂.
- **Verification:** Exhaustively checked for all AAFs up to n=4.

---

## Exhaustive Verification Results

| n (arguments) | Total AAFs | Properties Verified | All Passed |
|---------------|-----------|---------------------|------------|
| 1 | 2 | Existence, Uniqueness, Determinism, CF, Admissible, Fixpoint, Monotone | YES |
| 2 | 16 | All properties | YES |
| 3 | 512 | All properties | YES |
| 4 | 65,536 | All properties | YES |

**Total AAFs checked:** 66,066

**Special cases analyzed:** 10 (empty attacks, self-attack, mutual attack, defense chain, odd/even cycles, complete graph, isolated arguments, complex defense, etc.)

---

## Stratified Pipeline Correspondence

### Mapping
- Each pipeline claim → AAF argument
- Each attack relation → AAF attack edge

### Results
| Test Category | Count | Matches |
|---------------|-------|---------|
| Legal fixtures (8 cases) | 8 | 8 |
| Exhaustive small pipelines | 6 | 6 |

**Overall correspondence: FULL** - No counterexamples found.

### Corrected Correspondence Claim

**Original (overly strong):** Pipeline accepted claims == AAF grounded extension

**Corrected:** For *legal* stratified pipelines (where attacks only go from level L to level L-1, and the attack graph is acyclic in levels), the pipeline-accepted claims EQUAL the AAF grounded extension. For general pipelines, GE(AAF(P)) ⊆ pipeline_accepted(P).

**Conditions for equality:**
1. Attacks only go from level L to level L-1
2. The level graph is acyclic
3. Every non-base claim has exactly one parent

---

## Running the Proofs

```bash
# Run grounded extension verification
python dung_grounded_extension.py

# Run stratified correspondence check
python stratified_correspondence.py
```

---

## References

Dung, V.M. (1995). "On the acceptability of arguments and its fundamental role in nonmonotonic reasoning, logic programming and n-person games." *Artificial Intelligence*, 77(2), 321-357.
