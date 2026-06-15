# Theorem A1: No Total Collision-Free Cross-Jurisdiction Mapping Extension

## Scope
- **Inventory**: finite only — given the current finite inventory of 80 fact patterns (30 CN-only, 30 US-only, 20 HK-only, plus 14 cross-jurisdiction patterns in `claim_mapping.csv`).
- **Jurisdiction**: cross-jurisdiction (CN ↔ US ↔ HK).
- **Dimension**: multi-dimensional (fact pattern × jurisdiction × claim × legal consequence).

---

## 1. Primitive Sets (Finite)

Let the following be finite, non-empty sets:

- `Fact_C = {f₁, …, f_{n_C}}` with `n_C = 30` (CN fact patterns from `us_fact_patterns.jsonl` is US; CN patterns are in `claim_mapping.csv` rows 2–31).
- `Fact_U = {f₁, …, f_{n_U}}` with `n_U = 30` (US fact patterns from `us_fact_patterns.jsonl`).
- `Fact_H = {f₁, …, f_{n_H}}` with `n_H = 20` (HK fact patterns from `hk_fact_patterns.jsonl`).
- `Claim_C`, `Claim_U`, `Claim_H` — finite sets of legal claims, one per jurisdiction.

Define the disjoint unions:
- `Fact = Fact_C ⊔ Fact_U ⊔ Fact_H`, with `|Fact| = 80`.
- `Claim = Claim_C ⊔ Claim_U ⊔ Claim_H`.

---

## 2. Partial Mapping

A **claim mapping** is a partial function:

```
M: Fact ⇀ Claim
```

with the jurisdiction constraint:

```
∀f ∈ Fact_J: if M(f) is defined, then M(f) ∈ Claim_J,  for J ∈ {C, U, H}
```

The current data provides `M` as a finite set of 44 rows (including cross-jurisdiction rows where `mapping_status ∈ {CN_US_PARTIAL, CN_HK_PARTIAL, TRI_JURISDICTION_PARTIAL, COLLISION, ASYMMETRY}`).

---

## 3. Collision Predicate

Define the **legal consequence** function:

```
LC: Claim → Consequence
```

where `Consequence` is a finite set of abstract legal outcomes (e.g., `LIABLE`, `NOT_LIABLE`, `ENFORCEABLE`, `VOID`, `IMMUNE`, etc.).

Define the **collision** predicate `Collision: Fact × Fact → {⊤, ⊥}`:

```
Collision(f₁, f₂)  ⟺  ∃c₁, c₂ ∈ Claim:
    M(f₁) = c₁ ∧ M(f₂) = c₂
    ∧ PatternMatch(f₁, f₂)   // same underlying fact pattern
    ∧ LC(c₁) ⊥ LC(c₂)        // logical incompatibility of consequences
```

where `PatternMatch(f₁, f₂)` means `f₁` and `f₂` are the same fact pattern instantiated in different jurisdictions (e.g., FP-CNUS-003), and `⊥` is a symmetric, irreflexive relation on `Consequence`.

**Witnessed collisions in data**:
- `FP-CNUS-003`: CN platform strict liability `⊥` US Section 230 immunity.
- `FP-CNUS-004`: CN Data Security Law blocking `⊥` US CLOUD Act compelled disclosure.
- `FP-COLL-001`: CN 非法证据排除 `⊥` US exclusionary rule + attorney-client privilege `⊥` HK LPP.
- `FP-COLL-002`: CN 证监会 administrative penalty `⊥` SEC civil enforcement + scienter `⊥` HK judicial review.

---

## 4. Structure-Preserving Functor Condition

Let `𝓛_J = (Claim_J, ⊢_J)` be the entailment poset (preorder) of jurisdiction `J`, where `c₁ ⊢_J c₂` means claim `c₁` legally entails claim `c₂` in jurisdiction `J`.

A **structure-preserving cross-jurisdiction functor** is a function:

```
F: 𝓛_CN × 𝓛_US × 𝓛_HK → 𝓛_Unified
```

satisfying:

1. **Component preservation**: `π_J(F(c_C, c_U, c_H)) = c_J` for each projection `π_J`, or at least `F` preserves the individual claim structure.
2. **Order preservation (functoriality)**:
   ```
   (c_C ⊢_C c'_C) ∧ (c_U ⊢_U c'_U) ∧ (c_H ⊢_H c'_H)
   ⇒ F(c_C, c_U, c_H) ⊢_Unified F(c'_C, c'_U, c'_H)
   ```
3. **Collision-free**:
   ```
   ∀f₁, f₂ ∈ Fact: PatternMatch(f₁, f₂) ⇒ ¬Collision(f₁, f₂)
   ```
4. **Totality**: `F` is a total function (defined on all triples in the domain).

---

## 5. Theorem Statement (Split: Real Data vs Toy Model)

### 5.1 A1-real: Current Real Data Cannot Formally Prove No-Total Functor

> **Theorem A1-real (Data Insufficiency)**: Given the current finite inventory of 44 rows in `claim_mapping.csv` (30 CN-only + 14 cross-jurisdiction), the documented **COLLISION** and **ASYMMETRY** rows are **empirical legal findings** backed by source citations, **not formal logical derivations** from first principles.
>
> Therefore, the current data can provide **witnesses of collision** (e.g., `FP-CNUS-003`, `FP-CNUS-004`, `FP-COLL-001`, `FP-COLL-002`), but it **cannot formally prove** that no total, structure-preserving, collision-free functor `F: 𝓛_CN × 𝓛_US × 𝓛_HK → 𝓛_Unified` exists for all possible legal fact patterns.
>
> **Maximal honest claim**: `DATA_INSUFFICIENT_FOR_PROOF` (finite inventory has source-backed collisions, but no formal collision logic).

Formally, the data provides:

```
∃f₁, f₂ ∈ Fact: PatternMatch(f₁, f₂) ∧ Collision(f₁, f₂)    [empirically witnessed]
```

but **does NOT provide**:

```
¬∃F: Claim_C × Claim_U × Claim_H → Claim_Unified:
    (∀f ∈ dom(M): F(M|_C(f), M|_U(f), M|_H(f)) = M(f))
    ∧ (∀f₁, f₂: PatternMatch(f₁, f₂) ⇒ ¬Collision(f₁, f₂))
    ∧ (F is order-preserving)
    ∧ (F is total)
```

because `Collision(f₁, f₂)` relies on human-annotated `mapping_status` and legal consequence analysis, not on a decidable formal predicate.

---

### 5.2 A1-toy: Toy Model Proved Separately

> **Theorem A1-toy (Toy Synthetic)**: On a deliberately constructed toy model of 5 synthetic fact patterns with string-based collision detection, there does **not** exist a total, collision-free mapping extension.
>
> **Status**: `TOY_SYNTHETIC_PROOF_ONLY` — applies ONLY to the 5 synthetic patterns; does NOT generalize to real inventory.

See: `finite_no_total_mapping_checker.py` (243 assignments enumerated, 0 collision-free, min collisions = 6).

---

## 6. Proof Strategy (Split)

### 6.1 Real Data Strategy (Empirical Witness, Not Formal Proof)

1. Enumerate all 44 rows of `claim_mapping.csv`.
2. Identify the 7 COLLISION/ASYMMETRY rows (`FP-CNUS-003`, `FP-CNUS-004`, `FP-COLL-001`, `FP-COLL-002`, `FP-ASYM-001`, `FP-ASYM-002`).
3. For each collision row, document the **source-backed legal incompatibility** (e.g., CN platform strict liability vs US Section 230 immunity).
4. **Acknowledge**: These are empirical legal findings from corpus analysis, not formal logical derivations. The collision predicate `Collision(f₁, f₂)` is not formally decidable from the data alone.
5. **Conclusion**: Data provides collision witnesses, but `DATA_INSUFFICIENT_FOR_PROOF` for universal no-total-functor claim.

### 6.2 Toy Model Strategy (Formal Exhaustive Enumeration)

1. Define 5 synthetic fact patterns with explicit string-based collision rules.
2. Enumerate all 3⁵ = 243 possible jurisdiction-to-claim assignments.
3. For each assignment, check collision-freedom via string matching heuristic.
4. Verify: 0 collision-free total assignments exist; minimum collisions = 6.
5. **Conclusion**: `TOY_SYNTHETIC_PROOF_ONLY` for the 5-pattern toy model.

---

## 7. Status and Allowed Final States

### A1-real (Real Data)
- **Status**: `DATA_INSUFFICIENT_FOR_PROOF`
- **Reason**: The 44-row inventory contains 7 COLLISION/ASYMMETRY rows, but these are **human-annotated empirical legal findings**, not formal logical derivations. No formal collision logic exists to prove no-total-mapping from first principles.
- **Allowed Final States**: `DATA_INSUFFICIENT_FOR_PROOF`, `OPEN_CONJECTURE`

### A1-toy (Toy Model)
- **Status**: `TOY_SYNTHETIC_PROOF_ONLY`
- **Reason**: Exhaustive enumeration of 5 synthetic patterns (243 assignments) shows 0 collision-free total mappings. **Applies ONLY to the toy model; does NOT generalize to real inventory.**
- **Allowed Final States**: `TOY_SYNTHETIC_PROOF_ONLY`

---

## 8. Key Definitions Summary

| Symbol | Type | Definition |
|--------|------|------------|
| `Fact_J` | finite set | fact patterns per jurisdiction |
| `Claim_J` | finite set | legal claims per jurisdiction |
| `M` | partial function | `Fact ⇀ Claim` |
| `LC` | function | `Claim → Consequence` |
| `Collision` | predicate | `Fact × Fact → {⊤, ⊥}` |
| `F` | function (claimed) | `Claim_C × Claim_U × Claim_H → Claim_Unified` |
| `⊢_J` | preorder | entailment in jurisdiction `J` |
| `PatternMatch` | predicate | same underlying fact pattern |
