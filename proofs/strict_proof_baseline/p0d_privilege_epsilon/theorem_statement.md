# Theorem D1: Privilege Level Does Not Logically Entail Unique or Bounded DP Epsilon

## Scope
- **Inventory**: finite CN only (10 privilege levels).
- **Jurisdiction**: CN-only.
- **Dimension**: single-dimension (privilege level → DP epsilon).

---

## 1. Primitive Sets

### 1.1 Privilege Level Set

Let `P` be a finite set of legal privilege levels. In the current data:

```
P_CN = {
    国家秘密,
    商业秘密,
    个人隐私/个人信息,
    律师执业保密,
    未成年人犯罪记录封存,
    调解/和解保密,
    诉讼证据（有限公开）,
    裁判文书公开（技术处理后）,
    指导性案例/公报案例,
    法律法规
}
```

with `|P_CN| = 10`.

### 1.2 Epsilon Value Set

Let `ε` be a purported function:

```
ε: P → ℝ
```

mapping each privilege level to a differential privacy epsilon value.

---

## 2. Same-Privilege Predicate

Define the **same-privilege-level** predicate:

```
same_privilege_level: P × P → {⊤, ⊥}
```

In the current data, this is simply equality on `P_CN`:

```
same_privilege_level(p₁, p₂)  ⟺  p₁ = p₂
```

(If privilege levels were grouped into equivalence classes, this would be coarser than equality.)

---

## 3. Theorem Statement

> **Theorem D1**: The mapping from legal privilege level to DP epsilon is **not a function**. Formally:
>
> ```
> ¬∃ε: P → ℝ: ∀p₁, p₂ ∈ P: same_privilege_level(p₁, p₂) ⇒ ε(p₁) = ε(p₂)
> ```
>
> Equivalently:
> ```
> ∃p₁, p₂ ∈ P: same_privilege_level(p₁, p₂) ∧ ε(p₁) ≠ ε(p₂)
> ```

**Witness**: For every `p ∈ P_CN`, the data records:

```json
"dp_epsilon": "NOT_DETERMINED_BY_LAW"
```

This means that for a single privilege level `p`, the set of possible epsilon values is **unbounded** (in fact, the entire real line `ℝ`). Therefore, choosing any specific `ε(p) ∈ ℝ` is an arbitrary policy decision, not a logical entailment from the privilege level.

More precisely, define the **possible-epsilon set** for each privilege level:

```
E(p) = { r ∈ ℝ | r is a legally valid epsilon for p }
```

From the data:

```
∀p ∈ P_CN: E(p) = ℝ   (unconstrained)
```

Therefore:

```
∀p₁, p₂ ∈ P_CN: E(p₁) = E(p₂) = ℝ
```

which implies that the privilege level provides **no information** that constrains epsilon. The privilege-to-epsilon mapping is many-to-many (in fact, each privilege level maps to infinitely many possible epsilons).

---

## 4. Corollary: No Bounded Epsilon Without External Policy

> **Corollary D1.1**: There does not exist a bounded interval `[a, b] ⊂ ℝ` such that `ε(p) ∈ [a, b]` is logically entailed by `p` alone. Any such bound must be imposed by an **external policy function** `π: P → 2^ℝ` that is not derivable from the legal lattice structure.

Formally:

```
¬∃a, b ∈ ℝ: ∀p ∈ P: E(p) ⊆ [a, b]
```

since `E(p) = ℝ` for all `p`.

---

## 5. External Policy Function

Define an **external policy function**:

```
π: P × Context → 2^ℝ
```

where `Context` represents non-legal factors (organizational policy, technical constraints, risk appetite). Then a **bounded epsilon assignment** is only possible as:

```
ε(p) ∈ π(p, ctx) ⊆ [a, b]
```

This is a **policy choice**, not a mathematical theorem.

---

## 6. Refutation Method (Z3 Two-Model Witness)

**Status**: `REFUTED_BY_COUNTEREXAMPLE`

**Method**: Z3 SMT solver constructs two internally consistent policy models:

- **CN model**: `epsilon(5) = 1.0` (satisfiable)
- **US model**: `epsilon(5) = 2.5` (satisfiable)

Same privilege level, different epsilon values — privilege alone **underdetermines** epsilon.

**Important**: The epsilon values (1.0, 2.5) are **policy model constructions**, not empirical legal facts. The refutation proves that `privilege → epsilon` is **not a pure function**.

**Open question**: `epsilon = f(privilege, jurisdiction, policy)` remains an open policy design question.

---

## 7. Lean Formalization

### FiniteGaloisAdjunction.lean — 2 Supporting Theorems

- **Theorem 1**: If `α: P_CN → ℝ` is undefined on any element (as when `dp_epsilon = "NOT_DETERMINED_BY_LAW"`), the Galois adjunction property is vacuously unsatisfiable for that element.
- **Theorem 2**: The coproduct lattice `L_⊔` with `L_US = DATA_UNAVAILABLE` and `L_HK = DATA_UNAVAILABLE` cannot support a non-constant jurisdiction-independent morphism — directly implying that `ε: P → ℝ` cannot be derived from the lattice structure alone.

---

## 8. Status and Allowed Final States

- **Status**: `REFUTED_BY_COUNTEREXAMPLE` (two-model witness)
- **Allowed Final States**: `REFUTED_BY_COUNTEREXAMPLE`, `OPEN_CONJECTURE`

---

## 9. Key Definitions Summary

| Symbol | Type | Definition |
|--------|------|------------|
| `P` | finite set | privilege levels (`|P_CN| = 10`) |
| `ε` | purported function | `P → ℝ` (does not exist) |
| `same_privilege_level` | predicate | `P × P → {⊤, ⊥}` |
| `E(p)` | set | possible epsilon values for `p` |
| `π` | external policy | `P × Context → 2^ℝ` |
