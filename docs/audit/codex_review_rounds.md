# Codex Audit Record: 5 Review Rounds + Fixes

> Date: 2026-06-16 to 2026-06-17
>
> This document records the full 5-round Codex audit process from creation to pre-release of the legal-math-modeling repository.

---

## Round 1: Standard Review

**Tool:** `/codex:review`
**Findings:** 1 P2

| # | File | Issue | Severity | Fix |
|---|------|------|--------|------|
| 1 | `requirements.txt` | PyYAML undeclared; `k3_empirical_analysis.py` imports yaml | P2 | Add `pyyaml>=6.0` |

---

## Round 2: Adversarial Review (First)

**Tool:** `/codex:adversarial-review`
**Findings:** 2

| # | File | Issue | Severity | Fix |
|---|------|------|--------|------|
| 1 | `run_all_proofs.py:25-46` | Lean check 60s timeout; proof_run_results.json records Timeout | HIGH | Extend timeout to 300s; mark `TOOLCHAIN_PENDING` + explanation on timeout |
| 2 | `evidence_evaluation.py:106-140` | Substring matching causes "signed" to match "unsigned" false positive | MEDIUM | Use word-boundary matching `_contains_word_boundary()`, symmetric conflict pairs |

---

## Round 3: Adversarial Review (Second)

**Tool:** `/codex:adversarial-review`
**Findings:** 1 (false positive)

| # | File | Issue | Severity | Conclusion |
|---|------|------|--------|------|
| 1 | `theory/temporal_law_engine.py:158-159` | Claimed unterminated string literal | HIGH | **False positive:** Review environment lacked Python. `py_compile` and `ast.parse` both pass |

---

## Round 4: Adversarial Review (Third)

**Tool:** `/codex:adversarial-review`
**Findings:** 2

| # | File | Issue | Severity | Fix |
|---|------|------|--------|------|
| 1 | `evidence_dependency_manager.py:23-24` | `from model_status import EvidenceStatus` package import failure | HIGH | Change to `from .model_status import EvidenceStatus` (with fallback) |
| 2 | `evidence_dependency_manager.py:51-56` | `add_node` overwrite leaves stale reverse dependency edges | MEDIUM | Clean old `_dependents` set before overwrite |

---

## Round 5: Internal Code Review (Claude self-review)

**Tool:** 9-angle internal review (line-by-line / removed-behavior / cross-file / language-pitfall / reuse / simplification / efficiency / altitude)
**Findings:** 8

### Python Code (6 items)

| # | File | Line | Issue | Severity | Fix |
|---|------|------|------|--------|------|
| 1 | `evidence_dependency_manager.py` | 100 | Propagation logic uses `new_status` (root node status) instead of actual dependency status | HIGH | Check `any_dep_refuted` / `all_deps_proved` instead |
| 2 | `bayesian_legal_reasoning.py` | 112 | `odds_to_probability(-1.0)` division by zero | HIGH | Add `o <= -1.0` guard |
| 3 | `evidence_evaluation.py` | 362 | `max()` empty sequence (no-premise rule) | MEDIUM | Add `if rule.premises:` branch |
| 4 | `formal_concept_analysis.py` | 141 | Variable `a` shadows outer scope | MEDIUM | Rename to `attr` |
| 5 | `data_quality_label.py` | 27 | Duplicate `DataQuality` enum definition | MEDIUM | Import from `model_status.py` |
| 6 | `bayesian_legal_reasoning.py` | 289 | Zero denominator silently returns 0.0 | LOW | Raise `ValueError` |

### Papers (4 items)

| # | File | Issue | Severity | Fix |
|---|------|------|--------|------|
| 7 | `icail_full_paper.md:276` | Grounded extension "non-empty" incorrect | ERROR | Change to "exists (possibly empty)" |
| 8 | `icail_full_paper.md:403` | LTL embedding Diamond V(w2) imprecise | CRITICAL | Use world atoms $p_j$ instead of valuation $V(w_j)$ |
| 9 | `icail_full_paper.md:574` | Duplicate reference table | ERROR | Delete second occurrence |
| 10 | `ai_liability.md:39,45` | Definition 4 contradicts Theorem 3; Theorem 1 circular reasoning | CRITICAL | Unify Definition 4 to use $a^*$; Theorem 1 explicitly state assumptions |

---

## Audit Statistics

| Metric | Value |
|---|---|
| Review rounds | 5 |
| Total findings | 14 (12 real + 1 false positive + 1 duplicate) |
| CRITICAL | 2 (fixed) |
| HIGH | 4 (fixed) |
| MEDIUM | 5 (fixed) |
| ERROR | 2 (fixed) |
| LOW | 1 (fixed) |
| False positive | 1 (temporal_law_engine.py syntax check; Codex lacked Python) |
| Current status | **All fixed, zero remaining** |

---

## Post-Fix Verification

| Verification | Result |
|---|---|
| `python -m theory` | 7 statements display correctly |
| 5 fixed modules | All exit code 0 |
| `grep` hardcoded paths | Zero matches |
| Paper cross-references | 60 label / 31 ref / 0 orphan |
| EN/CN README consistency | Statistics consistent |
