# Public / Private Boundary -- Three-Repo Disclosure Policy

**Date:** 2026-06-27
**Effective:** Immediately upon commit
**Review:** Before any new public release or repository restructuring

---

## 1. Principle

The three repositories have distinct disclosure roles. This document freezes
what continues public, what stops expanding publicly, and what should
eventually become private.

**Core rule:** freeze disclosure boundary first, then physically split repos.
Not the reverse.

---

## 2. `legal-math-modeling` -- Continues Public

### Why continue public

This repo serves as the **industry-standard mathematical specification,
formalization boundary, and forbidden-claims source**. Publishing it
establishes upstream specification authority. The real commercial moat is in
rule maintenance, product workflows, certificate services, and the lawyer
work platform -- not in the math spec itself.

### What continues public

| Content | Reason |
|---------|--------|
| Lean specifications & theorem manifest (25 files, 94 theorems, 0 sorry) | Specification authority |
| Formal release boundary | Auditability |
| Canonical legal schema | Interoperability reference |
| DDL minimal core | Semantic contract |
| Horn -> AAF contract | Correctness boundary |
| Certificate/checker boundary | Verification reference |
| Allowed/forbidden claims | Honest public posture |
| Papers, audit, release evidence | Academic credibility |

### What stops expanding publicly

Nothing in this repo needs to stop. It is the specification source and should
remain public.

---

## 3. `juris-calculus` -- Public Kernel, Stop Expanding Commercial Layers

### Historical status

Already-public content is not being retracted. The boundary applies to
**future additions**.

### Continue public (the "auditable kernel")

| Content | Reason |
|---------|--------|
| Horn evaluator core | Specification implementation |
| AAF / grounded runtime core | Specification implementation |
| Canonical serialization | Interoperability |
| Independent grounded checker | Audit independence |
| Trust-label fail-closed core | Safety guarantee |
| Reference certificate formats | Interoperability |
| Academic/audit test fixtures | Reproducibility |

### Stop expanding publicly

| Content | Reason |
|---------|--------|
| Full commercial rule corpus | Competitive asset |
| High-quality rule upgrade versions | Business value |
| Customer-facing workflow orchestration | Product IP |
| Proprietary litigation automation | Competitive advantage |
| Customer data adaptation layers | Client confidentiality |
| Commercial prompt / orchestration assets | Business IP |
| Patent-candidate implementation details | IP protection |

### Action

- Already-public old versions: acknowledge as historical fact
- Future additions: do NOT merge into public main branch
- New high-value versions: route to private repo or private directory stream

---

## 4. `deli-autoresearch` -- Control / Audit / Research Automation

### Continue public

| Content | Reason |
|---------|--------|
| Playbooks | Process transparency |
| Release evidence | Audit trail |
| Red-team / audit reports | Accountability |
| Cross-repo control-plane artifacts | Reproducibility |

### Not public responsibility

This repo does not substitute for the semantic definitions of the other two.

---

## 5. Recommended Future Repository Structure

### Public repositories

| Repo | Role |
|------|------|
| `legal-math-modeling` | Mathematical spec, release boundary, formalization truth source |
| `juris-calculus-core` (future) | Auditable runtime kernel, checker, serialization, public test baseline |
| `juris-calculus-community-rules` (future) | Limited public community rules for reproducible experiments |

### Private repositories

| Repo | Role |
|------|------|
| `juris-calculus-pro` (future) | Product workflows, automation, customer features, ops APIs |
| `juris-calculus-rulebase-pro` (future) | Maintained commercial rule corpus |
| `juris-calculus-patent-lab` (optional) | Pre-patent evaluation implementations |

### If not splitting repos now

Apply these principles to current two repos:

1. `legal-math-modeling` continues public, spec-only
2. `juris-calculus` stays public but stops adding high-commercial-value layers to public main
3. New commercial rules, product automation, customer capabilities: do NOT merge into public main
4. Do directory-level classification and freeze first, then decide when to physically split

---

## 6. Enforcement

This boundary applies to ALL future work. Violations require explicit human
decision to override.

---

## 7. Verification

```bash
# Check no commercial rule corpus in public juris-calculus
ls juris-calculus/compiler_core/ | grep -i "commercial\|pro\|enterprise"

# Check no customer-specific adapters
find juris-calculus/ -name "*customer*" -o -name "*client*" -o -name "*enterprise*"

# Verify this document is referenced in README
grep -n "PUBLIC_PRIVATE_BOUNDARY\|disclosure\|public.*private" legal-math-modeling/README.md
```
