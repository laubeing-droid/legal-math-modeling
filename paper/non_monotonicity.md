# Non Monotonicity: A Release-Bounded Note

## Abstract

This rewritten paper states a source-bounded view of the `legal-math-modeling` project. The project separates formal specification work from runtime engineering. It uses Lean files, Python regression fixtures, and audit manifests to document a limited proof boundary for selected legal-reasoning structures. The paper does not claim that a production legal AI system, a full juris-calculus runtime, or private legal workflows have been formally proved correct.

## 1. Scope

The repository studies a specification layer for legal reasoning. The current public boundary is limited to canonical legal types, a minimal DDL model, a Horn-to-AAF compiler contract, a certificate/checker boundary, and four slices: contract breach, license, permission, and priority.

## 2. Formal Sources

Formal statements must be read from `proofs/lean/juris_lean/JurisLean/`. At rewrite time the tree contains 32 Lean source files and 126 theorem declarations. These counts are source inventory facts, not a release certificate for the current commit.

## 3. Method

The method is specification-first:

- define canonical legal objects before runtime use;
- keep LLM output as candidate material only;
- require source-bound verification before a fact can be used as verified input;
- separate mathematical proof, engineering tests, generated reports, and narrative explanation;
- preserve counterexamples and limitations instead of converting failures into positive claims.

## 4. Topic Contribution

For this paper topic, the contribution is a bounded framing rather than an unrestricted correctness result. The topic is useful only where its assumptions match the canonical schema and where runtime evidence is separately available.

## 5. Limitations

This paper does not establish full runtime correctness, jurisdiction-wide legal coverage, commercial workflow readiness, or private benchmark validity. Banach-related material and generated AI audit reports remain explanatory unless tied to current source and current verification evidence.

## 6. Disclosure

No customer data, private legal strategy, or private benchmark content is included. Claims in this paper are subordinate to the repository manifests and source files.

## References

See `paper/references.bib` for the local reference set used by the rewritten paper directory.
