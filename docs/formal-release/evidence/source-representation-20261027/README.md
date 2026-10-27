# Scoped identity, observation adequacy and rational quantities

Original 07.1, 07.4 and the quantity part of 07.8; S07. Independent subject `9a2d0bbfff264c8593fe148378a64460741a250a`, [run40457212969](https://github.com/laubeing-droid/legal-math-modeling/actions/runs/40457212969), [job122033215316](https://github.com/laubeing-droid/legal-math-modeling/actions/runs/40457212969/job/122033215316): 15 exact type/axiom targets and 12 guarded executions PASS. The 30 type/axiom message blocks are retained from the actual log; both LF-normalized sources are bound to the successful subject.

## Original obligations

- On the resolved domain of a fixed partial interpretation, same-object is an equivalence relation. The semantic key is constructed from the actual resolved object, and its equality is proved equivalent to same-object. This construction separates no-false-merge soundness from no-false-split completeness; neither is inferred from a bare event or reference string.
- The original finite examples have two references to one payment, another payment sharing the same bare event ID, unresolved references that are not equivalent, and two different amounts under one table key. First-match lookup changes with row order. The executable resolver requires one matching row and reports ambiguity even for a duplicated equal row; it does not silently adopt a first-match identity policy.
- Observation adequacy explicitly supplies a decoder for each declared observation. Equal representations preserve all those observations, and separation then gives injectivity. The original [10] and [4,3,3] payment histories both have terminal balance zero while remaining different histories; preservation on the image alone says nothing about unsupported model points.
- The new RationalQty syntax has rational Amount literals, addition that compares the full currency/unit/rule-version tag, and multiplication by an explicitly dimensionless rational scalar. Every rational Amount has an exact encoding. Addition refuses mismatched tags; scaling retains the full tag.
- The old QtyAst is not modified. Its existing division-free integer-valued theorem proves that no such expression can denote 1/2. The new exact bridge is not presented as a constructor of the old syntax or a legal authorization to retag amounts.

## Scope and validation

The executions cover copied/distinct/missing/ambiguous references, key-order dependence, the two original equal-balance histories, 1/2 exact encoding, addition, dimensionless scaling and separate currency/unit/rule-version refusals.

First draft `3fcc5bf0471d586eb342f4f407cc04eff7c50e40`, run40456886605/job122032188795, failed because decide did not reduce the rational max expression. Replacing that proof step with normalization preserved the statement and all checks. It is not counted as a successful subject.

The partial interpretation remains external and scoped; this is not a real-world entity-resolution algorithm. Full consumed-source views, material interpretation, record projections, common-model/stage composition and the actual source-to-compiler consumer are separate outstanding original obligations. This package does not claim all of topic 07 or U00 complete.

OPEN=20; closes_debt=false; no discharges change; frozen subject21862d9b/Authority40274167574/named61 unchanged. No local Lean/Lake/Elan.
