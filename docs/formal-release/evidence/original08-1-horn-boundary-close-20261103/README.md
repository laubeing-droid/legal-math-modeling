# Original 08.1: finite Horn boundary

**Mathematical disposition:** L101 and L103 are covered by reused finite-closure results and this round's finite conditional theorem and countermodels. The canonical row is marked `COVERED`; full-record PR acceptance is pending. This source-only module build is not full-chain or mainline acceptance.

## Frozen obligation

The frozen source is `D:\Codex\1.法律工作区\legal-math-modeling工作区\20261021挺进统一法律数学模型\理论统稿与ZCode施工包_v003补齐来源版_20261021T091138Z_fd4965\题单\08_规范时间证据与程序终局.md`, lines 99–104, SHA256 `1bf38abdd67bbacde464bc47814a672220a223d4a553f3cebf8812b066b3458a`. The operative paragraphs say:

> 精确定义立即后承算子、闭包、规则适用门控及对象语义，证明有限基原子条件下闭包存在、可计算并终止。证明一个条件性可靠性定理：在事实忠实、规则忠实、适用门控有效且对象语义满足规则的前提下，闭包导出的指定原子在对应世界成立。逐项说明哪条前提是内部可查结构，哪条仍需外部见证。

> 构造三个最小反例：规则形式正确但不忠实于所声明法律；规则本身正确但应用到错误版本或事项；事实基含未被证明的付款事实。三个例子均可让内部推导完成，却不能得到真实法律结论。用 10、7、7 说明数量结果正确不补足这些缺口。若一条规范带例外，请比较显式补充“例外不成立”的正向见证与仅未找到例外材料，两者为什么不等价。不要把本题扩成一般非单调逻辑的无界研究，只给一个足够表达该例外的有限子模型。

## What the finite model establishes

The source audit imports and reuses the existing finite closure, provenance, source extraction, four-stage ledger, and exception-witness results. Its new `same_source_completed_countermodels` theorem uses one accepted `sourceModel` output and one successful `compileView` output with the same `ExtractedView`. The finite closure contains query atom `3` and is closed under the coded active rule. On that same source fixture, the first payment leaves amount `3` and the second leaves `0`.

The fixture uses synthetic atoms: `1` is the supplied payment assertion, `3` is the proposed legal conclusion, and `4` is a positive witness that an exception does not apply. The coded rule is `[1] → 3`, its version metadata is read from the fixed `stageGamma`, and its coded gate returns `true`. The separately declared exception rule is `[1, 4] → 3`. These are finite countermodels, not statements about any actual statute, party, payment, or legal outcome.

| Frozen boundary | Internal finite result | What remains an external premise |
| --- | --- | --- |
| Finite Horn computation | Existing rule syntax, provenance checks, finite active-rule selection, closure, query membership, and closure-at-fuel results are reused. The new compile call succeeds and returns a closed finite output. | The code's `RuleUse`, version field, and Boolean gate do not establish that a rule faithfully states governing law or is applicable to a real matter. |
| Same source and ledger result | The accepted `sourceModel` and compiler output share the selected source view; the existing stage fixture supplies the `10, 7, 7` ledger calculation and the new theorem carries its `3` then `0` balances. | An actual payment must be established as a true fact in the relevant world. The encoded object interpretation and source `μ` must be faithful where required. |
| Wrong rule / wrong version / missing payment | The theorem gives three separate finite failures while the code-level compilation and closure still complete: the coded rule differs from the declared exception rule; changing the version metadata removes the active rule; and a world where the payment fact is false does not satisfy the proposed conclusion. | Actual Γ applicability, facts, legal object meaning, rule semantics, and the truth of source evidence are not proved by this synthetic model. |
| Exception evidence | `positive_exception_witness_is_not_absence` reuses `Acceptance.n03_missing_exception_is_not_positive_witness`. With only `[1]`, the rule `[1, 4] → 3` does not derive `3`; adding positive atom `4` changes the finite closure and rules out the exception-true world in the declared model. | Failure to find exception material is not evidence that the exception is false. A real positive witness and a faithful interpretation remain external. |

The reused `Compiler.u03_1_relative_soundness` is conditional: it takes a model of the facts and active rules and derives truth from derivability. The reused temporal results likewise state conditions for applicability and selection; they do not prove those conditions for a real legal source. Thus the package closes the frozen mathematical scope for finite Horn structure and its requested examples, while making no claim that Chinese law, actual source truth, or an existing runtime consumer has been verified.

## Historical remaining work and consumer boundary

The former row-level note was: “Temporal PR52及合后main40476502528/final122101285843全PASS。实际source/time/evidence/process有限联合验证器、逐段工程核对和U00继续。” That note referred to a broader source/time/evidence/process verifier, paragraph-level engineering checks, and U00 integration. Those remain in their existing U00 and engineering scopes; they are not added as assumptions to frozen 08.1 and are not claimed complete here.

The U00 update is producer-side evidence only for the related source/facts edges 1 and 2. The new compile/source results do not modify `Pipeline.run`, `runBound`, their callers, parameters, ratings, runtime flow, or consumer acceptance. No U00 edge status or global completion flag is upgraded.

## Source-only build evidence

The source checkpoint is commit `592906d2178a83a3d897e2f6c4b841b3882dd7d1`, tree `84ec16ee751c73b5094c38273c0b7ca3021c02eb`, parent `6ee19c74af15efb898f1f245fd9e98b840e782c4`, on `formal/close-original08-1-horn-semantics-20261103`. The only source changes were the new audit module and its mutable root import. The frozen `Final20261021/AxiomAudit.lean` blob is unchanged.

Changed-module run `41497387863`, attempt 1, job `125455798434` (`changed-modules`), completed successfully on that source checkpoint. The actual artifact is `changed-module-only-41497387863-1`, ID `13166827418`, ZIP 14,676 bytes, SHA256 `329a5d923b1a8f0620bc070524ef2903dc1097739b9a7f99cc43c2bb1134951a`. The ZIP's `changed-module.log` and `module-plan.json` are preserved byte-for-byte in this package. The plan requests `JurisLean.Candidates.SourceHornBoundaryAudit20261103` only and has no removed modules.

The audit emits 25 named `#check` / `#print axioms` pairs: two new theorems and 23 selected reused outputs. The two new outputs are at source lines 182–185 and raw-log lines 1593/1651 and 1654/1683. Their axiom sets are `[propext, Classical.choice, Quot.sound]` and `[propext, Quot.sound]`. The complete per-target raw-log line map and axiom sets are in `verification.json`; the output uses only the standard Lean axioms recorded there. The module build has no Lean errors or `sorryAx` output. This is changed-module evidence only; full-record PR and merge acceptance remain pending.
