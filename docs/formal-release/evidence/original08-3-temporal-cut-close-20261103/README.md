# Original 08.3: temporal cuts, late evidence, and input identity

**Disposition:** The frozen 08.3 L113/L115/L117 mathematical obligations are covered by the selected existing temporal results and the new finite identity theorem. This package records source-module evidence; full-record PR acceptance is pending.

## Frozen source and obligations

Source: `08_规范时间证据与程序终局.md`, lines 111–118; subparagraphs L113, L115, and L117. Frozen source SHA256: `eeaa6e20a4a475ff81dd25b77b36ffa28a27cdcf0e2b554f31b5710da9f6db0c`.

- **L113:** distinguish cutting visible history before selection from selecting then cutting, and state the locality/key-consistency/support conditions for commuting them. Reuse the late-material noncommutation witness. A present-day view does not by itself authorize changing a previously final legal effect.
- **L115:** distinguish monotonicity of derived facts, refinement of a fixed nonempty legal-world set for one fixed proposition, and truth in an actual world. Fact-set growth supports the derivation result only with fixed query/rules and retained facts; changing the rule gate or dropping facts is outside that premise. `knownAtAlternatives` retains the declared possible times, and an empty set remains unknown rather than supplying an invented historical time.
- **L117:** the accepted `visibleSet` retains each input `VersionRecord` whose `visible` predicate passes. The new theorem proves that two such records with distinct stable IDs both remain members and are unequal. It uses no ordering assumption on `DayInt`; the guarded examples remain examples rather than proofs.

## Reused conditions and limits

The cut/selection equation is conditional on the existing key-consistency, locality of `App`, and visible-support premises. `Compiler.derives_mono_facts` applies to a stable active rule set and a facts extension that keeps the earlier facts. `Must` refinement concerns one fixed proposition and a nonempty subset of the prior possible-world set; it does not establish truth without membership of the actual world.

The early/later counterexample changes both record and knowledge cutoffs; it is not evidence that changing only the knowledge cutoff caused the result. The interval latest-start theorem is restricted to its coverage, unique-start, ordering, half-open boundary, visibility, and `App` agreement premises. Publication/selection metadata does not establish a real legal rule’s validity or application, and `procedure` / `necessary_exhausted` remain independent process gates. No general retroactivity rule, actual-law truth, or production caller connection is claimed.

## Source-only build

Source checkpoint: `53f9e635d1209ad1b1b6a6e84fff18d1e2eae63d`, tree `1cc25a41daf017f90882d3c714400bbb507304cd`, parent `280f249d4a4d4e28d4988802b0282476de7b9788`. Run `41529170635`, attempt 1, changed-module job `125564632836` succeeded. Artifact ID `13181481502` (`changed-module-only-41529170635-1`) is recorded with its API digest and physical ZIP digest in `verification.json`. `changed-module.log` and `module-plan.json` are byte-for-byte copies of the ZIP members.

The actual driver has 27 theorem `#check` / `#print axioms` pairs: one new identity theorem and 26 reused outputs. The plan requests only `JurisLean.Candidates.SourceTemporalIdentityAudit20261103`; the source-only build does not represent full-record acceptance. The selected theorem names, actual source/log lines, and axiom sets are listed in `verification.json`.

## Consumer boundary

This is producer-side mathematical evidence associated with U00 edge 3. It does not change existing `Pipeline.run` or `runBound` callers, parameters, ratings, runtime flow, consumer acceptance, or the broader source/time/evidence/process engineering work.
