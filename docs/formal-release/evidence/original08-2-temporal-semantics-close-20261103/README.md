# Original 08.2: temporal applicability and lossless per-event answers

**Disposition:** The frozen 08.2 L107/L109 mathematical obligations are covered as a candidate mapping; full-record PR acceptance is pending. The source-only changed-module build is not full-PR acceptance.

## Frozen obligation

Source: 08_规范时间证据与程序终局.md, lines 105–110; subparagraphs L107 and L109. Frozen source SHA256 is inherited from the accepted 08.1 packet for the same source document: eeaa6e20a4a475ff81dd25b77b36ffa28a27cdcf0e2b554f31b5710da9f6db0c.

L107 asks whether e < c, f ≥ e, and t ≥ f identify a unique applicable version when B's effective date, repeal, and transition conditions are unknown; it asks for two completions with different results and separate conditions for publication, effectiveness at evaluation time, and applicability to the fact date.

L109 specifies A on [0,10) and B on [10,+∞), with event fact times 5 and 12 and evaluation time 20. It asks for per-event selection, a counterexample to one global latest-version choice, a whole-case lossless-compression criterion, and a distinction between preserving version labels, one question's answer, and all expressible answers.

## L107: publication, effectiveness, and fact-date applicability

The existing finite completion counterexample keeps the same publication observation and known order while changing B's effective date (4 versus 10); the selected version at fact date 6 changes. The new finite witness separately records e < c, e ≤ f ≤ t, and a case where B is effective by evaluation time 6 while the fact date is 5, so the selector returns A at 5 and B at 6.

The implication publication ≤ effectiveFrom ∧ effectiveFrom ≤ t → publication ≤ t follows by transitivity. The implication effectiveFrom ≤ publication ∧ publication ≤ t means the rule is effective by publication and published by evaluation. These are conditional calendar implications only. A real query also needs non-expiry/repeal and any transition conditions; applicability to a particular fact remains determined by the separately supplied application predicate and its fidelity to the governing law. The inequalities do not define that predicate.

The source audit's finite results are synthetic interval-calendar witnesses. They do not establish real-world legal publication dates, effective dates, repeal status, or transition rules. The distinction is: `publication ≤ effectiveFrom` and `effectiveFrom ≤ t` imply publication by t; `effectiveFrom ≤ publication` and `publication ≤ t` imply effectiveness and publication by t. These calendar implications follow from order transitivity. Continued effectiveness at t additionally needs non-expiry/repeal facts, and applicability to fact f remains an independently supplied predicate with external fidelity conditions.

## L109: whole-language answer preservation

whole_query_profile_compression_iff states that losslessness for every finite list of questions is equivalent to equality of the entire answer functions for each event and each candidate version. The whole declared Query type is quantified; the unrelated finite matter set is not substituted for that language. The criterion is equality of the complete answer functions over every event and candidate version. DecidableEq Answer is needed by the existing Boolean checker interface; it does not imply that one finite procedure enumerates an infinite question language. The theorem also instantiates directly for whole cases: for any Case, finite frozen case domain `cases`, compression C, full-case observation Obs, let the two internal branches be 0 and 1 and define `answer mode c q := if mode = 0 then Obs c q else Obs (C c) q`, with options `[0,1]` and chosen branch 1. Its criterion becomes equality of the complete case answer functions for every c in `cases`; by function extensionality this is equality for every question q. The two branch numbers are representation tags, not legal-version identifiers, and `cases` is not claimed to be the entire case universe.

all_query_answers_need_not_preserve_version_labels is a finite Bool-query countermodel: versions 8 and 9 have the same answer for every Bool question while their labels differ. The older one-question counterexample remains in the reused audit outputs and shows why preserving one answer is weaker than preserving all answers.

## Source-only build evidence

The source checkpoint is commit 577902c7906106d54ac8fd860e1ba95be327928d, tree 21279d7ada968c0fe94edec43c00526d0d190821, parent 42306521627c6e3f87628054f271dd83ed0cc1cb. Run 41511948575, attempt 1, job 125505750460 (changed-modules) succeeded. Artifact ID 13174745187 is changed-module-only-41511948575-1; its actual ZIP and API digest are bound in verification.json. The included raw log and module plan are byte-for-byte copies of the ZIP members.

The current driver contains 27 actual #check/#print axioms pairs: three new declarations and 24 selected reused declarations from the accepted Temporal audit. The plan requests only JurisLean.Candidates.SourceTemporalBoundaryAudit20261103. The three new targets' raw lines and axiom sets are in verification.json; the log has no build errors or sorryAx output, and every observed axiom belongs to {propext, Classical.choice, Quot.sound}.

## Scope boundary

This package covers only the frozen 08.2 L107/L109 mathematical mapping. It does not establish fidelity of a real temporal application predicate, validate actual law or source data, connect the candidate producer to the old runtime caller, or close the broader source/time/evidence/process and paragraph-engineering work. Those broader items remain under their existing U00 and engineering records. No consumer rating or runtime flow is upgraded here.
