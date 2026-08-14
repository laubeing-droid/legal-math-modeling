# Horn-to-AAF Translation Witness

## Contract

`horn-aaf-translation-witness-v1` binds the input facts, rules, exceptions, and
priorities to expected and produced arguments/attacks. The independent checker uses
exact identifier sets and full relation records.

For the fixed input language and `grounded@1` semantics, the checker requires:

- every output argument has an input rule and support facts;
- every expected argument and edge is present;
- no unexpected argument or edge is present;
- every edge has a known rebuttal/exception/priority kind and input witness;
- every edge endpoint exists;
- priority defeat preserves winner-to-loser direction;
- identifiers are unique and a cycle policy is explicit;
- the input and witness digests match their content.

The required mutation gates are omission, spurious edge, and reversed priority
direction. Unknown edge kinds, duplicate identifiers, missing cycle policy, missing
input witnesses, or unknown semantics fail closed.

## Proof boundary

Lean proves finite-set consequences of equality between expected and produced
relations: no omission, no spurious edge, and preserved priority endpoints. Python
recomputes concrete records and digests. Neither layer establishes translation
completeness beyond the bound input language, semantics version, and fixtures.
