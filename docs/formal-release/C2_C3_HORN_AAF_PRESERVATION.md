# Track C2/C3: Horn to AAF Preservation (MVM)

## C2: Argument Preservation

### argument_soundness
Every argument produced by the compiler maps to a Horn conclusion.
No argument is generated without a Horn source.

### argument_completeness
Every Horn conclusion that should enter the AAF has a corresponding argument.

## C3: Attack Preservation (MVM for rebuttal + priority)

### attack types
- rebuttal: contradictory conclusion
- exception: rule exception
- priority: hierarchical precedence
- prohibition: explicit prohibition
- undercut: premise attack

### MVM (Minimum Viable Math) for rebuttal
Prove: rebuttal edge exists in AAF iff corresponding Horn rules
have contradictory conclusions.

### MVM for priority
Prove: priority edge exists in AAF iff rule precedence chain
exists in Horn rule set.

### NOT YET
- exception soundness/completeness
- prohibition soundness/completeness
- undercut soundness/completeness

## Prohibited
- A single opaque "attacks_correct" boolean covering all attack types
- Numerical confidence score substituting for preservation proof
