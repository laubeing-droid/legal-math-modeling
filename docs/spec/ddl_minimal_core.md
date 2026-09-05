# DDL Minimal Core

## Scope

`proofs/lean/juris_lean/JurisLean/DDLDefinitions.lean` defines the repository's minimal deontic core for four modalities:

\[
M = \{\text{obligation},\text{ prohibition},\text{ permission},\text{ constitutive}\}.
\]

A direct violation is recognized only when an obligation or prohibition is active, its condition and deadline are satisfied in the same slice, the relevant fact is verified, and the required or forbidden state is breached. Permission and constitutive norms do not create a direct violation under this definition.

Defenses and exceptions require verified evidence. Remediation remains attached to the violated norm. Priority defeat requires verified priority evidence and preserves the declared winner-to-loser direction.

## Proved consequences

The Lean module includes named results such as:

- `violation_implies_norm_active`;
- `permission_no_direct_violation`;
- `constitutive_no_direct_violation`.

It also defines bounded helpers for the contract-breach, fact-admission, permission, and priority slices. Exact theorem statements in Lean are authoritative; this prose is only a guide.

## Non-claims

The minimal core does not establish that:

- these four modalities exhaust every legal system;
- a runtime correctly maps natural-language law or facts into the model;
- verified evidence is legally admissible or substantively true;
- the four slices cover all exceptions, remedies, conflicts, or temporal doctrines;
- a concrete legal decision is correct.

Use [Allowed Claims](../formal-release/ALLOWED_CLAIMS.md) and [Forbidden Claims](../formal-release/FORBIDDEN_CLAIMS.md) when describing results.
