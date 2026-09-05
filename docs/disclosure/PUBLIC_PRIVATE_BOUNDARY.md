# Public and Private Boundary

## Public repository

The public repository contains the auditable specification kernel: Lean and Python sources, public fixtures, checker contracts, release tooling, bounded evidence reports, and explanatory papers.

## Outside the public repository by default

The following are not required to make the public formal claims and should remain private unless separately cleared for disclosure:

- client or case data, personal information, privileged material, and litigation strategy;
- commercial rule libraries and proprietary lawyer workflows;
- private benchmarks, annotations, prompts, credentials, and infrastructure details;
- third-party material lacking a clear redistribution basis.

Public code may define a schema for such material without publishing the material itself.

## Claim boundary

The absence of private data does not weaken the named formal theorem. Conversely, a public theorem, certificate, digest, or fixture does not certify private data, a production deployment, or a legal conclusion.

Before adding a public artifact, verify that it is necessary for auditability, contains no secret or personal data, has a clear license/provenance basis, and does not expand the claim beyond [Allowed Claims](../formal-release/ALLOWED_CLAIMS.md). Unknown disclosure status is fail-closed.
