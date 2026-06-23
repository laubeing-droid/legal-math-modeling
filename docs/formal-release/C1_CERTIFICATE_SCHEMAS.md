# Track C1: Certificate Schemas & Independent Checkers

## HornCertificate

`
FactNode(id, value)
RuleNode(rule_id, premise_cert_ids[])
`

Core theorem: checkHornCertificate = true => target in hornClosure

## Grounded IN Certificate

Records:
- argument id
- first accepted iteration
- all attackers
- for each attacker: grounded defender
- defender's earlier iteration

## OUT Certificate

Records:
- one IN attacker
- attacker's IN certificate

## UNDEC Certificate

Must verify:
- argument belongs to universe
- NOT in IN
- NO IN attacker
- Grounded fixed-point certificate valid
- Cycle witness alone is NOT sufficient to prove UNDEC

## Independence Requirement

Checker MUST NOT call the main evaluator.
