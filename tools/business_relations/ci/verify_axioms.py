"""Check actual #print axioms output for the explicit seed inventory.
This is not a Lean source parser or an environment-wide declaration audit.
The existing project's compiled-environment audit remains authoritative.
"""
from pathlib import Path
import json,re,sys
if len(sys.argv)!=3:
    raise SystemExit('usage: verify_axioms.py DECLARATIONS.json ACTUAL_AXIOMS.log')
manifest=json.loads(Path(sys.argv[1]).read_text())
text=Path(sys.argv[2]).read_text()
allowed={'propext','Classical.choice','Quot.sound'}
expected={manifest['namespace']+'.'+n for n in manifest['names']}
pattern=r"['`]([^'`]+)['`]\s+(?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)"
found={}
for name, axioms in re.findall(pattern,text,re.S):
    if name in found:raise SystemExit('duplicate printed declaration: '+name)
    used={x.strip() for x in axioms.split(',') if x.strip()}
    if used-allowed:raise SystemExit('unapproved axiom dependencies: '+str(used-allowed))
    found[name]=sorted(used)
if set(found)!=expected:
    raise SystemExit('actual log inventory mismatch: '+str({'missing':sorted(expected-set(found)),'extra':sorted(set(found)-expected)}))
print(json.dumps({'printed_declarations':len(found),'dependencies':found,'status':'PRINTED_SEED_AXIOMS_ACCEPTED_NOT_BUSINESS_RELEASE'},indent=2))
