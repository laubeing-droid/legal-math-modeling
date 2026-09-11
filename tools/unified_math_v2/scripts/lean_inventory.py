#!/usr/bin/env python3
"""Generate the audit from actual seed declarations. Run before CI compilation."""
from pathlib import Path
import argparse,re,json

def main():
    p=argparse.ArgumentParser();p.add_argument('--repo-root',type=Path,required=True)
    p.add_argument('--output',type=Path,required=True);a=p.parse_args()
    root=a.repo_root/'proofs/lean/juris_lean/JurisLean/UnifiedV2'
    names=[];files=[]
    for f in sorted(root.glob('*.lean')):
        if f.name=='Audit.lean':continue
        text=f.read_text(encoding='utf-8')
        # Scan tokens outside block and line comments, not prose that discusses policy.
        stripped=re.sub(r'/\-.*?\-/','',text,flags=re.S)
        stripped=re.sub(r'--[^\n]*','',stripped)
        if re.search(r'\b(sorry|admit|axiom|unsafe)\b',stripped):
            raise SystemExit(f'Unacceptable proof token: {f}')
        decls=re.findall(r'\btheorem\s+([A-Za-z_][A-Za-z0-9_\']*)',stripped)
        for n in decls:names.append('JurisLean.ULM.UnifiedV2.'+n)
        files.append({'file':str(f.relative_to(a.repo_root)),'declarations':decls})
    if not names or len(set(names))!=len(names):raise SystemExit('Missing/duplicate seed declarations')
    a.output.parent.mkdir(parents=True,exist_ok=True)
    a.output.write_text(json.dumps({'module':'JurisLean.UnifiedV2.All','names':names,'files':files},indent=2)+'\n')
    (root/'Audit.lean').write_text('import JurisLean.UnifiedV2.All\n\n'+'\n'.join('#print axioms '+n for n in names)+'\n')
    print(json.dumps({'source_modules':len(files),'theorem_declarations':len(names),'status':'INVENTORY_ONLY'}))
if __name__=='__main__':main()
