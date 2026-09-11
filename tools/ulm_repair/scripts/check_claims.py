#!/usr/bin/env python3
"""Retain the existing phrase check. A text scan is not legal-claim verification."""
from pathlib import Path
import argparse,json,sys
FORBIDDEN=["entire juris-calculus has been formally verified",
"Python implementation has been fully refinement-proved",
"omits no edges or creates no spurious attacks","graph similarity is a metric",
"differential privacy guarantees are established"]
def main():
 p=argparse.ArgumentParser();p.add_argument('--output',type=Path,required=True);a=p.parse_args();hits=[]
 for f in Path('docs').rglob('*.md'):
  t=f.read_text(encoding='utf-8').lower()
  for phrase in FORBIDDEN:
   if phrase in t:hits.append({'file':str(f),'phrase':phrase})
 a.output.write_text(json.dumps({'forbidden_claim_hits':hits},indent=2)+'\n',encoding='utf-8')
 return int(bool(hits))
if __name__=='__main__':raise SystemExit(main())
