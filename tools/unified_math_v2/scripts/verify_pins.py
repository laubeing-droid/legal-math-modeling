#!/usr/bin/env python3
"""Read pinned manifests; never launches Lean/Lake/Elan."""
import argparse,json,subprocess
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
def check(repo):
    pins=json.loads((ROOT/'manifests/baseline-v21.json').read_text())
    lean=repo/'proofs/lean/juris_lean'
    if (lean/'lean-toolchain').read_text().strip()!=pins['lean_toolchain']:
        raise ValueError('Lean toolchain differs from reviewed baseline')
    manifest=json.loads((lean/'lake-manifest.json').read_text())
    found=[p for p in manifest['packages'] if p['name']=='mathlib']
    if len(found)!=1 or found[0]['rev']!=pins['mathlib_commit']:raise ValueError('Mathlib pin mismatch')
    return pins
if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--repo-root',type=Path,required=True);a=p.parse_args()
    print(json.dumps(check(a.repo_root),indent=2))
