#!/usr/bin/env python3
"""Patch the frozen Rosetta overclaim, retaining the EXACT proved proposition.

No GitHub writes. Run in the intended LMM working tree; review its git diff.
Updating references prevents the axiom audit from using a removed declaration.
"""
from pathlib import Path
import argparse,re,json

HEADER='''-- FiniteRosetta.lean
-- Frozen-sample mapping classification, not a categorical impossibility result.
-- Counts are computed from the explicitly encoded mappingStatus function.
-- These labels do not establish that a foreign legal institution is absent.

import Mathlib.Data.Fintype.Basic

/-!
# Frozen Mapping Sample

The encoded sample has 44 entries, of which 30 are labelled CN_ONLY.
`sample_mapping_not_total` establishes only that the encoded sample is not
entirely free of CN_ONLY labels. It quantifies over neither categories nor
functors, and makes no claim that a semantics-preserving alignment is
impossible. No majority threshold is needed for this sample statement.

The relationship between this encoding, source records, and legal
interpretations is a separate validation obligation.
-/

'''
DOC='''/-- The encoded sample contains at least one CN_ONLY label. This is NOT a
categorical theorem about functors or the absence of foreign legal concepts. -/'''

def transform(text):
    if 'theorem sample_mapping_not_total' in text:
        return text
    if 'theorem no_total_functor :' not in text or 'inductive MappingStatus : Type' not in text:
        raise ValueError('Not the frozen Rosetta source: manual review required')
    # Retain the encoded statuses, arithmetic declarations, and exact proposition.
    body=text[text.index('/-- Mapping status from claim_mapping.csv -/'):] 
    start=body.index('/-- No total functor can exist:')
    end=body.index('theorem no_total_functor :',start)
    body=body[:start]+DOC+'\n'+body[end:]
    body=body.replace('theorem no_total_functor :','theorem sample_mapping_not_total :')
    body=body.replace('entries with no foreign mapping','entries labelled CN_ONLY in the encoded sample')
    body=body.replace('The majority of entries lack foreign mappings','The majority of encoded entries carry CN_ONLY')
    original_proposition='¬ (∀ i : Fin 44, mappingStatus i.val ≠ .CN_ONLY)'
    if original_proposition not in body:
        raise ValueError('Original proposition was not preserved')
    return HEADER+body

def main():
    p=argparse.ArgumentParser();p.add_argument('--repo-root',type=Path,required=True)
    a=p.parse_args();target=a.repo_root/'proofs/lean/juris_lean/JurisLean/FiniteRosetta.lean'
    text=target.read_text(encoding='utf-8');new=transform(text)
    target.write_text(new,encoding='utf-8')
    changed=[str(target.relative_to(a.repo_root))]
    # Only exact references to the declaration are renamed; substantive prose
    # elsewhere must be reviewed, not replaced by a new global assertion.
    for root in ('proofs','theory','scripts','tests','docs','paper'):
        for file in (a.repo_root/root).rglob('*'):
            if 'unified-v2.1' in file.parts:continue
            if 'unified-v2.1' in file.parts:continue
            if file==target or file.suffix not in {'.lean','.py','.md','.json','.tex','.yaml','.yml'}:continue
            s=file.read_text(encoding='utf-8')
            if 'no_total_functor' in s:
                file.write_text(s.replace('no_total_functor','sample_mapping_not_total'),encoding='utf-8')
                changed.append(str(file.relative_to(a.repo_root)))
    print(json.dumps({'changed':changed,'proposition_preserved':True,'lean_acceptance':'CI_NOT_RUN'},indent=2))
if __name__=='__main__':main()
