#!/usr/bin/env python3
"""Generate Contracts.lean and Acceptance.lean (217 registrations).

Each contract statement is extracted verbatim from the mapped module
theorem's own signature (with its section variables), so the contract is
the real mathematical statement, never an alias. The acceptance proof is
the module theorem itself. C07 additionally conjoins all seven root
statements so its proof dependency closure covers the seven roots.
"""
import json, re, sys
from pathlib import Path

REPO = Path(__file__).resolve().parents[3]
FM = REPO / 'proofs/lean/juris_lean/JurisLean/FullMath'
sys.path.insert(0, str(REPO / 'work/full-math'))
from build_map import sig_of, inv  # noqa: E402

VAR_RE = re.compile(r'^variable (.+)$', re.M)
BOX_D = re.compile(r'Box \(d \+ 1\)')


def split_binders(s):
    out, depth, cur = [], 0, ''
    for ch in s:
        if ch in '([{':
            depth += 1
        elif ch in ')]}':
            depth -= 1
        if ch == ' ' and depth == 0:
            if cur:
                out.append(cur)
            cur = ''
        else:
            cur += ch
    if cur:
        out.append(cur)
    return out


def section_vars(thm):
    text = (REPO / inv[thm]).read_text(encoding='utf-8').replace('\r\n', '\n')
    decls = []
    for m in VAR_RE.finditer(text):
        decls.extend(split_binders(m.group(1)))
    return decls


def idents_of(binder):
    return re.findall(r"[A-Za-z_][A-Za-z0-9_'!?]*", binder)


def form_of(thm):
    binders, stmt = sig_of(thm)
    parts = []
    body_text = binders + ' ' + stmt
    for d in section_vars(thm):
        if any(re.search(r'\b' + re.escape(i) + r'\b', body_text) for i in idents_of(d)):
            kind = '{%s}' % d[1:-1] if d.startswith('{') else ('[%s]' % d[1:-1] if d.startswith('[') else '(%s)' % d)
            parts.append(kind)
    if BOX_D.search(body_text):
        parts = ['{d : ℕ}'] + parts
    if binders:
        parts.append(binders)
    if parts:
        return '∀ ' + ' '.join(parts) + ', ' + stmt
    return stmt


def main():
    T = json.loads((REPO / 'work/full-math/registration_map.json').read_text(encoding='utf-8'))
    reqs = json.loads((REPO / 'tools/full_math/spec/REQUIREMENTS.json').read_text(encoding='utf-8'))
    order = [r['theorem'].split('.')[-1] for r in reqs]

    opens = ['open JurisLean.FullMath.Core', 'open JurisLean.FullMath.Logic',
             'open JurisLean.FullMath.Evidence', 'open JurisLean.FullMath.Probability',
             'open JurisLean.FullMath.Numeric', 'open JurisLean.FullMath.Burden',
             'open JurisLean.FullMath.Action', 'open JurisLean.FullMath.Composition',
             'open JurisLean.FullMath.Representation', 'open JurisLean.FullMath.Causal',
             'open JurisLean.FullMath.Document', 'open JurisLean.FullMath.Roots',
             'open JurisLean.FullMath.Gaps', 'open JurisLean.FullMath.Numeric.Iv', '']
    header = ['import JurisLean.FullMath.Tranche1', 'import JurisLean.FullMath.Tranche2',
              'import JurisLean.FullMath.Tranche3', 'import JurisLean.FullMath.Tranche4',
              'import JurisLean.FullMath.Tranche5', 'import JurisLean.FullMath.Tranche6',
              'import JurisLean.FullMath.Tranche7', '',
              '/-! Generated from the module signatures: each contract is the real',
              'statement of its mapped theorem. This file contains no proofs. -/',
              ''] + opens
    contracts = list(header) + ['namespace JurisLean.FullMath.Contracts', '']
    acceptance = (['import JurisLean.FullMath.Contracts', '',
                   '/-! Generated acceptances: each is discharged by the mapped module',
                   'theorem (definitional equality on binder annotations). -/',
                   ''] + opens
                  + ['namespace JurisLean.FullMath.Acceptance', ''])
    c07_extra = ['JurisLean.FullMath.Roots.root_GENERIC_FINITE',
                 'JurisLean.FullMath.Roots.root_SYMBOLIC_EXACT_box',
                 'JurisLean.FullMath.Roots.root_STATISTICAL_COMPOSITION',
                 'JurisLean.FullMath.Roots.root_CIVIL',
                 'JurisLean.FullMath.Roots.root_CRIMINAL',
                 'JurisLean.FullMath.Roots.root_ADMINISTRATIVE',
                 'JurisLean.FullMath.Roots.root_DOCUMENT_DELIVERY']
    for name in order:
        thm = T[name]
        stmt = form_of(thm)
        if name == 'target_C07':
            stmt = '(' + stmt + ') ∧ ' + ' ∧ '.join('(' + form_of(r) + ')' for r in c07_extra)
        contracts.append('def %s : Prop := %s' % (name, stmt))
        contracts.append('')
        proof = ('⟨' + ', '.join([thm] + c07_extra) + '⟩') if name == 'target_C07' else thm
        acceptance.append('theorem %s : Contracts.%s := %s' % (name, name, proof))
        acceptance.append('')
    contracts.append('end JurisLean.FullMath.Contracts')
    acceptance.append('end JurisLean.FullMath.Acceptance')
    (FM / 'Contracts.lean').write_text('\n'.join(contracts) + '\n', encoding='utf-8', newline='\n')
    (FM / 'Acceptance.lean').write_text('\n'.join(acceptance) + '\n', encoding='utf-8', newline='\n')
    print('generated', len(order), 'rows')


if __name__ == '__main__':
    main()
