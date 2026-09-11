#!/usr/bin/env python3
"""Recursive, fully qualified Lean dependency planner. Never executes Lean.

Handles current and deleted/renamed source modules by using the union of the
base and head dependency graphs. Supports this repository's static `import`
syntax; this is a build planner, not a replacement for Lean elaboration.
"""
from __future__ import annotations
import argparse,json,re,subprocess
from pathlib import Path

LEAN_BASE=Path('proofs/lean/juris_lean')
NAME=re.compile(r"[A-Za-z_][A-Za-z_0-9']*(?:\.[A-Za-z_][A-Za-z_0-9']*)*")


def strip_comments_strings(text: str) -> str:
    """Preserve newlines and remove nested block/line comments and strings."""
    out=[];i=0;depth=0;quoted=False
    while i<len(text):
        ch=text[i]
        if depth:
            if text.startswith('/-',i):depth+=1;out.extend('  ');i+=2;continue
            if text.startswith('-/',i):depth-=1;out.extend('  ');i+=2;continue
            out.append('\n' if ch=='\n' else ' ');i+=1;continue
        if quoted:
            if ch=='\\' and i+1<len(text):out.extend('  ');i+=2;continue
            if ch=='"':quoted=False
            out.append('\n' if ch=='\n' else ' ');i+=1;continue
        if text.startswith('--',i):
            j=text.find('\n',i);j=len(text) if j<0 else j
            out.extend(' '*(j-i));i=j;continue
        if text.startswith('/-',i):depth=1;out.extend('  ');i+=2;continue
        if ch=='"':quoted=True;out.append(' ');i+=1;continue
        out.append(ch);i+=1
    if depth or quoted:raise ValueError('Unclosed source comment/string; do not silently omit imports')
    return ''.join(out)


def imports(text: str) -> set[str]:
    result=set()
    for ln in strip_comments_strings(text).splitlines():
        m=re.match(r'^\s*(?:(?:public|meta)\s+)*import\s+(.+?)\s*$',ln)
        if not m:continue
        for token in m[1].split():
            if not NAME.fullmatch(token):raise ValueError('Unsupported static import token: '+token)
            if token=='JurisLean' or token.startswith('JurisLean.'):
                result.add(token)
    return result


def module_of(path: str|Path) -> str|None:
    path=Path(path)
    try:rel=path.relative_to(LEAN_BASE)
    except ValueError:return None
    if rel.suffix!='.lean' or not rel.parts or rel.parts[0] not in {'JurisLean','JurisLean.lean'}:
        return None
    return '.'.join(rel.with_suffix('').parts)


def current_sources(repo: Path) -> dict[str,str]:
    ans={}
    for p in sorted((repo/LEAN_BASE).rglob('*.lean')):
        if '.lake' in p.parts:continue
        name=module_of(p.relative_to(repo))
        if name:ans[name]=p.read_text(encoding='utf-8')
    return ans


def git(repo: Path,*args: str) -> bytes:
    return subprocess.run(['git',*args],cwd=repo,check=True,capture_output=True).stdout


def old_sources(repo: Path,ref: str) -> dict[str,str]:
    # Failure to resolve a required base is a visible error, not an empty graph.
    names=git(repo,'ls-tree','-r','-z','--name-only',ref,'--',str(LEAN_BASE)).split(b'\0')
    ans={}
    for name in names:
        if not name:continue
        path=name.decode('utf-8');module=module_of(path)
        if module:ans[module]=git(repo,'show',ref+':'+path).decode('utf-8')
    return ans


def reverse_graph(*snapshots: dict[str,str]) -> dict[str,set[str]]:
    graph={}
    for snapshot in snapshots:
        for module,text in snapshot.items():
            for dep in imports(text):graph.setdefault(dep,set()).add(module)
    return graph


def affected(changed: set[str], graph: dict[str,set[str]]) -> set[str]:
    seen=set(changed);todo=list(changed)
    while todo:
        for dep in graph.get(todo.pop(),set()):
            if dep not in seen:seen.add(dep);todo.append(dep)
    return seen


def plan(repo: Path,base: str|None=None,head: str='HEAD',all_modules:bool=False,
         explicit:str|None=None) -> dict:
    current=current_sources(repo)
    if explicit:
        name=explicit if explicit.startswith('JurisLean.') or explicit=='JurisLean' else 'JurisLean.'+explicit
        if name not in current:raise ValueError('Unknown current module '+name)
        names={name};deleted=[]
    elif all_modules:names=set(current);deleted=[]
    else:
        if not base:raise ValueError('A verifiable base is required')
        previous=old_sources(repo,base)
        paths=git(repo,'diff','--no-renames','--name-only','-z',base,head,'--',str(LEAN_BASE)).split(b'\0')
        changed={m for raw in paths if raw for m in [module_of(raw.decode())] if m}
        deleted=sorted(changed-set(current))
        names=affected(changed,reverse_graph(previous,current))&set(current)
        if deleted and 'JurisLean' in current:names.add('JurisLean')
    return {'include':[{'module':n,'target':n} for n in sorted(names)],
            'removed_modules':deleted,'scope':'CURRENT_AND_REVERSE_DEPENDENTS_NOT_PROOF_ACCEPTANCE'}


def main():
    p=argparse.ArgumentParser();p.add_argument('--repo-root',type=Path,default=Path.cwd())
    p.add_argument('--all',action='store_true');p.add_argument('--base');p.add_argument('--head',default='HEAD')
    p.add_argument('--module');p.add_argument('--output',type=Path)
    a=p.parse_args();data=plan(a.repo_root.resolve(),a.base,a.head,a.all,a.module)
    s=json.dumps(data,indent=2)+'\n'
    if a.output:a.output.parent.mkdir(parents=True,exist_ok=True);a.output.write_text(s,encoding='utf-8')
    print(s,end='');return 0
if __name__=='__main__':raise SystemExit(main())
