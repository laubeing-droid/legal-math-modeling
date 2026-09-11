"""Finite full-tree argument identity, bounded generation, and Horn reference.

Depth is part of declared semantics. A depth bound is NOT proof of coverage
of unrestricted structured argumentation. No conclusion-only quotient is used.
"""
from __future__ import annotations
from dataclasses import dataclass
from itertools import product

@dataclass(frozen=True)
class Rule:
    identity: str
    premises: tuple[str,...]
    head: str

    def __post_init__(self):
        if not self.identity or not self.head or any(not p for p in self.premises):
            raise ValueError('Rule identity and atoms required')

@dataclass(frozen=True)
class Leaf:
    identity: str
    atom: str
    assumed: bool = False

@dataclass(frozen=True)
class Argument:
    context: str
    head: str
    rule: str | None
    leaf: str | None
    children: tuple['Argument',...]
    assumptions: frozenset[str]

    @property
    def depth(self):
        return 0 if self.rule is None else 1+max((c.depth for c in self.children),default=0)

    @property
    def identity(self):
        # Structural tuples avoid delimiter collisions and retain all vulnerabilities.
        return (self.context,self.head,self.rule,self.leaf,
                tuple(c.identity for c in self.children),tuple(sorted(self.assumptions)))

    def descendants(self):
        return frozenset({self}) | frozenset(a for c in self.children for a in c.descendants())


def validate_inputs(leaves, rules):
    if len({l.identity for l in leaves}) != len(leaves):
        raise ValueError('Duplicate fact identity')
    if len({r.identity for r in rules}) != len(rules):
        raise ValueError('Duplicate rule identity')


def generate(context: str, leaves: tuple[Leaf,...], rules: tuple[Rule,...], depth: int):
    if not context or type(depth) is not int or depth < 0:
        raise ValueError('Context and nonnegative semantic depth required')
    validate_inputs(leaves,rules)
    result = {Argument(context,l.atom,None,l.identity,(),frozenset({l.identity}) if l.assumed else frozenset()) for l in leaves}
    for _ in range(depth):
        previous = frozenset(result)
        for r in rules:
            choices = [tuple(a for a in previous if a.head == p) for p in r.premises]
            for children in product(*choices):
                taint = frozenset(x for c in children for x in c.assumptions)
                result.add(Argument(context,r.head,r.identity,None,tuple(children),taint))
    return frozenset(result)


def valid_argument(a: Argument, context: str, leaves, rules, depth: int):
    """Independent recursive full-tree checker; not a call to generate."""
    if a.context != context or a.depth > depth:
        return False
    if a.rule is None:
        ls = [l for l in leaves if l.identity == a.leaf and l.atom == a.head]
        return len(ls)==1 and not a.children and a.assumptions == (frozenset({ls[0].identity}) if ls[0].assumed else frozenset())
    rs = [r for r in rules if r.identity == a.rule]
    if len(rs)!=1 or a.leaf is not None or a.head!=rs[0].head:
        return False
    r=rs[0]
    return (tuple(c.head for c in a.children)==r.premises
            and all(valid_argument(c,context,leaves,rules,depth-1) for c in a.children)
            and a.assumptions==frozenset(x for c in a.children for x in c.assumptions))


def horn_closure(facts, rules):
    current=set(facts)
    universe=current | {r.head for r in rules} | {p for r in rules for p in r.premises}
    for _ in range(len(universe)+1):
        nxt=current|{r.head for r in rules if set(r.premises)<=current}
        if nxt==current:
            return frozenset(current)
        current=nxt
    raise AssertionError('Finite closure did not stabilize')


def attacks_on_subarguments(arguments, contraries):
    """Only explicit contrary pairs; no automatic priority or negation by failure."""
    return frozenset((a,b) for a in arguments for b in arguments
                     if any((a.head,c.head) in contraries for c in b.descendants()))
