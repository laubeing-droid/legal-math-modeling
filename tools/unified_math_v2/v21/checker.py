"""Closed reference checker: the certificate supplies no predicate/candidate domain.

Acceptances here mean Python cross-checks, NOT Lean-refined runtime certificates.
The trusted caller supplies the expected immutable Problem. This is not a
sandbox against malicious Python code with process-memory write access.
"""
from __future__ import annotations
from dataclasses import dataclass
from itertools import combinations
from fractions import Fraction as Q
from .context import ContextKey, require_same_context
from reference.core import rational


@dataclass(frozen=True)
class AffineIntegerProblem:
    lo: int
    hi: int
    a: Q
    b: Q
    rhs: Q
    def __post_init__(self):
        if type(self.lo) is not int or type(self.hi) is not int or self.lo > self.hi:
            raise ValueError('Finite integer domain required')
        for name in ('a','b','rhs'):
            object.__setattr__(self, name, rational(getattr(self,name)))


@dataclass(frozen=True)
class DungProblem:
    arguments: tuple[str, ...]
    defeats: frozenset[tuple[str, str]]
    profile: str
    def __post_init__(self):
        if (type(self.arguments) is not tuple or any(type(a) is not str or not a for a in self.arguments)
                or len(set(self.arguments)) != len(self.arguments)):
            raise ValueError('Unique argument identifiers required')
        if self.profile not in {'grounded','complete','preferred','stable'}:
            raise ValueError('Unknown semantic profile')
        if type(self.defeats) is not frozenset:
            raise TypeError('Immutable defeat graph required')
        if any(type(e) is not tuple or len(e)!=2 or not set(e)<=set(self.arguments) for e in self.defeats):
            raise ValueError('Unknown/malformed defeat endpoint')
        object.__setattr__(self, 'arguments', tuple(sorted(self.arguments)))


def candidate_domain(problem):
    if type(problem) is AffineIntegerProblem:
        if problem.hi-problem.lo+1 > 1_000_000:
            raise ValueError('CHECKER_BUDGET_UNAVAILABLE')
        return tuple(range(problem.lo, problem.hi+1))
    if type(problem) is DungProblem:
        # Explicit checker budget, not a silently changed semantic domain.
        if len(problem.arguments)>16:
            raise ValueError('CHECKER_BUDGET_UNAVAILABLE')
        return tuple(frozenset(s) for k in range(len(problem.arguments)+1)
                     for s in combinations(problem.arguments,k))
    raise TypeError('No registered finite semantics for this problem type')


def _defends(p, s, a):
    return all(any((c,b) in p.defeats for c in s)
               for b in p.arguments if (b,a) in p.defeats)


def _admissible(p, s):
    return (s<=set(p.arguments)
            and not any(a in s and b in s for a,b in p.defeats)
            and all(_defends(p,s,a) for a in s))


def _characteristic(p,s):
    return frozenset(a for a in p.arguments if _defends(p,s,a))


def checked_member(problem, candidate) -> bool:
    """Independent specification-side implementation; not the legacy evaluator."""
    if type(problem) is AffineIntegerProblem:
        return (type(candidate) is int and problem.lo<=candidate<=problem.hi
                and problem.a*candidate+problem.b>=problem.rhs)
    if type(problem) is not DungProblem or type(candidate) is not frozenset:
        return False
    p=problem; s=candidate
    if not s<=set(p.arguments): return False
    if p.profile=='stable':
        return (not any(a in s and b in s for a,b in p.defeats)
                and all(any((a,b) in p.defeats for a in s) for b in set(p.arguments)-s))
    if p.profile=='complete':
        return _admissible(p,s) and _characteristic(p,s)==s
    if p.profile=='preferred':
        return _admissible(p,s) and not any(s<t and _admissible(p,t) for t in candidate_domain(p))
    current=frozenset()
    for _ in range(len(p.arguments)+1):
        nxt=_characteristic(p,current)
        if nxt==current: return s==current
        current=nxt
    raise ValueError('Grounded fixed-point check incomplete')


@dataclass(frozen=True)
class PartitionCertificate:
    context: ContextKey
    problem: AffineIntegerProblem | DungProblem
    found: frozenset
    rejected: frozenset
    pending: frozenset
    complete: bool
    checker_id: str = 'closed-reference/2.1'


def solve(context, problem, budget=None):
    domain=candidate_domain(problem)
    if budget is None: budget=len(domain)
    if type(budget) is not int or budget<0: raise ValueError('Nonnegative search budget required')
    accepted=set(); rejected=set()
    # Solver uses the independently retained reference predicate; checker does not.
    from reference.unified_reference import dung_member
    for x in domain[:budget]:
        yes=(problem.a*x+problem.b>=problem.rhs if type(problem) is AffineIntegerProblem
             else dung_member(problem.profile,problem.arguments,problem.defeats,x))
        (accepted if yes else rejected).add(x)
    pending=frozenset(domain[budget:])
    return PartitionCertificate(context,problem,frozenset(accepted),frozenset(rejected),pending,not pending)


def check_partition(expected_context, expected_problem, cert) -> bool:
    if type(cert) is not PartitionCertificate or cert.checker_id!='closed-reference/2.1': return False
    if cert.context!=expected_context or cert.problem!=expected_problem or type(cert.complete) is not bool: return False
    if any(type(s) is not frozenset for s in (cert.found,cert.rejected,cert.pending)): return False
    domain=frozenset(candidate_domain(expected_problem))
    a,r,u=cert.found,cert.rejected,cert.pending
    if a&r or a&u or r&u or a|r|u!=domain or cert.complete!=(not u): return False
    return all(checked_member(expected_problem,x) for x in a) and all(not checked_member(expected_problem,x) for x in r)


def checked_query(expected_context, expected_problem, cert, claim_arguments):
    """No unsupported universal/negative conclusion from an incomplete family."""
    if not check_partition(expected_context,expected_problem,cert): raise ValueError('Rejected certificate')
    if type(expected_problem) is not DungProblem: raise ValueError('Extension query required')
    if not set(claim_arguments)<=set(expected_problem.arguments): raise ValueError('Unknown claim witnesses')
    yes=lambda e: bool(set(e)&set(claim_arguments))
    possible=any(yes(e) for e in cert.found)
    counterexample=any(not yes(e) for e in cert.found)
    return dict(exists=True if possible else (False if cert.complete else None),
                common=False if counterexample else (True if cert.complete and cert.found else None),
                family_status=('no_extensions' if cert.complete and not cert.found else
                               'complete_family' if cert.complete else 'incomplete_family'))


@dataclass(frozen=True)
class IntervalProblem:
    lower_bounds: tuple[Q,...]
    upper_bounds: tuple[Q,...]
    def __post_init__(self):
        if not self.lower_bounds or not self.upper_bounds: raise ValueError('Bounded real interval problem required')
        for n in ('lower_bounds','upper_bounds'):
            object.__setattr__(self,n,tuple(rational(x) for x in getattr(self,n)))

@dataclass(frozen=True)
class IntervalRep:
    lo: Q
    hi: Q
    def __post_init__(self):
        object.__setattr__(self,'lo',rational(self.lo));object.__setattr__(self,'hi',rational(self.hi))
        if self.lo>self.hi: raise ValueError('Use EmptyRep for empty set')

@dataclass(frozen=True)
class EmptyRep:
    pass

@dataclass(frozen=True)
class EnumRep:
    values: frozenset


def check_interval_exact(context, expected_context, problem, representation):
    require_same_context(context,expected_context)
    if type(problem) is not IntervalProblem: return False
    lo=max(problem.lower_bounds); hi=min(problem.upper_bounds)
    if lo>hi: return type(representation) is EmptyRep
    # Finite endpoints are NOT an exact representation of a nondegenerate real interval.
    return type(representation) is IntervalRep and representation.lo==lo and representation.hi==hi


@dataclass(frozen=True)
class Polyhedron:
    """Real set {x | A x <= b}; no implicit nonnegativity."""
    A: tuple[tuple[Q,...],...]
    b: tuple[Q,...]
    def __post_init__(self):
        if not self.A or len(self.A)!=len(self.b) or not self.A[0]: raise ValueError('Nonempty constraints required')
        if any(len(row)!=len(self.A[0]) for row in self.A): raise ValueError('Ragged matrix')
        object.__setattr__(self,'A',tuple(tuple(rational(x) for x in r) for r in self.A))
        object.__setattr__(self,'b',tuple(rational(x) for x in self.b))


def check_polyhedral_inclusion(source: Polyhedron, target: Polyhedron, multipliers):
    """Sufficient exact Farkas combinations. Rejection is not non-inclusion."""
    if len(source.A[0])!=len(target.A[0]) or len(multipliers)!=len(target.A): return False
    for row,bound,lambdas in zip(target.A,target.b,multipliers):
        if len(lambdas)!=len(source.A): return False
        ls=tuple(rational(v) for v in lambdas)
        if any(v<0 for v in ls): return False
        if any(sum((ls[i]*source.A[i][j] for i in range(len(ls))),Q(0))!=row[j] for j in range(len(row))): return False
        if sum((ls[i]*source.b[i] for i in range(len(ls))),Q(0))>bound: return False
    return True


def check_polyhedral_exact(problem, representation, forward, backward):
    return (check_polyhedral_inclusion(problem,representation,forward)
            and check_polyhedral_inclusion(representation,problem,backward))
