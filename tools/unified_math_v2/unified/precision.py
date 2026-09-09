"""Source-bound units, finite optimization, and a real contraction submodel."""
from dataclasses import dataclass
from fractions import Fraction as Q
from .contract import Envelope
from reference.core import rational

@dataclass(frozen=True)
class Quantity:
    value: Q
    dimension: str
    basis: str
    source: str
    def __post_init__(self):
        object.__setattr__(self,'value',rational(self.value))
        if not self.dimension or not self.basis or not self.source:
            raise ValueError('Dimension, policy basis and source required')
    def __add__(self, other):
        if (self.dimension,self.basis)!=(other.dimension,other.basis):
            raise ValueError('Cannot add different dimensions or legal calculation bases')
        return Quantity(self.value+other.value,self.dimension,self.basis,self.source+';'+other.source)


def optimize_finite(candidates, legal, cost, budget=None):
    from reference.unified_reference import scan
    result=scan(candidates,legal,budget)
    vals=tuple((cost(x),x) for x in result.found)
    if not vals:
        return {'status':'empty' if result.complete else 'incomplete','value':None,'choices':frozenset(),'classification':result}
    best=min(v for v,x in vals)
    return {'status':'optimal_on_declared_carrier' if result.complete else 'incumbent_only',
            'value':best,'choices':frozenset(x for v,x in vals if v==best),'classification':result}

@dataclass(frozen=True)
class QuadraticContraction:
    """f(x)=clip((1-step*a)x-step*b,[lo,hi]), for a>0, 0<step*a<2.

    Solves a declared strongly convex quadratic subproblem. Not a theorem that
    judicial discretion itself is contractive or that its objective is just.
    """
    a: Q
    b: Q
    step: Q
    lo: Q
    hi: Q
    source: str
    def __post_init__(self):
        for key in ('a','b','step','lo','hi'):
            object.__setattr__(self,key,rational(getattr(self,key)))
        if not self.source or self.a<=0 or self.lo>self.hi or not 0<self.step*self.a<2:
            raise ValueError('No contraction certificate for this parameter scope')
    @property
    def k(self):
        return abs(1-self.step*self.a)
    def clip(self,x):
        return max(self.lo,min(self.hi,x))
    def f(self,x):
        return self.clip((1-self.step*self.a)*x-self.step*self.b)
    def optimum(self):
        return self.clip(-self.b/self.a)
    def objective(self,x):
        return self.a*x*x/2+self.b*x
    def iterate(self,x,n):
        if type(n) is not int or n<0:
            raise ValueError('Iteration count must be nonnegative')
        x=self.clip(rational(x))
        for _ in range(n):
            x=self.f(x)
        radius=abs(x-self.f(x))/(1-self.k)
        return x,Envelope(max(self.lo,x-radius),min(self.hi,x+radius))


def verify_min_lp_optimum(A,b,c,x,dual):
    """Exact certificate: min c.x, A.x>=b, x>=0; dual max b.y, A.T.y<=c,y>=0.

    The retained legacy checker uses MAX with <=. Negating A,b,c converts the
    convention explicitly; the dual variable keeps the same nonnegative sign.
    """
    from reference.core import verify_lp_optimum,rational
    A=tuple(tuple(rational(v) for v in row) for row in A)
    b=tuple(rational(v) for v in b);c=tuple(rational(v) for v in c)
    return verify_lp_optimum(tuple(tuple(-v for v in row) for row in A),
                             tuple(-v for v in b),tuple(-v for v in c),x,dual)


def verify_ldl_psd(H,L,D):
    """Check an exact rational unit-lower LDL^T positive-semidefinite witness.

    It certifies this matrix only. It neither proves that arbitrary constraints
    are convex nor that a legal discretion problem should use this Hessian.
    """
    from reference.core import rational
    n=len(D)
    if not n or len(H)!=n or len(L)!=n or any(len(r)!=n for r in H) or any(len(r)!=n for r in L):
        raise ValueError('LDL dimensions')
    H=tuple(tuple(rational(x) for x in r) for r in H)
    L=tuple(tuple(rational(x) for x in r) for r in L);D=tuple(rational(x) for x in D)
    if any(d<0 for d in D):return False
    if any(L[i][i]!=1 for i in range(n)) or any(L[i][j]!=0 for i in range(n) for j in range(i+1,n)):return False
    return all(H[i][j]==sum((L[i][k]*D[k]*L[j][k] for k in range(n)),Q(0))
               for i in range(n) for j in range(n))
