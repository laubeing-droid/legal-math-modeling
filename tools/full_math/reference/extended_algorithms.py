"""Exact supplementary mathematical algorithms. No production or legal certification.

Algorithms operate on explicit finite models. They are executable counterparts
for proof construction, not a second JC kernel and not Lean completion evidence.
"""
from __future__ import annotations
from dataclasses import dataclass
from fractions import Fraction as Q
from itertools import combinations, product
from typing import Hashable, Iterable, Mapping, Sequence, Callable


class ModelError(ValueError):
    pass


def exact(x) -> Q:
    if isinstance(x, bool) or isinstance(x, float):
        raise ModelError('integer, decimal string or Fraction required; no float/bool')
    return Q(x)


def powerset(xs: Iterable[Hashable]):
    xs=tuple(xs)
    if len(set(xs)) != len(xs): raise ModelError('duplicate carrier member')
    for k in range(len(xs)+1):
        yield from (frozenset(s) for s in combinations(xs,k))


@dataclass(frozen=True)
class HornRule:
    identity: str
    premises: frozenset[str]
    conclusion: str


def horn_closure(atoms: frozenset[str], facts: frozenset[str], rules: Sequence[HornRule]):
    if not facts <= atoms or len({r.identity for r in rules}) != len(rules):
        raise ModelError('fact or rule identity')
    if any(not r.premises<=atoms or r.conclusion not in atoms for r in rules):
        raise ModelError('rule outside independent carrier')
    found=set(facts)
    while True:
        new=found|{r.conclusion for r in rules if r.premises<=found}
        if new==found:return frozenset(found)
        found=new


def antichain_minimal(sets):
    xs=set(map(frozenset,sets))
    return frozenset(a for a in xs if not any(b<a for b in xs))


def horn_supports(atoms: frozenset[str], fixed: frozenset[str],
                  assumptions: frozenset[str], rules: Sequence[HornRule]):
    """Least fixpoint of inclusion-minimal assumption supports (not probabilities)."""
    horn_closure(atoms,fixed,rules)
    if not assumptions<=atoms:raise ModelError('undeclared assumption')
    labels={a:set() for a in atoms}
    for a in fixed:labels[a].add(frozenset())
    for a in assumptions:labels[a].add(frozenset({a}))
    while True:
        before={a:frozenset(v) for a,v in labels.items()}
        for r in rules:
            slots=[labels[p] for p in sorted(r.premises)]
            for combo in product(*slots):
                labels[r.conclusion].add(frozenset().union(*combo))
            labels[r.conclusion]=set(antichain_minimal(labels[r.conclusion]))
        if all(frozenset(labels[a])==before[a] for a in atoms):
            return {a:antichain_minimal(v) for a,v in labels.items()}


def verify_supports(atoms,fixed,assumptions,rules,query,proposed):
    """Independent complete finite oracle; does not call horn_supports."""
    actual={s for s in powerset(sorted(assumptions))
            if query in horn_closure(atoms,fixed|s,rules)}
    expected={s for s in actual if not any(t<s for t in actual)}
    return frozenset(proposed)==frozenset(expected)


def event_probability(supports, joint_distribution: Mapping[frozenset[str],Q]) -> Q:
    masses={w:exact(p) for w,p in joint_distribution.items()}
    if any(p<0 for p in masses.values()) or sum(masses.values(),Q(0))!=1:
        raise ModelError('joint law is not normalized')
    return sum((p for w,p in masses.items() if any(s<=w for s in supports)),Q(0))


@dataclass(frozen=True)
class RelationBox:
    """Gamma is an explicit relation of joint tuples, NOT local embeddings."""
    gamma: frozenset[tuple]
    components: tuple[frozenset,...]
    def denotation(self):
        if any(len(w)!=len(self.components) for w in self.gamma):
            raise ModelError('joint-space arity')
        return frozenset(w for w in self.gamma
                         if all(w[i] in a for i,a in enumerate(self.components)))
    def reduce(self):
        s=self.denotation()
        return RelationBox(self.gamma,tuple(a & {w[i] for w in s}
                              for i,a in enumerate(self.components)))


def verify_reduction(old:RelationBox,new:RelationBox):
    return (old.gamma==new.gamma and len(old.components)==len(new.components)
        and all(b<=a for a,b in zip(old.components,new.components))
        and old.denotation()==new.denotation())


def conformal_cutoff(scores:Sequence[Q],alpha:Q):
    """None means +infinity, including the n+1 order statistic. No coverage claim here."""
    alpha=exact(alpha);s=tuple(map(exact,scores));n=len(s)
    if not 0<alpha<1:raise ModelError('0 < alpha < 1 required')
    v=(n+1)*(1-alpha);k=-(-v.numerator//v.denominator)
    return None if k>n else sorted(s)[k-1]


def conformal_set(scores:Sequence[Q],alpha:Q,label_scores:Mapping[Hashable,Q]):
    q=conformal_cutoff(scores,alpha)
    return frozenset(y for y,s in label_scores.items() if q is None or exact(s)<=q)


def union_coverage_lower(delta:Iterable[Q]):
    ds=tuple(map(exact,delta))
    if any(not 0<=d<=1 for d in ds):raise ModelError('bad failure budget')
    return max(Q(0),1-sum(ds,Q(0)))


def betting_path(losses:Sequence[Q],threshold:Q,bets:Sequence[Q]):
    """Numerical path only. The supermartingale property needs conditional-risk assumptions."""
    r=exact(threshold)
    if not 0<r<1 or len(losses)!=len(bets):raise ModelError('risk/bet shape')
    wealth=Q(1);out=[wealth]
    for l,b in zip(losses,bets):
        l,b=exact(l),exact(b)
        if not 0<=l<=1 or not 0<=b<=1/r:raise ModelError('admissible betting interval')
        wealth*=1+b*(l-r);out.append(wealth)
    return tuple(out)


def pav(values:Sequence[Q],weights:Sequence[Q]):
    y=tuple(map(exact,values));w=tuple(map(exact,weights))
    if not y or len(y)!=len(w) or any(t<=0 for t in w):raise ModelError('PAV domain')
    blocks=[]
    for i,(v,t) in enumerate(zip(y,w)):
        blocks.append([i,i+1,t,t*v])
        while len(blocks)>1 and blocks[-2][3]/blocks[-2][2]>blocks[-1][3]/blocks[-1][2]:
            b=blocks.pop();a=blocks.pop();blocks.append([a[0],b[1],a[2]+b[2],a[3]+b[3]])
    out=[Q(0)]*len(y)
    for a,b,t,z in blocks:out[a:b]=[z/t]*(b-a)
    return tuple(out)


def verify_pav(values,weights,result):
    """Independent exact KKT certificate from cumulative gradients; no PAV call."""
    y=tuple(map(exact,values));w=tuple(map(exact,weights));x=tuple(map(exact,result));n=len(y)
    if not n or len(w)!=n or len(x)!=n or any(t<=0 for t in w):return False
    if any(x[i]>x[i+1] for i in range(n-1)):return False
    # g_i + lambda_i - lambda_(i-1)=0; lambda_i=-sum_(j<=i) g_j.
    cumulative=Q(0)
    for i in range(n):
        cumulative+=2*w[i]*(x[i]-y[i])
        lam=-cumulative
        if i<n-1 and (lam<0 or lam*(x[i]-x[i+1])!=0):return False
    return cumulative==0


@dataclass(frozen=True)
class FiniteMDP:
    states: tuple[str,...]
    actions: Mapping[str,tuple[str,...]]
    transitions: Mapping[tuple[str,str],tuple[tuple[str,Q],...]]
    rewards: Mapping[tuple[str,str],Q]
    terminal: Mapping[str,Q]
    def validate(self):
        if not self.states or len(set(self.states))!=len(self.states):raise ModelError('state carrier')
        if set(self.actions)!=set(self.states) or set(self.terminal)!=set(self.states):raise ModelError('state coverage')
        expected=set()
        for s in self.states:
            aa=self.actions[s]
            if not aa or len(set(aa))!=len(aa):raise ModelError('empty/duplicate legal actions; model terminal action explicitly')
            for a in aa:
                expected.add((s,a));row=self.transitions.get((s,a),())
                if len({t for t,p in row})!=len(row) or any(t not in self.states or exact(p)<0 for t,p in row):raise ModelError('transition row')
                if sum((exact(p) for _,p in row),Q(0))!=1:raise ModelError('transition normalization')
        if set(self.rewards)!=expected or set(self.transitions)!=expected:raise ModelError('action coverage')


def finite_horizon(m:FiniteMDP,horizon:int):
    m.validate()
    if type(horizon) is not int or horizon<0:raise ModelError('horizon')
    values=[{s:exact(m.terminal[s]) for s in m.states}];policies=[]
    for _ in range(horizon):
        prev=values[-1];v={};pi={}
        for s in m.states:
            scores={a:exact(m.rewards[s,a])+sum((exact(p)*prev[t] for t,p in m.transitions[s,a]),Q(0)) for a in m.actions[s]}
            best=max(scores.values());pi[s]=next(a for a in m.actions[s] if scores[a]==best);v[s]=best
        policies.append(pi);values.append(v)
    return values,policies


def verify_bellman(m:FiniteMDP,values,policies):
    try:m.validate()
    except ModelError:return False
    if not values or len(values)!=len(policies)+1 or values[0]!={s:exact(m.terminal[s]) for s in m.states}:return False
    for t,pi in enumerate(policies):
        if set(pi)!=set(m.states) or set(values[t+1])!=set(m.states):return False
        for s in m.states:
            if pi[s] not in m.actions[s]:return False
            for a in m.actions[s]:
                q=exact(m.rewards[s,a])+sum((exact(p)*values[t][z] for z,p in m.transitions[s,a]),Q(0))
                if values[t+1][s]<q:return False
                if a==pi[s] and values[t+1][s]!=q:return False
    return True


def persistent_model_value(policy_payoffs:Mapping[str,Mapping[str,Q]],model_ids:Sequence[str]):
    """Whole-policy worst case under one shared model, not stagewise re-selection."""
    if not model_ids or not policy_payoffs:raise ModelError('empty model or policy space')
    keys=set(model_ids)
    if len(keys)!=len(model_ids) or any(set(v)!=keys for v in policy_payoffs.values()):raise ModelError('shared-model coverage')
    vv={p:min(exact(v[m]) for m in model_ids) for p,v in policy_payoffs.items()}
    opt=max(vv.values());return opt,tuple(p for p in vv if vv[p]==opt)


@dataclass(frozen=True)
class BinarySCM:
    """Declared deterministic structural tables over a finite exogenous law."""
    identity: str
    u_probs: tuple[Q,...]
    x_of_u: tuple[bool,...]
    y_of_xu: tuple[tuple[bool,bool],...]
    def validate(self):
        n=len(self.u_probs)
        if not n or len(self.x_of_u)!=n or len(self.y_of_xu)!=n:raise ModelError('SCM shape')
        if any(exact(p)<0 for p in self.u_probs) or sum(map(exact,self.u_probs),Q(0))!=1:raise ModelError('SCM exogenous law')
        if any(type(x) is not bool for x in self.x_of_u) or any(len(y)!=2 or any(type(z) is not bool for z in y) for y in self.y_of_xu):raise ModelError('SCM variable domain')
    def observations(self):
        self.validate();d={(x,y):Q(0) for x,y in product((False,True),repeat=2)}
        for p,x,y in zip(self.u_probs,self.x_of_u,self.y_of_xu):d[x,y[int(x)]]+=exact(p)
        return d
    def ate(self):
        self.validate();return sum((exact(p)*(int(y[1])-int(y[0])) for p,y in zip(self.u_probs,self.y_of_xu)),Q(0))


def identify_finite(models:Sequence[BinarySCM],observed:Mapping[tuple[bool,bool],Q]):
    if len({m.identity for m in models})!=len(models):raise ModelError('SCM model identity')
    if set(observed)!=set(product((False,True),repeat=2)) or any(exact(x)<0 for x in observed.values()) or sum(map(exact,observed.values()),Q(0))!=1:raise ModelError('observed joint law')
    witnesses=tuple((m.identity,m.ate()) for m in models if m.observations()==observed)
    if not witnesses:return {'status':'INCOMPATIBLE_DECLARED_MODEL_CLASS','witnesses':(), 'values':frozenset()}
    values=frozenset(x[1] for x in witnesses)
    return {'status':'EXACT_FINITE_MODEL_CLASS','witnesses':witnesses,'values':values,'inf':min(values),'sup':max(values),'lower_attained':True,'upper_attained':True}


def finite_regret(payoffs:Mapping[tuple,tuple],profile:tuple,actions:Sequence[Sequence]):
    carrier=set(product(*actions))
    if set(payoffs)!=carrier or profile not in carrier:raise ModelError('game carrier')
    n=len(actions)
    if any(len(v)!=n for v in payoffs.values()):raise ModelError('utility dimensions')
    out=[]
    for i,aa in enumerate(actions):
        base=exact(payoffs[profile][i]);best=Q(0)
        for a in aa:
            p=list(profile);p[i]=a
            best=max(best,exact(payoffs[tuple(p)][i])-base)
        out.append(best)
    return tuple(out)


def verify_dsic(types:Sequence[Sequence],utilities:Mapping[tuple,tuple]):
    """utilities[(true_profile, report_profile)] gives realized utility vector."""
    profiles=tuple(product(*types));expected=set(product(profiles,profiles))
    if not profiles or set(utilities)!=expected:raise ModelError('full type/report coverage required')
    n=len(types)
    if any(len(u)!=n for u in utilities.values()):raise ModelError('utility shape')
    for theta in profiles:
        for reports in profiles:
            for i in range(n):
                truthful=list(reports);truthful[i]=theta[i]
                if exact(utilities[theta,tuple(truthful)][i])<exact(utilities[theta,reports][i]):return False
    return True
