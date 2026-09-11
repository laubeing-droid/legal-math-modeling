"""An exact finite-hyperprior Bayesian win model + held-out isotonic calibration.

`win` is a declared event (party, issue, remedy, procedural stage and horizon),
not a universal success label. Training uses actual supplied labels. Synthetic
fixtures are permanently labelled non-empirical. No prior is law-prescribed.
"""
from __future__ import annotations
from dataclasses import dataclass
from fractions import Fraction as Q
from collections import defaultdict
from datetime import datetime
from math import log
from reference.core import rational, probability, rising

@dataclass(frozen=True)
class Row:
    identity: str
    cluster: str
    objective: str
    group: str
    split: str
    cutoff: str
    feature_latest: str
    outcome_time: str
    label: int
    source: str
    synthetic: bool = False

    def __post_init__(self):
        if self.split not in {'train','calibration','test'} or type(self.label) is not int or self.label not in (0,1):
            raise ValueError('Invalid split or outcome label')
        if not all(type(v) is str and v for v in (self.identity,self.cluster,self.objective,self.group,self.source)) or type(self.synthetic) is not bool:
            raise ValueError('Dataset identity and provenance required')
        times=[datetime.fromisoformat(x) for x in (self.feature_latest,self.cutoff,self.outcome_time)]
        if not times[0] <= times[1] < times[2]:
            raise ValueError('POST_OUTCOME_FEATURE_OR_INVALID_CUTOFF')


def validate_splits(rows):
    if not rows or len({r.identity for r in rows})!=len(rows):
        raise ValueError('Empty data or duplicate identity')
    if len({r.objective for r in rows})!=1:
        raise ValueError('Different definitions of win cannot be pooled')
    owner={}
    parts={s:[] for s in ('train','calibration','test')}
    for r in rows:
        if r.cluster in owner:
            raise ValueError('One forecast per objective and litigation cluster; duplicates or cross-split leakage')
        owner[r.cluster]=r.split
        parts[r.split].append(r)
    if any(not p for p in parts.values()):
        raise ValueError('All three time-held-out partitions are required')
    # Training labels must be available before calibration/test forecasting.
    for a,b in (('train','calibration'),('calibration','test')):
        if max(datetime.fromisoformat(r.outcome_time) for r in parts[a]) >= min(datetime.fromisoformat(r.cutoff) for r in parts[b]):
            raise ValueError('Temporal leakage or overlapping label availability')
    return parts

@dataclass(frozen=True)
class Hyper:
    mu: Q
    strength: Q
    prior: Q

    def __post_init__(self):
        if not 0 < self.mu < 1 or self.strength <= 0 or self.prior <= 0:
            raise ValueError('Positive finite hyperprior required')

@dataclass(frozen=True)
class WinModel:
    objective: str
    counts: tuple[tuple[str,int,int],...]
    posterior: tuple[tuple[Q,Q,Q],...] # mu, strength, normalized weight
    synthetic: bool

    def predict(self, group: str):
        w,l=next(((w,l) for g,w,l in self.counts if g==group),(0,0))
        return sum((weight*(k*mu+w)/(k+w+l) for mu,k,weight in self.posterior),Q(0))


def fit(rows, hyper=None):
    if not rows or any(r.split!='train' for r in rows):
        raise ValueError('Fit accepts training partition only')
    if len({r.objective for r in rows})!=1:
        raise ValueError('Mixed objectives')
    if len({r.identity for r in rows})!=len(rows) or len({r.cluster for r in rows})!=len(rows):
        raise ValueError('Repeated observation within training cluster')
    if hyper is None:
        hyper=tuple(Hyper(mu,k,Q(1,9)) for mu in (Q(1,4),Q(1,2),Q(3,4)) for k in (Q(4),Q(8),Q(32)))
    if sum((h.prior for h in hyper),Q(0))!=1:
        raise ValueError('Hyperprior must sum to one')
    counts=defaultdict(lambda:[0,0])
    for r in rows:
        counts[r.group][0 if r.label else 1]+=1
    weights=[]
    for h in hyper:
        weight=h.prior
        for w,l in counts.values():
            # Integrated likelihood for labelled Bernoulli observations;
            # combinatorial factors cancel between hyperparameter hypotheses.
            weight*=rising(h.strength*h.mu,w)*rising(h.strength*(1-h.mu),l)/rising(h.strength,w+l)
        weights.append(weight)
    z=sum(weights,Q(0))
    return WinModel(rows[0].objective,tuple(sorted((g,w,l) for g,(w,l) in counts.items())),
                    tuple((h.mu,h.strength,w/z) for h,w in zip(hyper,weights)),
                    any(r.synthetic for r in rows))

@dataclass(frozen=True)
class Calibrator:
    blocks: tuple[tuple[Q,Q,Q],...] # smallest score, largest score, observed block mean
    synthetic: bool

    def predict(self, p):
        p=probability(p)
        for lo,hi,val in self.blocks:
            if p<=hi:
                return val
        return self.blocks[-1][2]


def calibrate(model, rows):
    if not rows or any(r.split!='calibration' or r.objective!=model.objective for r in rows):
        raise ValueError('Separate same-objective calibration rows required')
    tied=defaultdict(lambda:[0,0])
    for r in rows:
        p=model.predict(r.group)
        tied[p][0]+=r.label; tied[p][1]+=1
    blocks=[]
    for p,(wins,n) in sorted(tied.items()):
        blocks.append([p,p,wins,n])
        while len(blocks)>1 and Q(blocks[-2][2],blocks[-2][3])>Q(blocks[-1][2],blocks[-1][3]):
            b=blocks.pop(); a=blocks.pop()
            blocks.append([a[0],b[1],a[2]+b[2],a[3]+b[3]])
    return Calibrator(tuple((a,b,Q(w,n)) for a,b,w,n in blocks),any(r.synthetic for r in rows))


def evaluate(model,calibrator,rows):
    if not rows or any(r.split!='test' or r.objective!=model.objective for r in rows):
        raise ValueError('Held-out test rows required')
    preds=[calibrator.predict(model.predict(r.group)) for r in rows]
    raw=[model.predict(r.group) for r in rows]
    scores=lambda ps: sum(((p-r.label)**2 for p,r in zip(ps,rows)),Q(0))/len(rows)
    eps=1e-12
    nll=-sum(r.label*log(max(eps,float(p)))+(1-r.label)*log(max(eps,1-float(p))) for p,r in zip(preds,rows))/len(rows)
    return {'n':len(rows),'brier_raw':str(scores(raw)),'brier_calibrated':str(scores(preds)),
            'log_loss_clipped':nll,'log_loss_clip':eps,
            'empirical_status':'SYNTHETIC_NOT_VALIDATED' if model.synthetic or calibrator.synthetic or any(r.synthetic for r in rows) else 'HELDOUT_MEASURED_NOT_AUTOMATICALLY_APPROVED',
            'predictions':[str(p) for p in preds]}


def train_evaluate(rows):
    parts=validate_splits(rows)
    model=fit(parts['train'])
    cal=calibrate(model,parts['calibration'])
    return model,cal,evaluate(model,cal,parts['test'])


def latent_rate_interval(model: WinModel, group: str, tail=Q(1,20), steps=24):
    """Exact outward credible bounds for the RAW latent Bernoulli rate.

    If all posterior Beta shapes are integers, its CDF is evaluated as an exact
    binomial polynomial and quantiles are enclosed by rational bisection. This
    is model-relative posterior mass, NOT frequentist case-level accuracy,
    NOT an interval for the binary next outcome, and NOT a calibrated-rate CI.
    General noninteger Beta shapes use a conservative Chebyshev bound.
    """
    from math import comb,isqrt
    tail=probability(tail)
    if not 0<tail<1 or type(steps) is not int or not 1<=steps<=64:
        raise ValueError('Invalid tail or bisection budget')
    w,l=next(((w,l) for g,w,l in model.counts if g==group),(0,0))
    components=[(k*mu+w,k*(1-mu)+l,p) for mu,k,p in model.posterior]
    mean=model.predict(group)
    second=sum((p*a*(a+1)/((a+b)*(a+b+1)) for a,b,p in components),Q(0))
    variance=second-mean*mean
    if all(a.denominator==b.denominator==1 for a,b,p in components):
        def cdf(x):
            ans=Q(0)
            for a,b,p in components:
                a,b=int(a),int(b); n=a+b-1
                ans+=p*sum((Q(comb(n,j))*x**j*(1-x)**(n-j) for j in range(a,n+1)),Q(0))
            return ans
        def bracket(q):
            lo,hi=Q(0),Q(1)
            for _ in range(steps):
                m=(lo+hi)/2
                if cdf(m)<q:lo=m
                else:hi=m
            return lo,hi
        lo=bracket(tail/2)[0];hi=bracket(1-tail/2)[1]
        assert cdf(lo)<=tail/2 and 1-cdf(hi)<=tail/2
        return {'lo':lo,'hi':hi,'mass_at_least':1-tail,'method':'exact_beta_mixture_outward_bisection',
                'target':'raw_latent_rate_given_model_and_data','posterior_variance':variance}
    v=variance/tail;den=10**6
    num=isqrt(v.numerator*den*den//v.denominator)
    if Q(num*num,den*den)<v:num+=1
    r=Q(num,den)
    return {'lo':max(Q(0),mean-r),'hi':min(Q(1),mean+r),'mass_at_least':1-tail,
            'method':'posterior_chebyshev_outward_sqrt','target':'raw_latent_rate_given_model_and_data',
            'posterior_variance':variance}
