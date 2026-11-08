
import numpy as np, json
rng = np.random.default_rng(20261109)
out = {}

def F(z):
    x,t = z
    p = x/4.0 + t/2.0 + 1/8.0
    return np.array([p, t/4.0 + p/2.0 + 1/8.0])

# (a) exact deterministic mean recursion and geometric bound
z0 = np.array([0.9,0.1]); zs=[z0]; z=z0.copy()
for n in range(60):
    z=F(z); zs.append(z.copy())
zs=np.array(zs)
bound = (0.75**np.arange(len(zs))) * max(abs(z0[0]-0.5),abs(z0[1]-0.5))
dev = np.maximum(abs(zs[:,0]-0.5),abs(zs[:,1]-0.5))
out["exact_mean_recursion"] = {
  "max_violation_dev_le_bound": float(np.max(dev-bound)),
  "ratio_at_n_5_10_20_40": [float(dev[n]/bound[n]) for n in [5,10,20,40]],
  "fixed_point_residual": float(np.max(abs(F(np.array([0.5,0.5]))-np.array([0.5,0.5]))))
}

# (b) weighted metric one-step expectation inequality: E[d_*'] <= 0.75 d_*
P=300000
z1=rng.random((P,2)); z2=rng.random((P,2))
p1=z1[:,0]/4+z1[:,1]/2+1/8; p2=z2[:,0]/4+z2[:,1]/2+1/8
Dstar=np.abs(z1[:,0]-z2[:,0])+4*np.abs(z1[:,1]-z2[:,1])
# Enumerate all four cells of the common-uniform coupling.
a00=1-np.maximum(p1,p2); a11=np.minimum(p1,p2)
a01=np.maximum(p2-p1,0); a10=np.maximum(p1-p2,0)
dt=z1[:,1]-z2[:,1]
Edn=(a00+a11)*np.abs(dt) + a01*(1+np.abs(dt-2)) + a10*(1+np.abs(dt+2))
triangle_upper=np.abs(dt)+3*np.abs(p1-p2)
assert np.all(Edn <= triangle_upper+1e-12)
assert np.all(Edn <= 0.75*Dstar+1e-12)
mask=Dstar>1e-12
ratio=Edn[mask]/Dstar[mask]
out["weighted_metric_coupling"] = {
  "max_ratio":float(np.max(ratio)), "mean_ratio":float(np.mean(ratio)),
  "violations_gt_0.75":int(np.sum(ratio>0.75+1e-12)),
  "metric":"d*(z,z')=|dx|+4|dtheta|",
  "meaning":"exact four-cell cost of one valid joint coupling",
  "old_triangle_mean_ratio":float(np.mean(triangle_upper[mask]/Dstar[mask]))}

# (c) naive sup-metric pathwise counterexample
eps=0.01; z=(0.5,0.5); zz=(0.5+eps,0.5)
p=0.5; pp=p+eps/4
U=pp+ (p-pp)/2   # between pp and p
y1=1.0 if U<p else 0.0; y2=1.0 if U<pp else 0.0
t1=z[1]/4+y1/2+1/8; t2=zz[1]/4+y2/2+1/8
out["sup_metric_pathwise_counterexample"]={
  "z":list(z),"z_prime":list(zz),"U":float(U),
  "dx_new":abs(y1-y2),"dtheta_new":abs(t1-t2),
  "D_sup":max(eps,0.0),"ratio":max(abs(y1-y2),abs(t1-t2))/eps,
  "note":"pathwise sup bound fails; use expectation and weighted L1"
}

# (d) distribution: P(x=1) range, theta variance, convergence of laws
N,T=6000,120
x=np.full(N,0.9); t=np.full(N,0.1)
snap=[]
for n in range(T+1):
    if n in [5,10,20,40,80,120]:
        snap.append((n,np.mean(x==1.0),np.mean(t),np.var(t)))
    p=np.clip(x/4+t/2+1/8,0,1); y=(rng.random(N)<p).astype(float)
    x,t=y,t/4+y/2+1/8
out["snapshots"] = [{"n":int(a),"P_x1":float(b),"theta_mean":float(c),"theta_var":float(d)} for a,b,c,d in snap]
# long run
N2,T2=20000,1500
x2=rng.random(N2)*0.2+0.4; t2=rng.random(N2)*0.2+0.4
for n in range(T2):
    p=np.clip(x2/4+t2/2+1/8,0,1); y=(rng.random(N2)<p).astype(float)
    x2,t2=y,t2/4+y/2+1/8
out["long_run"]={"P_x1":float(np.mean(x2==1)),"theta_mean":float(np.mean(t2)),
  "theta_var":float(np.var(t2)),"theta_q05":float(np.quantile(t2,.05)),
  "theta_q95":float(np.quantile(t2,.95)),"P_x1_theory":0.5}

# (e) Lower bound from two marginal optima; a true upper bound must use
# one joint pairing. Sorting by theta and retaining each paired x does that.
def ensemble(n_steps,m=8000):
    x=np.full(m,0.7); t=np.full(m,0.3)
    for _ in range(n_steps):
        p=np.clip(x/4+t/2+1/8,0,1); y=(rng.random(m)<p).astype(float)
        x,t=y,t/4+y/2+1/8
    return x,t

def law_gap(xa,ta,xb,tb):
    marginal_x=abs(np.mean(xa==1)-np.mean(xb==1))
    ia=np.argsort(ta); ib=np.argsort(tb)
    marginal_t=np.mean(np.abs(ta[ia]-tb[ib]))
    joint_upper=np.mean(np.abs(xa[ia]-xb[ib])+4*np.abs(ta[ia]-tb[ib]))
    lower=marginal_x+4*marginal_t
    assert lower <= joint_upper+1e-12
    return dict(marginal_x_W1=float(marginal_x),marginal_theta_W1=float(marginal_t),
        joint_W1_lower=float(lower),joint_W1_upper=float(joint_upper),
        upper_coupling="sort theta; retain each complete (x,theta) pair")
xa,ta=ensemble(20);xb,tb=ensemble(60)
out["law_gap_20_vs_60"]=law_gap(xa,ta,xb,tb)
xc,tc=ensemble(60);xd,td=ensemble(100)
out["law_gap_60_vs_100"]=law_gap(xc,tc,xd,td)

# (f) Beta posterior mean (analytic + Monte Carlo)
q=0.37
for yv in [0,1]:
    a,bb=q+yv, (1-q)+(1-yv)
    samples=rng.beta(a,bb,size=2000000)
    out.setdefault("beta_posterior_mean",{})[f"y={yv}"]={
      "analytic_beta_mean":float(a/(a+bb)),
      "target_(q+y)/2":float((q+yv)/2),
      "monte_carlo_mean":float(samples.mean())}
# (g) nonlinear update: mean map not equal to deterministic composite
th=0.3; yvals=np.array([-1.0,1.0]); probs=np.array([0.5,0.5])
E_update=np.sum(probs*(th/4 + yvals**2))   # U(theta,y)=theta/4+y^2
deterministic=th/4 + (np.sum(probs*yvals))**2
out["mean_vs_nonlinear_update"]={"E[U]":float(E_update),"U(E[Y])":float(deterministic),
  "gap":float(E_update-deterministic)}
out["stationary_theta_variance_exact"]=17/193
# Same marginals do not control joint W1 from above.
out["joint_vs_marginals_counterexample"]={"marginal_cost_sum":0,"joint_W1":1}
# A genuinely calibrated predictor can reverse action ranking.
from fractions import Fraction as R
rows=[(0,R(2,5),R(3,10),R(2,3)),(1,R(2,5),R(1,5),R(0)),
      (0,R(3,5),R(1,5),R(1)),(1,R(3,5),R(3,10),R(1,3))]
for q in (R(2,5),R(3,5)):
    assert sum(m*y for a,p,m,y in rows if p==q)/sum(m for a,p,m,y in rows if p==q)==q
values=[]
for a in (0,1):
    mass=sum(m for b,p,m,y in rows if b==a)
    values.append(dict(action=a,actual=str(sum(m*y for b,p,m,y in rows if b==a)/mass),
        predicted=str(sum(m*p for b,p,m,y in rows if b==a)/mass)))
out["calibrated_action_reversal"]=values
print(json.dumps(out,ensure_ascii=False,indent=1))
