# verify2 round 5: probe of "Lemma Z" (HANDOFF C4): a 5x5 complex matrix g with all row and column sums zero and all 25 4x4 minor
# permanents zero has a zero row or column.  LM search for a counterexample: all row and column norms >= delta (slack variables).
import numpy as np, itertools, sys, time
from scipy.optimize import least_squares
P4=np.array(list(itertools.permutations(range(4))))
MIN=[(np.array([r for r in range(5) if r!=i]),np.array([c for c in range(5) if c!=j])) for i in range(5) for j in range(5)]
def full(z):
    a=(z[:16]+1j*z[16:32]).reshape(4,4); g=np.zeros((5,5),complex); g[:4,:4]=a; g[:4,4]=-a.sum(1); g[4,:4]=-a.sum(0); g[4,4]=a.sum(); return g
def minors(g):
    out=np.empty(25,complex)
    for k,(r,c) in enumerate(MIN):
        A=g[np.ix_(r,c)]; out[k]=A[np.arange(4)[None,:],P4].prod(axis=1).sum()
    return out
def res(z,delta):
    g=full(z); m=minors(g); rn=(np.abs(g)**2).sum(1); cn=(np.abs(g)**2).sum(0)
    return np.concatenate([m.real,m.imag,[np.abs(g).max()**0*((np.abs(g)**2).sum()-5)],rn-delta-z[32:37]**2,cn-delta-z[37:42]**2])
seed=int(sys.argv[1]); tmax=float(sys.argv[2]); delta=float(sys.argv[3]); rng=np.random.default_rng(seed); t0=time.time(); n=0; hits=0; best=1e9
while time.time()-t0<tmax:
    n+=1; z0=np.concatenate([rng.normal(size=32)*0.5,rng.normal(size=10)])
    s=least_squares(res,z0,args=(delta,),method='lm',xtol=1e-15,ftol=1e-15,gtol=1e-15,max_nfev=500)
    r=np.linalg.norm(s.fun); best=min(best,r)
    if r<1e-10:
        g=full(s.x); hits+=1
        print('COUNTEREXAMPLE candidate: residual %.1e, rank %d, row norms %s, column norms %s'%(r,np.linalg.matrix_rank(g,tol=1e-8),np.round(np.linalg.norm(g,axis=1),3),np.round(np.linalg.norm(g,axis=0),3)),flush=True)
        np.save('/home/claude/work/L-gct-210/verify2/lemmaz_hit_%d_%d.npy'%(seed,n),g)
print('seed %d delta %.2f: %d starts, %d solutions with all row/column norms^2 >= delta, smallest residual %.2e'%(seed,delta,n,hits,best))
# control: without the norm constraints solutions must exist (e.g. a zero row)
def res0(z):
    g=full(z); m=minors(g); return np.concatenate([m.real,m.imag,[(np.abs(g)**2).sum()-5]])
c=0
for _ in range(10):
    s=least_squares(res0,rng.normal(size=32)*0.5,method='lm',xtol=1e-15,ftol=1e-15,gtol=1e-15,max_nfev=500)
    if np.linalg.norm(s.fun)<1e-10:
        g=full(s.x); c+=1; print('  control solution: rank %d, min row norm %.1e, min column norm %.1e'%(np.linalg.matrix_rank(g,tol=1e-8),np.linalg.norm(g,axis=1).min(),np.linalg.norm(g,axis=0).min()))
print('control (no norm constraints): %d of 10 starts converge'%c)
