import numpy as np, itertools, time, sys
from scipy.optimize import least_squares
# Safety check of MIN-E (b): five 2-planes in C^4 (one column vanishes on M), scalar (Q4): the 4x4 permanent vanishes on
# P_a x P_b x P_c x P_d for all five 4-sets; every column nonzero. Theorem: three planes must equal one coordinate plane (NT fails).
DMIN=float(sys.argv[1]); TMAX=float(sys.argv[2])
P4=np.array(list(itertools.permutations(range(4))))
SETS=list(itertools.combinations(range(5),4))
RI=np.array([S for S in SETS for eps in itertools.product(range(2),repeat=4)])
RE=np.array([eps for S in SETS for eps in itertools.product(range(2),repeat=4)])
def planes(x): return (x[:40]+1j*x[40:]).reshape(5,2,4)
def res(x,w=3.0):
    A=planes(x); Mx=A[RI,RE,:]                                         # (80,4,4)
    r=sum(Mx[:,0,p[0]]*Mx[:,1,p[1]]*Mx[:,2,p[2]]*Mx[:,3,p[3]] for p in P4)
    G=np.einsum('iaj,ibj->iab',A,A.conj())-np.eye(2)[None]
    cn=np.sqrt((np.abs(A)**2).sum(axis=(0,1))); hinge=w*np.maximum(0,0.5-cn)
    out=[r.real,r.imag,G.real.ravel(),G.imag.ravel(),hinge]
    if DMIN>0:
        Pr=np.einsum('iaj,iak->ijk',A.conj(),A); d=np.array([np.linalg.norm(Pr[i]-Pr[k]) for i in range(5) for k in range(i)])
        out.append(w*np.maximum(0,DMIN-d))
    return np.concatenate(out)
rng=np.random.default_rng(31); t0=time.time(); nconv=0; best=[]; kinds={}
for s in range(1000):
    if time.time()-t0>TMAX: break
    sol=least_squares(res,rng.normal(size=80)*0.6,method='lm',max_nfev=1500); c=np.sqrt(2*sol.cost); best.append(c)
    if c<1e-8:
        nconv+=1; A=planes(sol.x)
        supp=[tuple((np.abs(A[i])>1e-5).any(axis=0).astype(int)) for i in range(5)]
        coord=[s_ for s_ in supp if sum(s_)==2]; nt=max([coord.count(c_) for c_ in set(coord)],default=0)
        kinds[nt]=kinds.get(nt,0)+1
print('DMIN %.1f: starts %d, zero-residual solutions (all columns >= 0.5): %d ; by max #equal coordinate planes: %s ; residual min/median %.1e / %.1e (%.0f s)'%(DMIN,s,nconv,dict(sorted(kinds.items())),min(best),np.median(best),time.time()-t0))
