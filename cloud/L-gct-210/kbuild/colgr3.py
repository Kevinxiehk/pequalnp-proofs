"""column-graded (Z5-translation invariant) 3-row level spaces: S = sum_k R_k (x) chi_k, R_k subset C^3. LM over the R_k."""
import sys; sys.path.insert(0,'.')
import numpy as np, itertools
from fast import Pall
from core import chi
from scipy.optimize import least_squares
def run(typ,seed):
    rng=np.random.default_rng(seed); d=sum(typ); e=3*d
    npts=4*d+15; A=rng.normal(size=(npts,d))+1j*rng.normal(size=(npts,d))
    cols=[k for k in range(5) for _ in range(typ[k])]
    CH=np.array([chi(k) for k in cols])  # d x 5
    def res(z):
        R=(z[:e]+1j*z[e:]).reshape(d,3)
        B=np.zeros((d,5,5),complex); B[:,:3,:]=R[:,:,None]*CH[:,None,:]
        T=np.einsum('pi,iab->pab',A,B); o=Pall(T)[:,1:4].ravel()
        # normalization: each R row unit norm; within same k, orthonormal
        G=[]
        for k in range(5):
            idx=[i for i in range(d) if cols[i]==k]
            if idx: Rk=R[idx]; G.append((Rk.conj()@Rk.T-np.eye(len(idx))).ravel())
        o=np.concatenate([o]+G); return np.concatenate([o.real,o.imag])
    r=least_squares(res,rng.normal(size=2*e),method='lm',max_nfev=2000,xtol=1e-15,ftol=1e-15)
    return np.linalg.norm(res(r.x))
D=int(sys.argv[1]); seeds=int(sys.argv[2])
types=[t for t in itertools.product(range(4),repeat=5) if sum(t)==D]
# reduce by symmetry: k -> m*k (m in 1..4) acting on indices 1..4
def canon(t):
    return min(tuple(t[(m*k)%5] for k in range(5)) for m in range(1,5))
types=sorted(set(canon(t) for t in types))
print(len(types),'types up to multipliers',flush=True)
for t in types:
    best=min(run(t,s) for s in range(seeds))
    print('type',t,'best res %.1e'%best,flush=True)
print('done')
