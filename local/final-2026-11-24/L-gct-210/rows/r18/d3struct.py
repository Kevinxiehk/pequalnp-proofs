# structure of 3x4 matrices with all four 3x3 subpermanents zero (no zero column): rank, zero rows, row/column patterns (numerical)
import numpy as np, itertools, sys
from scipy.optimize import least_squares
rng=np.random.default_rng(int(sys.argv[1])); NST=int(sys.argv[2]); D2='D2' in sys.argv
def perm3(m): return sum(m[0,p[0]]*m[1,p[1]]*m[2,p[2]] for p in itertools.permutations(range(3)))
cz=rng.normal(size=(4,3))+1j*rng.normal(size=(4,3)); wf=rng.normal(size=3)+1j*rng.normal(size=3)
def res(x):
    z=x[:12]+1j*x[12:]; M=z.reshape(3,4); r=[perm3(M[:,list(c)]) for c in itertools.combinations(range(4),3)]
    r+=[cz[k]@M[:,k]-1 for k in range(4)]
    if D2:
        f=M.sum(1); r+=[M[:,k]@(f-M[:,k]) for k in range(4)]+[wf@f-1]
    r=np.array(r); return np.r_[r.real,r.imag]
for st in range(NST):
    sol=least_squares(res,rng.normal(size=24),xtol=1e-15,ftol=1e-15,gtol=1e-15,max_nfev=3000)
    nr=np.linalg.norm(res(sol.x)); z=sol.x[:12]+1j*sol.x[12:]; M=z.reshape(3,4)
    sv=np.linalg.svd(M,compute_uv=False); rk=int((sv>1e-7*sv[0]).sum())
    zr=[int(np.linalg.norm(M[r])<1e-7) for r in range(3)]
    small=(np.abs(M)<1e-7).sum()
    print('start %d: res %.1e rank %d zero rows %s zero entries %d'%(st,nr,rk,zr,small),flush=True)
