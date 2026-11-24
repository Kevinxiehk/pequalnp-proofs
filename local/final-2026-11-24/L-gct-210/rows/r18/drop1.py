# (SM4'') with ONE triple condition dropped: do solutions with f != 0 and 4 nonzero columns exist?  Report the dropped triple's value.
import numpy as np, itertools, sys
from scipy.optimize import least_squares
rng=np.random.default_rng(int(sys.argv[1])); NST=int(sys.argv[2])
def perm3(m): return sum(m[0,p[0]]*m[1,p[1]]*m[2,p[2]] for p in itertools.permutations(range(3)))
cz=rng.normal(size=(4,3))+1j*rng.normal(size=(4,3)); wf=rng.normal(size=3)+1j*rng.normal(size=3)
trip=list(itertools.combinations(range(4),3))
def res(x):
    z=x[:12]+1j*x[12:]; M=z.reshape(3,4); f=M.sum(1)
    r=[perm3(M[:,list(c)]) for c in trip[:3]]+[M[:,k]@(f-M[:,k]) for k in range(4)]+[wf@f-1]+[cz[k]@M[:,k]-1 for k in range(4)]
    r=np.array(r); return np.r_[r.real,r.imag]
for st in range(NST):
    sol=least_squares(res,rng.normal(size=24),xtol=1e-15,ftol=1e-15,gtol=1e-15,max_nfev=3000)
    nr=np.linalg.norm(res(sol.x)); z=sol.x[:12]+1j*sol.x[12:]; M=z.reshape(3,4); f=M.sum(1)
    print('start %d: res %.1e  dropped triple value %.3e  |f.f|/|f|^2 %.3f  min col norm %.3f'%(st,nr,abs(perm3(M[:,list(trip[3])])),abs(f@f)/np.vdot(f,f).real,min(np.linalg.norm(M[:,k]) for k in range(4))),flush=True)
