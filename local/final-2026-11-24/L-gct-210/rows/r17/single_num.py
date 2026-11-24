# numerical: single strongly level 4x5 matrices with isotropic row sum f and columns (f - g_j)/2, g_j isotropic, sum g_j = 2f (4 columns)
import numpy as np, itertools, sys
from scipy.optimize import least_squares
H=np.array([[1,1,1],[1,-1,-1],[-1,1,-1],[-1,-1,1]],float)
rng=np.random.default_rng(int(sys.argv[1])); NST=int(sys.argv[2])
P4=np.array(list(itertools.permutations(range(4))))
cz=rng.normal(size=(4,3))+1j*rng.normal(size=(4,3)); w0=rng.normal(size=3)+1j*rng.normal(size=3)
def t3(a,b,c): return (a*b*c).sum()
def res(x):
    z=x[:15]+1j*x[15:]; f=z[0:3]; g=z[3:15].reshape(4,3)
    r=[f@f]+[g[j]@g[j] for j in range(4)]+list(g.sum(0)-2*f)+[w0@f-1]
    cols=[H@((f-g[j])/2) for j in range(4)]
    for (i,j,l) in itertools.combinations(range(4),3): r.append(t3(cols[i],cols[j],cols[l]))
    M=np.array(cols).T; r.append(np.prod(M[np.arange(4)[None,:],P4],axis=1).sum())
    for j in range(4): r.append(cz[j]@(f-g[j])-1)    # force columns nonzero
    r=np.array(r); return np.r_[r.real,r.imag]
ok=0
for st in range(NST):
    sol=least_squares(res,rng.normal(size=30),xtol=1e-15,ftol=1e-15,gtol=1e-15,max_nfev=4000)
    nr=np.linalg.norm(res(sol.x))
    if nr<1e-9:
        ok+=1; J=np.array([(res(sol.x+1e-7*e)-res(sol.x-1e-7*e))/2e-7 for e in np.eye(30)]).T
        print('start %d: SOLUTION residual %.1e, local dim %d'%(st,nr,(30-np.linalg.matrix_rank(J,1e-5))//2),flush=True)
    else: print('start %d: residual %.2e'%(st,nr),flush=True)
print('converged %d / %d'%(ok,NST))
