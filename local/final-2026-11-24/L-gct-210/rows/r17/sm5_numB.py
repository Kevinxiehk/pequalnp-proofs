# (SM5) numerical census: single strongly level 4x5 matrices (column-centred) with ISOTROPIC nonzero row sum and all 5 columns nonzero.
import numpy as np, itertools, sys
from scipy.optimize import least_squares
H=np.array([[1,1,1],[1,-1,-1],[-1,1,-1],[-1,-1,1]],float)
rng=np.random.default_rng(int(sys.argv[1])); NST=int(sys.argv[2]); NC=int(sys.argv[3])
P4=np.array(list(itertools.permutations(range(4))))
cz=rng.normal(size=(5,3))+1j*rng.normal(size=(5,3)); w0=rng.normal(size=3)+1j*rng.normal(size=3)
def parts(Y):
    G=Y.T@Y; Sall=(G.sum()-np.trace(G))/2; out=[]
    for k in range(5):
        idx=[j for j in range(5) if j!=k]; Yk=Y[:,idx]
        e1=Yk.sum(1); p2r=(Yk**2).sum(1); p3r=(Yk**3).sum(1)
        out+=[-2*(Sall-(G[k].sum()-G[k,k])), 2*((e1**3-3*e1*p2r+2*p3r)/6).sum(), np.prod(Yk[np.arange(4)[None,:],P4],axis=1).sum()]
    return np.array(out)
def res(x):
    z=x[:15]+1j*x[15:]; y=z.reshape(5,3)
    if NC<5: y=np.vstack([y[:NC],np.zeros((5-NC,3))])
    f=y.sum(0); r=[f@f, w0@f-1]
    for j in range(NC): r.append(cz[j]@y[j]-1)
    pp=parts(H@y.T)
    if 'NOPERM' in sys.argv: pp=np.array([pp[i] for i in range(len(pp)) if i%3!=2])
    r+=list(pp)
    r=np.array(r); return np.r_[r.real,r.imag]
ok=0
for st in range(NST):
    sol=least_squares(res,rng.normal(size=30),xtol=1e-15,ftol=1e-15,gtol=1e-15,max_nfev=4000)
    nr=np.linalg.norm(res(sol.x)); ok+= nr<1e-9
    print('start %d: residual %.2e'%(st,nr),flush=True)
print('NC=%d converged %d / %d'%(NC,ok,NST))
