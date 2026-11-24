# numerical census: principal strongly level PLANES on 4 columns with nondegenerate row-sum plane (reflection strata of (PL)), rows round 17
import numpy as np, itertools, sys
from scipy.optimize import least_squares
H=np.array([[1,1,1],[1,-1,-1],[-1,1,-1],[-1,-1,1]],float)
rng=np.random.default_rng(int(sys.argv[1])); NST=int(sys.argv[2]); FORCE=int(sys.argv[3])
P4=np.array(list(itertools.permutations(range(4))))
YY=rng.normal(size=(10,2))+1j*rng.normal(size=(10,2)); cz=rng.normal(size=(4,6))+1j*rng.normal(size=(4,6))
def parts(Y):
    G=Y.T@Y; Sall=(G.sum()-np.trace(G))/2; out=[]
    for k in range(5):
        idx=[j for j in range(5) if j!=k]; Yk=Y[:,idx]
        e1=Yk.sum(1); p2r=(Yk**2).sum(1); p3r=(Yk**3).sum(1)
        out+=[-2*(Sall-(G[k].sum()-G[k,k])), 2*((e1**3-3*e1*p2r+2*p3r)/6).sum(), np.prod(Yk[np.arange(4)[None,:],P4],axis=1).sum()]
    return np.array(out)
def res(x):
    z=x[:30]+1j*x[30:]; p1,p2=z[0:3],z[3:6]; b=z[6:30].reshape(4,2,3); r=[p1@p1-1,p2@p2-1,p1@p2]
    for j in range(4): r+=[b[j,0]@b[j,0]-1,b[j,1]@b[j,1]-1,b[j,0]@b[j,1]]
    r+=list(b[:,0].sum(0)-2*p1)+list(b[:,1].sum(0)-2*p2)
    r+=[z[0]-0.3-0.2j]   # gauge: kill the O(2) rotation inside P (one coordinate of p1 fixed; generic)
    if FORCE:
        for j in range(4): r+=[cz[j,:3]@(p1-b[j,0])+cz[j,3:]@(p2-b[j,1])-1]
    for y in YY:
        cols=[(y[0]*(p1-b[j,0])+y[1]*(p2-b[j,1]))/2 for j in range(4)]+[np.zeros(3)]
        Y=H@np.array(cols).T; r+=list(parts(Y))
    r=np.array(r); return np.r_[r.real,r.imag]
from collections import Counter
C=Counter()
for st in range(NST):
    sol=least_squares(res,rng.normal(size=60),xtol=1e-15,ftol=1e-15,gtol=1e-15,max_nfev=3000)
    nr=np.linalg.norm(res(sol.x)); z=sol.x[:30]+1j*sol.x[30:]
    b=z[6:30].reshape(4,2,3); p1,p2=z[0:3],z[3:6]
    nz=[np.linalg.norm(np.r_[p1-b[j,0],p2-b[j,1]])>1e-6 for j in range(4)]
    cn=[np.linalg.norm(np.r_[p1-b[j,0],p2-b[j,1]]) for j in range(4)]
    print('start %d: residual %.1e, nonzero plane columns %d, column norms %s'%(st,nr,sum(nz),np.round(cn,6)),flush=True)
    np.save('ppn_%s_%d.npy'%(sys.argv[1],st),z)
    C[(nr<1e-8,sum(nz))]+=1
print(C)
