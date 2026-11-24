# numerical census: (2,1) strongly level 3-spaces on FIVE columns (support size), rows round 13.  cc columns, explicit P2/P3/P4.
import numpy as np, itertools, sys
from scipy.optimize import least_squares
H=np.array([[1,1,1],[1,-1,-1],[-1,1,-1],[-1,-1,1]],float)
rng=np.random.default_rng(int(sys.argv[1])); NST=int(sys.argv[2])
P4=np.array(list(itertools.permutations(range(4))))
WW=rng.normal(size=(18,3))+1j*rng.normal(size=(18,3))
def parts(Y):  # Y 4x5 complex, column-centred
    G=Y.T@Y; Sall=(G.sum()-np.trace(G))/2; out=[]
    for k in range(5):
        idx=[j for j in range(5) if j!=k]; Yk=Y[:,idx]
        p2=-2*(Sall-(G[k].sum()-G[k,k]))
        e1=Yk.sum(1); p2r=(Yk**2).sum(1); p3r=(Yk**3).sum(1)
        e3=(e1**3-3*e1*p2r+2*p3r)/6; p3=2*e3.sum()
        p4=np.prod(Yk[np.arange(4)[None,:],P4],axis=1).sum()
        out+= [p2,p3,p4]
    return np.array(out)
def build(x):
    z=x[:45]+1j*x[45:]; return [H@z[15*r:15*r+15].reshape(5,3).T for r in range(3)]
Lv=rng.normal(size=(3,15))+1j*rng.normal(size=(3,15))
def f(x):
    Ms=build(x); r=[]
    for w in WW: r.extend(parts(w[0]*Ms[0]+w[1]*Ms[1]+w[2]*Ms[2]))
    r.extend(Ms[2].sum(1))                                    # n doubly centred
    z=x[:45]+1j*x[45:]; r.extend([Lv[k]@z[15*k:15*k+15]-1 for k in range(3)])
    r=np.array(r); return np.r_[r.real,r.imag]
from collections import Counter
C=Counter()
for st in range(NST):
    sol=least_squares(f,rng.normal(size=90),xtol=1e-15,ftol=1e-15,gtol=1e-15,max_nfev=3000)
    nr=np.linalg.norm(f(sol.x))
    if nr>1e-9: C['nonconv']+=1; continue
    Ms=build(sol.x)
    cols=[int(np.linalg.matrix_rank(np.array([M[:,j] for M in Ms]),1e-6)) for j in range(5)]
    q=int(np.linalg.matrix_rank(np.array([M.sum(1) for M in Ms]),1e-6)); dK=int(np.linalg.matrix_rank(np.array([M.ravel() for M in Ms]),1e-6))
    key=(dK,q,tuple(sorted(cols,reverse=True))); C[key]+=1
    print('start %d: dim %d q %d column ranks %s support %d'%(st,dK,q,cols,sum(c>0 for c in cols)),flush=True)
    if sum(c>0 for c in cols)>=4 and q==2 and dK==3: np.save('k21five_%s_%d.npy'%(sys.argv[1],st),np.array(Ms))
print(C)
