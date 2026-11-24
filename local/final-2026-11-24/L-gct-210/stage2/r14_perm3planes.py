# Census of 2-dim spaces P of 3x5 matrices on which ALL ten 3x3 subpermanents vanish identically (C4 condition for X_ri) [NOTES R14-2].
# LM on Gr(2,15): residual = the 4 coefficients (in alpha, beta) of perm3((alpha p1 + beta p2)_S) for each of the 10 column triples S,
# plus orthonormality of (p1,p2). Every converged solution is classified: column support, row support, ranks, single-column/single-row elements.
import sys, itertools, numpy as np
from scipy.optimize import least_squares
SEED=int(sys.argv[1]) if len(sys.argv)>1 else 1; NTR=int(sys.argv[2]) if len(sys.argv)>2 else 20
rg=np.random.default_rng(SEED)
P3=list(itertools.permutations(range(3))); TR=list(itertools.combinations(range(5),3))
def perm3(M): return sum(M[0,p[0]]*M[1,p[1]]*M[2,p[2]] for p in P3)
AB=[(1,0),(0,1),(1,1),(1,-1),(1,2),(2,1),(1,1j),(1,-2)]
def res(x):
    p=(x[:30]+1j*x[30:]).reshape(2,3,5); out=[]
    for (al,be) in AB:
        M=al*p[0]+be*p[1]
        for S in TR: out.append(perm3(M[:,S]))
    g=p.reshape(2,15)@p.reshape(2,15).conj().T-np.eye(2); out+=list(g.ravel())
    o=np.array(out); return np.concatenate([o.real,o.imag])
def classify(p):
    tol=1e-6; colsupp=[j for j in range(5) if np.abs(p[:,:,j]).max()>tol]; rowsupp=[i for i in range(3) if np.abs(p[:,i,:]).max()>tol]
    # single-column elements: c with c0 p0 + c1 p1 supported in one column
    sc=[]
    for j in range(5):
        mask=np.ones((3,5),bool); mask[:,j]=False; M=np.stack([p[0][mask],p[1][mask]],axis=1); sv=np.linalg.svd(M,compute_uv=False)
        sc.append(int((sv<1e-6).sum()))
    sr=[]
    for i in range(3):
        mask=np.ones((3,5),bool); mask[i,:]=False; M=np.stack([p[0][mask],p[1][mask]],axis=1); sv=np.linalg.svd(M,compute_uv=False)
        sr.append(int((sv<1e-6).sum()))
    return colsupp,rowsupp,sc,sr
stats={}
for tr in range(NTR):
    x0=rg.normal(size=60)
    s=least_squares(res,x0,method='lm',xtol=1e-15,ftol=1e-15,gtol=1e-15,max_nfev=4000)
    nr=np.linalg.norm(s.fun)
    if nr<1e-9:
        p=(s.x[:30]+1j*s.x[30:]).reshape(2,3,5); c=classify(p)
        key='cols%d rows%d sc%s sr%s'%(len(c[0]),len(c[1]),c[2],c[3])
        stats[key]=stats.get(key,0)+1
        print('trial %2d res %.0e: column support %s, row support %s, single-column dims %s, single-row dims %s'%(tr,nr,c[0],c[1],c[2],c[3]),flush=True)
    else: print('trial %2d res %.1e'%(tr,nr),flush=True)
print('SUMMARY',stats)
