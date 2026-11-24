# numerics: 3x4 level space span(e_1 d', e_2 d', y), sum of the rows of y = -(d' o d'), d' zero-sum isotropic; MODE ka1 | ka0 (calibration: rows of y sum to 0)
import numpy as np, itertools, sys
seed,NS,MODE=int(sys.argv[1]),int(sys.argv[2]),sys.argv[3]; rg=np.random.default_rng(seed)
def sig(M,m,cols):
    tot=0
    for R in itertools.combinations(range(M.shape[0]),m):
        for C in itertools.permutations(cols,m): tot=tot+np.prod([M[R[k],C[k]] for k in range(m)])
    return tot
S=rg.normal(size=(10,3))+1j*rg.normal(size=(10,3))
def build(x):
    d=np.r_[1,x[0],x[1],-1-x[0]-x[1]]; r0=x[2:6]; r1=x[6:10]; r2=-r0-r1-(d*d if MODE=='ka1' else 0); return d,r0,r1,r2
def F(x):
    d,r0,r1,r2=build(x); out=[d@d]
    for al,c1,c2 in S:
        X=np.array([al*r0,al*r1+c1*d,al*r2+c2*d]); out+=[sig(X,m,range(4)) for m in (1,2,3)]
    out.append(x[10]*(np.array([0.3,-0.5,0.8,0.2])@r0+np.array([0.1,0.9,-0.4,0.6])@r1)-1)   # y not in span(e_1 d', e_2 d') (generic hinge)
    return np.array(out)
NV=11
def lm(x,it=200):
    lam=1e-2
    for _ in range(it):
        f=F(x); nf=np.linalg.norm(f)
        if nf<1e-12: break
        Jm=np.array([(F(x+1e-7*np.eye(NV)[i])-f)/1e-7 for i in range(NV)]).T
        A=Jm.conj().T@Jm; g=Jm.conj().T@f; ok=False
        for _ in range(10):
            dx=np.linalg.solve(A+lam*np.eye(NV),g)
            if np.linalg.norm(F(x-dx))<nf: x=x-dx; lam=max(lam/4,1e-15); ok=True; break
            lam*=4
        if not ok: break
    return x,np.linalg.norm(F(x))
for st in range(NS):
    x,nf=lm(rg.normal(size=NV)+1j*rg.normal(size=NV)); d,r0,r1,r2=build(x)
    print('start %d res %.1e |r0| %.2e'%(st,nf,np.abs(r0).max()),flush=True)
