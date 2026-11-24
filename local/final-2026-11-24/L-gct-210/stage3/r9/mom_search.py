# Round 9: completeness check of the C1/C3 classification. Unknowns y_a..y_d, p, w (complex). Equations: level of the twisted free
# column N (eps(Y_T)=0 |T|>=2, eps(Y_T P)=0 |T|>=1, eps(Y_T W)=0 all T, s(y_r)=s, s(p)=-s) with s = 1 (or s = 0 + normalisation),
# (Y4) all 4x4 subperms of [y_a..y_d] = 0, (YU) all 4x4 subperms of [y_T; u], u in {w, p}. Normalisation <r1,w> = 1, gauge <r2,p> = 0.
# usage: python3 -I mom_search.py SEED NSTARTS S
import numpy as np, itertools, sys
seed,NS,S=int(sys.argv[1]),int(sys.argv[2]),int(sys.argv[3]); rg=np.random.default_rng(seed)
def perm(A):
    n=A.shape[0]
    if n==0: return 1.0+0j
    tot=0
    for P in itertools.permutations(range(n)): tot=tot+np.prod(A[np.arange(n),list(P)])
    return tot
def eps(rows):   # sum of all k x k subpermanents of the k x 5 matrix
    k=len(rows); A=np.array(rows); return sum(perm(A[:,list(C)]) for C in itertools.combinations(range(5),k))
def sub(rows):
    A=np.array(rows); return [perm(A[:,list(C)]) for C in itertools.combinations(range(5),4)]
RHO=[rg.normal(size=5)+1j*rg.normal(size=5) for _ in range(6)]
r1=rg.normal(size=5)+1j*rg.normal(size=5); r2=rg.normal(size=5)+1j*rg.normal(size=5); r3=rg.normal(size=5)+1j*rg.normal(size=5)
def F(x):
    y=x[:20].reshape(4,5); p=x[20:25]; w=x[25:30]; out=[]
    sv=S
    for r in range(4): out.append(y[r].sum()-sv)
    out.append(p.sum()+sv); out.append(w.sum())
    for k in range(2,5):
        for T in itertools.combinations(range(4),k): out.append(eps([y[i] for i in T]))
    for k in range(1,5):
        for T in itertools.combinations(range(4),k):
            out.append(eps([y[i] for i in T]+[p])); out.append(eps([y[i] for i in T]+[w]))
    out+=sub(list(y))
    for T in itertools.combinations(range(4),3):
        for u in (w,p): out+=sub([y[i] for i in T]+[u])
    out.append(r1@w-1); out.append(r2@p)
    if S==0: out.append(r3@y[0]-1)          # scale normalisation when s = 0
    tau=x[30:35]                              # Rabinowitsch: y_r != 0 (r = a..d) and (w, p) independent
    for r in range(4): out.append(tau[r]*(RHO[r]@y[r])-1)
    out.append(tau[4]*((RHO[4]@w)*(RHO[5]@p)-(RHO[5]@w)*(RHO[4]@p))-1)
    return np.array(out)
def J(x,h=1e-7):
    f0=F(x); Jm=np.empty((len(f0),len(x)),complex)
    for i in range(len(x)):
        d=np.zeros(len(x),complex); d[i]=h; Jm[:,i]=(F(x+d)-f0)/h
    return f0,Jm
def lm(x,it=150):
    lam=1e-2; f,Jm=J(x); nf=np.linalg.norm(f)
    for _ in range(it):
        A=Jm.conj().T@Jm; g=Jm.conj().T@f; ok=False
        for _ in range(10):
            d=np.linalg.solve(A+lam*np.eye(len(x)),g); f2=F(x-d); n2=np.linalg.norm(f2)
            if n2<nf: x=x-d; lam=max(lam/4,1e-14); ok=True; break
            lam*=4
        if not ok: break
        f,Jm=J(x); nf=np.linalg.norm(f)
        if nf<1e-13: break
    return x,nf
def classify(x):
    y=x[:20].reshape(4,5); p=x[20:25]; w=x[25:30]; tol=1e-6
    nz=(np.abs(y)>tol).sum(axis=0)                     # nonzero y-coordinates per column
    ones=[j for j in range(5) if np.allclose(y[:,j],1,atol=1e-6)]
    par=np.linalg.matrix_rank(y,1e-6)
    return 'cols(#nonzero y-coords)=%s  all-ones columns=%s  rank(Y)=%d  |w| supp=%d'%(sorted(nz.tolist()),ones,par,(np.abs(w)>tol).sum())
sols={}; fl=[]
for st in range(NS):
    x0=(rg.normal(size=35)+1j*rg.normal(size=35))*0.6
    x,nf=lm(x0); fl.append(nf)
    if nf<1e-10:
        k=classify(x); sols[k]=sols.get(k,0)+1
    print('start',st,'residual %.2e'%nf,classify(x) if nf<1e-10 else '','max|tau| %.1e'%np.abs(x[30:35]).max(),flush=True)
print('seed',seed,'S',S,'starts',NS,'converged',sum(sols.values()),'residual quantiles',np.round(np.quantile(fl,[0,.25,.5]),5))
for k,v in sorted(sols.items(),key=lambda t:-t[1]): print('  %3d  %s'%(v,k))
