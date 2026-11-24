# [numerical, calibrated] d-dim 4x4 level spaces in Walsh coordinates with rank u <= RU, rank v <= RV (u = column-sum, v = row-sum data).
# Basis rows: u = Bu Cu, v = Bv Cv, x = Bx.  Equations perm(J + T(t)) = 24 at NS random t; LM with ANALYTIC Jacobian
# (permanental cofactors), basis re-orthonormalised every step (left GL_d action, which preserves the factorisation).
# usage: python3 -I qsearch2.py d RU RV starts seed [iters]
import sys, itertools, numpy as np
d,RU,RV,NST,seed=[int(a) for a in sys.argv[1:6]]; ITS=int(sys.argv[6]) if len(sys.argv)>6 else 400
rng=np.random.default_rng(seed)
Ht=np.array([[1,1,1,1],[1,1,-1,-1],[1,-1,1,-1],[1,-1,-1,1]],float)
perms=list(itertools.permutations(range(4)))
def perm4(A): return sum(A[0,p[0]]*A[1,p[1]]*A[2,p[2]]*A[3,p[3]] for p in perms)
def pcof(A):
    C=np.zeros((4,4),complex)
    for p in perms:
        pr=[A[i,p[i]] for i in range(4)]
        for i in range(4):
            q=1
            for k in range(4):
                if k!=i: q*=pr[k]
            C[i,p[i]]+=q
    return C
nmon=sum(len(list(itertools.combinations_with_replacement(range(d),k))) for k in (2,3,4)); NS=2*nmon+20
def split(p):
    i=0; out=[]
    for shp in ((d,RU),(RU,3),(d,RV),(RV,3),(d,9)):
        n=shp[0]*shp[1]; out.append(p[i:i+n].reshape(shp)); i+=n
    return out
def join(parts): return np.concatenate([q.ravel() for q in parts])
def eval_all(p,ts,jac=True):
    Bu,Cu,Bv,Cv,Bx=split(p); r=np.empty(len(ts),complex); J=np.zeros((len(ts),len(p)),complex) if jac else None
    for s,t in enumerate(ts):
        tu=t@Bu; tv=t@Bv; u=tu@Cu; v=tv@Cv; x=t@Bx
        X=np.zeros((4,4),complex); X[0,1:]=u; X[1:,0]=v; X[1:,1:]=x.reshape(3,3)
        A=np.ones((4,4))+Ht@X@Ht.T; r[s]=perm4(A)-24
        if jac:
            G=Ht.T@pcof(A)@Ht   # df/dX
            gu=G[0,1:]; gv=G[1:,0]; gx=G[1:,1:].ravel()
            dBu=np.outer(t,Cu@gu); dCu=np.outer(tu,gu); dBv=np.outer(t,Cv@gv); dCv=np.outer(tv,gv); dBx=np.outer(t,gx)
            J[s]=join([dBu,dCu,dBv,dCv,dBx])
    return r,J
def renorm(p):
    Bu,Cu,Bv,Cv,Bx=split(p)
    for C,Bm in ((Cu,Bu),(Cv,Bv)):
        nrm=np.linalg.norm(C,axis=1); C/=nrm[:,None]; Bm*=nrm[None,:]
    Bfull=np.hstack([Bu@Cu,Bv@Cv,Bx]); U_,S,Vh=np.linalg.svd(Bfull,full_matrices=False)
    G=np.diag(1/S)@U_.conj().T
    return join([G@Bu,Cu,G@Bv,Cv,G@Bx]), S[-1]/S[0]
hits=0
for st in range(NST):
    ts=(rng.normal(size=(NS,d))+1j*rng.normal(size=(NS,d)))/np.sqrt(2)
    npar=d*RU+RU*3+d*RV+RV*3+d*9
    p=rng.normal(size=npar)+1j*rng.normal(size=npar); p,_=renorm(p); lam=1e-2
    for it in range(ITS):
        r,J=eval_all(p,ts); nr=np.linalg.norm(r)
        if nr<1e-13: break
        A=J.conj().T@J; g=J.conj().T@r
        step=np.linalg.lstsq(A+lam*np.eye(len(p))*(np.trace(A).real/len(p)),-g,rcond=None)[0]
        pn,cond=renorm(p+step); rn=np.linalg.norm(eval_all(pn,ts,False)[0])
        if rn<nr: p=pn; lam=max(lam/3,1e-14)
        else: lam*=5
        if lam>1e10: lam=1e-2; p=p+0.05*(rng.normal(size=len(p))+1j*rng.normal(size=len(p))); p,_=renorm(p)
    ts2=rng.normal(size=(NS,d))+1j*rng.normal(size=(NS,d))
    r2=np.linalg.norm(eval_all(p,ts2,False)[0])/np.sqrt(NS); p,cond=renorm(p)
    ok=(nr<1e-10 and r2<1e-9 and cond>1e-6); hits+=ok
    print('start %d: it %d res %.1e fresh %.1e cond %.1e %s'%(st,it,nr,r2,cond,'HIT' if ok else ''),flush=True)
print('HITS',hits,'of',NST)
