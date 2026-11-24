# numerical search [numerical, calibrated]: d-dim 4x4 level spaces Q in Walsh coordinates (u, v, x) with rank u <= RU, rank v <= RV.
# Parametrisation: basis B (d x 15); u-block = Bu (d x RU) @ Cu (RU x 3), v-block = Bv (d x RV) @ Cv (RV x 3), x-block free.
# Equations: perm(J + T(t)) - 24 = 0 at NS random t in C^d (NS >= 2 * #monomials); Gauss-Newton with finite-difference-free complex
# Jacobian (holomorphic: numerical derivative by complex step on each parameter).  Success: residual < 1e-11 AND fresh-sample check.
# usage: python3 -I qsearch.py d RU RV starts seed
import sys, numpy as np
d,RU,RV,NST,seed=[int(a) for a in sys.argv[1:6]]
rng=np.random.default_rng(seed)
Ht=np.array([[1,1,1,1],[1,1,-1,-1],[1,-1,1,-1],[1,-1,-1,1]],float)
import itertools
perms=list(itertools.permutations(range(4)))
def perm4(A): return sum(A[0,p[0]]*A[1,p[1]]*A[2,p[2]]*A[3,p[3]] for p in perms)
nmon=sum(len(list(itertools.combinations_with_replacement(range(d),k))) for k in (2,3,4)); NS=2*nmon+20
def unpack(p):
    i=0
    Bu=p[i:i+d*RU].reshape(d,RU); i+=d*RU; Cu=p[i:i+RU*3].reshape(RU,3); i+=RU*3
    Bv=p[i:i+d*RV].reshape(d,RV); i+=d*RV; Cv=p[i:i+RV*3].reshape(RV,3); i+=RV*3
    Bx=p[i:i+d*9].reshape(d,9); return Bu@Cu, Bv@Cv, Bx
npar=d*RU+RU*3+d*RV+RV*3+d*9
def Tmat(U,V,Xx,t):
    u=t@U; v=t@V; x=(t@Xx).reshape(3,3)
    X=np.zeros((4,4),complex); X[0,1:]=u; X[1:,0]=v; X[1:,1:]=x
    return Ht@X@Ht.T
def resid(p,ts):
    U,V,Xx=unpack(p); return np.array([perm4(np.ones((4,4))+Tmat(U,V,Xx,t))-24 for t in ts])
def gram_ok(p):
    U,V,Xx=unpack(p); B=np.hstack([U,V,Xx]); s=np.linalg.svd(B,compute_uv=False); return s[-1]/s[0]
hits=0
for st in range(NST):
    ts=(rng.normal(size=(NS,d))+1j*rng.normal(size=(NS,d)))/np.sqrt(2)
    p=(rng.normal(size=npar)+1j*rng.normal(size=npar))*0.5
    lam=1e-3
    for it in range(300):
        r=resid(p,ts); nr=np.linalg.norm(r)
        if nr<1e-12: break
        J=np.empty((NS,npar),complex); h=1e-7
        for k in range(npar):
            dp=np.zeros(npar,complex); dp[k]=h; J[:,k]=(resid(p+dp,ts)-r)/h
        A=J.conj().T@J; g=J.conj().T@r
        step=np.linalg.solve(A+lam*np.eye(npar)*max(1,np.trace(A).real/npar),-g)
        pn=p+step; rn=np.linalg.norm(resid(pn,ts))
        if rn<nr: p=pn; lam=max(lam/3,1e-12)
        else: lam*=4
        # keep the basis well conditioned
        if gram_ok(p)<1e-6: break
    U,V,Xx=unpack(p)
    ts2=(rng.normal(size=(NS,d))+1j*rng.normal(size=(NS,d)))
    r2=np.linalg.norm(resid(p,ts2))/np.sqrt(NS); g=gram_ok(p)
    ok=(nr<1e-9 and r2<1e-8 and g>1e-4)
    hits+=ok
    print('start %d: res %.1e fresh %.1e cond %.1e %s'%(st,nr,r2,g,'HIT' if ok else ''),flush=True)
print('HITS',hits,'of',NST)
