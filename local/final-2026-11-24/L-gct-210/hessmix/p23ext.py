import sys; sys.path.insert(0,'/home/kevxhk/work/L-gct-210/hessmix')
from hk import *
from scipy.optimize import least_squares
name=sys.argv[1]; m=int(sys.argv[2]); ks=tuple(int(c) for c in sys.argv[3])
rng=np.random.default_rng(5)
B=orth(examples()[name]); l=len(B)
c=rng.normal(size=(200,l))+1j*rng.normal(size=(200,l))
P,G=Pk_grad(np.einsum('rk,kij->rij',c,B))
rows=G[:,list(ks)].reshape(-1,25)@VB.T
u,s,vh=np.linalg.svd(rows); r=int((s>1e-8*s[0]).sum()); E=vh[r:].conj()  # E basis in V coords (rows), complex
LV=toV(B)
# complement of L inside E
coef=E.conj()@LV.T  # project
Pm=np.eye(len(E))-np.linalg.pinv(coef.T.conj()@np.eye(1) if False else coef.conj().T)@coef.conj().T if False else None
# simpler: orthonormal basis of E, remove span L
M=np.vstack([LV,E]); q,_=np.linalg.qr(M.T); Nb=q[:,l:len(E)].T   # complement directions (approx in E since L in E)
print(name,'dim E wrt',ks,'=',len(E),' complement',len(Nb))
def Bof(x):
    C=(x[:len(x)//2]+1j*x[len(x)//2:]).reshape(m,len(Nb)); return np.vstack([LV,C@Nb])
pts=rng.normal(size=(240,l+m))+1j*rng.normal(size=(240,l+m))
def res(x):
    BV=Bof(x); Bq=np.linalg.qr(BV.T)[0].T; T=fromV(Bq)
    Pv=Pk(np.einsum('rk,kij->rij',pts/np.linalg.norm(pts,axis=1,keepdims=True),T))[:,list(ks)]
    v=Pv.ravel(); return np.concatenate([v.real,v.imag])
best=9
for st in range(4):
    x0=rng.normal(size=2*m*len(Nb))
    r=least_squares(res,x0,method='lm',max_nfev=400)
    BV=Bof(r.x); T=fromV(np.linalg.qr(BV.T)[0].T)
    Pv=np.abs(Pk(np.einsum('rk,kij->rij',rng.normal(size=(50,l+m))+1j*rng.normal(size=(50,l+m)),T))).max(0)
    print(' start',st,'res %.1e'%np.linalg.norm(r.fun),'fresh |P_k| k=1..5:',' '.join('%.0e'%v for v in Pv[1:]), 'minsv %.2e'%sv(BV)[-1],flush=True)
