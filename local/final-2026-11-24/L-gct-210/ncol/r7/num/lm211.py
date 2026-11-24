# R2.11 sub-system, numerical: L5 = K' (+) e_0 U_0 inside a (7,3) space L'.  K' = 3-dim column-centred zero-row (row 0) space with defect in
# C t, U_0 = 2-dim, t perp U_0 (bilinear), C = U_0 + C t (3-dim, inside V5).  Conditions: R(Y) in C for Y in L5 (4x5 deletion defects),
# R(k) in C t for k in K'.  Normalisation: Gram(K') = I, Gram(U_0) = I, |t| = 1 (Hermitian).  usage: python3 -I lm211.py SEED NSTARTS [nK]
import numpy as np, itertools, sys
seed=int(sys.argv[1]); nst=int(sys.argv[2]); nK=int(sys.argv[3]) if len(sys.argv)>3 else 3
rng=np.random.default_rng(seed)
perms=list(itertools.permutations(range(4)))
def perm4(A): return sum(A[0,p[0]]*A[1,p[1]]*A[2,p[2]]*A[3,p[3]] for p in perms)
def R(Y):
    JY=1+Y; return np.array([perm4(np.delete(JY,k,axis=1))-24 for k in range(5)])
# bases: column-centred 3x5 blocks (10-dim), V5 (4-dim)
Bk=[]
for i in range(2):
    for j in range(5):
        M=np.zeros((3,5)); M[i,j]=1; M[2,j]=-1; Bk.append(M)
Bk=np.array(Bk,complex)
F=np.array([[1,-1,0,0,0],[0,1,-1,0,0],[0,0,1,-1,0],[0,0,0,1,-1]],complex)
NS=16
ptsK=[rng.normal(size=nK)+1j*rng.normal(size=nK) for _ in range(NS)]
ptsU=[rng.normal(size=2)+1j*rng.normal(size=2) for _ in range(NS)]
nKv=nK*10; nUv=8; nT=4; nvar=2*(nKv+nUv+nT)
def unpack(x):
    z=x[:nvar//2]+1j*x[nvar//2:]
    K=z[:nKv].reshape(nK,10); U=z[nKv:nKv+nUv].reshape(2,4); T=z[nKv+nUv:]
    return K,U,T
def perp(v,Bas):     # component of v orthogonal (bilinear-free: use least squares in C^5) to span(Bas)
    c,*_=np.linalg.lstsq(Bas.T,v,rcond=None); return v-Bas.T@c
def resid(x):
    K,U,T=unpack(x); Kb=np.tensordot(K,Bk,axes=(1,0)); Ub=U@F; t=T@F
    Cb=np.vstack([Ub,t])
    out=[]
    for ck,cu in zip(ptsK,ptsU):
        k=np.tensordot(ck,Kb,axes=(0,0)); u=cu@Ub
        Y=np.zeros((4,5),complex); Y[1:]=k; Y[0]=u
        out+=list(perp(R(Y),Cb))
        Yk=np.zeros((4,5),complex); Yk[1:]=k
        out+=list(perp(R(Yk),t[None,:]))
    out+=list(Ub@t)                                   # t perp U_0 (bilinear)
    out+=list((K@K.conj().T-np.eye(nK)).ravel()); out+=list((U@U.conj().T-np.eye(2)).ravel()); out.append(T@T.conj()-1)
    out=np.array(out); return np.concatenate([out.real,out.imag])
def jac(x,f0,h=1e-7):
    J=np.zeros((len(f0),len(x)))
    for i in range(len(x)):
        xp=x.copy(); xp[i]+=h; J[:,i]=(resid(xp)-f0)/h
    return J
best=[]
for st in range(nst):
    x=rng.normal(size=nvar)*0.5; lam=1e-2; f=resid(x); c=f@f
    for it in range(120):
        J=jac(x,f); g=J.T@f; H=J.T@J
        while True:
            dx=np.linalg.solve(H+lam*np.diag(np.diag(H)+1e-12),-g); xn=x+dx; fn=resid(xn); cn=fn@fn
            if cn<c: x,f,c=xn,fn,cn; lam=max(lam/3,1e-12); break
            lam*=4
            if lam>1e8: break
        if lam>1e8 or c<1e-26: break
    best.append(c); print('start %d: residual %.3e after %d its'%(st,c,it),flush=True)
    if c<1e-20: np.save('sol211_s%d_%d.npy'%(seed,st),x)
print('min residual',min(best))
