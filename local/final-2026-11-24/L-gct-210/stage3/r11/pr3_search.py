# Round 11: (PR3) probe -- 3-dim 3x5 level spaces X inside (+)_{i<3} e_i (x) P_i (P_i unknown 2-planes), no single-row element (hinge HNS=1),
# then their 3-row defect = dim span{c(x), D_2(x), D_3(x)} (deletion vectors, all in 1^perp). (PR2-split') <=> no such X with defect <= 2.
import sys, itertools, numpy as np
seed,NS,HNS=int(sys.argv[1]),int(sys.argv[2]),int(sys.argv[3]); rg=np.random.default_rng(seed)
NP=60; PT=rg.normal(size=(NP,3))+1j*rg.normal(size=(NP,3))
AL=rg.normal(size=(3,5))+1j*rg.normal(size=(3,5)); BE=rg.normal(size=(3,5))+1j*rg.normal(size=(3,5))
RH=[(rg.normal(size=3)+1j*rg.normal(size=3),rg.normal(size=3)+1j*rg.normal(size=3)) for _ in range(3)]
RN=[rg.normal(size=(4,3))+1j*rg.normal(size=(4,3)) for _ in range(3)]
def coef(X):   # coefficients of prod_j (1 + sum_i t_i x_ij) over the 8 subsets of 3 rows
    N=X.shape[0]; G=np.zeros((N,8),complex); G[:,0]=1
    for j in range(X.shape[2]):
        H=G.copy()
        for i in range(3):
            mk=1<<i; idx=[S for S in range(8) if not S&mk]; H[:,[S|mk for S in idx]]+=X[:,i,j][:,None]*G[:,idx]
        G=H
    return G
DEG=np.array([bin(S).count('1') for S in range(8)])
def esig(X): G=coef(X); return np.stack([G[:,DEG==k].sum(1) for k in (1,2,3)],1)
def unpack(x):
    U=x[:15].reshape(3,5); V=x[15:30].reshape(3,5); Wm=x[30:39].reshape(3,3); Gm=np.concatenate([np.eye(3),Wm],1)
    B=np.zeros((3,3,5),complex)
    for r in range(3): B[:,r,:]=Gm[:,2*r][:,None]*U[r][None,:]+Gm[:,2*r+1][:,None]*V[r][None,:]
    return B,U,V,Gm
NX=39+3+(3 if HNS else 0)
def F(x):
    B,U,V,Gm=unpack(x); X=np.einsum('nk,kab->nab',PT,B); eq=[]
    for r in range(3): eq+=[AL[r]@U[r]-1,BE[r]@U[r],AL[r]@V[r],BE[r]@V[r]-1]
    for r in range(3):
        Gr=Gm[:,2*r:2*r+2]; a,b=RH[r]; eq.append(x[39+r]*np.linalg.det(np.array([a@Gr,b@Gr]))-1)
        if HNS:
            O=np.concatenate([Gm[:,2*s:2*s+2] for s in range(3) if s!=r],1); eq.append(x[42+r]*np.linalg.det(O@RN[r])-1)
    return np.concatenate([esig(X).ravel()/5,np.array(eq)])
def J(x,h=1e-7):
    f0=F(x); Jm=np.empty((len(f0),len(x)),complex)
    for i in range(len(x)):
        d=np.zeros(len(x),complex); d[i]=h; Jm[:,i]=(F(x+d)-f0)/h
    return f0,Jm
def lm(x,it=200):
    lam=1e-2; f,Jm=J(x); nf=np.linalg.norm(f)
    for _ in range(it):
        A=Jm.conj().T@Jm; g=Jm.conj().T@f; ok=False
        for _ in range(10):
            d=np.linalg.solve(A+lam*np.eye(len(x)),g); n2=np.linalg.norm(F(x-d))
            if n2<nf: x=x-d; lam=max(lam/4,1e-14); ok=True; break
            lam*=4
        if not ok: break
        f,Jm=J(x); nf=np.linalg.norm(f)
        if nf<1e-12: break
    return x,nf
def rank(A,tol=1e-6):
    s=np.linalg.svd(np.atleast_2d(A),compute_uv=False); return int((s>tol*max(1,s[0])).sum()) if s.size else 0
def defect(B):
    Q=rg.normal(size=(40,3))+1j*rg.normal(size=(40,3)); X=np.einsum('nk,kab->nab',Q,B); vecs=[]
    for x in X:
        for j in range(5):
            Gj=coef(np.delete(x,j,axis=1)[None])[0]; vecs.append([Gj[DEG==k].sum() for k in (1,2,3)])
    D=np.array(vecs).reshape(40,5,3).transpose(0,2,1).reshape(-1,5); return rank(D,1e-7)
res={}
for st in range(NS):
    x,nf=lm((rg.normal(size=NX)+1j*rg.normal(size=NX))*0.6)
    if nf<1e-9:
        B,U,V,Gm=unpack(x); d=len(B)
        u=[d-rank(np.array([[B[k][i,j] for k in range(d)] for i in range(3) if i!=r for j in range(5)])) for r in range(3)]
        e=defect(B); key='single-row %s defect %d'%(u,e); res[key]=res.get(key,0)+1; print('start %d res %.1e %s'%(st,nf,key),flush=True)
    else: print('start %d res %.1e'%(st,nf),flush=True)
print('SUMMARY seed %d HNS %d starts %d:'%(seed,HNS,NS),res,flush=True)
