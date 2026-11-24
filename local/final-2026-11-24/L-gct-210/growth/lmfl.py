# LM search: L (l-dim, Q-iso), F (f-dim), Q(L,F)=0, T(L,L,F)=0  <=>  dim(L + L∘L) <= 24 - f  (L iso)
import numpy as np, sys, time
sys.path.insert(0,'.')
from core import *
TT=np.zeros((24,24,24))
for a in range(24):
    for b in range(a,24):
        pr=prod(UB[a],UB[b])[0]  # u-matrix
        # T(UB a, UB b, UB c) = Q(pr, UB c)
        v=np.array([Qf(pr,UB[c])[0] for c in range(24)]).real
        TT[a,b]=v; TT[b,a]=v
def run(l,f,seed,iters=300,FFixed=None,verbose=False):
    rng=np.random.default_rng(seed)
    FrL=np.linalg.qr(rng.normal(size=(24,24))+1j*rng.normal(size=(24,24)))[0]
    FrF=np.linalg.qr(rng.normal(size=(24,24))+1j*rng.normal(size=(24,24)))[0]
    X=0.5*(rng.normal(size=(l,24-l))+1j*rng.normal(size=(l,24-l)))
    Y=0.5*(rng.normal(size=(f,24-f))+1j*rng.normal(size=(f,24-f)))
    iu=np.triu_indices(l)
    def mats(X,Y):
        L=np.hstack([np.eye(l),X])@FrL; F=np.hstack([np.eye(f),Y])@FrF; return L,F
    def res(X,Y):
        L,F=mats(X,Y)
        r1=(L@QM@L.T)[iu]; r2=(L@QM@F.T).ravel()
        r3=np.einsum('ijk,ai,bj,ck->abc',TT,L,L,F)[iu].ravel()
        return np.concatenate([r1,r2,r3])
    def jac(X,Y):
        L,F=mats(X,Y)
        nL=l*24; nF=f*24
        # derivatives wrt L entries and F entries, then chain
        QL=L@QM  # l x 24
        J1L=np.zeros((l,l,l,24),complex)
        for a in range(l):
            J1L[a,:,a,:]+=QL; J1L[:,a,a,:]+=QL
        J1L=J1L[iu].reshape(-1,nL); J1F=np.zeros((len(iu[0]),nF))
        QF=F@QM
        J2L=np.zeros((l,f,l,24),complex); J2F=np.zeros((l,f,f,24),complex)
        for a in range(l): J2L[a,:,a,:]=QF
        for c in range(f): J2F[:,c,c,:]=QL
        J2L=J2L.reshape(l*f,nL); J2F=J2F.reshape(l*f,nF)
        M1=np.einsum('ijk,bj,ck->bci',TT,L,F)  # l f 24
        J3L=np.zeros((l,l,f,l,24),complex)
        for a in range(l):
            J3L[a,:,:,a,:]+=M1; J3L[:,a,:,a,:]+=M1
        J3L=J3L[iu].reshape(-1,nL)
        M2=np.einsum('ijk,ai,bj->abk',TT,L,L)  # l l 24
        J3F=np.zeros((l,l,f,f,24),complex)
        for c in range(f): J3F[:,:,c,c,:]=M2
        J3F=J3F[iu].reshape(-1,nF)
        JL=np.vstack([J1L,J2L,J3L]); JF=np.vstack([np.zeros((J1L.shape[0],nF)),J2F,J3F])
        # chain: L = [I X] FrL -> dL[a,:] = dX[a,:] @ FrL[l:,:]
        CX=FrL[l:,:]; CY=FrF[f:,:]
        JX=np.einsum('rak,mk->ram',JL.reshape(-1,l,24),CX).reshape(JL.shape[0],-1)
        JY=np.einsum('rak,mk->ram',JF.reshape(-1,f,24),CY).reshape(JF.shape[0],-1)
        return np.hstack([JX,JY])
    mu=1e-2; r=res(X,Y); nr=np.linalg.norm(r); t0=time.time()
    for it in range(iters):
        J=jac(X,Y)
        A=J.conj().T@J; g=J.conj().T@r
        while True:
            d=-np.linalg.solve(A+mu*np.eye(len(A)),g)
            X2=X+d[:X.size].reshape(X.shape); Y2=Y+d[X.size:].reshape(Y.shape)
            r2=res(X2,Y2); n2=np.linalg.norm(r2)
            if n2<nr: X,Y,r,nr=X2,Y2,r2,n2; mu=max(mu/3,1e-12); break
            mu*=4
            if mu>1e8: break
        if mu>1e8 or nr<1e-13: break
        if time.time()-t0>40: break
    L,F=mats(X,Y)
    Lu=to_mat(L); Fu=to_mat(F)
    g=growth(Lu,1e-7)
    sL=np.linalg.svd(L,compute_uv=False); sF=np.linalg.svd(F,compute_uv=False)
    # overlap of L and F
    ov=24-rank(np.vstack([L,F]),1e-6)  # not exactly; dim(L cap F)=l+f-rank
    ov=l+f-rank(np.vstack([L,F]),1e-6)
    return nr,g,sL[-1]/sL[0],sF[-1]/sF[0],ov,it,L,F
if __name__=='__main__':
    l,f=int(sys.argv[1]),int(sys.argv[2]); seeds=range(int(sys.argv[3]),int(sys.argv[4]))
    for s in seeds:
        nr,g,cL,cF,ov,it,L,F=run(l,f,s)
        print('l=%d f=%d seed %d res %.2e growth %s condL %.1e condF %.1e dim(L cap F) %d iters %d'%(l,f,s,nr,g,cL,cF,ov,it),flush=True)
        if nr<1e-9: np.save('lmfl_%d_%d_%d.npy'%(l,f,s),np.stack([np.pad(L,((0,max(0,f-l)),(0,0))),np.pad(F,((0,max(0,l-f)),(0,0)))]))
