# variable-projection LM: minimize dist of [L; L∘L] to a rank-m subspace, L Q-isotropic (l-dim)
import numpy as np, sys, time
sys.path.insert(0,'.')
from core import *
PT=np.zeros((24,24,24))
for i in range(24):
    for j in range(i,24):
        v=to_coords(prod(UB[i],UB[j]))[0].real; PT[i,j]=v; PT[j,i]=v
iu=None
def run(l,m,L0=None,seed=0,tlim=60,wq=1.0):
    global iu
    rng=np.random.default_rng(seed); iu=np.triu_indices(l)
    if L0 is None: L0=to_coords(rand_iso(l,rng))
    Fr=np.linalg.qr(rng.normal(size=(24,24))+1j*rng.normal(size=(24,24)))[0]
    # chart: L = [I X] Fr ; initial X from L0: L0 = A [I X] Fr -> L0 Fr^H = A [I X]
    M=L0@Fr.conj().T; A=M[:,:l]; X=np.linalg.solve(A,M[:,l:])
    def Lof(X): return np.hstack([np.eye(l),X])@Fr
    def N(L): 
        P=np.einsum('ijk,ai,bj->abk',PT,L,L)[iu]
        return np.vstack([L,P])
    def res(X,Up):
        L=Lof(X); r1=wq*(L@QM@L.T)[iu]; r2=(N(L)@Up.conj()).ravel()
        return np.concatenate([r1,r2])
    def Uperp(X):
        u,s,vh=np.linalg.svd(N(Lof(X))); return vh[m:].T  # 24 x (24-m), columns = complement (Hermitian)
    def jac(X,Up):
        L=Lof(X); nL=l*24
        QL=L@QM
        J1=np.zeros((l,l,l,24),complex)
        for a in range(l): J1[a,:,a,:]+=QL; J1[:,a,a,:]+=QL
        J1=wq*J1[iu].reshape(-1,nL)
        # N rows: L rows then products
        JN1=np.zeros((l,24-m,l,24),complex)
        for a in range(l): JN1[a,:,a,:]=Up.conj().T
        JN1=JN1.reshape(-1,nL)
        M1=np.einsum('ijk,bj,kc->bic',PT,L,Up.conj())  # b,i,c : d(L_a∘L_b . Up_c)/dL_a,i
        JP=np.zeros((l,l,24-m,l,24),complex)
        for a in range(l):
            JP[a,:,:,a,:]+=M1.transpose(0,2,1); JP[:,a,:,a,:]+=M1.transpose(0,2,1)
        JP=JP[iu].reshape(-1,nL)
        J=np.vstack([J1,JN1,JP])
        CX=Fr[l:,:]
        return np.einsum('rak,mk->ram',J.reshape(-1,l,24),CX).reshape(J.shape[0],-1)
    Up=Uperp(X); r=res(X,Up); nr=np.linalg.norm(r); mu=1e-3; t0=time.time(); it=0
    while time.time()-t0<tlim:
        it+=1
        J=jac(X,Up); A_=J.conj().T@J; g=J.conj().T@r
        improved=False
        for _ in range(30):
            d=-np.linalg.solve(A_+mu*np.eye(len(A_)),g)
            X2=X+d.reshape(X.shape); Up2=Uperp(X2); r2=res(X2,Up2); n2=np.linalg.norm(r2)
            if n2<nr: X,Up,r,nr=X2,Up2,r2,n2; mu=max(mu/3,1e-14); improved=True; break
            mu*=5
        if not improved or nr<1e-12: break
    L=Lof(X); Lu=to_mat(L)
    sv=np.linalg.svd(N(L)/np.linalg.norm(L,axis=1).max()**2,compute_uv=False)
    return nr,Lu,sv,it
if __name__=='__main__':
    l,m=int(sys.argv[1]),int(sys.argv[2]); s0,s1=int(sys.argv[3]),int(sys.argv[4]); tl=float(sys.argv[5])
    for s in range(s0,s1):
        nr,Lu,sv,it=run(l,m,seed=s,tlim=tl)
        q,t=checkP23(orth(Lu))
        print('l=%d m=%d seed %d res %.2e it %d |Q| %.1e |T| %.1e growth %s sv[m-2:m+3] %s'%(l,m,s,nr,it,q,t,growth(orth(Lu),1e-7),np.array2string(sv[m-2:m+3],precision=2)),flush=True)
        if nr<1e-9: np.save('ming_%d_%d_%d.npy'%(l,m,s),Lu)
