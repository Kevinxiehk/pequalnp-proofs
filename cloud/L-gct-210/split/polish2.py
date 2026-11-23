import sys,time; sys.path.insert(0,'.')
from core import *
from math import comb
from ext2 import fresh
from rab import info
def gpolish(B,Amb,tlimit=120,maxit=500,seed=0):
    rng=np.random.default_rng(seed); B=np.asarray(B); dim=len(B); m=len(Amb)
    Af=Amb.reshape(m,-1)
    C=np.linalg.lstsq(Af.T,B.reshape(dim,-1).T,rcond=None)[0].T   # dim x m coords
    print(' projection error',np.abs(C@Af-B.reshape(dim,-1)).max())
    # chart: complete C to basis
    u,s,vh=np.linalg.svd(C); Q=np.vstack([vh[:dim],vh[dim:]])  # rows orthonormal; first dim span C
    X=np.zeros((dim,m-dim),complex)
    # C = G [I X] Q  -> choose G = C Q[:dim]^H ; X = G^{-1} C Q[dim:]^H
    G=C@Q[:dim].conj().T; X=np.linalg.solve(G,C@Q[dim:].conj().T)
    nsamp=comb(dim+4,5)+30; xs=rnd((nsamp,dim),rng); xs/=np.linalg.norm(xs,axis=1,keepdims=True)
    Am=np.einsum('pq,qab->pab',Q,Amb.astype(complex)); Cq=Am[dim:]
    def res(X,jac=True):
        Bn=np.einsum('iq,qab->iab',np.hstack([np.eye(dim),X]),Am)
        T=np.einsum('ri,iab->rab',xs,Bn)
        if not jac: return Pk(T)[:,1:].reshape(-1)
        P,G_=level.Pk_grad(T); GC=np.einsum('rkab,pab->rkp',G_[:,1:],Cq)
        J=np.einsum('ri,rkp->rkip',xs,GC); R,K=GC.shape[:2]
        return P[:,1:].reshape(-1), J.reshape(R*K,-1)
    lam=1e-3; r,J=res(X); f=np.linalg.norm(r); t0=time.time(); hist=[f]
    for it in range(maxit):
        if time.time()-t0>tlimit: break
        H=J.conj().T@J; g=J.conj().T@r
        Xn=X+np.linalg.solve(H+lam*np.diag(np.diag(H).real+1e-12),-g).reshape(X.shape)
        fn=np.linalg.norm(res(Xn,False))
        if fn<f: X=Xn; lam=max(lam/3,1e-14); r,J=res(X); f=fn; hist.append(f)
        else:
            lam*=4
            if lam>1e10: break
        if f<1e-13: break
    Bn=np.einsum('iq,qab->iab',np.hstack([np.eye(dim),X]),Am)
    sv=np.linalg.svd(J,compute_uv=False)
    return f,Bn,hist,sv
if __name__=='__main__':
    B=np.load(sys.argv[1])
    Amb=[]
    for i in (0,1,3):
        for j in range(5):
            M=np.zeros((5,5)); M[i,j]=1; Amb.append(M)
    M=np.zeros((5,5)); M[4,2]=1; M[2,2]=-1; Amb.append(M)
    f,Bn,hist,sv=gpolish(B,np.array(Amb),tlimit=float(sys.argv[2]))
    print('res history',[('%.1e'%h) for h in hist[::max(1,len(hist)//12)]], 'final %.2e'%f)
    print('fresh %.2e'%fresh(Bn), info(Bn,1e-6))
    print('Jacobian smallest sv',sv[-6:])
    np.save('cand13_rows013.npy',Bn)
