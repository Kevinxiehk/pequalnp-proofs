import sys; sys.path.insert(0,'.')
from seed13 import *
from math import comb
import time
rng=np.random.default_rng(0)
L=np.load('d1_ext1.npy'); Lf=L.reshape(len(L),-1); Q,_=np.linalg.qr(Lf.T); O=Q.T.reshape(len(L),5,5)
D=rde(L,1e-6)['D'][0]
c=rnd((2,len(L)),rng); S=np.concatenate([D[None],np.einsum('qk,kij->qij',c,O)])   # same S as seed13d (seed 0)
E=ext_space(S); C=complement(S,E); m=len(C)
L4=np.load('L4_near.npy'); y0=L4[3].reshape(-1)
# coordinates of y0 in S + C : y0 = S-part + C^T x
A=np.vstack([S.reshape(3,-1),C]); coef=np.linalg.lstsq(A.T,y0,rcond=None)[0]; x0=coef[3:]
print('y0 in span(S,C) err',np.abs(A.T@coef-y0).max())
cS,alS,beS,gS=decomp(S); Pa,_=np.linalg.qr(alS[1:].T)  # orthonormal basis of alpha(S) (2-dim)  [delta has alpha 0]
cC,alC,beC,gC=decomp(C.reshape(m,5,5))
# n_alpha: unit vector in sum-zero space, hermitian-orthogonal to alpha(S)
v=alC.T@x0; v=v-Pa@(Pa.conj().T@v); v=v-v.mean(); n=v/np.linalg.norm(v)
lin=alC@n.conj()   # functional x -> <n, alpha_y> = sum_q x_q <n, alpha(C_q)>  (hermitian inner product)
print('current eta',lin@x0)
xs=rnd((comb(4+4,5)+20,4),rng); xs/=np.linalg.norm(xs,axis=1,keepdims=True)
def solve(eta,x_init,tl=25):
    m0=x_init.conj()/np.vdot(x_init,x_init)  # normalisation m0.x = 1
    Cons=np.vstack([lin,m0]); rhs=np.array([eta,1.0])
    xp=np.linalg.lstsq(Cons,rhs,rcond=None)[0]; u,s,vh=np.linalg.svd(Cons); N=vh[2:].T
    z=np.linalg.lstsq(N,x_init-xp,rcond=None)[0]
    def res(z,jac=True):
        x=xp+N@z; y=(C.T@x).reshape(5,5); B=np.concatenate([S,y[None]]); T=np.einsum('ri,iab->rab',xs,B)
        if not jac: return Pk(T)[:,1:].reshape(-1)
        P,G=level.Pk_grad(T); dy=(C.T@N).T.reshape(-1,5,5)
        J=np.einsum('rkab,pab->rkp',G[:,1:],dy)*xs[:,3][:,None,None]
        return P[:,1:].reshape(-1), J.reshape(-1,N.shape[1])
    lam=1e-3; r,J=res(z); f=np.linalg.norm(r); t0=time.time()
    while time.time()-t0<tl:
        H=J.conj().T@J; g=J.conj().T@r
        zn=z+np.linalg.solve(H+lam*np.diag(np.diag(H).real+1e-14),-g); fn=np.linalg.norm(res(zn,False))
        if fn<f: z=zn; f=fn; lam=max(lam/3,1e-14); r,J=res(z)
        else:
            lam*=4
            if lam>1e10: break
        if f<1e-13: break
    return f,xp+N@z
x=x0.copy(); eta0=lin@x0
for fac in [1]:
    eta=eta0*fac
    f,x=solve(eta,x)
    y=(C.T@x).reshape(5,5); B=np.concatenate([S,y[None]])
    Bf=B.reshape(4,-1); Qb,_=np.linalg.qr(Bf.T); Ob=Qb.T.reshape(4,5,5); cc,al,be,g=decomp(Ob)
    print('eta x%5d |eta| %.2e  res %.2e  sv alpha'%(fac,abs(eta),f), np.linalg.svd(al,compute_uv=False).round(6),flush=True)
    np.save('L4_curve_%d.npy'%fac,B)
